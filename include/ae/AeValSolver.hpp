#ifndef AEVALSOLVER__HPP__
#define AEVALSOLVER__HPP__
#include <assert.h>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{

  /** engine to solve validity of \forall-\exists formulas and synthesize Skolem relation */

  Expr mixQE(Expr s, Expr constVar, ExprMap &substsMap, ZSolver<EZ3>::Model &m);
  Expr static createQuantifiedFormulaRestr (Expr def, Expr a, bool forall);
  Expr multTrans(Expr t, Expr constVar);
  Expr singleExprNormPrep(Expr t, Expr constVar, bool isInt = false);

  class AeValSolver {
  private:

    Expr s;
    Expr t;
    ExprSet v; // existentially quantified vars
    ExprVector sVars;
    ExprVector stVars;

    ExprSet tConjs;
    ExprSet usedConjs;
    ExprMap defMap;
    ExprMap cyclicDefs;
    ExprMap modelInvalid;
    ExprMap separateSkols;

    ExprFactory &efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;

    unsigned partitioning_size;
    ExprVector projections;
    ExprVector instantiations;
    vector<ExprMap> skolMaps;
    vector<ExprMap> someEvals;
    ExprSet sensitiveVars; // for compaction
    set<int> bestIndexes; // for compaction
    map<Expr, ExprVector> skolemConstraints;
    bool skol;
    bool debug;
    unsigned fresh_var_ind;

  public:

    AeValSolver (Expr _s, Expr _t, ExprSet &_v, bool _debug, bool _skol) :
      s(_s), t(_t), v(_v),
      efac(s->getFactory()),
      z3(efac),
      smt (z3),
      u(efac),
      fresh_var_ind(0),
      partitioning_size(0),
      skol(_skol),
      debug(_debug)
    {
      filter (s, bind::IsConst (), back_inserter (sVars));
      filter (boolop::land(s,t), bind::IsConst (), back_inserter (stVars));
      getConj(t, tConjs);

      for (auto &exp: v) {
        if (!bind::isBoolConst(exp)) continue;
        Expr definition = getBoolDefinitionFormulaFromT(exp);
        if (definition != NULL) defMap[exp] = u.simplifyITE(definition);
      }

      for (auto &exp: v) {
        if (defMap[exp] != NULL) continue;
        Expr definition = getDefinitionFormulaFromT(exp);
        if (definition != NULL) defMap[exp] = u.simplifyITE(definition);
      }

      splitDefs(defMap, cyclicDefs);
    }

    void splitDefs (ExprMap &m1, ExprMap &m2, int curCnt = 0)
    {
      ExprMap m3;
      ExprMap m4;
      for (auto & a : m1)
      {
        if (a.second == NULL) continue;
        if (emptyIntersect(a.second, v))
        {
          m3.insert(a);
        }
        else
        {
          m4.insert(a);
        }
      }
      if (m3.size() == curCnt)
      {
        m2 = m4;
        return;
      }

      for (auto & a : m3)
      {
        for (auto & b : m1)
        {
          if (b.second == NULL) continue;
          if (a.first != b.first)
          {
            b.second = replaceAll(b.second, a.first, a.second);
          }
        }
      }
      splitDefs(m1, m2, m3.size());
    }

    /**
     * Decide validity of \forall s => \exists v . t
     */
    boost::tribool solve ()
    {
      smt.reset();
      smt.assertExpr (s);

      if (!smt.solve ()) {
        if (debug) outs () << "The S-part is unsatisfiable;\nFormula is trivially valid\n";
        return false;
      } else {
        ZSolver<EZ3>::Model m = smt.getModel();

        for (auto &e: sVars)
          // keep a model in case the formula is invalid
          modelInvalid[e] = m.eval(e);
      }

      if (v.size () == 0)
      {
        smt.assertExpr (boolop::lneg (t));
        boost::tribool res = smt.solve ();
        return res;
      }

      smt.push ();
      smt.assertExpr (t);

      boost::tribool res = true;

      while (smt.solve ())
      {
        outs().flush ();

        ZSolver<EZ3>::Model m = smt.getModel();

        if (debug && false)
        // if (true) //outTest
        {
          outs() << "\nmodel " << partitioning_size << ":\n";
          for (auto &exp: stVars)
          {
            if (exp != m.eval(exp))
              outs() << "[" << *exp << "=" << *m.eval(exp) << "],";
          }
          outs() <<"\n";
        }

        getMBPandSkolem(m);
        smt.pop();
        smt.assertExpr(boolop::lneg(projections.back()));
        if (!smt.solve()) {
          res = false; break;
        } else {
          // keep a model in case the formula is invalid
          m = smt.getModel();
          for (auto &e: sVars)
            modelInvalid[e] = m.eval(e);
        }

        smt.push();
        smt.assertExpr (t);
      }
      return res;
    }

    Expr getTrueLiterals(Expr ex, ZSolver<EZ3>::Model &m)
    {
      ExprVector ites;
      getITEs(ex, ites);
      if (ites.empty())
      {
        ExprSet tmp;
        // outs() << "Before calling getLiterals(ex, tmp)" << *ex << endl; //outTest
        getLiterals(ex, tmp);

        for (auto it = tmp.begin(); it != tmp.end(); ){
          if (isOpX<TRUE>(m.eval(*it))) ++it;
          else it = tmp.erase(it);
        }
        // outs() << "After calling getLiterals(ex, tmp): " << conjoin(tmp, efac) << endl; //outTest
        return conjoin(tmp, efac);
      }
      else
      {
        // eliminate ITEs first
        for (auto it = ites.begin(); it != ites.end();)
        {
          if (isOpX<TRUE>(m((*it)->left())))
          {
            ex = replaceAll(ex, *it, (*it)->right());
            ex = mk<AND>(ex, (*it)->left());
          }
          else if (isOpX<FALSE>(m((*it)->left())))
          {
            ex = replaceAll(ex, *it, (*it)->last());
            ex = mk<AND>(ex, mkNeg((*it)->left()));
          }
          else
          {
            ex = replaceAll(ex, *it, (*it)->right()); // TODO
            ex = mk<AND>(ex, mk<EQ>((*it)->right(), (*it)->last()));
          }
          it = ites.erase(it);
        }
        return getTrueLiterals(ex, m);
      }
    }

    void lastSanityCheck()
    {
      ExprVector args;
      for (auto temp : v) args.push_back(temp->last());
      args.push_back(mk<IMPL>(s, t));
      Expr sImpT =  mknary<EXISTS>(args);
      Expr disjProj = mk<IMPL>(s, disjoin(projections, efac));
      // outs() << "\nDisjunctions of projections: " << *disjProj << "\n";
      // outs() << "exists v. s => t: " << sImpT << endl; //outTest
      u.print(disjProj);
      outs () << "\n\n";
      // u.print(sImpT);
      // outs () << "\n\n";
      SMTUtils u1(t->getFactory());
      outs() << "'exists v. s => t' isEquiv to 'disjunctions of projections': ";
      outs () << u1.implies(disjProj, sImpT);
      outs () << u1.implies(sImpT, disjProj) << "\n\n\n\n";
    }

    /**
     * Extract MBP and local Skolem
     */
    void getMBPandSkolem(ZSolver<EZ3>::Model &m)
    {
      Expr pr = t, tempPr = t;
      ExprMap substsMap;
      ExprMap modelMap;
      // outs() << "Before MBP, pr: " << *pr << endl; //outTest
      for (auto & exp : v)
      {
        ExprMap map;
        tempPr = z3_qe_model_project_skolem (z3, m, exp, tempPr, map);
        // outs() << "before mixQEMethod pr: " << pr << endl; // outTest
        pr = simplifyArithm(mixQE(getTrueLiterals(pr, m), exp, substsMap, m));
        // outs() << "after mixQEMethod pr: " << pr << endl; //outTest
        if (m.eval(exp) != exp) modelMap[exp] = mk<EQ>(exp, m.eval(exp));
        // if (skol) getLocalSkolems(m, exp, map, substsMap, modelMap, pr);
      }

      if (debug) assert(emptyIntersect(pr, v));

      someEvals.push_back(modelMap);
      skolMaps.push_back(substsMap);
      projections.push_back(pr);
      // outs() << "current MBP: " << pr << "\n";  //outTest
      // outs() << "z3_qe_model_project_skolem output: " << tempPr << "\n"; //outTest
      if (true)
      {
        SMTUtils u1(t->getFactory());
        outs () << "Sanity MBP (1): " << isOpX<TRUE>(m.eval(pr)) << "\n";
        ExprVector args;
        for (auto temp : v) args.push_back(temp->last());
        args.push_back(t);
        outs () << "Sanity MBP (2): " << (bool)u1.implies(pr, mknary<EXISTS>(args)) << "\n";
        outs() << "Checking implications: \n";
        outs() << "cur MBP => z3_qe_model_project_skolem: " << u1.implies(pr, tempPr) << endl;
        outs() << "z3_qe_model_project_skolem => cur MBP: " << u1.implies(tempPr, pr) << endl;
      }
      partitioning_size++;
    }

    void fillSubsts (Expr ef, Expr es, Expr mbp, ExprSet& substs)
    {
      if (!sameBoolOrCmp(ef, es))
      {
        substs.insert(mk<EQ>(ineqNegReverter(ef), ineqNegReverter(es)));
      }
      else if (isOpX<FALSE>(es))
      {
        // useless (just for optim)
      }
      else if (isOpX<TRUE>(es) || u.implies(mbp, es))
      {
        substs.insert(ineqNegReverter(ef));
      }
      else
      {
        substs.insert(mk<IMPL>(ineqNegReverter(es), ineqNegReverter(ef)));
      }
    }

    /**
     * Compute local skolems based on the model
     */
    void getLocalSkolems(ZSolver<EZ3>::Model &m, Expr exp,
                           ExprMap &map, ExprMap &substsMap, ExprMap &modelMap, Expr& mbp)
    {
      if (map.size() > 0){
        ExprSet substs;
        for (auto &e: map) fillSubsts(e.first, e.second, mbp, substs);
        if (substs.size() == 0)
        {
          if (debug) outs() << "WARNING: subst is empty for " << *exp << "\n";
        }
        else
        {
          substsMap[exp] = conjoin(substs, efac);
        }
      }
      if (m.eval(exp) != exp){
        modelMap[exp] = mk<EQ>(exp, m.eval(exp));
      }
    }

    bool sameBoolOrCmp (Expr ef, Expr es)
    {
      return (isOp<BoolOp>(ef) && isOp<BoolOp>(es)) ||
         (isOp<ComparissonOp>(ef) && isOp<ComparissonOp>(es)) ||
         (isOp<BoolOp>(ef) && isOp<ComparissonOp>(es)) ||
         (isOp<ComparissonOp>(ef) && isOp<BoolOp>(es));
    }

    /**
     * Valid Subset of S (if overall AE-formula is invalid)
     */
    Expr getValidSubset(bool compact)
    {
      if (partitioning_size == 0){
        if (debug) outs() << "WARNING: Trivial valid subset (equal to False) due to 0 iterations\n";
        return mk<FALSE>(efac);
      }

      Expr prs;
      if (compact)
      {
        ExprSet all;
        vector<ExprSet> pprs;

        for (auto & a : projections)
        {
          ExprSet tmp;
          getConj(a, tmp);
          pprs.push_back(tmp);
          all.insert(tmp.begin(), tmp.end());
        }

        ExprSet common;

        for (auto & a : all)
        {
          bool everywhere = true;
          vector<ExprSet> pprsTmp = pprs;
          for (auto & p : pprsTmp)
          {
            bool found = false;
            for (auto it = p.begin(); it != p.end(); ++it)
            {
              if (*it == a) {
                found = true;
                p.erase(it);
                break;
              }
            }
            if (!found)
            {
              everywhere = false;
              break;
            }
          }
          if (everywhere)
          {
            pprs = pprsTmp;
            common.insert(a);
          }
        }

        ExprSet cnjs;
        for (auto & p : pprs) cnjs.insert(conjoin(p, efac));

        if (!cnjs.empty()) common.insert(simplifyBool(disjoin(cnjs, efac)));
        prs = conjoin(common, efac);
      }
      else
      {
        prs = disjoin(projections, efac);
      }
      if (isOpX<TRUE>(s)) return prs;
      return mk<AND>(s, prs);
    }

    /**
     * Model of S /\ \neg T (if AE-formula is invalid)
     */
    void printModelNeg()
    {
      outs () << "(model\n";
      Expr s_witn = s;
      Expr t_witn = t;
      for (auto &var : sVars){
        Expr assnmt = var == modelInvalid[var] ? getDefaultAssignment(var) : modelInvalid[var];
        if (debug) {
          s_witn = replaceAll(s_witn, var, assnmt);
          t_witn = replaceAll(t_witn, var, assnmt);
        }

        outs () << "  (define-fun " << *var << " () " <<
          (bind::isBoolConst(var) ? "Bool" : (bind::isIntConst(var) ? "Int" : "Real"))
                << "\n    " << *assnmt << ")\n";
      }
      outs () << ")\n";

      if (debug){
        outs () << "Sanity check [model, S-part]: " << !((bool)(u.isSat(mk<NEG>(s_witn)))) << "\n";
        outs () << "Sanity check [model, T-part]: " << !((bool)(u.isSat(t_witn))) << "\n";
      }
    }

    /**
     * Mine the structure of T to get what was assigned to a variable
     */
    Expr getDefinitionFormulaFromT(Expr var)
    {
      ExprSet defs;
      for (auto & cnj : tConjs)
      {
        // get equality (unique per variable)
        if (std::find(std::begin(usedConjs),
                      std::end  (usedConjs), cnj) != std::end(usedConjs)) continue;

        if (isOpX<EQ>(cnj))
        {
          if (var == cnj->left() || var == cnj->right())
          {
            defs.insert(cnj);
          }
        }
      }

      // now find `the best` one

      if (defs.empty()) return NULL;

      Expr def = *defs.begin();
      for (auto & a : defs)
      {
        if (!emptyIntersect(a, sVars)) def = a;
      }

      usedConjs.insert(def);
      return (var == def->left() ? def->right() : def->left());
    }

    /**
     * Mine the structure of T to get what was assigned to a variable
     */
    Expr getBoolDefinitionFormulaFromT(Expr var)
    {
      Expr def;
      for (auto & cnj : tConjs)
      {
        if (std::find(std::begin(usedConjs),
                      std::end  (usedConjs), cnj) != std::end(usedConjs)) continue;

        if (bind::isBoolConst(cnj) && var == cnj)
        {
          def = mk<TRUE>(efac);
          usedConjs.insert(cnj);
        }
        else if (isOpX<NEG>(cnj) && bind::isBoolConst(cnj->left()) && var == cnj->left())
        {
          def = mk<FALSE>(efac);
          usedConjs.insert(cnj);
        }
      }

      if (def != NULL) extendTWithDefs(var, def);
      return def;
    }

    void extendTWithDefs(Expr var, Expr def)
    {
      for (auto & cnj : tConjs)
      {
        if (std::find(std::begin(usedConjs),
                      std::end  (usedConjs), cnj) != std::end(usedConjs)) continue;

        if (isOpX<EQ>(cnj))
        {
          if (var == cnj->left())
          {
            usedConjs.insert(cnj);
            if (def == NULL)
            {
              def = cnj->right();
              break;
            }
            else
            {
              getConj(isOpX<TRUE>(def) ? cnj->right() : mk<NEG> (cnj->right()), tConjs);
            }
          }
          else if (var == cnj->right())
          {
            usedConjs.insert(cnj);
            if (def == NULL)
            {
              def = cnj->left();
              break;
            }
            else
            {
              getConj(isOpX<TRUE>(def) ? cnj->left() : mk<NEG> (cnj->left()), tConjs);
            }
          }

          if (debug && tConjs.empty())
            outs () << "WARNING: getBoolDefinitionFormulaFromT has cleared tConjs\n";
        }
      }
    }

    /**
     * Mine the structure of T `conditionally`
     */
    Expr getCondDefinitionFormula(Expr var, Expr pre)
    {
      Expr res = NULL;
      ExprSet eqs;
      ExprSet eqsFilt;
      getEqualities(t, var, eqs);
      for (auto a : eqs)
      {
        if (u.implies(pre, a) && !u.isEquiv(a, mk<TRUE>(efac))) eqsFilt.insert(a);
      }

      int maxSz = 0;
      for (auto & a : eqsFilt) if (boolop::circSize(a) > maxSz) res = a;
      return res;
    }

    /**
     * Self explanatory
     */
    void getSymbolicMax(ExprSet& vec, Expr& curMax, bool isInt)
    {
      if (vec.size() == 0) return;
      ExprVector replFrom;
      ExprVector replTo;
      curMax = *vec.begin();
      if (vec.size() == 1) return;
      for (auto it = vec.begin(); ++it != vec.end(); ){
        auto &a = *it;
        if (u.isEquiv(mk<LT>(curMax, a), mk<TRUE>(efac))){
          curMax = a;
        } else if (u.isEquiv(mk<LT>(curMax, a), mk<FALSE>(efac))){
          //  curMax is OK
        } else {
          string ind = lexical_cast<string> (fresh_var_ind++);

          Expr varName = mkTerm ("_aeval_tmp_max_" + ind, efac);
          Expr var = isInt ? bind::intConst(varName) : bind::realConst(varName);

          replFrom.push_back(var);
          replTo.push_back(mk<ITE>(mk<LT>(curMax, a), a, curMax));

          curMax = var;
        }
      }
      for (int i = replFrom.size() - 1; i >= 0; i--)
        curMax = replaceAll(curMax, replFrom[i], replTo[i]);
    }

    /**
     * Self explanatory
     */
    void getSymbolicMin(ExprSet& vec, Expr& curMin, bool isInt)
    {
      if (vec.size() == 0) return;
      ExprVector replFrom;
      ExprVector replTo;
      curMin = *vec.begin();
      if (vec.size() == 1) return;
      for (auto it = vec.begin(); ++it != vec.end(); ){
        auto &a = *it;
        if (u.isEquiv(mk<GT>(curMin, a), mk<TRUE>(efac))){
          curMin = a;
        } else if (u.isEquiv(mk<GT>(curMin, a), mk<FALSE>(efac))){
          //  curMin is OK
        } else {
          string ind = lexical_cast<string> (fresh_var_ind++);

          Expr varName = mkTerm ("_aeval_tmp_min_" + ind, efac);
          Expr var = isInt ? bind::intConst(varName) : bind::realConst(varName);

          replFrom.push_back(var);
          replTo.push_back(mk<ITE>(mk<GT>(curMin, a), a, curMin));

          curMin = var;
        }
      }
      for (int i = replFrom.size() - 1; i >= 0; i--)
        curMin = replaceAll(curMin, replFrom[i], replTo[i]);
    }

    void getSymbolicNeq(ExprSet& vec, Expr& lower, Expr& curNeq, Expr eps, bool isInt)
    {
      ExprVector replFrom;
      ExprVector replTo;

      Expr var1 = lower;
      Expr eps1;

      string ind = lexical_cast<string> (fresh_var_ind++);
      Expr varName = mkTerm ("_aeval_tmp_neq_" + ind, efac);
      Expr var2 = isInt ? bind::intConst(varName) : bind::realConst(varName);

      curNeq = var2;
      for (int i = 0; i < vec.size(); i++)
      {
        ExprSet neqqedConstrs;
        for (auto &a : vec) neqqedConstrs.insert(mk<EQ>(a, var1));

        string ind = lexical_cast<string> (fresh_var_ind++);
        Expr varName = mkTerm ("_aeval_tmp_neq_" + ind, efac);
        Expr newVar = isInt ? bind::intConst(varName) : bind::realConst(varName);

        replFrom.push_back(var2);
        replTo.push_back(mk<ITE>(disjoin(neqqedConstrs, efac), newVar, var1));

        eps1 = multVar(eps, i+1);
        var1 = mk<PLUS>(lower, eps1);
        var2 = newVar;
      }

      replFrom.push_back(var2);
      replTo.push_back(var1);

      for (int i = 0; i < replFrom.size(); i++)
        curNeq = replaceAll(curNeq, replFrom[i], replTo[i]);
    }

    /**
     * Based on type
     */
    Expr getDefaultAssignment(Expr var)
    {
      if (bind::isBoolConst(var)) return mk<TRUE>(efac);
      if (bind::isIntConst(var)) return mkTerm (mpz_class (0), efac);
      else           // that is, isRealConst(var) == true
        return mkTerm (mpq_class (0), efac);
    }

    /**
     * Return "e + eps"
     */
    Expr plusEps(Expr e, bool isInt = true)
    {
      if (isOpX<MPZ>(e) && isInt)
        return mkTerm (mpz_class (boost::lexical_cast<int> (e) + 1), efac);

      if (isInt) return mk<PLUS>(e, mkTerm (mpz_class (1), efac));
      else return mk<PLUS>(e, mkTerm (mpq_class (1), efac));
    }

    /**
     * Return "e - eps"
     */
    Expr minusEps(Expr e, bool isInt = true)
    {
      if (isOpX<MPZ>(e) && isInt)
        return mkTerm (mpz_class (boost::lexical_cast<int> (e) - 1), efac);

      if (isInt) return mk<MINUS>(e, mkTerm (mpz_class (1), efac));
      else return mk<MINUS>(e, mkTerm (mpq_class (1), efac));
    }

    /**
     * Extract function from relation
     */
    Expr getAssignmentForVar(Expr var, Expr exp)
    {
      if (bind::typeOf(var) == mk<INT_TY>(s->efac())) exp = oldNormalizationGen(exp, var);
      if (!isNumeric(var))
      {
        if (isOpX<EQ>(exp))
        {
          if (var == exp->left()) return exp->right();
          if (var == exp->right()) return exp->left();
        }
        outs() << "assertion fail" << endl; 
        assert(0);
      }

      if (true) outs () << "getAssignmentForVar " << *var << " in:  " << *exp << "\n";

      bool isInt = bind::isIntConst(var);

      if (isOp<ComparissonOp>(exp))
      {
        if (isOpX<NEG>(exp)) exp = mkNeg(exp->left());

        if (!bind::isBoolConst(var) && var != exp->left())
          exp = ineqReverter(ineqMover(exp, var));
        // TODO: write a similar simplifier fo booleans

        assert (var == exp->left());

        if (isOpX<EQ>(exp) || isOpX<GEQ>(exp) || isOpX<LEQ>(exp)){
          if (exp->left() == exp->right()) return getDefaultAssignment(var);
          return exp->right();
        }
        else if (isOpX<LT>(exp)){
          return minusEps (exp->right(), isInt);
        }
        else if (isOpX<GT>(exp)){
          return plusEps (exp->right(), isInt);
        }
        else if (isOpX<NEQ>(exp)){
          return plusEps (exp->right(), isInt);
        }
        else assert(0);
      }
      else if (isOpX<NEG>(exp)){
        if (isOpX<EQ>(exp->left())) {
          return plusEps (getAssignmentForVar(var, exp->left()), isInt);
        }
      }
      else if (isOpX<AND>(exp))
      {
        exp = u.numericUnderapprox(exp); // try to see if there are only numerals
        if (isOpX<EQ>(exp)) return exp->right();

        ExprSet cnjs;
        getConj (exp, cnjs);
        u.removeRedundantConjuncts(cnjs);

        map<Expr, ExprSet> pre;
        for (auto & cnj : cnjs)
        {
          if (isOpX<IMPL>(cnj)) pre[cnj->left()].insert(cnj->right());
          else pre[mk<TRUE>(efac)].insert(cnj);
        }

        // sort keys of pre
        ExprVector sortedPre;
        for (auto & a : pre)
        {
          if (isOpX<TRUE>(a.first)) continue;
          int i = 0;
          while (i < sortedPre.size())
          {
            if (a.first != sortedPre[i] && u.implies (sortedPre[i], a.first)) break;
            i++;
          }
          sortedPre.insert(sortedPre.begin()+i, a.first);
        }

        // enhace the pre keys to avoid conflicts
        ExprVector preNegged;
        for (int i = 0; i < sortedPre.size(); i++)
        {
          ExprSet negged;
          negged.insert(sortedPre[i]);
          for (int j = 0; j < i; j++)
          {
            if (u.isSat(conjoin(negged, efac), mkNeg(sortedPre[j])))
              negged.insert(mkNeg(sortedPre[j]));
          }
          preNegged.push_back(conjoin(negged, efac));
        }

        // create the final ITE
        Expr sk = compositeAssm(pre[mk<TRUE>(efac)], var, isInt);
        for (int i = 0; i < sortedPre.size(); i++)
        {
          for (auto & b : pre)
          {
            if (sortedPre[i] != b.first && u.implies (preNegged[i], b.first))
            {
              pre[sortedPre[i]].insert(b.second.begin(), b.second.end());
            }
          }
          sk = mk<ITE>(preNegged[i], compositeAssm(pre[sortedPre[i]], var, isInt), sk);
        }

        return sk;
      }
      return exp;
    }

    // normalization generator for integer 
    Expr oldNormalizationGen(Expr s, Expr var)
    {
      outs() << "Printing original SMT formula:\n" << *s << endl;
      // Preparation
      s = simplifyBool(s);
      ExprSet temp; ExprVector sVec;
      getConj(s, temp);
      Expr constOne = mkTerm(mpz_class(1), s->getFactory());
      //initializing Expression Vector, ensure y is not on rhs, remove LT & GEQ;
      for (auto t : temp) sVec.push_back(singleExprNormPrep(t, var, true));
      // Normalization
      while (true)
      {
        ExprVector sVecTemp;
        auto locIte = sVec.begin(); // location iterator
        while (locIte != sVec.end())
        {
          Expr lhs = (*locIte) -> left(), rhs = (*locIte) -> right(), curExp = (*locIte);
          if (!contains(curExp, var)) outs() << "Error, oldNormalizationGen, curExp doesn't have var: " << *curExp << endl;
          //MULTIPLICATION TRANSFORMATION
          if (isOp<MULT>(lhs)) {
            sVecTemp.push_back(multTrans(curExp, var));
            sVec.erase(locIte); break;
          }
          //DIVISION TRANSFORMATION
          else if (isOp<IDIV>(lhs))
          {
            Expr lhs = curExp->left(), rhs = curExp->right();
            Expr alpha = lhs->right(), varSide = lhs->left();
            if (!contains(varSide, var)) {
              outs() << "Error on divTrans, f(x)/y format not supported." << endl;
              exit(0);
            }
            //applying section 4.2, divisibility constraints
            if (isOpX<EQ>(curExp)) {
              sVecTemp.push_back(mk<GT>(varSide, mk<MINUS>(mk<MULT>(alpha, rhs), constOne)));
              sVecTemp.push_back(mk<LEQ>(varSide, mk<MINUS>(mk<PLUS>(mk<MULT>(alpha, rhs), alpha), constOne)));
            } else if (isOpX<GT>(curExp)) {
              sVecTemp.push_back(mk<GT>(varSide, mk<MINUS>(mk<PLUS>(mk<MULT>(alpha, rhs), alpha), constOne)));
            } else if (isOpX<LEQ>(curExp)) {
              sVecTemp.push_back(mk<LEQ>(varSide, mk<MINUS>(mk<PLUS>(mk<MULT>(alpha, rhs), alpha), constOne)));
            } else if (isOpX<NEQ>(curExp)) {
              int i = -1;
              if (isOpX<MPZ>(alpha)) i = lexical_cast<int>(*(alpha)) - 1;
              else outs() << "Issue with NEQ expression, no alpha found." << *curExp << endl;
              while (i >= 0)
              {
                sVecTemp.push_back(mk<NEQ>(varSide, i != 0 ? //Ensure 0 is not added to expression
                  mk<PLUS>(mk<MULT>(alpha, rhs), mkTerm(mpz_class(i), s->getFactory())) :
                  mk<MULT>(alpha, rhs)));
                --i;
              }
            }
            sVec.erase(locIte); break;
          } else ++locIte;
        }
        // no change detected, break outer while loop.
        if (sVecTemp.empty()) break; 
        // Merging sVecTemp w/ sVec and continue the loop.
        else for (auto ite = sVecTemp.begin(); ite != sVecTemp.end(); ++ite) sVec.push_back(*ite);
      }
      ExprSet fin;
      for (auto t : sVec) fin.insert(t);
      SMTUtils u1(s->getFactory());
      outs() << "Expressions after oldNormalizationGen(): " << conjoin(fin, s->getFactory()) << endl;
      outs() << "oldNormalizationGen check, beginning equivalent to result: " << u1.isEquiv(s, conjoin(fin, s->getFactory())) << endl;
      return conjoin(fin, s->getFactory());
    }

    Expr compositeAssm(ExprSet& cnjs, Expr var, bool isInt)
    {
//      outs() << "Var: " << var << endl;
//      outs() << "cnjs: " << conjoin(cnjs, efac) << endl;
        bool incomplete = false;

        // split constraints

        ExprSet conjLT;
        ExprSet conjLE;
        ExprSet conjGT;
        ExprSet conjGE;
        ExprSet conjNEQ;
        ExprSet conjEQ;

        u.removeRedundantConjuncts(cnjs);

        for (auto cnj : cnjs)
        {
          // preprocessing starts
          if (isOpX<NEG>(cnj)) cnj = mkNeg(cnj->left());
          cnj = ineqReverter(ineqMover(cnj, var));
          int c = isMultVar(cnj->left(), var);
          if (c == 1 && !isInt)
            cnj = reBuildCmp(cnj, var, cnj->right());
          if (c == -1 && !isInt)
            cnj = reBuildCmp(cnj, cnj->right(), var);
          if (c > 1 && !isInt)
            cnj = reBuildCmp(cnj, var, mk<DIV>(cnj->right(),
                    mkTerm (mpq_class (c), efac)));
          if (c < 0 && !isInt)
            cnj = reBuildCmp(cnj, mk<DIV>(cnj->right(),
                    mkTerm (mpq_class (-c), efac)), var);
          c = isMultVar(cnj->right(), var);
          if (c == 1 && !isInt)
            cnj = reBuildCmp(cnj, cnj->left(), var);
          if (c == -1 && !isInt)
            cnj = reBuildCmp(cnj, var, cnj->left());
          if (c > 1 && !isInt)
            cnj = reBuildCmp(cnj, mk<DIV>(cnj->left(),
                    mkTerm (mpq_class (c), efac)), var);
          if (c < 0 && !isInt)
            cnj = reBuildCmp(cnj, var, mk<DIV>(cnj->left(),
                    mkTerm (mpq_class (-c), efac)));
          // preprocessing ends

          if (isOpX<EQ>(cnj)){
            if (var == cnj->left()) {
              conjEQ.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LT>(cnj)){
            if (var == cnj->left()) {
              conjLT.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjGT.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LEQ>(cnj)){
            if (var == cnj->left()) {
              conjLE.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjGE.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GT>(cnj)){
            if (var == cnj->left()) {
              conjGT.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjLT.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GEQ>(cnj)){
            if (var == cnj->left()) {
              conjGE.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjLE.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<NEQ>(cnj)){
            if (var == cnj->left()) {
              conjNEQ.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }
          else {
            incomplete = true;
          }

          if (incomplete && debug)
            outs() << "WARNING: This constraint is unsupported: " << *cnj << "\n";
        }

        // simplify some:
        for (auto & b : conjLE)
        {
          bool toBrk = false;
          for (auto & a : conjNEQ)
          {
            if (a == b)
            {
              conjLT.insert(a);
              conjNEQ.erase(a);
              conjLE.erase(b);
              toBrk = true;
              break;
            }
          }
          if (toBrk) break;
        }

        // simplify some:
        for (auto & b : conjGE)
        {
          bool toBrk = false;
          for (auto & a : conjNEQ)
          {
            if (a == b)
            {
              conjGT.insert(a);
              conjNEQ.erase(a);
              conjGE.erase(b);
              toBrk = true;
              break;
            }
          }
          if (toBrk) break;
        }

        // get the assignment (if exists)

        if (conjEQ.size() > 0) return *(conjEQ.begin()); // GF: maybe try to find the best of them

        // get symbolic max and min
        Expr curMaxGT, curMaxGE, curMinLT, curMinLE, curMax, curMin;
        getSymbolicMax(conjGT, curMaxGT, isInt);
        getSymbolicMax(conjGE, curMaxGE, isInt);
        getSymbolicMin(conjLT, curMinLT, isInt);
        getSymbolicMin(conjLE, curMinLE, isInt);

        if (isInt)
        {
          if (curMaxGT != NULL || curMaxGE != NULL)
          {
            if (curMaxGE == NULL) curMax = plusEps(curMaxGT);
            else if (curMaxGT == NULL) curMax = curMaxGE;
            else curMax = mk<ITE>(mk<GEQ>(curMaxGT, curMaxGE), plusEps(curMaxGT), curMaxGE);
          }

          if (curMinLT != NULL || curMinLE != NULL)
          {
            if (curMinLE == NULL) curMin = minusEps(curMinLT);
            else if (curMinLT == NULL) curMin = curMinLE;
            else curMin = mk<ITE>(mk<LEQ>(curMinLT, curMinLE), minusEps(curMinLT), curMinLE);
          }
        }
        else
        {
          if (curMaxGT != NULL || curMaxGE != NULL)
          {
            if (curMaxGE == NULL) curMax = curMaxGT;
            else if (curMaxGT == NULL) curMax = curMaxGE;
            else curMax = mk<ITE>(mk<GEQ>(curMaxGT, curMaxGE), curMaxGT, curMaxGE);
          }

          if (curMinLT != NULL || curMinLE != NULL)
          {
            if (curMinLE == NULL) curMin = curMinLT;
            else if (curMinLT == NULL) curMin = curMinLE;
            else curMin = mk<ITE>(mk<LEQ>(curMinLT, curMinLE), curMinLT, curMinLE);
          }
        }
        // outs() << "curMaxGT: " << curMaxGT << "\n";
        // outs() << "curMaxGE: " << curMaxGE << "\n";
        // outs() << "curMinLT: " << curMinLT << "\n";
        // outs() << "curMinLE: " << curMinLE << "\n";
        // outs() << "curMax: " << curMax << "\n";
        // outs() << "curMin: " << curMin << "\n";
        // outs() << "conjLT: " << conjoin(conjLT, efac) << endl;
        // outs() << "conjLE: " << conjoin(conjLE, efac) << endl;
        // outs() << "conjGT: " << conjoin(conjGT, efac) << endl;
        // outs() << "conjGE: " << conjoin(conjGE, efac) << endl;
        // outs() << "conjNEQ: " << conjoin(conjNEQ, efac) << endl;
        // outs() << "conjEQ: " << conjoin(conjEQ, efac) << endl;

        if (conjNEQ.size() == 0)
        {
          if (isInt)
          {
            if (curMax != NULL) return curMax;
            if (curMin != NULL) return curMin;
            assert (0);
          }

          if (curMinLT == NULL && curMinLE != NULL)
          {
            return curMinLE;
          }

          if (curMaxGT == NULL && curMaxGE != NULL)
          {
            return curMaxGE;
          }

          if (curMin == NULL)
          {
            return plusEps(curMaxGT, isInt);
          }

          if (curMax == NULL)
          {
            return minusEps(curMin, isInt);
          }

          // get value in the middle of max and min
          assert (curMin != NULL && curMax != NULL);
          return mk<DIV>(mk<PLUS>(curMin, curMax), mkTerm (mpq_class (2), efac));
        }

        // here conjNEQ.size() > 0

        Expr tmpMin;
        getSymbolicMin(conjNEQ, tmpMin, isInt);
        Expr tmpMax;
        getSymbolicMax(conjNEQ, tmpMax, isInt);

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return plusEps(tmpMax, isInt);
        }

        if (curMinLE != NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMinLE, tmpMin), curMinLE, tmpMin), isInt);
        }

        if (curMinLE == NULL && curMinLT != NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMinLT, tmpMin), curMinLT, tmpMin), isInt);
        }

        if (curMinLE != NULL && curMinLT != NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMin, tmpMin), curMin, tmpMin), isInt);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE != NULL && curMaxGT == NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMaxGE, tmpMax), curMaxGE, tmpMax), isInt);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT != NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMaxGT, tmpMax), curMaxGT, tmpMax), isInt);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE != NULL && curMaxGT != NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMax, tmpMax), curMax, tmpMax), isInt);
        }

        assert (curMinLE != NULL || curMinLT != NULL);
        assert (curMaxGE != NULL || curMaxGT != NULL);

        Expr eps;
        if (isInt)
        {
          eps = mkTerm (mpz_class (1), efac);

          if (curMaxGE == NULL) curMax = mk<PLUS>(curMaxGT, eps);
          else if (curMaxGT == NULL) curMax = curMaxGE;
          else curMax = mk<ITE>(mk<GEQ>(curMaxGT, curMaxGE), mk<PLUS>(curMaxGT, eps), curMaxGE);
        }
        else
        {
          eps = mk<DIV>(mk<MINUS>(curMin, curMax), mkTerm (mpq_class (conjNEQ.size() + 2), efac));
          curMax = mk<PLUS>(curMax, eps);
        }

        Expr curMid;
        getSymbolicNeq(conjNEQ, curMax, curMid, eps, isInt); // linear scan
        return curMid;
      }

    void searchDownwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug)
      {
        outs () << "searchDownwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      if (indexes.empty()) return;

      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        return;
      }
      else
      {
        Expr subs = ae.getValidSubset(false);
        if (isOpX<FALSE>(subs))
        {
//          for (int j : indexes)
//          {
//            set<int> indexes2 = indexes;
//            indexes2.erase(j);
//            searchDownwards(indexes2, var, skol);
//          }
          return;
        }
        else
        {
          bool erased = false;

          for (auto i = indexes.begin(); i != indexes.end();)
          {
            if (!u.implies(subs, projections[*i]))
            {
              i = indexes.erase(i);
              erased = true;
            }
            else
            {
              ++i;
            }
          }
          if (erased)
          {
            searchDownwards(indexes, var, skol);
          }
          else
          {
            for (int j : indexes)
            {
              set<int> indexes2 = indexes;
              indexes2.erase(j);
              searchDownwards(indexes2, var, skol);
            }
          }
        }
      }
    }

    void searchUpwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug)
      {
        outs () << "searchUpwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        for (int i = 0; i < partitioning_size; i++)
        {
          if (find (indexes.begin(), indexes.end(), i) != indexes.end()) continue;
          set<int> indexes2 = indexes;
          indexes2.insert(i);
          searchUpwards(indexes2, var, skol);
        }
        return;
      }
    }

    void breakCyclicSubsts(ExprMap& cyclicSubsts, ExprMap& evals, ExprMap& substsMap)
    {
      if (cyclicSubsts.empty()) return;

      map<Expr, int> tmp;
      for (auto & a : cyclicSubsts)
      {
        ExprSet vars;
        filter (a.second, bind::IsConst (), inserter (vars, vars.begin()));
        for (auto & b : vars)
        {
          if (find(v.begin(), v.end(), b) != v.end())
            tmp[b]++;
        }
      }

      int min = 0;
      Expr a;
      for (auto & b : tmp)
      {
        if (b.second >= min)
        {
          min = b.second;
          a = b.first;
        }
      }

      for (auto b = cyclicSubsts.begin(); b != cyclicSubsts.end(); b++)
        if (b->first == a)
        {
          substsMap[a] = evals[a]->right();
          cyclicSubsts.erase(b); break;
        }

      substsMap.insert (cyclicSubsts.begin(), cyclicSubsts.end());
      splitDefs(substsMap, cyclicSubsts);
      breakCyclicSubsts(cyclicSubsts, evals, substsMap);
    }

    Expr combineAssignments(ExprMap& allAssms, ExprMap& evals)
    {
      ExprSet skolTmp;
      ExprMap cyclicSubsts;
      splitDefs(allAssms, cyclicSubsts);

      breakCyclicSubsts(cyclicSubsts, evals, allAssms);
      assert (cyclicSubsts.empty());
      for (auto & a : sensitiveVars)
      {
        assert (emptyIntersect(allAssms[a], v));
        skolTmp.insert(mk<EQ>(a, allAssms[a]));
      }
      return conjoin(skolTmp, efac);
    }

    bool propagateMap(Expr var, int i)
    {
      if (skolMaps[i][var] != NULL && defMap[var] != NULL)
      {
        ExprSet vars;
        filter (defMap[var], bind::IsConst (), inserter (vars, vars.begin()));
        if (vars.size() != 1) return false; //GF: to extend
        for (auto & var1 : vars)
        {
          Expr tmp = skolMaps[i][var];
          if (find(v.begin(), v.end(), var1) != v.end() && skolMaps[i][var1] == NULL)
          {
            skolMaps[i][var1] = simplifyArithm(replaceAll(tmp, var, defMap[var]));;
            skolMaps[i][var] = NULL;
            return true;
          }
        }
      }
      return false;
    }

    Expr getSkolemFunction (bool compact = false)
    {
      if (partitioning_size == 0)
        return mk<TRUE>(efac);

      ExprSet skolUncond;
      ExprSet eligibleVars;
      skolemConstraints.clear(); // GF: just in case

      bool toRestart = true;
      while(toRestart)
      {
        for (auto &var: v)
        {
          toRestart = false;
          for (int i = 0; i < partitioning_size; i++)
          {
            toRestart |= propagateMap(var, i);
          }
          if (toRestart) break;
        }
      }

      for (auto &var: v)
      {
        bool elig = compact;
        for (int i = 0; i < partitioning_size; i++)
        {
          if (defMap[var] != NULL)
          {
            skolMaps[i][var] = mk<EQ>(var, defMap[var]);
          }
          else if (skolMaps[i][var] == NULL)
          {
            ExprSet pre;
            for (auto & a : skolMaps[i]) if (a.second != NULL) pre.insert(a.second);
            pre.insert(t);
            Expr assm = getCondDefinitionFormula(var, conjoin(pre, efac));
            if (assm != NULL)
            {
              skolMaps[i][var] = assm;
            }
            else if (someEvals[i][var] != NULL)
            {
              skolMaps[i][var] = someEvals[i][var];
            }
            else skolMaps[i][var] = mk<EQ>(var, getDefaultAssignment(var));
          }

          if (compact) // small optim:
          {
            if (bind::isBoolConst(var) && u.isEquiv(skolMaps[i][var]->right(), mk<TRUE>(efac)))
              skolMaps[i][var] = mk<EQ>(var, mk<TRUE>(efac));
            if (bind::isBoolConst(var) && u.isEquiv(skolMaps[i][var]->right(), mk<FALSE>(efac)))
              skolMaps[i][var] = mk<EQ>(var, mk<FALSE>(efac));
          }

          elig &= (1 == intersectSize (skolMaps[i][var], v));
        }
        if (elig) eligibleVars.insert(var);
        else sensitiveVars.insert(var);
      }

      for (auto & a : v)
      {
        ExprVector t;
        for (int i = 0; i < partitioning_size; i++)
        {
          assert(skolMaps[i][a] != NULL);
          t.push_back(skolMaps[i][a]); // should be on i-th position
          outs () << " skolMaps [ " << i << ", " << *a << " ] = " << skolMaps[i][a] << "\n";
        }
        skolemConstraints[a] = t;
      }

      map<Expr, set<int>> inds;
      ExprMap sameAssms;
      for (auto & var : eligibleVars)
      {
        outs () << "  eligibleVar " << var << ":\n";
        bool same = true;
        auto & a = skolemConstraints[var];
        for (int i = 1; i < partitioning_size; i++)
        {
          if (a[0] != a[i])
          {
            same = false;
            break;
          }
        }
        if (same)
        {
          sameAssms[var] = getAssignmentForVar(var, a[0]);
          Expr skol = mk<EQ>(var, sameAssms[var]);
          skolUncond.insert(skol);
          separateSkols [var] = sameAssms[var];
        }
        else
        {
          sensitiveVars.insert(var);
        }
      }

      for (auto & var : sensitiveVars)
      {
        bestIndexes.clear();
        if (find(eligibleVars.begin(), eligibleVars.end(), var) != eligibleVars.end()
            && compact)
        {
          set<int> indexes;
          for (int i = 0; i < partitioning_size; i++) indexes.insert(i);
          searchDownwards (indexes, var, skolemConstraints[var]);
          searchUpwards (bestIndexes, var, skolemConstraints[var]);
        }
        inds[var] = bestIndexes;
      }

      Expr skol;
      ExprSet skolTmp;
      if (sensitiveVars.size() > 0)
      {
        set<int> intersect;
        for (int i = 0; i < partitioning_size; i ++)
        {
          int found = true;
          for (auto & a : inds)
          {
            if (find (a.second.begin(), a.second.end(), i) == a.second.end())
            {
              found = false;
              break;
            }
          }
          if (found) intersect.insert(i);
        }

        if (intersect.size() <= 1)
        {
          int maxSz = 0;
          int largestPre = 0;
          for (int i = 0; i < partitioning_size; i++)
          {
            int curSz = treeSize(projections[i]);
            if (curSz > maxSz)
            {
              maxSz = curSz;
              largestPre = i;
            }
          }
          intersect.clear();
          intersect.insert(largestPre);
        }

        ExprMap allAssms = sameAssms;
        for (auto & a : sensitiveVars)
        {
          // outs () << "sensitive var: " << *a << "\n"; //outTest
          ExprSet cnjs;
          for (int b : intersect) getConj(skolemConstraints[a][b], cnjs);
          Expr def = getAssignmentForVar(a, conjoin(cnjs, efac));
          // outs () << "  - - -> " << *def << "\n"; //outTest
          allAssms[a] = def;
        }
        Expr bigSkol = combineAssignments(allAssms, someEvals[*intersect.begin()]);
        // outs() << "BigSkol: " << bigSkol << endl; //outTest

        for (auto & evar : v)
        {
          for (int i = 0; i < partitioning_size; i++)
          {
            int curSz = treeSize(projections[i]);
          }
        }

        for (int i = 0; i < partitioning_size; i++)
        {
          // outs() << " partition " << i << ": " << projections[i] << endl; //outTest
          allAssms = sameAssms;
          if (find(intersect.begin(), intersect.end(), i) == intersect.end())
          {
            for (auto & a : sensitiveVars)
            {
              // outs() << "a: " << a << endl; //outTest
              Expr def = getAssignmentForVar(a, skolemConstraints[a][i]);
              // outs () << "  - - -> " << *def << "\n"; //outTest
              allAssms[a] = def;
            }
            bigSkol = mk<ITE>(projections[i], combineAssignments(allAssms, someEvals[i]), bigSkol);
            // outs() << "new BigSkol: " << bigSkol << endl; //outTest
            if (compact) bigSkol = u.simplifyITE(bigSkol);
          }
        }

        for (auto & a : sensitiveVars) separateSkols [a] = projectITE (bigSkol, a);

        skolUncond.insert(bigSkol);
      }
      return conjoin(skolUncond, efac);
    }

    Expr getSeparateSkol (Expr v) { return separateSkols [v]; }

    int getPartitioningSize() { return partitioning_size; }

    // Runnable only after getSkolemFunction
    Expr getSkolemConstraints(int i)
    {
      ExprSet constrs;
      for (auto & a : skolemConstraints)
        constrs.insert(a.second[i]);
      return conjoin(constrs, efac);
    }
  };

  Expr negativeCoefCheck(Expr t);
  Expr revExpr(Expr s);
  Expr convertNegCoefNum(Expr t);

  /* OLD HELPER FUNCTIONS */
  // Most basic initializer, also work as helper for vecElemInitInt & vecElemInitReal
  Expr singleExprNormPrep(Expr t, Expr constVar, bool isInt)
  {
    if (isOp<ComparissonOp>(t))
    {
      //ensure y is on lhs.
      if (contains(t->right(), constVar)) t = revExpr(t);
      if ( t == NULL ) return NULL;
      //ensure lhs is not negative
      if (t->left()->arity() == 2) {
        if (isInt) t = convertNegCoefNum(t);
        t = negativeCoefCheck(t);
      }
      // constant change to lhs & rhs may occur, thus placing initialization in the middle.
      Expr lhs = t->left(), rhs = t->right();
      if (isInt) {
        //applying (3) to integer Expr, getting rid of LT and GEQ
        Expr constOne = mkTerm(mpz_class(1), t->getFactory());
        if (isOpX<LT>(t)) t = mk<LEQ>(lhs, mk<MINUS>(rhs, constOne));
        else if (isOpX<GEQ>(t)) t = mk<GT>(lhs, mk<MINUS>(rhs, constOne));
      }
      return t;
    } else {
      outs() << "Error, (singleExprNormPrep) The input Expr " << *t << " is not comparison!" << endl;
      return NULL;
    }
  }

  /* GIVEN HELPER FUNCTION */
  // create forall & exists formulas
  Expr static createQuantifiedFormulaRestr (Expr def, Expr a, bool forall = false)
  {// want to have quantifiers in def
    ExprVector args; 
    args.push_back(a->last()); // push variable y into vars.
    args.push_back(def);
    if (forall) return mknary<FORALL>(args);
    else return mknary<EXISTS>(args);
  }

  // overloaded create quantifiers that takes in ExprSet of vars.
  Expr static createQuantifiedFormulaRestr (Expr def, ExprSet& vars, bool forall = false)
  {
    if (vars.empty()) return def;
    ExprVector args;
    for (auto & a : vars) args.push_back(a->last());
    args.push_back(def);
    if (forall) return mknary<FORALL>(args);
    else return mknary<EXISTS>(args);
  }


  /* GENERAL HELPER FUNCTIONS */
  //get a constant y with a type depend on given expression.
  Expr getConstYByInput(Expr s) 
  {
    Expr constYTemp = mkTerm<std::string>("y", s->getFactory());
    Expr intY = bind::intConst(constYTemp),
      realY = bind::realConst(constYTemp),
      boolY = bind::boolConst(constYTemp);
    if (contains(s, intY)) return intY;
    else if (contains(s, realY)) return realY;
    else if (contains(s, boolY)) return boolY;
    else return NULL; //Input expression does not contain y, no QE needed.
  }
  //normalize comparison expression through dividing both side
  Expr multTrans(Expr t, Expr constVar)
  {
    if (isOp<ComparissonOp>(t))
    {
      Expr lhs = t->left(), rhs = t->right();
      while (isOp<MULT>(lhs))//until lhs is no longer *
      {
        bool divLeft;
        Expr lOperand = lhs->left(), rOperand = lhs->right();
        if (contains(lOperand, constVar) ) divLeft = false;
        else if (contains(rOperand, constVar)) divLeft = true;
        else outs() << "Cannot find variable y in " << *lhs << endl; //debug check
        rhs = mk<DIV>(rhs, divLeft ? lOperand : rOperand);
        lhs = divLeft ? rOperand : lOperand;
      }
      return (mk(t->op(), lhs, rhs));
    } else {
      outs() << "(multTrans) input Expr is not comparison!" << endl;
      return NULL;
    }
  }
  
  // reverse the current comparison expression.
  Expr revExpr(Expr s)
  {
    Expr lhs = s->left(), rhs = s->right();
    if (isOpX<LT>(s)) return mk<GT>(rhs, lhs);
    else if (isOpX<LEQ>(s)) return mk<GEQ>(rhs, lhs);
    else if (isOpX<GT>(s)) return mk<LT>(rhs, lhs);
    else if (isOpX<GEQ>(s)) return mk<LEQ>(rhs, lhs);
    outs() << "Error in revExpr(): current comparison for expression ";
    outs() << *s << " is not supported." << endl;
    return NULL;
  }

  // check if expression is all integer (returns 1) or all real (returns -1). 
  int intOrReal(Expr s)
  {
    ExprVector sVec;
    int realCt = 0, intCt = 0;
    filter(s, bind::IsNumber(), back_inserter(sVec));
    filter(s, bind::IsConst(), back_inserter(sVec));
    for (auto ite : sVec)
    {
      if (isOpX<MPQ>(ite)) outs() << "real? " << *ite << endl;
      if (bind::isIntConst(ite) || isOpX<MPZ>(ite)) ++intCt;
      else if (bind::isRealConst(ite) || isOpX<MPQ>(ite)) ++realCt;
      else outs() << "Error identifying: " << *ite << " in intOrReal()." <<endl;
    }
    if (realCt == 0 && intCt > 0) return 1;
    else if (realCt > 0 && intCt == 0) return -1;
    else if (realCt == 0 && intCt == 0) return 2;
    outs() << "For s: " << s << "\n\tCurrent realCt = " << realCt << "\n\tCurrent intCt = " << intCt << endl;
    return 0; //mixture of int and real.
  }
  
  /* INTEGER HELPER FUNCTION */
  Expr divTransHelper(Expr t, Expr constVar)
  { // only for GT & LEQ Expr
    if (isOpX<GT>(t) || isOpX<LEQ>(t)) {
      Expr lhs = t->left(), rhs = t->right(), y, coef, one = mkTerm(mpz_class(1), t->getFactory());
      if (contains(lhs->left(), constVar)) y = lhs->left(), coef = lhs->right();
      else y = lhs->right(), coef = lhs->left();
      return mk(t->op(), y, mk<MINUS>(mk<MULT>(mk<PLUS>(rhs, one), coef), one));
    } else {
      outs() << "Error, divTransInt(): " << *t << " is not GT nor LEQ." <<endl;
      return t;
    }
  }

  // For single integer Expr normalization, only capable of handling LT & GEQ Exprs 
  Expr divMultTransInt(Expr t, Expr constVar)
  {
    // outs() << "divMultTransInt begin: t " << t << endl;
    Expr lhs = t->left(), rhs = t->right();
    if (lhs->arity() == 2) {
      int coef = 1;
      while (true) {
        // outs() << "t during transformation: " << *t << endl;
        if (lhs->arity() == 1) break;
        else if (isOpX<MULT>(lhs)) {
          if (isOpX<MPZ>(lhs->left())) {
            coef *= boost::lexical_cast<int>(lhs->left());
            t = mk(t->op(), lhs->right(), rhs);
          } else if (isOpX<MPZ>(lhs->right())) {
            coef *= boost::lexical_cast<int>(lhs->right());
            t = mk(t->op(), lhs->left(), rhs);
          } else { 
            outs() << "Error: " << *t << " contains coefficient that's not a integer constant!" << endl;
            exit(0); //critical Error
          }
        } else if (isOpX<IDIV>(lhs)) {
          t = divTransHelper(t, constVar);
        } else {
          outs() << "Error, divMultTransInt(): Unexpected operation (not idiv or mult)." << endl;
          break;
        }
        lhs = t->left(), rhs = t->right();
      }
      // outs() << "divMultTransInt end: t " << mk(t->op(), lhs, rhs) << endl;
      if (coef > 1) return mk(t->op(), mk<MULT>(mkTerm(mpz_class(coef), t->getFactory()), lhs), rhs);
      else return mk(t->op(), lhs, rhs);
    } else return t;
  }

  bool negCoefNumCheck(Expr lhs)
  {
    if (isOpX<MULT>(lhs)) {
      if (isOpX<MPZ>(lhs->left()) && (boost::lexical_cast<int>(lhs->left()) < 0)) return true;
      if (isOpX<MPZ>(lhs->right()) && (boost::lexical_cast<int>(lhs->right()) < 0)) return true;
    }
    return false;
  }

  //converting the negative coefficient into a positive coefficient that's being added an UN_MINUS.
  Expr convertNegCoefNum(Expr t)
  {
    if (!negCoefNumCheck(t->left())) return t; // if t doesn't contain negative coefficient, then do nothing.
    Expr coef = NULL, remain = NULL, lhs = t->left(), rhs = t->right();
    if (isOpX<MPZ>(lhs->left())) coef = lhs->left(), remain = lhs->right();
    else if (isOpX<MPZ>(lhs->right())) coef = lhs->right(), remain = lhs->left();
    if (coef != NULL) {
      coef = mk<UN_MINUS>(mkTerm(mpz_class(boost::lexical_cast<int>(coef) * -1), t->getFactory()));
      t = mk(t->op(), mk<MULT>(coef, remain), rhs);
    } else outs() << "Error, convertNegCoefNum: Unable to locate lhs coefficient.\n";
    return t;
  }

  // Move all neg coef to rhs so lhs doesn't have any negative coefficient
  Expr negativeCoefCheck(Expr t)
  {
    Expr lhs = t->left(), rhs = t->right();
    if (isOpX<UN_MINUS>(lhs->left()))
    {
      Expr coef = lhs->left()->left();
      lhs = mk(lhs->op(), coef, lhs->right());
    } else if (isOpX<UN_MINUS>(lhs->right()))
    {
      Expr coef = lhs->right()->left();
      lhs = mk(lhs->op(), lhs->left(), coef);
    } else {
      return t;
    }
    rhs = mk<MULT>(mk<UN_MINUS>(mkTerm(mpz_class(1), t->getFactory())), rhs);
    if (isOpX<LT>(t)) return mk<GT>(lhs, rhs);
    else if (isOpX<LEQ>(t)) return mk<GEQ>(lhs, rhs);
    else if (isOpX<GT>(t)) return mk<LT>(lhs, rhs);
    else if (isOpX<GEQ>(t)) return mk<LEQ>(lhs, rhs);
    outs() << "Error in negativeCoefCheck(): current comparison for expression ";
    outs() << *t << " is not supported." << endl;
    return NULL;
  }

  Expr vecElemInitInt(Expr t, Expr constVar)
  {
    // outs() << "VecElemInitInt beginning t: " << t << endl; //outTest
    if (isOp<ComparissonOp>(t))
    {
      //EQ or NEQ expression are not currently supported.
      if (isOpX<EQ>(t) || isOpX<NEQ>(t)) return NULL; 
      //ensure y is on lhs, lhs not negative, & get rid of LT and GEQ
      t = singleExprNormPrep(t, constVar, true);
      if (t == NULL) return t;
      // Single conjunct Mult & Div transformation.
      if (isOp<MULT>(t->left()) || isOp<IDIV>(t->left())) t = divMultTransInt(t, constVar);
      // outs() << "VecElemInitInt after t: " << *t << endl << endl; //outTest
      return t;
    } else {
      outs() << "(vecElemInitInt)The input Expr " << *t << " is not comparison!" << endl;
      return NULL;
    }
  }

  // Helper function for coefTrans
  Expr coefApply(Expr t, Expr constVar, int LCM)
  {
    Expr lhs = t->left(), rhs = t->right();
    Expr newCoef = mkTerm(mpz_class(LCM), t->getFactory());
    if (isOp<MULT>(lhs)) {
      Expr origCoef = (isOpX<MPZ>(lhs->left())) ? lhs->left() : lhs->right();
      Expr rhsCoef = mkTerm(mpz_class(LCM / boost::lexical_cast<int>(origCoef)), t->getFactory());
      rhs = mk<MULT>(rhsCoef, rhs);
    } else rhs = mk<MULT>(newCoef, rhs);
    lhs = mk<MULT>(newCoef, constVar);
    return (mk(t->op(), lhs, rhs));
  }

  // helper to find least common multiple.
  int findLCM(int a, int b)
  { // lcm(a,b) = a*b/gcd(a,b) 
    int prod = a * b;
    while (a != b)
    {
      if (a > b) a = a - b;
      else b = b - a;
    }
    return prod / a;
  }

  ExprVector coefTrans(ExprVector sVec, Expr constVar)
  {
    ExprVector outVec;
    int LCM = 1;
    vector<int> intVec;
    // Gather LCM
    for (auto ite = sVec.begin(); ite != sVec.end(); ite++) {
      // outs() << "\tite: " << *ite << endl;
      Expr lhs = (*ite)->left();
      if (isOp<MULT>(lhs)) {
        if (isOpX<MPZ>(lhs->left())) intVec.push_back(boost::lexical_cast<int>(*lhs->left()));
        else if (isOpX<MPZ>(lhs->right())) intVec.push_back(boost::lexical_cast<int>(*lhs->right()));
        else outs() << "Coef not found in " << *ite << endl;
      }
    }
    for (auto i : intVec) LCM = findLCM(LCM, i);
    // Making all Coefs for y into LCM
    if (LCM > 1) for (auto t : sVec) outVec.push_back(coefApply(t, constVar, LCM));
    else for (auto t : sVec) outVec.push_back(t);
    // Append the coefficient at the end
    outVec.push_back(mkTerm(mpz_class(LCM), (*sVec.begin())->getFactory()));
    return outVec;
  }
  
  Expr intQE(ExprSet sSet, Expr constVar)
  {
    ExprSet outSet, upVec, loVec;
    ExprVector sVec;
    Expr factoryGetter = *(sSet.begin());
    /* Transformation Stage */
    for (auto t : sSet) {
      Expr initEx = vecElemInitInt(t, constVar);
      if (initEx != NULL) sVec.push_back(initEx);
      else outSet.insert(t);
    }
    // Coefficient Transformation, and extract the coefficient.
    sVec = coefTrans(sVec, constVar); 
    Expr coef = *(sVec.end() - 1);
    sVec.pop_back();
    // Collecting upper & lower bound
    for (auto ite = sVec.begin(); ite != sVec.end(); ite++) {
      if (isOpX<GT>(*ite)) loVec.insert(*ite);
      else if (isOpX<LEQ>(*ite)) upVec.insert(*ite);
    }
    sVec.clear();
    // Merging upper & lower bound.
    bool divFlag = boost::lexical_cast<int>(coef) > 1 ? true : false;
    while (!loVec.empty()) {
      Expr loBound = (*loVec.begin())->right();
      for (auto loIte = upVec.begin(); loIte != upVec.end(); ++loIte) {
        Expr upBound = (*loIte)->right();
        sVec.push_back(mk<LT>(loBound, upBound));
        if (divFlag)  sVec.push_back(mk<LT>(mk<IDIV>(loBound, coef), mk<IDIV>(upBound, coef)));
      }
      loVec.erase(loVec.begin());
    }
    for(auto t : sVec) outSet.insert(t);
    return conjoin(outSet, factoryGetter->getFactory());
  }


  /* REAL HELPER FUNCTION */
  //used when initializing the element for sVec.
  Expr vecElemInitReal(Expr t, Expr constVar)
  {
    if (isOp<ComparissonOp>(t))
    {
      //EQ or NEQ expression are not currently supported.
      if (isOpX<EQ>(t) || isOpX<NEQ>(t)) return NULL; 
      t = singleExprNormPrep(t, constVar);
      if (t == NULL) return t;
      //MULTIPLICATION TRANSFORMATION
      if (isOp<MULT>(t->left())) t = multTrans(t, constVar);
      return t;
    } else {
      outs() << "(vecElemInitReal)The input Expr " << *t << " is not comparison!" << endl;
      return NULL;
    }
  }

  Expr realQE(ExprSet sSet, Expr constVar)
  {
    ExprSet outSet, upVec, loVec;
    ExprVector sVec;
    Expr factoryGetter = *(sSet.begin());
    // Initializing Expression Vector, ensure y is not on rhs, ensure lhs doesn't have multiplication.
    for (auto t : sSet) {
      Expr initEx = vecElemInitReal(t, constVar);
      if (initEx != NULL) sVec.push_back(initEx);
      else outSet.insert(t);
    }
    // Collecting upper & lower bound
    for (auto ite = sVec.begin(); ite != sVec.end(); ite++) {
      if (isOpX<GT>(*ite) || isOpX<GEQ>(*ite)) loVec.insert(*ite);
      else if (isOpX<LT>(*ite) || isOpX<LEQ>(*ite)) upVec.insert(*ite);
    }
    sVec.clear();
    // Merging upper & lower bound.
    while (!loVec.empty()) {
      Expr loBound = (*loVec.begin())->right();
      bool upGEQ = isOpX<GEQ>(*loVec.begin()) ? true : false;
      for (auto loIte = upVec.begin(); loIte != upVec.end(); ++loIte) {
        Expr upBound = (*loIte)->right();
        if (upGEQ && isOpX<LEQ>(*loIte)) sVec.push_back(mk<LEQ>(loBound, upBound));
        else sVec.push_back(mk<LT>(loBound, upBound));
      }
      loVec.erase(loVec.begin());
    }
    for(auto t : sVec) outSet.insert(t);
    return conjoin(outSet, factoryGetter->getFactory());
  }

  /* MIXED HELPER FUNCTIONS */
  // case for identifying if Mixture is usable
  Expr mixQE(Expr s, Expr constVar, ExprMap &substsMap, ZSolver<EZ3>::Model &m)
  {
    Expr orig = createQuantifiedFormulaRestr(s, constVar), output; //Prepare for sanity check
    ExprSet outSet, temp, sameTypeSet;
    if (constVar == NULL) return s; // taking care of the y does not exist situation.
    Expr yType = bind::typeOf(constVar); // identify and store the type of y.
    // outs() << "constVar: " << *constVar << ", type: " << *yType << endl; //outTest
    // Support for boolean case.
    if (yType == mk<BOOL_TY>(s->efac()))
    {
      if (m.eval(constVar) != constVar) substsMap[constVar] = mk<EQ>(constVar, m.eval(constVar));
      output = simplifyBool(mk<OR>(replaceAll(s, constVar, mk<TRUE>(s->efac())), replaceAll(s, constVar, mk<FALSE>(s->efac()))));
      if (true) {
        SMTUtils u1(s->getFactory());
        outs() << "Before mixQE: " << orig << "\nAfter mixQE: " << output << endl; //outTest
        outs() << "mixQE() Equivalence Check: " << u1.isEquiv(orig, output) << endl << endl; //outTest
        if (contains(output, constVar)) outs() << "MIXQE didn't remove var!\n";
      }
      return output;
    }
    // gather conjuncts that's the same type with y into sameTypeSet.
    getConj(s, temp);
    for (auto t : temp) {
      if (contains (t, constVar)) {
        if (isOpX<NEG>(t) && isOp<ComparissonOp>(t->left()))
          t = mkNeg(t->left());
        if (isOp<ComparissonOp>(t))
        {        
          t = simplifyArithm(reBuildCmp(t, mk<PLUS>(t->arg(0), additiveInverse(t->arg(1))), mkMPZ (0, s->efac())));
          t = ineqSimplifier(constVar, t);
        } else {
          assert (0);
        }
        int intVSreal = intOrReal(t);
        // outs() << bind::typeOf(t->right()) << "\nyType: " << yType << "\nintVSreal: " << intVSreal << endl; //outTest
        if (yType == mk<REAL_TY>(s->efac()) && (intVSreal == -1))
          sameTypeSet.insert(t);
        else if (yType == mk<INT_TY>(s->efac()) && (intVSreal == 1))
          sameTypeSet.insert(t);
        else if (intVSreal != 2) { // if intVSreal == 2, thus t == true, so do nothing in that case.
          outs() << "Nothing eliminated\nyType: " << yType << "\nintVSreal: " << intVSreal << endl; //outTest
          outs() << "contains var? " << contains(s, constVar) << endl; //outTest
          outs() << "s: " << s << endl;
          return s;
        } //no change can be made, return original expr.
      }
      else outSet.insert(t);
    }
    // outs() << "sameTypeSet: " << conjoin(sameTypeSet, s->getFactory()) << endl; // outTest
    if (sameTypeSet.empty()) return conjoin(outSet, s->efac());
    // Append map to substsMap
    substsMap[constVar] = conjoin(sameTypeSet, s->getFactory());
    outSet.insert(yType == mk<REAL_TY>(s->efac()) ? realQE(sameTypeSet, constVar) : intQE(sameTypeSet, constVar));
    output = conjoin(outSet, s->getFactory()); //prepare for Sanity Check

    // SANITY CHECK
    if (true) {
      SMTUtils u1(s->getFactory());
      outs() << "Before mixQE: " << orig << "\nAfter mixQE: " << output << endl; //outTest 
      u1.print(output);
      outs() << "\n";
      outs() << "mixQE() Equivalence Check: " << u1.isEquiv(orig, output) << endl; //outTest

      if (contains(output, constVar)) outs() << "MixedQE didn't eliminate var!" << endl;
      // if (u1.isEquiv(orig, output) == false) exit(0);
    }
    return output;
  }

  /**
   * Simple wrapper
   */
  inline void aeSolveAndSkolemize(Expr s, Expr t, bool skol, bool debug, bool compact, bool split)
  {
    outs() << "t at beginning of aeSolveAndSkolemize" << t << endl;
    ExprSet t_quantified;
    if (t == NULL)
    {
      if (!(isOpX<FORALL>(s) && isOpX<EXISTS>(s->last()))) exit(0);

      s = regularizeQF(s);
      t = s->last()->last();
      for (int i = 0; i < s->last()->arity() - 1; i++)
        t_quantified.insert(bind::fapp(s->last()->arg(i)));

      s = mk<TRUE>(s->getFactory());
    }
    else
    {
      ExprSet s_vars;
      ExprSet t_vars;

      filter (s, bind::IsConst (), inserter (s_vars, s_vars.begin()));
      filter (t, bind::IsConst (), inserter (t_vars, t_vars.begin()));

      // for (auto t : t_vars) t_quantified.insert(t);
      t_quantified = t_vars;
      minusSets(t_quantified, s_vars);
    }

    s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    SMTUtils u1(s->getFactory()); //for future t equivalence test.

    Expr t_orig = t;
    Expr t_orig_qua = createQuantifiedFormulaRestr(t_orig, t_quantified);
    // outs() << "original t after applying quantifiers: " << t_orig_qua << endl << endl;

    t = simplifyBool(t);
    ExprSet hardVars, cnjs;
    filter (t, bind::IsConst (), inserter(hardVars, hardVars.begin()));
    Expr t_qua = createQuantifiedFormulaRestr(t, t_quantified);
    // outs() << "\nt after simplifyBool: " << t << endl;
    // outs() << "t_quantified: " << conjoin(t_quantified, t->getFactory()) << endl;
    // outs() << "hardVars: " << conjoin(hardVars, t->getFactory()) << endl;
    // outs() << "t_qua (t After applying quantifiers): " << t_qua << endl;
    // outs() << "sanity check t after simplifyBool: " << u1.implies(t_qua, t_orig_qua) << u1.implies(t_orig_qua, t_qua) << "\n"; //sanity check

    getConj(t, cnjs);
    minusSets(hardVars, t_quantified);
    // outs() << "hardVars after minusSets: " << conjoin(hardVars, t->getFactory()) << endl;
    
    ExprSet elimSkol; // eliminated skolems
    constantPropagation(hardVars, cnjs, elimSkol, true);
    // outs() << "elimSkol: " << conjoin(elimSkol, t->getFactory()) << endl;
    // t_qua = createQuantifiedFormulaRestr(conjoin(cnjs, t->getFactory()), t_quantified);
    // outs() << "\ncnjs(t) After constantPropagation: " << conjoin(cnjs, t->getFactory()) << endl;
    // outs() << "t_qua (After applying quantifiers): " << t_qua << endl;
    // outs() << "sanity check t after constantPropagation: " 
    //        << u1.implies(t_qua, t_orig_qua) << u1.implies(t_orig_qua, t_qua) << "\n"; //sanity check

    // Expr tmp = simpEquivClasses(hardVars, cnjs, t->getFactory());
    // outs() << "\ncnjs After simpEq`uivClasses: " << conjoin(cnjs, t->getFactory()) << endl;
    // outs() << "tmp after simpEquivClasses with hardVars & cnjs: " << tmp << endl;
    // outs() << "sanity check tmp: " << u1.implies(tmp, t_orig) << u1.implies(t_orig, tmp) << "\n"; 
    
    t = simpleQE(conjoin(cnjs, t->getFactory()), t_quantified, elimSkol);
    // outs() << "\nt after simpleQE with conjoined cnjs: " << t << endl;
    // t_qua = createQuantifiedFormulaRestr(t, t_quantified);
    // outs() << "t_qua: " << t_qua << endl;
    // outs() << "sanity check t: " << u1.implies(t_qua, t_orig_qua) << u1.implies(t_orig_qua, t_qua) << "\n"; 

    // t = tmp; 
    t = simplifyBool(t);
    // outs() << "\nFinal t: " << t << endl;
    // outs() << "sanity check final t: " << u1.implies(t, t_orig_qua) << u1.implies(t_orig_qua, t) << "\n\n\n";
    
    // exit(0);

    if (debug && false) // outTest
    // if (true)
    {
      outs() << "S: " << *s << "\n";
      outs() << "T: \\exists ";
      for (auto &a: t_quantified) outs() << *a << ", ";
      outs() << *t << "\n";
    }

    SMTUtils u(s->getFactory());
    AeValSolver ae(s, t, t_quantified, debug, skol);

    if (ae.solve()){
      outs () << "Iter: " << ae.getPartitioningSize() << "; Result: invalid\n";
      ae.lastSanityCheck();
      ae.printModelNeg();
      outs() << "\nvalid subset:\n";
      u.serialize_formula(simplifyBool(simplifyArithm(ae.getValidSubset(compact))));
    } else {
      outs () << "Iter: " << ae.getPartitioningSize() << "; Result: valid\n";
      ae.lastSanityCheck();
      if (skol)
      {
        Expr skol = ae.getSkolemFunction(compact);
        if (split)
        {
          outs() << "\telimSkol: " << conjoin(elimSkol, s->getFactory()) << endl;
          ExprVector sepSkols;
          for (auto & evar : t_quantified) sepSkols.push_back(mk<EQ>(evar,
                           simplifyBool(simplifyArithm(ae.getSeparateSkol(evar)))));
          for (auto t : elimSkol) sepSkols.push_back(t);
          u.serialize_formula(sepSkols);
          if (debug) 
          {
            for (auto t : elimSkol) sepSkols.push_back(t);
            outs () << "Sanity check [split]: " <<
              u.implies(mk<AND>(s, conjoin(sepSkols, s->getFactory())), t_orig) << "\n";
          }
          
          // u.outSanCheck("extractedSanChecks/multEx10.smt2");
        }
        else
        {
          outs() << "\nextracted skolem:\n";
          u.serialize_formula(simplifyBool(simplifyArithm(skol)));
          if (debug) outs () << "Sanity check: " << u.implies(mk<AND>(s, skol), t_orig) << "\n";
        }
      }
    }
  }

  inline void getAllInclusiveSkolem(Expr s, Expr t, bool debug, bool compact)
  {
    // GF: seems to be broken
    ExprSet s_vars;
    ExprSet t_vars;

    filter (s, bind::IsConst (), inserter (s_vars, s_vars.begin()));
    filter (t, bind::IsConst (), inserter (t_vars, t_vars.begin()));

    ExprSet t_quantified = t_vars;
    // for (auto t : t_vars) t_quantified.insert(t);
    minusSets(t_quantified, s_vars);

    s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    SMTUtils u(s->getFactory());

    if (debug)
    {
      outs() << "S: " << *s << "\n";
      outs() << "T: \\exists ";
      for (auto &a: t_quantified) outs() << *a << ", ";
      outs() << *t << "\n";
    }

    Expr t_init = t;
    ExprVector skolems;
    while (true)
    {
      AeValSolver ae(s, t, t_quantified, debug, true);

      if (ae.solve()){
        if (skolems.size() == 0)
        {
          outs () << "Result: invalid\n";
          ae.printModelNeg();
          outs() << "\nvalid subset:\n";
          u.serialize_formula(ae.getValidSubset(compact));
          return;
        }
        break;
      } else {
        skolems.push_back(ae.getSkolemFunction(compact));
        t = mk<AND>(t, mk<NEG>(ae.getSkolemConstraints(0)));
      }
    }

    Expr skol = skolems.back();
    if (skolems.size() > 1)
    {
      Expr varName = mkTerm <std::string> ("_aeval_tmp_rnd", s->getFactory());
      Expr var = bind::intConst(varName);
      for (int i = skolems.size() - 2; i >= 0; i--)
      {
        skol = mk<ITE>(mk<EQ>(var, mkTerm (mpz_class (i), s->getFactory())),
                       skolems[i], skol);
      }
    }
    if (debug)
    {
      outs () << "Sanity check [all-inclusive]: " <<
        u.implies(mk<AND>(s, skol), t_init) << "\n";
    }
    outs () << "Result: valid\n\nextracted skolem:\n";
    u.serialize_formula(skol);
  };
}

#endif
