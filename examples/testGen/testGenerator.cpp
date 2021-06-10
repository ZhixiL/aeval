#include <iostream>
#include <fstream>
#include <string>
using namespace std;

// var "y" has to be on pos 0, other variables can be anywhere after that.
const string VARS[] = {"y", "x"};
const int VARS_SIZE = sizeof(VARS) / sizeof(VARS[0]);
// File count, expression count per example(at least 1), length of final Expression (at least 2)
const int F_COUNT = 10, EXPR_COUNT_MIN = 5, EXPR_COUNT_MAX = 20, MAX_EXPR_LEN = 10, MIN_EXPR_LEN = 5;
const int CONST_MAX = 100;


//Variable declaration generator
string declVar(string input);
//wrapping around the conjunctions
void conGenWrap(); 
//Generate conjunctions of expressions.
string conGen(int exprCount);
//Comparison Expression Generation
string compExprGen();
//Expression generation (without comparison)
string expr(int ct);
//Expression generation (without comparison, with y)
string exprWY(int ct, bool y = true);
//Generate random comparison operator
string compOpGen();
//Generate random arithmetic operator
string opGen();
//Generate y side specific random arithmetic operator
string opGenWY(); // for now, only support * and /
//Generate random variable that's not y from VARS[]
string varGen();

int main()
{
  conGenWrap();
  return 0;
}

string declVar(string input)
{
  return "(declare-fun " + input + " () Int)";
}
void conGenWrap()
{
  ofstream fileOut;
  for (int curFile = 1; curFile <= F_COUNT; ++curFile)
  {
    fileOut.open("genEx" + to_string(curFile) + ".smt2");
    for (auto variable : VARS) fileOut << (declVar(variable)) << endl;
    fileOut << endl << "(assert (" << endl; // starting assertion
    fileOut << conGen(rand() % (EXPR_COUNT_MAX - EXPR_COUNT_MIN + 1) + EXPR_COUNT_MIN);
    fileOut << endl << "))"; // the end
    fileOut.close();
  }
}
string conGen(int exprCount)
{
  int lCount = exprCount / 2 + exprCount % 2;
  int rCount = exprCount - lCount;
  if (exprCount > 3)
    return ("and (" + conGen(lCount) + ") (" + conGen(rCount) +")");
  else if (exprCount > 2)
    return ("and (" + conGen(lCount) + ") (\n" + compExprGen() + "\n)");
  else if (exprCount > 1)
    return ("and (\n" + compExprGen() + "\n) (\n" + compExprGen() + "\n)");
  else
    return compExprGen();
}
string compExprGen()
{
  int exprCt = rand() % (MAX_EXPR_LEN - MIN_EXPR_LEN + 1) + MIN_EXPR_LEN;
  int lhsCt = rand() % (exprCt - 1) + 1;
  int rhsCt = exprCt - lhsCt;
  string exprStr = "", op = compOpGen(), lhsExpr = exprWY(lhsCt), rhsExpr = expr(rhsCt);
  if ((rand() % 2) == 1) {
    swap(lhsExpr, rhsExpr);
    swap(lhsCt, rhsCt);
  }
  if (lhsCt > 1 && rhsCt > 1) exprStr = op + "(" + lhsExpr + ") (" + rhsExpr + ")";
  else if (lhsCt > 1) exprStr = op + "(" + lhsExpr + ") " + rhsExpr;
  else if (rhsCt > 1) exprStr = op + lhsExpr + " (" + rhsExpr + ")";
  else exprStr = op + lhsExpr + " " + rhsExpr;
  if (op == "= " && (rand() % 2) == 1) exprStr = ("not (" + exprStr + ")"); //convert 50% of "=" to "!="
  return exprStr;
}
string expr(int ct)
{
  if(ct > 1)
  {
    int lhsCt = rand() % (ct - 1) + 1, rhsCt = ct - lhsCt;
    string exprFin = opGen();
    if (lhsCt > 1) exprFin = exprFin + "(" + expr(lhsCt) + ") ";
    else exprFin = exprFin + expr(lhsCt) + " ";
    if (rhsCt > 1) exprFin = exprFin + "(" + expr(rhsCt) + ")";
    else exprFin = exprFin + expr(rhsCt);
    return exprFin;
  }
  // 50% for variable, 50% for constant
  if (rand() % 2 == 1) return varGen();
  return to_string(rand() % CONST_MAX + 1);
}
string exprWY(int ct, bool y)
{
  if(ct > 1)
  {
    bool lhsY = false, rhsY = false;
    int lhsCt = rand() % (ct - 1) + 1, rhsCt = ct - lhsCt;
    string exprFin = opGenWY();
    if (y) // check if y is inherited.
    {
      //ensuring y is on lhs for division.
      if (exprFin == "/ ") lhsY = true; 
      //50% for either side to get y.
      else (rand() % 2 == 1) ? lhsY = true : rhsY = true; 
    }
    if (lhsCt > 1) exprFin = exprFin + "(" + exprWY(lhsCt, lhsY) + ") ";
    else exprFin = exprFin + exprWY(lhsCt, lhsY) + " ";
    if (rhsCt > 1) exprFin = exprFin + "(" + exprWY(rhsCt, rhsY) + ")";
    else exprFin = exprFin + exprWY(rhsCt, rhsY);
    return exprFin;
  }
  if (y) return VARS[0];
  return to_string(rand() % CONST_MAX + 1);
}
string compOpGen()
{
  int choice = rand() % 6;
  switch (choice)
  {
    case 0: return "= ";
    case 1: return "> ";
    case 2: return ">= ";
    case 3: return "< ";
    case 4: return "<= ";
  }
  return "= "; // Double chance for eq, for later wrapping of neq.
}
string opGen()
{
  int choice = rand() % 4;
  switch (choice)
  {
    case 0: return "+ ";
    case 1: return "- ";
    case 2: return "* ";
    case 3: return "/ ";
  }
  cout << "ERROR: occured in opGen()." << endl;
  return 0;
}
string opGenWY()
{
  int choice = rand() % 2;
  switch (choice)
  {
    case 0: return "* ";
    case 1: return "/ ";
  }
  cout << "ERROR: occured in opGenWY()." << endl;
  return 0;
}
string varGen()
{
  if (VARS_SIZE > 1) return VARS[rand() % (VARS_SIZE - 1) + 1];
  else cout << "ERROR, sizeof(VARS) should be > 2";
  return 0;
}