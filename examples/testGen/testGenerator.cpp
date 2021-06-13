#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <vector>
#include <chrono>
#include <sys/time.h>

using namespace std;

// var "y" has to be on pos 0, other variables can be anywhere after that.
const string constY = "y";
// File count, expression count per example(at least 1), length of final Expression (at least 1)
const int EXPR_COUNT_MIN = 1, EXPR_COUNT_MAX = 4, MIN_EXPR_LEN = 1, MAX_EXPR_LEN = 3;
const int CONST_MAX = 5;
const bool NEQ = true;


//Variable declaration generator
string declVar();
//wrapping around the conjunctions
void conGenWrap(); 
//Generate conjunctions of expressions.
string conGen(int exprCount);
//Comparison Expression Generation
string compExprGen();
//Simple Expression Generator given a variable
string exprGen(string var);
//Simple Expression Generator with random variables conjoin with +
string exprGenWRandVars();
//Generate random comparison operator
string compOpGen();
//Generate random arithmetic operator
string opGen(); //only * and /

int main(int argc, char ** argv)
{
  struct timeval time_now{};
  gettimeofday(&time_now, nullptr);
  int timeSeed = static_cast<int>(time_now.tv_usec);
  srand(timeSeed);
  conGenWrap();
  return 0;
}

string declVar()
{
  string declOut = "(declare-fun y () Int)\n";
  for (int i = 1; i <= MAX_EXPR_LEN; i++) declOut = declOut + "(declare-fun x" + to_string(i) + " () Int)\n";
  return declOut;
}
void conGenWrap() 
{
  // ofstream fileOut;
  // for (int curFile = 1; curFile <= F_COUNT; ++curFile)
  // {
  //   fileOut.open("genEx" + to_string(curFile) + ".smt2");
  //   fileOut << declVar();
  //   fileOut << endl << "(assert (" << endl; // starting assertion
  //   fileOut << conGen(rand() % (EXPR_COUNT_MAX - EXPR_COUNT_MIN + 1) + EXPR_COUNT_MIN);
  //   fileOut << endl << "))"; // the end
  //   fileOut.close();
  // }
  cout << declVar();
  cout << endl << "(assert (" << endl; // starting assertion
  cout << conGen(rand() % (EXPR_COUNT_MAX - EXPR_COUNT_MIN + 1) + EXPR_COUNT_MIN);
  cout << endl << "))"; // the end
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
  string exprStr = "", op = compOpGen();
  string lhsExpr = ("(" + exprGen(constY) + ")"), rhsExpr = exprGenWRandVars();
  if ((rand() % 2) == 1) swap(lhsExpr, rhsExpr);
  exprStr = op + lhsExpr + " " + rhsExpr;
  if (op == "= " && (rand() % 2) == 1 && NEQ) exprStr = ("not (" + exprStr + ")"); //convert 50% of "=" to "!="
  return exprStr;
}
string exprGen(string var)
{
  string finResult;
  if (var == "y") finResult = opGen();
  else finResult = opGen();
  if (finResult == "/ ")
    return (finResult + var + " " + to_string((rand() % (CONST_MAX - 2)) + 2));
  else if (finResult == "* ") {
    bool neg = (rand() % 2 == 1 ? true : false);
    int coef = (rand() % (CONST_MAX - 2) + 2) + 1;
    if (neg) return (finResult + "(- " + to_string(coef) + ") " + var);
    return (finResult + to_string(coef) + " " + var);
  }
  return (finResult + var + " " + to_string((rand() % (CONST_MAX -1)) +1));
}
string exprGenWRandVars()
{
  int exprCount = rand() % (MAX_EXPR_LEN - MIN_EXPR_LEN + 1) + MIN_EXPR_LEN;
  vector<string> vars;
  for (int i = 1; i <= exprCount; i++) vars.push_back("x" + to_string(i));
  random_shuffle (vars.begin(), vars.end());
  string retStr = "";
  for (auto i : vars)
  {
    if (retStr == "") retStr = "(" + exprGen(i) + ")";
    else retStr = "(+ " + retStr + " (" + exprGen(i) + "))";
  }
  if (rand() % 2 == 1) retStr = "(+ " + retStr + " " + to_string((rand() % (CONST_MAX - 1)) + 1) + " )";
  return retStr;
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
  int choice = rand() % 2;
  switch (choice)
  {
    case 0: return "* ";
    case 1: return "/ ";
    // case 2: return "+ ";
    // case 3: return "- ";
  }
  cout << "ERROR: occured in opGen()." << endl;
  return 0;
}