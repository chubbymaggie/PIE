#include <algorithm>
#include <fstream>
#include <iostream>
#include <list>
#include <string>
#include <vector>
#include <utility>
#include <locale>

#include <cstdlib>

#include <clang/AST/ExprCXX.h>

#include "ClangSACheckers.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/Analyses/CFGReachabilityAnalysis.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/AnalysisManager.h"

#include "llvm/Support/raw_ostream.h"

#include "tinyxml2.h"

using namespace tinyxml2;
using namespace std;

#define ABDUCER_PATH "__ABDUCER_PATH_FROM_SETUP_SCRIPT__"

string MAIN_FILENAME;
string WORKING_PATH = "__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__/";

unsigned long COUNT = 0, ABDUCTION_COUNT = 0, VERIFICATION_COUNT = 0;

struct PredicateNode {
    string val;
    list<PredicateNode> children;
};

enum CheckStatus { FAILED, PASSED, VERIFIED };
struct CheckResult {
  CheckStatus status;
  PredicateNode guess;
};

using namespace clang;
using namespace ento;

namespace {

  class LoopInvariantChecker : public Checker<check::ASTDecl<FunctionDecl>> {

  public:
    void checkASTDecl(const Decl *D,
                      AnalysisManager &mgr,
                      BugReporter &BR) const;
  };

} // end anonymous namespace


/*
 * Anonymous namespace for all the helper functions
 */
namespace {

  //FIXME: Add support for whole word replacement only
  void replaceAll(string &str, const string &from, const string &to) {
    if(from.empty()) return;

    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != string::npos) {
      str.replace(start_pos, from.length(), to);
      start_pos += to.length();
    }
  }

  string intersperse(string delim, list<string> lstr) {
    if(lstr.empty()) return "";

    string r = lstr.front();
    lstr.pop_front();

    while(!lstr.empty()) {
      r += delim + lstr.front();
      lstr.pop_front();
    }

    return r;
  }

  string PredicateNode2MCF_helper(PredicateNode r) {
    if(!r.children.size())
      return r.val;

    list<string> args;
    transform(r.children.begin(), r.children.end(), std::back_inserter(args), PredicateNode2MCF_helper);
    if(!isalpha(r.val[0])) {
      if(r.val == "!")
        return "(!" + args.front() + ")";
      else
        return "(" + intersperse(" " + r.val + " ", args) + ")";
    } else {
      return r.val + "(" + intersperse(", ", args) + ")";
    }
  }

  string PredicateNode2MCF(PredicateNode r) {
    string mcf = PredicateNode2MCF_helper(r);

    replaceAll(mcf, "get(", "#get(");
    replaceAll(mcf, "cat(", "#cat(");
    replaceAll(mcf, "has(", "#has(");
    replaceAll(mcf, "eql(", "#eql(");
    replaceAll(mcf, "ind(", "#ind(");
    replaceAll(mcf, "len(", "#len(");
    replaceAll(mcf, "rep(", "#rep(");
    replaceAll(mcf, "sub(", "#sub(");

    return mcf;
  }

  PredicateNode XMLElement2PredicateNode(XMLElement *x) {
    PredicateNode r;

    XMLPrinter p;
    x->Accept(&p);

    if(!(x->FirstChildElement("expr"))) {
      r.val = x->GetText();
    } else {
      x = x->FirstChildElement("expr");
      r.val = x->GetText();
      while(x = x->NextSiblingElement("expr")) {
        r.children.push_back(XMLElement2PredicateNode(x));
      }
    }

    return r;
  }

  PredicateNode escape(PredicateNode node) {
    replaceAll(node.val, "&amp;", "&");
    replaceAll(node.val, "&gt;", ">");
    replaceAll(node.val, "&lt;", "<");

    list<PredicateNode> nchildren;
    for(auto & c : node.children)
      nchildren.push_back(escape(c));
    node.children = nchildren;

    return node;
  }

  PredicateNode XMLDoc2PredicateNode(string file) {
    XMLDocument xmldoc;
    xmldoc.LoadFile(file.c_str());
    return escape(XMLElement2PredicateNode(xmldoc.FirstChildElement("expr")));
  }

  PredicateNode substituteVar(PredicateNode t, string var, PredicateNode r) {
    PredicateNode res;
    if(t.children.empty() && t.val == var) {
      res.val = r.val;
      res.children = r.children;
    } else {
      res.val = t.val;
      for(auto & c : t.children)
        res.children.push_back(substituteVar(c, var, r));
    }

    return res;
  }

  PredicateNode getAbductionResultFor(const PredicateNode pred) {
    string target = WORKING_PATH + "/" + to_string(++COUNT) + "A" + to_string(++ABDUCTION_COUNT) + ".mcf";
    {
      ofstream mcf_file(target);
      mcf_file << ("-\n-\n" + PredicateNode2MCF(pred));
    }

    string command = ABDUCER_PATH "/abduce.sh ";
    command += target;
    command += " > /dev/null";
    system(command.c_str());

    command = WORKING_PATH + "/mcf2xml ";
    command += target;
    command += ".sinf > ";
    command += target + ".xml";
    system(command.c_str());

    return XMLDoc2PredicateNode(target + ".xml");
  }

  bool chkVALID(const PredicateNode pred, bool add_counter = false) {
    string target = WORKING_PATH + "/" + to_string(++COUNT) + "V" + to_string(++VERIFICATION_COUNT) + ".mcf";
    {
      ofstream mcf_file(target);
      mcf_file << ("-\n-\n" + PredicateNode2MCF(pred));
    }

    string command = WORKING_PATH + "/chkVALID ";
    command += target;
    command += " 0 > ";
    command += target + ".res 2>/dev/null";
    system(command.c_str());

    string result;
    {
      ifstream in(target + ".res");
      getline(in, result);
    }

    if(result.substr(0,5) == "VALID") return true;

    if(add_counter) {
      string command = WORKING_PATH + "/add_counter " + WORKING_PATH + "/final_tests " + target + ".res";
      system(command.c_str());
    }

    return false;
  }

  PredicateNode simplify(PredicateNode pred) {
    string target = WORKING_PATH + "/" + to_string(++COUNT) + "S.mcf";
    {
      ofstream mcf_file(target);
      mcf_file << PredicateNode2MCF(pred);
    }

    string command = WORKING_PATH + "/simplify ";
    command += target;
    command += " 0 > ";
    command += target + ".sim 2>/dev/null";
    system(command.c_str());

    command = WORKING_PATH + "/mcf2xml ";
    command += target;
    command += ".sim > ";
    command += target + ".xml";
    system(command.c_str());

    return XMLDoc2PredicateNode(target + ".xml");
  }

  PredicateNode getASTFor(const Expr * pred) {
    string mcf;
    {
      llvm::raw_string_ostream mcf_stream(mcf);
      LangOptions lo;
      pred -> printPretty(mcf_stream, nullptr, PrintingPolicy(lo));
    }

    // replaceAll(mcf, "true", "1=1");
    // replaceAll(mcf, "false", "1=0");
    replaceAll(mcf, "==", "=");
    replaceAll(mcf, "&&", "&");
    replaceAll(mcf, "||", "|");

    replaceAll(mcf, "get(", "#get(");
    replaceAll(mcf, "cat(", "#cat(");
    replaceAll(mcf, "has(", "#has(");
    replaceAll(mcf, "eql(", "#eql(");
    replaceAll(mcf, "ind(", "#ind(");
    replaceAll(mcf, "len(", "#len(");
    replaceAll(mcf, "rep(", "#rep(");
    replaceAll(mcf, "sub(", "#sub(");

    string target = "/tmp/" + MAIN_FILENAME + "_ast_" + to_string(COUNT);
    {
      ofstream mcf_file(target + ".mcf");
      mcf_file << mcf;
    }

    string command = WORKING_PATH + "/mcf2xml ";
    command += target;
    command += ".mcf > ";
    command += target + ".xml";
    system(command.c_str());

    return XMLDoc2PredicateNode(target + ".xml");
  }

  bool isUnknownFunction(Expr *expr) {
    expr = expr->IgnoreCasts();

    if(dyn_cast<CXXConstructExpr>(expr)) return true;

    CallExpr *ce = dyn_cast<CallExpr>(expr);
    if(!ce) return false;

    FunctionDecl *fd = ce->getDirectCallee();
    if(!fd || fd->getNameAsString().find("unknown") == string::npos)
      return false;

    return true;
  }

  PredicateNode wpOfVarDecl(PredicateNode pred, const VarDecl *vdecl) {
    if(!vdecl->hasInit()) return pred;

    Expr *expr = const_cast<Expr*>(vdecl->getInit()->IgnoreCasts());
    if(isUnknownFunction(expr)) return pred;

    return substituteVar(pred, vdecl->getNameAsString(), getASTFor(expr));
  }

  PredicateNode wpOfCallExpr(PredicateNode pred, const CallExpr *call) {
    const FunctionDecl *fd = call->getDirectCallee();
    if(!fd) return pred;

    IdentifierInfo *FnInfo = fd->getIdentifier();
    if (!FnInfo) return pred;

    if(FnInfo->isStr("assert") || FnInfo->isStr("static_assert"))
      return {"&", {pred, getASTFor(const_cast<Expr*>(call->getArg(0)->IgnoreCasts()))}};
    else if(FnInfo->isStr("assume"))
      return {"|", {{"!", {getASTFor(const_cast<Expr*>(call->getArg(0)->IgnoreCasts()))}}, pred}};
    else if(FnInfo->isStr("set"))
      return substituteVar(
          pred,
          dyn_cast<DeclRefExpr>(call->getArg(0)->IgnoreCasts())->getFoundDecl()->getNameAsString(),
          getASTFor(const_cast<Expr*>(call->getArg(1))->IgnoreCasts()));

    return pred;
  }

  PredicateNode wpOfDeclStmt(PredicateNode pred, const DeclStmt * decls) {
    for(DeclStmt::const_decl_iterator di = decls->decl_begin(); di != decls->decl_end(); ++di)
      if(const VarDecl * vdecl = dyn_cast<VarDecl>(*di))
        pred = wpOfVarDecl(pred, vdecl);
    return pred;
  }

  PredicateNode wpOfUnaryOperator(PredicateNode pred, const UnaryOperator * uop) {
    if(uop->getOpcode() == UO_PostInc || uop->getOpcode() == UO_PreInc)
      return substituteVar(pred,
                           (dyn_cast<DeclRefExpr>(uop->getSubExpr()))->getNameInfo().getAsString(),
                           PredicateNode {"+", {
                             getASTFor(uop->getSubExpr()),
                             PredicateNode {"1", {}}}});
    else if(uop->getOpcode() == UO_PostDec || uop->getOpcode() == UO_PreDec)
      return substituteVar(pred,
                           (dyn_cast<DeclRefExpr>(uop->getSubExpr()))->getNameInfo().getAsString(),
                           PredicateNode {"-", {
                             getASTFor(uop->getSubExpr()),
                             PredicateNode {"1", {}}}});
    return pred;
  }

  PredicateNode wpOfBinaryOperator(PredicateNode pred, const BinaryOperator * bop) {
    if(bop->getOpcode() == BO_Assign) {
      if(!isUnknownFunction(bop->getRHS()->IgnoreCasts()))
        return substituteVar(pred,
                             (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString(),
                             getASTFor(bop->getRHS()));
    } if(bop->getOpcode() == BO_AddAssign) {
      return substituteVar(pred,
                           (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString(),
                           PredicateNode {"+", {getASTFor(bop->getLHS()), getASTFor(bop->getRHS())}});
    }
    return pred;
  }

  PredicateNode wpOfStmt(PredicateNode pred, const Stmt *stmt) {
    if(const CallExpr *call = dyn_cast<CallExpr>(stmt))
      return wpOfCallExpr(pred, call);
    else if(const DeclStmt *decls = dyn_cast<DeclStmt>(stmt))
      return wpOfDeclStmt(pred, decls);
    else if(const UnaryOperator *uop = dyn_cast<UnaryOperator>(stmt)) {
      if(uop->isIncrementDecrementOp())
        return wpOfUnaryOperator(pred, uop);
    } else if(const BinaryOperator *bop = dyn_cast<BinaryOperator>(stmt)) {
      if(bop->isAssignmentOp())
        return wpOfBinaryOperator(pred, bop);
    } //else
      //stmt->dump();
    return pred;
  }

  PredicateNode wpOfBlock(PredicateNode pred, const CFGBlock *block) {
    for(CFGBlock::const_reverse_iterator bi = block->rbegin(); bi != block->rend(); ++bi)
      if(Optional<CFGStmt> cs = bi->getAs<CFGStmt>())
        if(const Stmt *stmt = cs->getStmt())
          pred = wpOfStmt(pred, stmt);
    return pred;
  }

  bool isReachable(CFGReverseBlockReachabilityAnalysis *reachables,
                   const CFGBlock *src, const CFGBlock *dst) {
    return (src == dst || reachables->isReachable(src, dst));
  }

  PredicateNode wpOfSubgraph(PredicateNode pred, CFGBlock *from, CFGBlock *to,
                             const DominatorTree* dom_tree,
                             CFGReverseBlockReachabilityAnalysis *reachables) {
    if(from == to)
      return wpOfBlock(pred, from);

    CFGBlock* single;
    register unsigned cnt = 0;
    for(CFGBlock::const_pred_iterator pre = from->pred_begin(), epre = from->pred_end(); pre != epre; ++pre)
      if(isReachable(reachables, to, *pre) && !dom_tree->dominates(from, *pre)) {
        ++cnt;
        single = *pre;
      }

    if(cnt == 1)
      return wpOfSubgraph(wpOfBlock(pred, from), single, to, dom_tree, reachables);

    cnt = 0;
    for(CFGBlock::const_succ_iterator succ = to->succ_begin(), esucc = to->succ_end(); succ != esucc; ++succ)
      if(isReachable(reachables, *succ, from)) {
        ++cnt;
        single = *succ;
      }

    if(cnt == 1)
      return wpOfBlock(wpOfSubgraph(pred, from, single, dom_tree, reachables), to);

    //FIXME: Exponential exploration happening. Jump from dominator to dominator

    //FIXME: Assumed order: then, else
    bool non_deterministic = false;
    Expr* cond_expr = dyn_cast<Expr>(to->getTerminatorCondition(false));
    PredicateNode cond;

    if(isUnknownFunction(cond_expr)) {
      non_deterministic = true;
      cond = PredicateNode {"true", {}};
    } else
      cond = getASTFor(cond_expr);
    PredicateNode ncond {"!", {cond}};

    return wpOfBlock(
        {"&", {
            {"|", {wpOfSubgraph(pred, from, *(to->succ_begin()), dom_tree, reachables), ncond}},
            {"|", {wpOfSubgraph(pred, from, *(to->succ_begin() + 1), dom_tree, reachables), non_deterministic ? ncond : cond}}}},
        to);
  }

  PredicateNode abduce(PredicateNode query) {
    llvm::errs() << "\n   [Q] Abduction query = " << PredicateNode2MCF(query) << "\n";
    PredicateNode res = getAbductionResultFor(query);
    llvm::errs() << "\n     - Result = " << PredicateNode2MCF(res) << "\n";
    return res;
  }

  CheckResult checkValidity(PredicateNode pred,
                            CFGBlock *loop_head,
                            CFG *cfg,
                            DominatorTree *dom_tree,
                            CFGReverseBlockReachabilityAnalysis *reachables,
                            PredicateNode guard,
                            PredicateNode nguard);

  CheckResult checkPreconditionValidity(PredicateNode pred,
                                        CFGBlock* loop_head,
                                        CFG * cfg,
                                        DominatorTree *dom_tree,
                                        CFGReverseBlockReachabilityAnalysis *reachables,
                                        PredicateNode guard,
                                        PredicateNode nguard) {

    PredicateNode verif = wpOfSubgraph(pred, loop_head, &(cfg->getEntry()), dom_tree, reachables);

    llvm::errs() << "\n   [V" << VERIFICATION_COUNT+1 << "] Verification query {pre} = "
                 << PredicateNode2MCF(verif) << "\n";

    bool res;
    llvm::errs() << "     - Result = " << (res = chkVALID(verif, true)) << "\n";

    if(!res) {
      llvm::errs() << "\n ----------------------------------------< RESTART >---------------------------------------- \n";
      return checkValidity(PredicateNode {"true", {}}, loop_head, cfg, dom_tree, reachables, guard, nguard);
    }

    return CheckResult { PASSED, pred };
  }

  CheckResult checkInductiveValidity(PredicateNode pred,
                                     CFGBlock *loop_head,
                                     CFG *cfg,
                                     DominatorTree *dom_tree,
                                     CFGReverseBlockReachabilityAnalysis *reachables,
                                     PredicateNode guard,
                                     PredicateNode nguard) {

    CFGBlock* end_loop;
    for(CFGBlock::const_pred_iterator pred = loop_head->pred_begin(), epred = loop_head->pred_end(); pred != epred; ++pred)
      if(dom_tree->dominates(loop_head, *pred)) {
        end_loop = *pred;
        break;
      }

    PredicateNode wp = wpOfSubgraph(pred, end_loop, loop_head, dom_tree, reachables);
    PredicateNode verif {"|", {{"!", {pred}}, nguard, wp}};

    llvm::errs() << "\n   [V" << VERIFICATION_COUNT+1 << "] Verification query {ind} = "
                 << PredicateNode2MCF(verif) << "\n";

    bool res;
    llvm::errs() << "     - Result = " << (res = chkVALID(verif)) << "\n";

    if(!res) {
      pred = simplify(PredicateNode {"&", {abduce(verif), pred}});
      return checkValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard);
    }

    return CheckResult { PASSED, pred };
  }

  CheckResult checkPostconditionValidity(PredicateNode pred,
                                         CFGBlock *loop_head,
                                         CFG *cfg,
                                         DominatorTree *dom_tree,
                                         CFGReverseBlockReachabilityAnalysis *reachables,
                                         PredicateNode guard,
                                         PredicateNode nguard) {

    CFGBlock *post_loop;
    for(CFGBlock::const_succ_iterator succ = loop_head->succ_begin(), esucc = loop_head->succ_end(); succ != esucc; ++succ)
      if(dom_tree->dominates(*succ, &(cfg->getExit()))) {
        post_loop = *succ;
        break;
      }
    PredicateNode post_cond = wpOfSubgraph({"true", {}}, &(cfg->getExit()), post_loop, dom_tree, reachables);
    PredicateNode verif {"|", {{"!", {pred}}, guard, post_cond}};

    llvm::errs() << "\n   [V" << VERIFICATION_COUNT+1 << "] Verification query {pos} = "
                 << PredicateNode2MCF(verif) << "\n";

    bool res;
    llvm::errs() << "     - Result = " << (res = chkVALID(verif)) << "\n";

    if(!res) {
      pred = simplify({"&", {abduce(verif), pred}});
      return checkValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard);
    }

    return CheckResult { PASSED, pred };
  }

  CheckResult checkValidity(PredicateNode pred,
                            CFGBlock *loop_head,
                            CFG *cfg,
                            DominatorTree *dom_tree,
                            CFGReverseBlockReachabilityAnalysis *reachables,
                            PredicateNode guard,
                            PredicateNode nguard) {
    llvm::errs() << "\n   # Invariant Guess = " << PredicateNode2MCF(pred) << "\n";

    CheckResult cr;

    if((cr = checkPreconditionValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard)).status != PASSED)
      return cr;

    if((cr = checkPostconditionValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard)).status != PASSED)
      return cr;

    if((cr = checkInductiveValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard)).status != FAILED)
      return CheckResult { VERIFIED, cr.guess};

    return { FAILED, cr.guess };
  }

} // end anonymous namespace


void LoopInvariantChecker :: checkASTDecl(const Decl *D,
                                          AnalysisManager &mgr,
                                          BugReporter &BR) const {
  const FunctionDecl *fd = dyn_cast<FunctionDecl>(D);
  if(!fd) return;

  IdentifierInfo *FnInfo = fd->getIdentifier();
  if(!FnInfo || !FnInfo->isStr("main")) return;

  CFG *cfg = mgr.getCFG(D);
  if(!cfg) return;

  StringRef main_path = mgr.getSourceManager().getFilename(D->getLocation());
  MAIN_FILENAME = main_path.drop_front(main_path.rfind('/') + 1).str();
  WORKING_PATH += MAIN_FILENAME;

  DominatorTree dom_tree;
  dom_tree.buildDominatorTree(* mgr.getAnalysisDeclContext(D));

  CFGReverseBlockReachabilityAnalysis reachables(*cfg);

  //FIXME: Single loop assumed
  CFGBlock *loop_head;
  vector<bool> isLoopHeader(cfg->getNumBlockIDs());

  for(CFG::iterator it = cfg->begin(), ei = cfg->end(); it != ei; ++it) {
    CFGBlock *block = *it;
    for(CFGBlock::succ_iterator succ = block->succ_begin(), esucc = block->succ_end(); succ != esucc; ++succ) {
      if(dom_tree.dominates(*succ, block)) {
        isLoopHeader[(*succ)->getBlockID()] = true;
        loop_head = *succ;
        break;
      }
    }
  }

  Expr *guard_expr = dyn_cast<Expr>(loop_head -> getTerminatorCondition(false));
  PredicateNode guard;

  llvm::errs() << "\n   + Found guard in B" << loop_head->getBlockID() << "\n";

  bool non_deterministic = false;
  //FIXME: The guard may `contain' a call instead of `being' a  call
  if(isUnknownFunction(guard_expr)) {
    non_deterministic = true;
    guard = PredicateNode {"true", {}};
    llvm::errs() << "     - guard : NON-DETERMINISTIC\n";
  } else {
    guard = getASTFor(guard_expr);
    llvm::errs() << "     - guard : " << PredicateNode2MCF(guard) << "\n";
  }

  PredicateNode nguard {"!", {guard}};

  //FIXME: Generalize treatment of non-determinism. Can occur elsewhere too.

  // nguard and guard behaviour:
  // NON-DETERMINISTIC ... guard = true  ; nguard = false
  // DETERMINISTIC     ... guard = guard ; nguard = !guard

  CheckResult res = checkValidity(PredicateNode {"true", {}}, loop_head, cfg, &dom_tree, &reachables, non_deterministic ? nguard : guard, nguard);

  if(res.status == VERIFIED)
    llvm::errs() << "\n\n[###] Final invariant = " << PredicateNode2MCF(res.guess) << " [###]\n";
  else
    llvm::errs() << "\n\n[---] Invariant could not be determined. [---]\n";
}

void ento::registerLoopInvariantChecker(CheckerManager &mgr) {
  mgr.registerChecker<LoopInvariantChecker>();
}
