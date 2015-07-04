#include <fstream>
#include <iostream>
#include <regex>
#include <set>
#include <string>
#include <vector>
#include <utility>

#include <cstdlib>

#include "ClangSACheckers.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/Analyses/CFGReachabilityAnalysis.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/HeaderSearch.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/AnalysisManager.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/IntrusiveRefCntPtr.h"
#include "llvm/Support/raw_ostream.h"

#include "../../Sema/TreeTransform.h"

#define MISTRAL_PATH __MISTRAL_PATH_FROM_SETUP_SCRIPT__
#define ABDUCER_PATH __ABDUCER_PATH_FROM_SETUP_SCRIPT__

std::string WORKING_PATH = __WORKING_PATH_BASE_FROM_SETUP_SCRIPT__ "/";

unsigned long COUNT = 0, ABDUCTION_COUNT = 0, VERIFICATION_COUNT = 0;

namespace clang {

  template<>
  ActionResult<Expr*, true>::ActionResult(const void * cv) {}

}

using namespace clang;
using namespace ento;

namespace {

  typedef std::list<CFGBlock*> CFGPath;

  class LoopInvariantChecker : public Checker<check::ASTDecl<FunctionDecl>> {

  public:
    void checkASTDecl(const Decl *D,
                      AnalysisManager &mgr,
                      BugReporter &BR) const;
  };

  class VarSubstituteTransform : public TreeTransform<VarSubstituteTransform> {

    Expr * val;
    const std::string & var;

  public:
    explicit VarSubstituteTransform(Sema & sema, Expr * val, const std::string & var)
      : TreeTransform<VarSubstituteTransform>(sema), val(val), var(var) {}

    ExprResult TransformDeclRefExpr(DeclRefExpr * dref) {
      if(dref->getNameInfo().getAsString() == var)
        return val;
      return dref;
    }
  };

} // end anonymous namespace


/*
 * Anonymous namespace for all the helper functions
 */
namespace {

  //FIXME: Add support for whole word replacement only
  void replaceAll(std::string& str, const std::string& from, const std::string& to) {
    if(from.empty()) return;

    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
      str.replace(start_pos, from.length(), to);
      start_pos += to.length();
    }
  }

  void writeMCF(const Expr * pred, const std::string & filename) {
    std::string mcf("-\n-\n");
    {
      llvm::raw_string_ostream mcf_stream(mcf);
      LangOptions lo;
      pred -> printPretty(mcf_stream, nullptr, PrintingPolicy(lo));
    }

    replaceAll(mcf, "true", "1=1");
    replaceAll(mcf, "false", "1=0");
    replaceAll(mcf, "==", "=");
    replaceAll(mcf, "&&", "&");
    replaceAll(mcf, "||", "|");

    {
      std::ofstream mcf_file(filename);
      mcf_file << mcf;
    }
  }

  std::set<std::string> getIdentifiersIn(const std::string & exp) {
    std::regex rx("_*[a-zA-Z]+[a-zA-Z0-9_]*");
    std::sregex_iterator rit(exp.begin(), exp.end(), rx);
    std::sregex_iterator rend;

    std::set<std::string> ids;
    while(rit != rend) {
      ids.insert(rit->str());
      rit++;
    }

    return ids;
  }

  std::string joinStringSet(const std::set<std::string> & strs, const std::string & d) {
    return std::accumulate(strs.begin(), strs.end(), std::string(),
                           [d](const std::string & p, std::string x) {
                             return p + x + d;
                           });
  }

  std::string & doCPPify(std::string & c_str) {
    replaceAll(c_str, "&", "&&");
    replaceAll(c_str, "|", "||");
    replaceAll(c_str, "=", "==");
    replaceAll(c_str, "!==", "!=");
    replaceAll(c_str, ">==", ">=");
    replaceAll(c_str, "<==", "<=");

    c_str = "const int " + joinStringSet(getIdentifiersIn(c_str), " = 1, ")
           + "__end__; int res = " + c_str + ";";

    return c_str;
  }

  std::string getAbductionResultFor(const Expr * pred) {
    std::string target = WORKING_PATH + "/" + std::to_string(++COUNT) + "A" + std::to_string(++ABDUCTION_COUNT) + ".mcf";
    writeMCF(pred, target);

    std::string command = ABDUCER_PATH "/abduce.sh ";
    command += target;
    command += " > /dev/null";
    system(command.c_str());

    std::string result;
    {
      std::ifstream in(target + ".sinf");
      std::getline(in, result);
    }
    return result;
  }

  bool chkVALID(const Expr * pred) {
    std::string target = WORKING_PATH + "/" + std::to_string(++COUNT) + "V" + std::to_string(++VERIFICATION_COUNT) + ".mcf";
    writeMCF(pred, target);

    std::string command = MISTRAL_PATH "/example/chkVALID ";
    command += target;
    command += " 0 > ";
    command += target + ".res";
    system(command.c_str());

    std::string result;
    {
      std::ifstream in(target + ".res");
      std::getline(in, result);
    }
    return result.substr(0,5) == "VALID";
  }

  std::string simplify(std::string mcf_pred) {
    std::string target = WORKING_PATH + "/" + std::to_string(++COUNT) + "S.mcf";
    {
      std::ofstream mcf_file(target);
      mcf_file << mcf_pred;
    }

    std::string command = MISTRAL_PATH "/example/simplify ";
    command += target;
    command += " 0 > ";
    command += target + ".sim";
    system(command.c_str());

    {
      std::ifstream in(target + ".sim");
      std::getline(in, mcf_pred);
    }

    return mcf_pred;
  }

  Expr * getASTFor(const std::string & mcf, bool in_mcf = true) {
    std::string c_code = mcf;
    if(in_mcf) doCPPify(c_code);
    {
      std::ofstream out("/tmp/00X00.c");
      out << c_code;
    }

    std::unique_ptr<std::vector<const char *> > args(new std::vector<const char*>());
    args->push_back("/tmp/00X00.c");

    //FIXME: Possible memory leak? When is this ASTUnit destroyed?
    ASTUnit * au = ASTUnit::LoadFromCommandLine(
      &(*args)[0],
      &(*args)[0] + args->size(),
      IntrusiveRefCntPtr<DiagnosticsEngine>(
        CompilerInstance::createDiagnostics(new DiagnosticOptions)),
      StringRef()
    );

    if(au) {
      Decl * d = *(au -> getASTContext() . getTranslationUnitDecl() -> decls_begin());
      while(d -> getNextDeclInContext())
        d = d -> getNextDeclInContext();
      return const_cast<Expr*>(dyn_cast<VarDecl>(d)->getAnyInitializer());
    }

    return nullptr;
  }

  void substituteVarInAST(ASTContext & ac, Expr * & pred, const std::string & var, Expr * val) {
    ASTConsumer astc;
    CompilerInstance ci;

    HeaderSearch hs(IntrusiveRefCntPtr<HeaderSearchOptions>(new HeaderSearchOptions()),
                    ac.getSourceManager(),
                    ac.getDiagnostics(),
                    ac.getLangOpts(),
                    nullptr);

    Preprocessor pp(IntrusiveRefCntPtr<PreprocessorOptions>(new PreprocessorOptions()),
                    ac.getDiagnostics(),
                    const_cast<LangOptions&>(ac.getLangOpts()),
                    ac.getSourceManager(),
                    hs,
                    ci);

    Sema sema(pp, ac, astc, TU_Complete, nullptr);
    pred = VarSubstituteTransform(sema, val, var).TransformExpr(pred).getAs<Expr>();
  }

  Expr * cloneExpr(ASTContext & ac, Expr * pred) {
    substituteVarInAST(ac, pred, "", nullptr);
    return pred;
  }

  void wpOfVarDecl(Expr * & pred, const VarDecl * vdecl) {
    if(vdecl->hasInit())
      substituteVarInAST(vdecl->getASTContext(), pred, vdecl->getNameAsString(),
        new (vdecl->getASTContext()) ParenExpr(
          SourceLocation(), SourceLocation(),
          const_cast<Expr*>(vdecl->getInit())));
  }

  void wpOfCallExpr(Expr * & pred, const CallExpr* call) {
    const FunctionDecl *fd = call->getDirectCallee();
    if(!fd) return;

    IdentifierInfo *FnInfo = fd->getIdentifier();
    if (!FnInfo) return;

    if(FnInfo->isStr("assert") || FnInfo->isStr("static_assert")) {
      pred = new (fd->getASTContext()) ParenExpr(
        SourceLocation(),
        SourceLocation(),
        new (fd->getASTContext()) BinaryOperator(
          pred,
          const_cast<Expr*>(call->getArg(0)),
          BO_LAnd,
          pred->getType(),
          VK_LValue,
          OK_Ordinary,
          SourceLocation(),
          false));
    } else if(FnInfo->isStr("assume")) {
      pred = new (fd->getASTContext()) ParenExpr(
        SourceLocation(),
        SourceLocation(),
        new (fd->getASTContext()) BinaryOperator(
          new (fd->getASTContext()) UnaryOperator(
            const_cast<Expr*>(call->getArg(0)),
            UO_LNot,
            pred->getType(),
            VK_LValue,
            OK_Ordinary,
            SourceLocation()
          ),
          pred,
          BO_LOr,
          pred->getType(),
          VK_LValue,
          OK_Ordinary,
          SourceLocation(),
          false));
    }
  }

  void wpOfDeclStmt(Expr * & pred, const DeclStmt * decls) {
    for(DeclStmt::const_decl_iterator di = decls->decl_begin(); di != decls->decl_end(); ++di)
      if(const VarDecl * vdecl = dyn_cast<VarDecl>(*di))
        wpOfVarDecl(pred, vdecl);
  }

  void wpOfUnaryOperator(Expr * & pred, const UnaryOperator * uop) {
    ASTContext & ac = (dyn_cast<DeclRefExpr>(uop->getSubExpr()))->getDecl()->getASTContext();
    std::string var = (dyn_cast<DeclRefExpr>(uop->getSubExpr()))->getNameInfo().getAsString();

    llvm::APInt onev(32, 1);
    Expr * one = IntegerLiteral::Create(ac, onev, uop->getType(), SourceLocation());

    if(uop->getOpcode() == UO_PostInc || uop->getOpcode() == UO_PreInc) {
      substituteVarInAST(ac, pred, var, new (ac) ParenExpr(
                                          SourceLocation(), SourceLocation(),
                                          new (ac) BinaryOperator(uop->getSubExpr(),
                                                                  one,
                                                                  BO_Add,
                                                                  uop->getType(),
                                                                  VK_LValue,
                                                                  OK_Ordinary,
                                                                  SourceLocation(),
                                                                  false)));
    } else if(uop->getOpcode() == UO_PostDec || uop->getOpcode() == UO_PreDec) {
      substituteVarInAST(ac, pred, var, new (ac) ParenExpr(
                                          SourceLocation(), SourceLocation(),
                                          new (ac) BinaryOperator(uop->getSubExpr(),
                                                                  one,
                                                                  BO_Sub,
                                                                  uop->getType(),
                                                                  VK_LValue,
                                                                  OK_Ordinary,
                                                                  SourceLocation(),
                                                                  false)));
    }
  }

  void wpOfBinaryOperator(Expr * & pred, const BinaryOperator * bop) {
    if(bop->getOpcode() == BO_Assign) {
      ASTContext & ac = (dyn_cast<DeclRefExpr>(bop->getLHS()))->getDecl()->getASTContext();
      std::string var = (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString();
      substituteVarInAST(ac, pred, var, new (ac) ParenExpr(
                                          SourceLocation(), SourceLocation(),
                                          bop->getRHS()));
    } if(bop->getOpcode() == BO_AddAssign) {
      ASTContext & ac = (dyn_cast<DeclRefExpr>(bop->getLHS()))->getDecl()->getASTContext();
      std::string var = (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString();
      substituteVarInAST(ac, pred, var, new (ac) ParenExpr(
                                          SourceLocation(), SourceLocation(),
                                          new (ac) BinaryOperator(bop->getRHS(),
                                                                  bop->getLHS(),
                                                                  BO_Add,
                                                                  bop->getType(),
                                                                  VK_LValue,
                                                                  OK_Ordinary,
                                                                  SourceLocation(),
                                                                  false)));
    }
  }

  void wpOfStmt(Expr * & pred, const Stmt * stmt) {
    if(const CallExpr * call = dyn_cast<CallExpr>(stmt))
      wpOfCallExpr(pred, call);
    else if(const DeclStmt * decls = dyn_cast<DeclStmt>(stmt))
      wpOfDeclStmt(pred, decls);
    else if(const UnaryOperator * uop = dyn_cast<UnaryOperator>(stmt)) {
      if(uop->isIncrementDecrementOp())
        wpOfUnaryOperator(pred, uop);
    } else if(const BinaryOperator * bop = dyn_cast<BinaryOperator>(stmt)) {
      if(bop->isAssignmentOp())
        wpOfBinaryOperator(pred, bop);
    } //else
      //stmt->dump();
  }

  void wpOfBlock(Expr * & pred, const CFGBlock * block) {
    for(CFGBlock::const_reverse_iterator bi = block->rbegin(); bi != block->rend(); ++bi)
      if(Optional<CFGStmt> cs = bi->getAs<CFGStmt>())
        if(const Stmt * stmt = cs->getStmt())
          wpOfStmt(pred, stmt);
  }

  bool isReachable(CFGReverseBlockReachabilityAnalysis * reachables, const CFGBlock * src, const CFGBlock * dst) {
    return (src == dst || reachables->isReachable(src, dst));
  }

  void wpOfSubgraph(Expr * & pred, CFGBlock* from, CFGBlock* to, const DominatorTree* dom_tree,
                    CFGReverseBlockReachabilityAnalysis *reachables, AnalysisManager & mgr) {
    if(from == to) {
      wpOfBlock(pred, from);
      return;
    }

    CFGBlock* single;
    register unsigned cnt = 0;
    for(CFGBlock::const_pred_iterator pred = from->pred_begin(), epred = from->pred_end(); pred != epred; ++pred)
      if(isReachable(reachables, to, *pred) && !dom_tree->dominates(from, *pred)) {
        ++cnt;
        single = *pred;
      }

    if(cnt == 1) {
      wpOfBlock(pred, from);
      wpOfSubgraph(pred, single, to, dom_tree, reachables, mgr);
      return;
    }

    cnt = 0;
    for(CFGBlock::const_succ_iterator succ = to->succ_begin(), esucc = to->succ_end(); succ != esucc; ++succ)
      if(isReachable(reachables, *succ, from)) {
        ++cnt;
        single = *succ;
      }

    if(cnt == 1) {
      wpOfSubgraph(pred, from, single, dom_tree, reachables, mgr);
      wpOfBlock(pred, to);
      return;
    }

    //FIXME: Exponential exploration happening. Jump from dominator to dominator

    //FIXME: Assumed order: then, else
    Expr* cond = dyn_cast<Expr>(to->getTerminatorCondition(false));

    ASTContext & ac = mgr.getASTContext();
    Expr* else_pred = cloneExpr(ac, pred);

    wpOfSubgraph(pred, from, *(to->succ_begin()), dom_tree, reachables, mgr);
    pred = new (ac) ParenExpr(
      SourceLocation(),
      SourceLocation(),
      new (ac) BinaryOperator(
        new (ac) UnaryOperator (
          cond,
          UO_LNot,
          cond->getType(),
          VK_LValue,
          OK_Ordinary,
          SourceLocation()
        ),
        pred,
        BO_LOr,
        cond->getType(),
        VK_LValue,
        OK_Ordinary,
        SourceLocation(),
        false
      ));

    wpOfSubgraph(else_pred, from, *(to->succ_begin() + 1), dom_tree, reachables, mgr);
    else_pred = new (ac) ParenExpr(
      SourceLocation(), SourceLocation(),
      new (ac) BinaryOperator(
        cond,
        else_pred,
        BO_LOr,
        cond->getType(),
        VK_LValue,
        OK_Ordinary,
        SourceLocation(),
        false
      ));

    pred = new (ac) ParenExpr(
      SourceLocation(), SourceLocation(),
      new (ac) BinaryOperator(
        pred,
        else_pred,
        BO_LAnd,
        cond->getType(),
        VK_LValue,
        OK_Ordinary,
        SourceLocation(),
        false
      ));
    wpOfBlock(pred, to);
  }

  std::string abduce(AnalysisManager & mgr, const Expr * query) {
    llvm::errs() << "\n   ? Abduction query = ";
    query -> printPretty(llvm::errs(), nullptr, mgr.getASTContext().getPrintingPolicy());
    llvm::errs() << "\n";

    std::string res = getAbductionResultFor(query);
    llvm::errs() << "\n     - Result = " << res << "\n";
    return res;
  }

  bool checkPreconditionValidity(AnalysisManager & mgr, const std::string & pred, CFGBlock * loop_head,
                                 CFG* cfg, DominatorTree * dom_tree, CFGReverseBlockReachabilityAnalysis * reachables) {
    Expr * verif = getASTFor(pred);

    wpOfSubgraph(verif, loop_head, &(cfg->getEntry()), dom_tree, reachables, mgr);

    llvm::errs() << "\n   [V" << VERIFICATION_COUNT << "] Verification query (pre) = ";
    verif -> printPretty(llvm::errs(), nullptr, mgr.getASTContext().getPrintingPolicy());
    llvm::errs() << "\n";

    bool res;
    llvm::errs() << "     - Result = " << (res = chkVALID(verif)) << "\n";

    return res;
  }

  bool checkValidity(AnalysisManager & mgr,
                     std::string & pred,
                     CFGBlock* loop_head,
                     CFG * cfg,
                     DominatorTree *dom_tree,
                     CFGReverseBlockReachabilityAnalysis *reachables,
                     Expr * guard,
                     Expr * nguard);

  bool checkInductiveValidity(AnalysisManager & mgr,
                              std::string & pred,
                              CFGBlock* loop_head,
                              CFG* cfg,
                              DominatorTree *dom_tree,
                              CFGReverseBlockReachabilityAnalysis *reachables,
                              Expr * guard,
                              Expr * nguard) {

    Expr * inv_guess = getASTFor(pred);

    Expr * verif = getASTFor(pred);
    CFGBlock* end_loop;
    for(CFGBlock::const_pred_iterator pred = loop_head->pred_begin(), epred = loop_head->pred_end(); pred != epred; ++pred)
      if(dom_tree->dominates(loop_head, *pred)) {
        end_loop = *pred;
        break;
      }
    wpOfSubgraph(verif, end_loop, loop_head, dom_tree, reachables, mgr);

    verif = new (mgr.getASTContext()) BinaryOperator(
      new (mgr.getASTContext()) BinaryOperator(
        new (mgr.getASTContext()) UnaryOperator(
          inv_guess,
          UO_LNot,
          guard->getType(),
          VK_LValue,
          OK_Ordinary,
          SourceLocation()
        ),
        nguard,
        BO_LOr,
        guard->getType(),
        VK_LValue,
        OK_Ordinary,
        SourceLocation(),
        false
      ),
      verif,
      BO_LOr,
      guard->getType(),
      VK_LValue,
      OK_Ordinary,
      SourceLocation(),
      false
    );

    llvm::errs() << "\n   [V" << VERIFICATION_COUNT << "] Verification query (ind) = ";
    verif -> printPretty(llvm::errs(), nullptr,
                         mgr.getASTContext().getPrintingPolicy());
    llvm::errs() << "\n";

    bool res;
    llvm::errs() << "     - Result = " << (res = chkVALID(verif)) << "\n";

    if(!res) {
      pred = simplify(abduce(mgr, verif) + " & (" + pred + ")");
      return checkValidity(mgr, pred, loop_head, cfg, dom_tree, reachables, guard, nguard);
    }

    return res;
  }

  bool checkPostconditionValidity(AnalysisManager & mgr,
                                  std::string & pred,
                                  CFGBlock* loop_head,
                                  CFG* cfg,
                                  DominatorTree *dom_tree,
                                  CFGReverseBlockReachabilityAnalysis *reachables,
                                  Expr * guard,
                                  Expr * nguard) {

    Expr * inv_guess = getASTFor(pred);

    Expr * post_cond = getASTFor("true");
    CFGBlock* post_loop;
    for(CFGBlock::const_succ_iterator succ = loop_head->succ_begin(), esucc = loop_head->succ_end(); succ != esucc; ++succ)
      if(dom_tree->dominates(*succ, &(cfg->getExit()))) {
        post_loop = *succ;
        break;
      }
    wpOfSubgraph(post_cond, &(cfg->getExit()), post_loop, dom_tree, reachables, mgr);

    Expr * verif = new (mgr.getASTContext()) BinaryOperator(
      new (mgr.getASTContext()) BinaryOperator(
        new (mgr.getASTContext()) UnaryOperator(
          inv_guess,
          UO_LNot,
          guard->getType(),
          VK_LValue,
          OK_Ordinary,
          SourceLocation()
        ),
        guard,
        BO_LOr,
        guard->getType(),
        VK_LValue,
        OK_Ordinary,
        SourceLocation(),
        false
      ),
      post_cond,
      BO_LOr,
      guard->getType(),
      VK_LValue,
      OK_Ordinary,
      SourceLocation(),
      false
    );

    llvm::errs() << "\n   [V" << VERIFICATION_COUNT << "] Verification query = ";
    verif -> printPretty(llvm::errs(), nullptr,
                         mgr.getASTContext().getPrintingPolicy());
    llvm::errs() << "\n";

    bool res;
    llvm::errs() << "     - Result = " << (res = chkVALID(verif)) << "\n";

    if(!res) {
      pred = simplify(abduce(mgr, verif) + " & (" + pred + ")");
      return checkValidity(mgr, pred, loop_head, cfg, dom_tree, reachables, guard, nguard);
    }

    return res;
  }

  bool checkValidity(AnalysisManager & mgr,
                     std::string & pred,
                     CFGBlock* loop_head,
                     CFG* cfg,
                     DominatorTree *dom_tree,
                     CFGReverseBlockReachabilityAnalysis *reachables,
                     Expr * guard,
                     Expr * nguard) {
    llvm::errs() << "\n   # Invariant Guess = " << pred << "\n";

    if(!checkPreconditionValidity(mgr, pred, loop_head, cfg, dom_tree, reachables))
      return false;

    if(!checkPostconditionValidity(mgr, pred, loop_head, cfg, dom_tree, reachables, guard, nguard))
      return false;

    //TODO: May avoid checking again, if the previous call already fails and finally returns a verified pred
    return checkInductiveValidity(mgr, pred, loop_head, cfg, dom_tree, reachables, guard, nguard);
  }

} // end anonymous namespace


void LoopInvariantChecker :: checkASTDecl(const Decl *D,
                                          AnalysisManager &mgr,
                                          BugReporter &BR) const {
  const FunctionDecl *fd = dyn_cast<FunctionDecl>(D);
  if(!fd) return;

  IdentifierInfo *FnInfo = fd->getIdentifier();
  if (!FnInfo) return;

  if(!FnInfo->isStr("main"))
    return;

  CFG *cfg = mgr.getCFG(D);
  if(!cfg)
    return;

  StringRef main_path = mgr.getSourceManager().getFilename(D->getLocation()).str();
  WORKING_PATH += main_path.drop_front(main_path.rfind('/') + 1).str();
  {
    std::string command = "rm -rf " + WORKING_PATH + "; mkdir " + WORKING_PATH;
    system(command.c_str());
  }

  DominatorTree dom_tree;
  dom_tree.buildDominatorTree(* mgr.getAnalysisDeclContext(D));

  CFGReverseBlockReachabilityAnalysis reachables(*cfg);

  //FIXME: Single loop assumed
  CFGBlock *loop_head;
  std::vector<bool> isLoopHeader(cfg->getNumBlockIDs());

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

  Expr *guard = dyn_cast<Expr>(loop_head -> getTerminatorCondition(false));

  llvm::errs() << "\n   + Found guard in B" << loop_head->getBlockID() << "\n";
  llvm::errs() << "     - guard : ";
  guard -> printPretty(llvm::errs(), nullptr,
                       mgr.getASTContext().getPrintingPolicy());
  llvm::errs() << "\n";

  bool non_deterministic = false;
  //FIXME: The guard may `contain' a call instead of `being' a  call
  if(isa<CallExpr>(guard->IgnoreCasts())) {
    non_deterministic = true;
    guard = new (mgr.getASTContext()) CXXBoolLiteralExpr(true,
                                                         guard->getType(),
                                                         SourceLocation());

    llvm::errs() << "     - guard : NON-DETERMINISTIC\n";
  }

  Expr *nguard = new (mgr.getASTContext()) UnaryOperator(
                                             guard,
                                             UO_LNot,
                                             guard->getType(),
                                             VK_LValue,
                                             OK_Ordinary,
                                             SourceLocation());

  //FIXME: Generalize treatment of non-determinism. Can occur elsewhere too.

  // nguard is not not-guard always:
  // NON-DETERMINISTIC ... guard = true  ; nguard = false
  // DETERMINISTIC     ... guard = guard ; nguard = !guard

  //FIXME: Node sharing issues?!
  //Does TreeTransform do multiple replacements for shared nodes?

  std::string guess = "true";

  if(checkValidity(mgr, guess, loop_head, cfg, &dom_tree, &reachables, non_deterministic ? nguard : guard, nguard))
    llvm::errs() << "\n\n[###] Final invariant = " << guess << " [###]\n";
  else
    llvm::errs() << "\n\n[---] Invariant could not be determined. [---]\n";
}

void ento::registerLoopInvariantChecker(CheckerManager &mgr) {
  mgr.registerChecker<LoopInvariantChecker>();
}
