#include <string>

#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/AnalysisManager.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

#include "llvm/Support/CommandLine.h"

#include "abduction.h"
#include "wp_computation.h"

using namespace llvm;

using namespace clang::ast_matchers;
using namespace clang::tooling;
using namespace clang::ento;
using namespace clang;

using namespace std;

string MAIN_FILENAME, CONFLICT_SIZE;

long COUNT = 0, ABDUCTION_COUNT = 0, VERIFICATION_COUNT = 0;

DeclarationMatcher MainFunctionDeclMatcher =
  functionDecl(hasName("main")).bind("mainFunction");

class InvariantGenerator : public MatchFinder::MatchCallback {
  public:
    virtual void run(const MatchFinder::MatchResult &Result) {
        if(const FunctionDecl *fd = Result.Nodes.getNodeAs<FunctionDecl>("mainFunction")) {
          errs() << string(80, '=') << "\n"
                 << "[#] Starting Loop Invariant Generation ...\n";

          AnalyzerOptions ao;
          CheckerManager cm(Result.Context->getLangOpts(),
                            IntrusiveRefCntPtr<AnalyzerOptions>(&ao));
          AnalysisManager mgr (*Result.Context,
                               Result.SourceManager->getDiagnostics(),
                               Result.Context->getLangOpts(),
                               PathDiagnosticConsumers(),
                               StoreManagerCreator(),
                               ConstraintManagerCreator(),
                               &cm, ao);

          StringRef main_path = Result.SourceManager->getFilename(fd->getLocation());
          MAIN_FILENAME = main_path.drop_front(main_path.rfind('/') + 1).str();

          CFG *cfg = mgr.getCFG(fd);
          CFGReverseBlockReachabilityAnalysis *reachables =
              mgr.getAnalysisDeclContext(fd)->getCFGReachablityAnalysis();

          DominatorTree dom_tree;
          dom_tree.buildDominatorTree(* mgr.getAnalysisDeclContext(fd));

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
            guard = Expr2PredicateNode(guard_expr);
            llvm::errs() << "     - guard : " << PredicateNode2MCF(guard) << "\n";
          }

          PredicateNode nguard {"!", {guard}};

          //FIXME: Generalize treatment of non-determinism. Can occur elsewhere too.

          // nguard and guard behaviour:
          // NON-DETERMINISTIC ... guard = true  ; nguard = false
          // DETERMINISTIC     ... guard = guard ; nguard = !guard

          CheckResult res = checkValidity(PredicateNode {"true", {}}, loop_head, cfg, &dom_tree, reachables, non_deterministic ? nguard : guard, nguard);

          if(res.status == VERIFIED)
            llvm::errs() << "\n\n[###] Final invariant = " << PredicateNode2MCF(res.guess) << " [###]\n";
          else
            llvm::errs() << "\n\n[---] Invariant could not be determined. [---]\n";

          errs() << string(80, '=') << "\n";
        }
    }
};

string ABDUCER_PATH, WORKING_PATH;
static cl::opt<string> opt_ABDUCER_PATH("abducer", cl::desc("Location of abducer script"), cl::value_desc("path/to/abduce.sh"), cl::Required);
static cl::opt<string> opt_WORKING_PATH("wpath", cl::desc("Working path (where logs are generated)"), cl::value_desc("directory"), cl::Required);

enum ToolType { escher, pie };
static cl::opt<ToolType> opt_USE_TOOL("tool", cl::desc("Inference engine to use:"),
        cl::values(
            clEnumVal(escher, "Escher"),
            clEnumVal(pie, "PIE"),
            clEnumValEnd
        ), cl::init(pie));

static cl::opt<string> opt_CONFLICT_SIZE("csize", cl::desc("Maximum size of conflict group"), cl::value_desc("<n> or all"), cl::Required);

static cl::OptionCategory PInvGenCategory("pinvgen options");
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

int main(int argc, const char **argv) {
  CommonOptionsParser op(argc, argv, PInvGenCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  if(opt_USE_TOOL == escher && opt_CONFLICT_SIZE != "all") {
    errs() << "[!] For `escher` mode, csize MUST BE all.";
    return 1;
  }

  CONFLICT_SIZE = opt_CONFLICT_SIZE;
  WORKING_PATH = opt_WORKING_PATH;

  if(opt_USE_TOOL == escher)    ABDUCER_PATH = opt_ABDUCER_PATH + " escher ";
  else if(opt_USE_TOOL == pie)  ABDUCER_PATH = opt_ABDUCER_PATH + " pie ";

  MatchFinder Finder;
  InvariantGenerator InvGen;
  Finder.addMatcher(MainFunctionDeclMatcher, &InvGen);

  return Tool.run(newFrontendActionFactory(&Finder).get());
}
