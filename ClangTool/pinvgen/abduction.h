#ifndef __CLANG_TOOLS_PINVGEN_ABDUCTION__
#define __CLANG_TOOLS_PINVGEN_ABDUCTION__ 1

#include "clang/Analysis/CFG.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/Analyses/CFGReachabilityAnalysis.h"

#include "PredicateNode.h"

enum CheckStatus { FAILED, PASSED, VERIFIED };
struct CheckResult {
  CheckStatus status;
  PredicateNode guess;
};

extern long COUNT;
extern long ABDUCTION_COUNT;
extern long VERIFICATION_COUNT;

extern std::string ABDUCER_PATH;
extern std::string WORKING_PATH;

PredicateNode abduce(PredicateNode);
PredicateNode simplify(PredicateNode);
bool chkVALID(const PredicateNode, bool);

PredicateNode getAbductionResultFor(const PredicateNode);

CheckResult checkValidity(PredicateNode,
                          clang::CFGBlock*,
                          clang::CFG*,
                          clang::DominatorTree*,
                          clang::CFGReverseBlockReachabilityAnalysis*,
                          PredicateNode,
                          PredicateNode);

CheckResult checkPreconditionValidity(PredicateNode,
                                      clang::CFGBlock*,
                                      clang::CFG*,
                                      clang::DominatorTree*,
                                      clang::CFGReverseBlockReachabilityAnalysis*,
                                      PredicateNode,
                                      PredicateNode);

CheckResult checkInductiveValidity(PredicateNode,
                                   clang::CFGBlock*,
                                   clang::CFG*,
                                   clang::DominatorTree*,
                                   clang::CFGReverseBlockReachabilityAnalysis*,
                                   PredicateNode,
                                   PredicateNode);

CheckResult checkPostconditionValidity(PredicateNode,
                                       clang::CFGBlock*,
                                       clang::CFG*,
                                       clang::DominatorTree*,
                                       clang::CFGReverseBlockReachabilityAnalysis*,
                                       PredicateNode,
                                       PredicateNode);

#endif
