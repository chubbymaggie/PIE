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
extern std::string MAIN_FILENAME;
extern std::string CONFLICT_SIZE;

void copyTests(const int);
PredicateNode abduce(PredicateNode);
PredicateNode simplify(PredicateNode);
bool chkVALID(const PredicateNode, bool);

PredicateNode getAbductionResultFor(const PredicateNode);

CheckResult checkValidity(clang::CFG*,
                          clang::DominatorTree*,
                          clang::CFGReverseBlockReachabilityAnalysis*);

#endif
