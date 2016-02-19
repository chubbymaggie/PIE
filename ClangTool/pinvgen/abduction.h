#ifndef __CLANG_TOOLS_PINVGEN_ABDUCTION__
#define __CLANG_TOOLS_PINVGEN_ABDUCTION__ 1

#include "clang/Analysis/CFG.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/Analyses/CFGReachabilityAnalysis.h"

#include "PredicateNode.h"

extern long COUNT;
extern long ABDUCTION_COUNT;
extern long VERIFICATION_COUNT;

extern std::string ABDUCER_PATH;
extern std::string WORKING_PATH;
extern std::string MAIN_FILENAME;
extern std::string CONFLICT_SIZE;

PredicateNode abduce(PredicateNode, std::string);
PredicateNode simplify(PredicateNode);
bool chkVALID(const PredicateNode, bool);

PredicateNode getAbductionResultFor(const PredicateNode);

void checkValidity(clang::CFG*,
                   clang::DominatorTree*,
                   clang::CFGReverseBlockReachabilityAnalysis*);

#endif
