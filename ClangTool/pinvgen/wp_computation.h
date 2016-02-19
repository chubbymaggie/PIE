#ifndef __CLANG_TOOLS_PINVGEN_WP_COMPUTATION__
#define __CLANG_TOOLS_PINVGEN_WP_COMPUTATION__ 1

#include "clang/Analysis/CFG.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/Analyses/CFGReachabilityAnalysis.h"

#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

#include "abduction.h"

extern std::map<std::string, PredicateNode> guesses;

bool isUnknownFunction(clang::Expr*);
bool isReachable(clang::CFGReverseBlockReachabilityAnalysis*,
                 const clang::CFGBlock*, const clang::CFGBlock*);

PredicateNode wpOfVarDecl(PredicateNode, const clang::VarDecl*);
PredicateNode wpOfCallExpr(PredicateNode, const clang::CallExpr*);
PredicateNode wpOfDeclStmt(PredicateNode, const clang::DeclStmt*);
PredicateNode wpOfUnaryOperator(PredicateNode, const clang::UnaryOperator*);
PredicateNode wpOfBinaryOperator(PredicateNode, const clang::BinaryOperator*);

PredicateNode wpOfStmt(PredicateNode, const clang::Stmt*);
PredicateNode wpOfBlock(PredicateNode,
						clang::CFGBlock*,
						clang::CFG*,
						const clang::DominatorTree*,
                        clang::CFGReverseBlockReachabilityAnalysis*);
PredicateNode wpOfSubgraph(PredicateNode,
                           clang::CFGBlock*,
                           clang::CFGBlock*,
                           clang::CFG*,
                           const clang::DominatorTree*,
                           clang::CFGReverseBlockReachabilityAnalysis*);

#endif
