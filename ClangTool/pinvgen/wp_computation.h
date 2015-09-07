#ifndef __CLANG_TOOLS_PINVGEN_WP_COMPUTATION__
#define __CLANG_TOOLS_PINVGEN_WP_COMPUTATION__ 1

#include "clang/Analysis/CFG.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/Analyses/CFGReachabilityAnalysis.h"

#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

#include "abduction.h"

bool isUnknownFunction(clang::Expr*);
bool isReachable(clang::CFGReverseBlockReachabilityAnalysis*,
                 const clang::CFGBlock*, const clang::CFGBlock*);

PredicateNode wpOfVarDecl(PredicateNode, const clang::VarDecl*);
PredicateNode wpOfCallExpr(PredicateNode, const clang::CallExpr*);
PredicateNode wpOfDeclStmt(PredicateNode, const clang::DeclStmt*);
PredicateNode wpOfUnaryOperator(PredicateNode, const clang::UnaryOperator*);
PredicateNode wpOfBinaryOperator(PredicateNode, const clang::BinaryOperator*);

PredicateNode wpOfStmt(PredicateNode, const clang::Stmt*);
PredicateNode wpOfBlock(PredicateNode, const clang::CFGBlock*);
PredicateNode wpOfSubgraph(PredicateNode,
                           clang::CFGBlock*,
                           clang::CFGBlock*,
                           const clang::DominatorTree*,
                           clang::CFGReverseBlockReachabilityAnalysis*);

#endif
