#include "wp_computation.h"

#include "clang/AST/ExprCXX.h"

using namespace clang;
using namespace std;

bool isUnknownFunction(Expr *expr) {
  expr = expr->IgnoreCasts();
  if(dyn_cast<ExprWithCleanups>(expr))
    return isUnknownFunction(dyn_cast<ExprWithCleanups>(expr)->getSubExpr());

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

  return substituteVar(pred, vdecl->getNameAsString(), Expr2PredicateNode(expr));
}

PredicateNode wpOfCallExpr(PredicateNode pred, const CallExpr *call) {
  const FunctionDecl *fd = call->getDirectCallee();
  if(!fd) return pred;

  IdentifierInfo *FnInfo = fd->getIdentifier();
  if (!FnInfo) return pred;

  if(FnInfo->isStr("assert") || FnInfo->isStr("static_assert"))
    return {"&", {pred, Expr2PredicateNode(const_cast<Expr*>(call->getArg(0)->IgnoreCasts()))}};
  else if(FnInfo->isStr("assume"))
    return {"|", {{"!", {Expr2PredicateNode(const_cast<Expr*>(call->getArg(0)->IgnoreCasts()))}}, pred}};
  else if(FnInfo->isStr("set"))
    return substituteVar(
        pred,
        dyn_cast<DeclRefExpr>(call->getArg(0)->IgnoreCasts())->getFoundDecl()->getNameAsString(),
        Expr2PredicateNode(const_cast<Expr*>(call->getArg(1))->IgnoreCasts()));

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
                           Expr2PredicateNode(uop->getSubExpr()),
                           PredicateNode {"1", {}}}});
  else if(uop->getOpcode() == UO_PostDec || uop->getOpcode() == UO_PreDec)
    return substituteVar(pred,
                         (dyn_cast<DeclRefExpr>(uop->getSubExpr()))->getNameInfo().getAsString(),
                         PredicateNode {"-", {
                           Expr2PredicateNode(uop->getSubExpr()),
                           PredicateNode {"1", {}}}});
  return pred;
}

PredicateNode wpOfBinaryOperator(PredicateNode pred, const BinaryOperator * bop) {
  if(bop->getOpcode() == BO_Assign) {
    if(!isUnknownFunction(bop->getRHS()->IgnoreCasts()))
      return substituteVar(pred,
                           (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString(),
                           Expr2PredicateNode(bop->getRHS()));
  } if(bop->getOpcode() == BO_AddAssign) {
    return substituteVar(pred,
                         (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString(),
                         PredicateNode {"+", {Expr2PredicateNode(bop->getLHS()), Expr2PredicateNode(bop->getRHS())}});
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
    cond = Expr2PredicateNode(cond_expr);
  PredicateNode ncond {"!", {cond}};

  return wpOfBlock(
      {"&", {
          {"|", {wpOfSubgraph(pred, from, *(to->succ_begin()), dom_tree, reachables), ncond}},
          {"|", {wpOfSubgraph(pred, from, *(to->succ_begin() + 1), dom_tree, reachables), non_deterministic ? ncond : cond}}}},
      to);
}
