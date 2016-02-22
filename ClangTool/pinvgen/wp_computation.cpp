#include "wp_computation.h"

#include "clang/AST/ExprCXX.h"

using namespace llvm;
using namespace clang;
using namespace std;

string loopId = "1";

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
  if(FnInfo->isStr("assume"))
    return {"|", {{"!", {Expr2PredicateNode(const_cast<Expr*>(call->getArg(0)->IgnoreCasts()))}}, pred}};
  if(FnInfo->isStr("set"))
    return substituteVar(
        pred,
        dyn_cast<DeclRefExpr>(call->getArg(0)->IgnoreCasts())->getFoundDecl()->getNameAsString(),
        Expr2PredicateNode(const_cast<Expr*>(call->getArg(1))->IgnoreCasts()));
  if(FnInfo->isStr("PRINT_BAR"))
    loopId = PredicateNode2MCF(Expr2PredicateNode(const_cast<Expr*>(call->getArg(0))->IgnoreCasts()));
  return pred;
}

PredicateNode wpOfDeclStmt(PredicateNode pred, const DeclStmt *decls) {
  for(DeclStmt::const_decl_iterator di = decls->decl_begin(); di != decls->decl_end(); ++di)
    if(const VarDecl * vdecl = dyn_cast<VarDecl>(*di))
      pred = wpOfVarDecl(pred, vdecl);
  return pred;
}

PredicateNode wpOfUnaryOperator(PredicateNode pred, const UnaryOperator *uop) {
  if(uop->getOpcode() == UO_PostInc || uop->getOpcode() == UO_PreInc)
    return substituteVar(pred,
                         (dyn_cast<DeclRefExpr>(uop->getSubExpr()))->getNameInfo().getAsString(),
                         PredicateNode {"+", {
                           Expr2PredicateNode(uop->getSubExpr()),
                           PredicateNode {"1", {}}}});
  if(uop->getOpcode() == UO_PostDec || uop->getOpcode() == UO_PreDec)
    return substituteVar(pred,
                         (dyn_cast<DeclRefExpr>(uop->getSubExpr()))->getNameInfo().getAsString(),
                         PredicateNode {"-", {
                           Expr2PredicateNode(uop->getSubExpr()),
                           PredicateNode {"1", {}}}});
  return pred;
}

PredicateNode wpOfBinaryOperator(PredicateNode pred, const BinaryOperator *bop) {
  if(isUnknownFunction(bop->getRHS()->IgnoreCasts()))
    return pred;
  if(bop->getOpcode() == BO_Assign) {
    return substituteVar(pred,
                         (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString(),
                         Expr2PredicateNode(bop->getRHS()));
  }
  if(bop->getOpcode() == BO_AddAssign) {
    return substituteVar(pred,
                         (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString(),
                         PredicateNode {"+", {Expr2PredicateNode(bop->getLHS()), Expr2PredicateNode(bop->getRHS())}});
  }
  if(bop->getOpcode() == BO_SubAssign) {
    return substituteVar(pred,
                         (dyn_cast<DeclRefExpr>(bop->getLHS()))->getNameInfo().getAsString(),
                         PredicateNode {"-", {Expr2PredicateNode(bop->getLHS()), Expr2PredicateNode(bop->getRHS())}});
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

PredicateNode wpOfBlock(PredicateNode pred,
                        CFGBlock *block,
                        CFG *cfg,
                        const DominatorTree* dom_tree,
                        CFGReverseBlockReachabilityAnalysis *reachables) {

  //errs() << "\n   wp of Block B" << block->getBlockID() << "\n";

  /* If current block has a loop head */
  for(CFGBlock::const_pred_iterator end_loop = block->pred_begin(), epre = block->pred_end(); end_loop != epre; ++end_loop) {
    if (dom_tree->dominates(block, *end_loop)) {
      CFGBlock *loop_head = block;
      string currentLoopId = loopId;
      errs() << "\n   + Found guard in B" << loop_head->getBlockID() << " for loop #" << currentLoopId << "\n";
      errs() << "\n     - post_" << currentLoopId << " : " << PredicateNode2MCF(pred) << "\n";

      PredicateNode guard;
      PredicateNode nguard;
      Expr *guard_expr = dyn_cast<Expr>(loop_head -> getTerminatorCondition(false));
      if (isUnknownFunction(guard_expr)) {
        guard = PredicateNode {"false", {}};
        nguard = PredicateNode {"false", {}};
        errs() << "     - guard : NON-DETERMINISTIC\n";
      } else {
        guard = Expr2PredicateNode(guard_expr);
        nguard = {"!", {guard}};
        errs() << "     - guard : " << PredicateNode2MCF(guard) << "\n";
      }

      PredicateNode verif = {"|", {guard, pred}};
      PredicateNode inv = simplify(abduce(verif, currentLoopId));
      errs() << "\n   # Invariant@Postcondition: " << PredicateNode2MCF(inv) << "\n";

      CFGBlock* start_loop = *(loop_head->succ_begin());
      while (1) {
        PredicateNode wp = wpOfSubgraph(inv, *end_loop, start_loop, cfg, dom_tree, reachables);
        verif = {"|", {{"!", {inv}}, nguard, wp}};
        errs() << "\n   # Verification@Inductivecondition: " << PredicateNode2MCF(verif);

        if (chkVALID(verif, false)) {
          errs() << " is valid!\n";
          break;
        }
        errs() << " is not valid!\n";

        inv = simplify({"&", {abduce(verif, currentLoopId), inv}});
        errs() << "\n   # Invariant@Inductivecondition: " << PredicateNode2MCF(inv) << "\n";
      }

      guesses[currentLoopId] = inv;
      return inv;
    }
  }

  /* Otherwise, current block is loop-free */
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

PredicateNode wpOfSubgraph(PredicateNode pred,
                           CFGBlock *from, CFGBlock *to,
                           CFG *cfg,
                           const DominatorTree* dom_tree,
                           CFGReverseBlockReachabilityAnalysis *reachables) {

  //errs() << "\n   wp of Subgraph from B" << from->getBlockID() << " to B" << to->getBlockID() << "\n";

  if(from == to) {
    return wpOfBlock(pred, from, cfg, dom_tree, reachables);
  }

  CFGBlock* single;
  unsigned cnt = 0;
  for(CFGBlock::const_pred_iterator pre = from->pred_begin(), epre = from->pred_end(); pre != epre; ++pre)
    if(isReachable(reachables, to, *pre) && !dom_tree->dominates(from, *pre)) {
      ++cnt;
      single = *pre;
    }

  if(cnt == 1)
    return wpOfSubgraph(wpOfBlock(pred, from, cfg, dom_tree, reachables), single, to, cfg, dom_tree, reachables);

  cnt = 0;
  for(CFGBlock::const_succ_iterator succ = to->succ_begin(), esucc = to->succ_end(); succ != esucc; ++succ)
    if(isReachable(reachables, *succ, from)) {
      ++cnt;
      single = *succ;
    }

  if(cnt == 1)
    return wpOfBlock(wpOfSubgraph(pred, from, single, cfg, dom_tree, reachables), to, cfg, dom_tree, reachables);

  CFGBlock* if_head = to;
  for (CFG::iterator it = cfg->begin(), ei = cfg->end(); it != ei; ++it) {
    CFGBlock *block = *it;
    if (!dom_tree->dominates(to, block)) continue;
    if (!dom_tree->dominates(block, from)) continue;
    if (block == from) continue;
    if (block->getBlockID() < if_head->getBlockID())
      if_head = block;
  }

  Expr* cond_expr = dyn_cast<Expr>(if_head->getTerminatorCondition(false));
  PredicateNode cond;
  PredicateNode ncond;

  if(isUnknownFunction(cond_expr)) {
    cond = PredicateNode {"false", {}};
    ncond = PredicateNode {"false", {}};
  } else {
    cond = Expr2PredicateNode(cond_expr);
    ncond = PredicateNode {"!", {cond}};
  }

  CFGBlock* then_head = *(if_head->succ_begin());
  CFGBlock* else_head = *(if_head->succ_begin() + 1);

  CFGBlock* then_end = nullptr;
  CFGBlock* else_end = nullptr;

  for(CFGBlock::const_pred_iterator pre = from->pred_begin(), epre = from->pred_end(); pre != epre; ++pre) {
    if(dom_tree->dominates(then_head, *pre))
      then_end = *pre;
    if(dom_tree->dominates(else_head, *pre) && from->getBlockID() < (*pre)->getBlockID())
      else_end = *pre;
  }

  pred = wpOfBlock(pred, from, cfg, dom_tree, reachables);

  return wpOfSubgraph(
      {"&", {
          {"|", {wpOfSubgraph(pred, then_end, then_head, cfg, dom_tree, reachables), ncond}},
          {"|", {else_end == nullptr ? pred : wpOfSubgraph(pred, else_end, else_head, cfg, dom_tree, reachables), cond}}}},
      if_head, to, cfg, dom_tree, reachables);
}
