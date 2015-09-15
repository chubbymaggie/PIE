#include <fstream>

#include "clang/AST/ExprCXX.h"

#include "llvm/Support/raw_ostream.h"

#include "abduction.h"
#include "wp_computation.h"

using namespace llvm;
using namespace clang;
using namespace std;

PredicateNode getAbductionResultFor(const PredicateNode pred) {
  string target = WORKING_PATH + "/" + to_string(++COUNT) + "A" + to_string(++ABDUCTION_COUNT) + ".mcf";
  {
    ofstream mcf_file(target);
    mcf_file << ("-\n-\n" + PredicateNode2MCF(pred));
  }

  string command = ABDUCER_PATH + "/abduce.sh ";
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
  command += target + ".res";
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

PredicateNode abduce(PredicateNode query) {
  errs() << "\n   [Q" << ABDUCTION_COUNT+1 << "] Abduction query = " << PredicateNode2MCF(query) << "\n";
  PredicateNode res = getAbductionResultFor(query);
  errs() << "\n     - Result = " << PredicateNode2MCF(res) << "\n";
  return res;
}

CheckResult checkPreconditionValidity(PredicateNode pred,
                                      CFGBlock* loop_head,
                                      CFG * cfg,
                                      DominatorTree *dom_tree,
                                      CFGReverseBlockReachabilityAnalysis *reachables,
                                      PredicateNode guard,
                                      PredicateNode nguard) {

  PredicateNode verif = wpOfSubgraph(pred, loop_head, &(cfg->getEntry()), dom_tree, reachables);

  errs() << "\n   [V" << VERIFICATION_COUNT+1 << "] Verification query {pre} = "
               << PredicateNode2MCF(verif) << "\n";

  bool res;
  errs() << "     - Result = " << ((res = chkVALID(verif, true)) ? "VALID" : "FAILED") << "\n";

  if(!res) {
    errs() << "\n ----------------------------------------< RESTART >---------------------------------------- \n";
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

  errs() << "\n   [V" << VERIFICATION_COUNT+1 << "] Verification query {ind} = "
               << PredicateNode2MCF(verif) << "\n";

  bool res;
  errs() << "     - Result = " << ((res = chkVALID(verif)) ? "VALID" : "FAILED") << "\n";

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

  errs() << "\n   [V" << VERIFICATION_COUNT+1 << "] Verification query {pos} = "
               << PredicateNode2MCF(verif) << "\n";

  bool res;
  errs() << "     - Result = " << ((res = chkVALID(verif)) ? "VALID" : "FAILED") << "\n";

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
  errs() << "\n   # Invariant Guess = " << PredicateNode2MCF(pred) << "\n";

  CheckResult cr;

  if((cr = checkPreconditionValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard)).status != PASSED)
    return cr;

  if((cr = checkPostconditionValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard)).status != PASSED)
      return cr;

  if((cr = checkInductiveValidity(pred, loop_head, cfg, dom_tree, reachables, guard, nguard)).status != FAILED)
    return CheckResult { VERIFIED, cr.guess};

  return { FAILED, cr.guess };
}
