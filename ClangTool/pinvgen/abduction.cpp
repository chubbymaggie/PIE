#include <fstream>
#include <vector>

#include "clang/AST/ExprCXX.h"

#include "llvm/Support/raw_ostream.h"

#include "abduction.h"
#include "wp_computation.h"

using namespace llvm;
using namespace clang;
using namespace std;

void copyTests(const int loop_num = 1) {
  string command = "cp " + WORKING_PATH + "/tests_" + to_string(loop_num) + " " + WORKING_PATH + "/final_tests";
  system(command.c_str());
}

PredicateNode getAbductionResultFor(const PredicateNode pred) {
  string target = WORKING_PATH + "/" + to_string(++COUNT) + "A" + to_string(++ABDUCTION_COUNT) + ".mcf";
  {
    ofstream mcf_file(target);
    mcf_file << ("-\n-\n" + PredicateNode2MCF(pred));
  }

  string command = ABDUCER_PATH + target;
  command += " " + CONFLICT_SIZE + " count > /dev/null";
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
  command += " 0 " + WORKING_PATH + "/count" + " > ";
  command += target + ".res";
  system(command.c_str());

  string result;
  {
    ifstream in(target + ".res");
    getline(in, result);
  }

  if(result.substr(0,5) == "VALID") return true;

  if(add_counter) {
    string command = WORKING_PATH + "/add_counter " + WORKING_PATH + "/" + MAIN_FILENAME + ".x "
                                                    + WORKING_PATH + "/tests "
                                                    + WORKING_PATH + "/header "
                                                    + target + ".res ";
    system(command.c_str());
    command = WORKING_PATH + "/separate_tests " + WORKING_PATH + "/tests";
    system(command.c_str());
    command = "rm -rf " + WORKING_PATH + "/tests";
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

PredicateNode abduce(PredicateNode query, int loop_num) {
  copyTests(loop_num);
  errs() << "\n   [Q" << ABDUCTION_COUNT+1 << "] Abduction query = " << PredicateNode2MCF(query) << "\n";
  PredicateNode res = getAbductionResultFor(query);
  errs() << "\n     - Result = " << PredicateNode2MCF(res) << "\n";
  return res;
}

CheckResult checkValidity(CFG *cfg,
                          DominatorTree *dom_tree,
                          CFGReverseBlockReachabilityAnalysis *reachables) {

  vector<CFGBlock*> loop_head;
  for (CFG::iterator it = cfg->begin(), ei = cfg->end(); it != ei; ++it) {
    CFGBlock *block = *it;
    for (CFGBlock::succ_iterator succ = block->succ_begin(), esucc = block->succ_end(); succ != esucc; ++succ) {
      if (dom_tree->dominates(*succ, block)) {
        loop_head.push_back(*succ);
      }
    }
  }

  int loop_num = loop_head.size();
  if (loop_num == 0) {
    errs() << "\nThe code contains no loops. Exit.\n";
    return { FAILED, {"true", {}} };
  }

  for (int i = 0; i < loop_num; i++)
    for (int j = i + 1; j < loop_num; j++) {
      if (dom_tree->dominates(loop_head[j], loop_head[i])) {
        CFGBlock *block = loop_head[i];
        loop_head[i] = loop_head[j];
        loop_head[j] = block;
      }
    }

  vector<PredicateNode> guard;
  vector<PredicateNode> nguard;
  for (int i = 0; i < loop_num; i++) {
    Expr *guard_expr = dyn_cast<Expr>(loop_head[i] -> getTerminatorCondition(false));
    errs() << "\n   + Found guard in B" << loop_head[i]->getBlockID() << " for loop #" << i + 1 << "\n";
    if (isUnknownFunction(guard_expr)) {
      guard.push_back(PredicateNode {"false", {}});
      nguard.push_back(PredicateNode {"false", {}});
      errs() << "     - guard : NON-DETERMINISTIC\n";
    } else {
      guard.push_back(Expr2PredicateNode(guard_expr));
      nguard.push_back({"!", {guard[i]}});
      errs() << "     - guard : " << PredicateNode2MCF(guard[i]) << "\n";
    }
  }

  vector<CFGBlock*> post_loop;
  for (int i = 0; i < loop_num; i++) {
    for (CFGBlock::const_succ_iterator succ = loop_head[i]->succ_begin(), esucc = loop_head[i]->succ_end(); succ != esucc; ++succ)
      if (dom_tree->dominates(*succ, &(cfg->getExit()))) {
        post_loop.push_back(*succ);
        break;
      }
  }

  vector<CFGBlock*> end_loop;
  for (int i = 0; i < loop_num; i++) {
    for (CFGBlock::const_pred_iterator pred = loop_head[i]->pred_begin(), epred = loop_head[i]->pred_end(); pred != epred; ++pred)
      if (dom_tree->dominates(loop_head[i], *pred)) {
        end_loop.push_back(*pred);
        break;
      }
  }

  vector<PredicateNode> p(loop_num + 1);
  p[loop_num] = wpOfSubgraph({"true", {}}, &(cfg->getExit()), post_loop[loop_num - 1], dom_tree, reachables);

  while (1) {
    for (int i = loop_num - 1; i >= 0; i--) {
      errs() << "\n   Post condition of loop #" << i + 1 << ": " << PredicateNode2MCF(p[i + 1]) << "\n";
      PredicateNode verif = {"|", {guard[i], p[i + 1]}};
      PredicateNode inv = simplify(abduce(verif, i + 1));
      errs() << "\n   # Invariant@Pos: " << PredicateNode2MCF(inv) << "\n";
      while (1) {
        PredicateNode wp = wpOfSubgraph(inv, end_loop[i], loop_head[i], dom_tree, reachables);
        verif = {"|", {{"!", {inv}}, nguard[i], wp}};
        errs() << "\n   # Verification@Ind: " << PredicateNode2MCF(verif);
        if (chkVALID(verif)) {
          errs() << " is valid!\n";
          break;
        }
        errs() << " is not valid!\n";
        inv = simplify({"&", {abduce(verif, i + 1), inv}});
        errs() << "\n   # Invariant@Ind: " << PredicateNode2MCF(inv) << "\n";
      }
      if (i > 0) {
        p[i] = wpOfSubgraph(inv, loop_head[i], post_loop[i - 1], dom_tree, reachables);
        errs() << "\n   # Invariant@Pre: " << PredicateNode2MCF(p[i]) << "\n";
      } else {
        p[i] = wpOfSubgraph(inv, loop_head[i], &(cfg->getEntry()), dom_tree, reachables);
        errs() << "\n   # Verification@Pre: " << PredicateNode2MCF(p[i]);
        if (chkVALID(p[i], true)) {
          errs() << " is valid!\n";
          return { VERIFIED, inv };
        }
        errs() << " is not valid!\n";
      }
    }
    errs() << "\n----------------------------------< RESTART >-----------------------------------\n";
  }
}