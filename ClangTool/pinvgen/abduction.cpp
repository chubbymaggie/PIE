#include <fstream>

#include "clang/AST/ExprCXX.h"

#include "llvm/Support/raw_ostream.h"

#include "abduction.h"
#include "wp_computation.h"

using namespace llvm;
using namespace clang;
using namespace std;

StringMap<PredicateNode> guesses;

void copyTests(const string loopId) {
  string command = "cp " + WORKING_PATH + "/tests_" + loopId + " " + WORKING_PATH + "/final_tests";
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

bool chkVALID(const PredicateNode pred, bool add_counter) {
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

PredicateNode abduce(PredicateNode query, string loopId) {
  copyTests(loopId);
  errs() << "\n   [Q" << ABDUCTION_COUNT+1 << "] Abduction query = " << PredicateNode2MCF(query) << "\n";
  PredicateNode res = getAbductionResultFor(query);
  errs() << "\n     - Result = " << PredicateNode2MCF(res) << "\n";
  return res;
}

void checkValidity(CFG *cfg,
                   DominatorTree *dom_tree,
                   CFGReverseBlockReachabilityAnalysis *reachables) {
  while (1) {
    guesses.clear();

    PredicateNode wp = wpOfSubgraph({"true", {}}, &(cfg->getExit()), &(cfg->getEntry()), cfg, dom_tree, reachables);
    errs() << "\n   # Verification@Precondition: " << PredicateNode2MCF(wp);

    if (chkVALID(wp, true)) {
      errs() << " is valid!\n";
      break;
    }

    errs() << " is not valid!\n";
    errs() << "\n----------------------------------< RESTART >-----------------------------------\n";  
  }

  errs() << "\n\n[###] Final invariants: [###]\n";
  for (const auto & guess : guesses) {
    errs() << "Loop #" << guess.getKey() << ": " << PredicateNode2MCF(guess.getValue()) << '\n';
  }
}
