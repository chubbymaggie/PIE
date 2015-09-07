#include "clang/Basic/LangOptions.h"

#include "clang/AST/Expr.h"
#include "clang/AST/PrettyPrinter.h"

#include <algorithm>
#include <fstream>

#include "llvm/Support/raw_ostream.h"

#include "string_utilities.h"
#include "PredicateNode.h"

using namespace tinyxml2;
using namespace llvm;
using namespace clang;
using namespace std;

PredicateNode XMLElement2PredicateNode(XMLElement *x) {
  PredicateNode r;

  if(!(x->FirstChildElement("expr"))) {
    r.val = x->GetText();
  } else {
    x = x->FirstChildElement("expr");
    r.val = x->GetText();
    while(x = x->NextSiblingElement("expr")) {
      r.children.push_back(XMLElement2PredicateNode(x));
    }
  }

  return r;
}

PredicateNode escape(PredicateNode node) {
  replaceAll(node.val, "&amp;", "&");
  replaceAll(node.val, "&gt;", ">");
  replaceAll(node.val, "&lt;", "<");

  list<PredicateNode> nchildren;
  for(auto & c : node.children)
    nchildren.push_back(escape(c));
  node.children = nchildren;

  return node;
}

PredicateNode XMLDoc2PredicateNode(string file) {
  XMLDocument xmldoc;
  xmldoc.LoadFile(file.c_str());
  return escape(XMLElement2PredicateNode(xmldoc.FirstChildElement("expr")));
}

PredicateNode Expr2PredicateNode(const Expr * pred) {
  string mcf;
  {
    raw_string_ostream mcf_stream(mcf);
    LangOptions lo;
    pred -> printPretty(mcf_stream, nullptr, PrintingPolicy(lo));
  }

  // replaceAll(mcf, "true", "1=1");
  // replaceAll(mcf, "false", "1=0");
  replaceAll(mcf, "==", "=");
  replaceAll(mcf, "&&", "&");
  replaceAll(mcf, "||", "|");

  replaceAll(mcf, "get(", "#get(");
  replaceAll(mcf, "cat(", "#cat(");
  replaceAll(mcf, "has(", "#has(");
  replaceAll(mcf, "eql(", "#eql(");
  replaceAll(mcf, "ind(", "#ind(");
  replaceAll(mcf, "len(", "#len(");
  replaceAll(mcf, "rep(", "#rep(");
  replaceAll(mcf, "sub(", "#sub(");

  string target = "/tmp/" + MAIN_FILENAME + "_ast_" + to_string(COUNT);
  {
    ofstream mcf_file(target + ".mcf");
    mcf_file << mcf;
  }

  string command = WORKING_PATH + "/mcf2xml ";
  command += target;
  command += ".mcf > ";
  command += target + ".xml";
  system(command.c_str());

  return XMLDoc2PredicateNode(target + ".xml");
}

string PredicateNode2MCF_helper(PredicateNode r) {
  if(!r.children.size())
    return r.val;

  list<string> args;
  transform(r.children.begin(), r.children.end(), back_inserter(args), PredicateNode2MCF_helper);
  if(!isalpha(r.val[0])) {
    if(r.val == "!")
      return "(!" + args.front() + ")";
    else
      return "(" + intersperse(" " + r.val + " ", args) + ")";
  } else {
    return r.val + "(" + intersperse(", ", args) + ")";
  }
}

string PredicateNode2MCF(PredicateNode r) {
  string mcf = PredicateNode2MCF_helper(r);

  replaceAll(mcf, "get(", "#get(");
  replaceAll(mcf, "cat(", "#cat(");
  replaceAll(mcf, "has(", "#has(");
  replaceAll(mcf, "eql(", "#eql(");
  replaceAll(mcf, "ind(", "#ind(");
  replaceAll(mcf, "len(", "#len(");
  replaceAll(mcf, "rep(", "#rep(");
  replaceAll(mcf, "sub(", "#sub(");

  return mcf;
}

PredicateNode substituteVar(PredicateNode t, string var, PredicateNode r) {
  PredicateNode res;
  if(t.children.empty() && t.val == var) {
    res.val = r.val;
    res.children = r.children;
  } else {
    res.val = t.val;
    for(auto & c : t.children)
      res.children.push_back(substituteVar(c, var, r));
  }

  return res;
}
