#ifndef __CLANG_TOOLS_PINVGEN_PREDICATE_NODE__
#define __CLANG_TOOLS_PINVGEN_PREDICATE_NODE__ 1

#include <list>
#include <string>

#include "clang/AST/Expr.h"

#include "tinyxml2.h"

struct PredicateNode {
  std::string val;
  std::list<PredicateNode> children;
};

extern long COUNT;

extern std::string WORKING_PATH;
extern std::string MAIN_FILENAME;

PredicateNode XMLDoc2PredicateNode(std::string);
PredicateNode XMLElement2PredicateNode(tinyxml2::XMLElement*);

PredicateNode Expr2PredicateNode(const clang::Expr*);

std::string PredicateNode2MCF(PredicateNode);

PredicateNode substituteVar(PredicateNode, std::string, PredicateNode);

#endif
