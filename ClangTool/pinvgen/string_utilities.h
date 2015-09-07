#ifndef __CLANG_TOOLS_PINVGEN_STRING_UTILS__
#define __CLANG_TOOLS_PINVGEN_STRING_UTILS__ 1

#include <list>
#include <string>

std::string intersperse(std::string, std::list<std::string>);
void replaceAll(std::string &, const std::string &, const std::string &);

#endif
