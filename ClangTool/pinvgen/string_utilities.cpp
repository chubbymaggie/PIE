#include "string_utilities.h"

using namespace std;

//FIXME: Add support for whole word replacement only
void replaceAll(string &str, const string &from, const string &to) {
  if(from.empty()) return;

  size_t start_pos = 0;
  while((start_pos = str.find(from, start_pos)) != string::npos) {
    str.replace(start_pos, from.length(), to);
    start_pos += to.length();
  }
}

string intersperse(string delim, list<string> lstr) {
  if(lstr.empty()) return "";

  string r = lstr.front();
  lstr.pop_front();

  while(!lstr.empty()) {
    r += delim + lstr.front();
    lstr.pop_front();
  }

  return r;
}
