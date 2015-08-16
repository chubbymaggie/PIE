#ifndef __BM_OOPSLA_H__
#define __BM_OOPSLA_H__ 1

#include <algorithm>
#include <string>
#include <cstdio>
#include <cstdlib>

#include <sys/time.h>

using std::string;

/*
 * Random integer generation
 */

int rand_interval(int min, int max) { return min + (rand() % (max - min)); }

// Uniform distribution (from: http://stackoverflow.com/a/17554531/554436)
int uni_rand_interval(int min, int max) {
    int r;
    const unsigned int range = 1 + max - min;
    const unsigned int buckets = RAND_MAX / range;
    const unsigned int limit = buckets * range;

    /* Create equal size buckets all in a row, then fire randomly towards
     * the buckets until you land in one of them. All buckets are equally
     * likely. If you land off the end of the line of buckets, try again. */
    do { r = rand(); } while (r >= limit);

    return min + (r / buckets);
}

#define RAND_LOW -48
#define RAND_HIGH 48

//TODO: Hack to terminate early. Assumes termination condition is zero.
//      Better idea?
#define MAX_RUNS 512
unsigned short runs = 0;

int unknown() {
  ++runs;
  return runs > MAX_RUNS ? 0 : uni_rand_interval(RAND_LOW, RAND_HIGH);
}

int unknown1() { return unknown(); }
int unknown2() { return unknown(); }
int unknown3() { return unknown(); }

// A boolean unknown function
int unknown4() { return uni_rand_interval(0, 1); }

// Overloaded unknown accepts range
int unknown(int low, int high) { return uni_rand_interval(low, high); }



/*
 * Random string generation
 */

#define RAND_STR_LEN_MAX 16

char unknown_upper() { return uni_rand_interval(65, 90); }
char unknown_lower() { return uni_rand_interval(97, 122); }
char unknown_alpha() { return unknown4() ? unknown_lower() : unknown_upper(); }
char unknown_printable() { return uni_rand_interval(33, 126); }

string unknown_s() {
  string s(unknown(0, RAND_STR_LEN_MAX), 0);
  for(int i = 0; i < s.length(); ++i) s[i] = unknown_alpha();
  return s;
}



void assume(bool condition) { if(!condition) exit(EXIT_FAILURE); }
void assert(bool condition) { if(!condition) exit(EXIT_FAILURE); }


bool contains(string haystack, string needle) {
  return haystack.find(needle) != string::npos;
}

#define OUTPUT_STREAM stdout

// In-string substring replacement (http://stackoverflow.com/a/15372760/554436)
void replaceAll( string &s, const string &search, const string &replace ) {
  for( size_t pos = 0; ; pos += replace.length() ) {
    // Locate the substring to replace
    pos = s.find( search, pos );
    if( pos == string::npos ) break;
    // Replace by erasing and inserting
    s.erase( pos, search.length() );
    s.insert( pos, replace );
  }
}

#define INITIALIZE(format, args...)                                       \
          struct timeval ___t___; gettimeofday(&___t___, NULL);           \
          srand(___t___.tv_usec * ___t___.tv_sec);                        \
          string ___vars___ = #args;                                      \
          std::replace(___vars___.begin(), ___vars___.end(), ',', '\t');  \
          replaceAll(___vars___, ".c_str()", "");                         \
          fprintf(OUTPUT_STREAM, "%s\n", ___vars___.c_str());             \
          auto PRINT_VARS = [&]() {                                       \
            fprintf(OUTPUT_STREAM, format, ##args);                       \
          }

#endif
