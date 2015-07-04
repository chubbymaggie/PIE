#ifndef __BM_OOPSLA_H__
#define __BM_OOPSLA_H__ 1

#include <algorithm>
#include <string>
#include <cstdio>
#include <cstdlib>

#include <sys/time.h>

using std::string;

int rand_interval(int min, int max) { return min + (rand() % (max - min)); }

// Uniform distribution (from: http://stackoverflow.com/a/17554531/554436)
int uni_rand_interval(int min, int max)
{
    int r;
    const unsigned int range = 1 + max - min;
    const unsigned int buckets = RAND_MAX / range;
    const unsigned int limit = buckets * range;

    /* Create equal size buckets all in a row, then fire randomly towards
     * the buckets until you land in one of them. All buckets are equally
     * likely. If you land off the end of the line of buckets, try again. */
    do {
        r = rand();
    } while (r >= limit);

    return min + (r / buckets);
}

#define RAND_LOW -16
#define RAND_HIGH 16

//TODO: Hack to terminate early. Assumes termination condition is zero.
//      Better idea?
#define MAX_RUNS 64
unsigned short runs = 0;

int unknown() {
  ++runs;
  return runs > MAX_RUNS ? 0 : uni_rand_interval(RAND_LOW, RAND_HIGH);
}

int unknown1() { return unknown(); }
int unknown2() { return unknown(); }
int unknown3() { return unknown(); }
int unknown4() { return unknown(); }

void assume(bool condition) { if(!condition) exit(EXIT_FAILURE); }
void assert(bool condition) { if(!condition) exit(EXIT_FAILURE); }

#define OUTPUT_STREAM stdout

#define INITIALIZE(count, args...)                                          \
          struct timeval ___t___; gettimeofday(&___t___, NULL);             \
          srand(___t___.tv_usec * ___t___.tv_sec);                          \
          string ___vars___ = #args;                                        \
          std::replace(___vars___.begin(), ___vars___.end(), ',', '\t');    \
          fprintf(OUTPUT_STREAM, "%s\n", ___vars___.c_str());               \
          auto PRINT_VARS = [&]() {                                         \
            fprintf(OUTPUT_STREAM, rep<count>("%d").c_str(), ##args);       \
          }

template <unsigned int N>
string rep(const string str) { return str + " \t " + rep<N-1>(str); }

template <> string rep<1>(const string str) { return str + "\n"; }

#endif
