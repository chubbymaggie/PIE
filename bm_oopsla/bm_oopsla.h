#ifndef __BM_OOPSLA_H__
#define __BM_OOPSLA_H__ 1

#include <cstdio>
#include <cstdlib>

#include <map>
#include <vector>
#include <iterator>

#include <string>
#include <regex>

#include <algorithm>
#include <functional>

#include <sys/time.h>

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

#define RAND_LOW -64
#define RAND_HIGH 64

int unknown() {
  return uni_rand_interval(RAND_LOW, RAND_HIGH);
}

int unknown1() { return unknown(); }
int unknown2() { return unknown(); }
int unknown3() { return unknown(); }

// A boolean unknown function
int unknown4() { return uni_rand_interval(0, 1); }

void assume(bool condition) { if(!condition) exit(EXIT_FAILURE); }
void assert(bool condition) { if(!condition) exit(EXIT_FAILURE); }

#define OUTPUT_STREAM stdout

#define _FE_9(TASK, arg0, args...)  TASK(arg0) _FE_8(TASK, args)
#define _FE_8(TASK, arg0, args...)  TASK(arg0) _FE_7(TASK, args)
#define _FE_7(TASK, arg0, args...)  TASK(arg0) _FE_6(TASK, args)
#define _FE_6(TASK, arg0, args...)  TASK(arg0) _FE_5(TASK, args)
#define _FE_5(TASK, arg0, args...)  TASK(arg0) _FE_4(TASK, args)
#define _FE_4(TASK, arg0, args...)  TASK(arg0) _FE_3(TASK, args)
#define _FE_3(TASK, arg0, args...)  TASK(arg0) _FE_2(TASK, args)
#define _FE_2(TASK, arg0, args...)  TASK(arg0) _FE_1(TASK, args)
#define _FE_1(TASK, arg0)           TASK(arg0)

std::map<std::string, std::string> init_values;
#define GEN_INIT_TASK(var)                                                      \
          auto INIT_ ## var = [&](std::function<int()> def_val) {           \
            if(init_values[#var] == "-")    var = def_val();                \
            else                            var = stoi(init_values[#var]);  \
          };

std::vector<std::string> split(const std::string& input, std::regex rgx) {
  std::sregex_token_iterator
    first{input.begin(), input.end(), rgx, -1},
    last;
  return {first, last};
}

void set_init_values(std::string args, int argc, char* argv[]) {
  std::vector<std::string> vars(split(args, std::regex(", ")));
  if(argc > 1) {
    std::vector<std::string> var_vals(argv+1, argv+argc);
    for(int i = 0; i < vars.size(); ++i)
      init_values[vars[i]] = var_vals[i];
  } else {
    for(int i = 0; i < vars.size(); ++i)
      init_values[vars[i]] = "-";
  }
}

#define RECORD(count, args...)                                              \
          int args;                                                         \
          set_init_values(#args, argc, argv);                               \
          struct timeval ___t___; gettimeofday(&___t___, NULL);             \
          srand(___t___.tv_usec * ___t___.tv_sec);                          \
          std::string ___vars___(#args);                                    \
          _FE_ ## count (GEN_INIT_TASK, args);                              \
          std::replace(___vars___.begin(), ___vars___.end(), ',', '\t');    \
          fprintf(OUTPUT_STREAM, "%s\n", ___vars___.c_str());               \
          auto PRINT_VARS = [&]() {                                         \
            fprintf(OUTPUT_STREAM, rep<count>("%d").c_str(), args);         \
          }

template <unsigned int N>
std::string rep(const std::string str) { return str + " \t " + rep<N-1>(str); }

template <> std::string rep<1>(const std::string str) { return str + "\n"; }

#endif
