#include <iostream>
#include <sstream>
#include <cassert>
#include <random>
#include <thread>
#include <mutex>
#include <unordered_map>
#include <future>
#include <atomic>

typedef std::minstd_rand Generator;   // 32 bit RNG state
//typedef std::mt19937_64 Generator;

class RandomGenerator
{
 public:
  int rand();
  void srand(unsigned newSeed);
  char randomBool();
  uint64_t randomUint64();
  void setTerminationFlag(std::atomic<bool> & f);
  void checkFuture();
  void setSeed(unsigned newSeed);
  void registerRand();
  void saveState();
  void restoreState();
 private:
  Generator generator;
  static std::atomic<bool> * _termination_flag;
  // all distributions have default lower bound of 0
  static std::uniform_int_distribution<int> int_distribution;
  static std::uniform_int_distribution<char> bool_distribution;
  static std::uniform_int_distribution<int64_t> int64_distribution;
};


namespace Random
{
  int rand();
  int random();
  char randomBool();
  uint64_t randomUint64();
  void srand(unsigned int seed);    // for this thread
  void set_seed(unsigned int seed); // called once to set initial seed
  void save_state();
  void restore_state();
  void register_thread();
  void check_future();
  void set_termination_flag(std::atomic<bool> &tf);
}
