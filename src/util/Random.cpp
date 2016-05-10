#include "Random.h"
#include "Error.h"

using namespace std;

thread_local static RandomGenerator RNG; // one per thread
thread_local static Generator saved_state;
static unsigned int seed = 0; // initial seed for all threads

int RandomGenerator::rand()
{
  checkFuture();
  return int_distribution(RNG.generator);
}

void RandomGenerator::srand(unsigned newSeed)
{
  // set seed for this thread
  RNG.generator.seed(newSeed);
}

char RandomGenerator::randomBool()
{
  checkFuture();
  return bool_distribution(RNG.generator);
}

uint64_t RandomGenerator::randomUint64()
{
  checkFuture();
  return int64_distribution(RNG.generator);
}

void RandomGenerator::setTerminationFlag(atomic<bool> & tf)
{
  _termination_flag = &tf;
}

void RandomGenerator::checkFuture()
{
  thread_local static int delayCounter(0);
  if( _termination_flag == nullptr)
    return;
  // for single thread 1000 is usually << 1 sec, at 10000 usually ~1 sec
  if (delayCounter++ > 1000) {
    delayCounter = 0;
    if (*_termination_flag) {
      throw Termination("Promise satisfied.");
    }
  }
}

void RandomGenerator::setSeed(unsigned newSeed)
{
  // called (once) to initialize the random seed
  seed = newSeed;
}

void RandomGenerator::registerRand()
{
  RNG.generator.seed(seed);
  saved_state = RNG.generator;
}

void RandomGenerator::saveState()
{
  // ony allows one state per thread to be saved at a time
  saved_state = RNG.generator;
}

void RandomGenerator::restoreState()
{
  RNG.generator = saved_state;
}

std::atomic<bool> * RandomGenerator::_termination_flag = nullptr;
std::uniform_int_distribution<char> RandomGenerator::bool_distribution(0, 1);
std::uniform_int_distribution<int64_t> RandomGenerator::int64_distribution(0, -1LL);
std::uniform_int_distribution<int> RandomGenerator::int_distribution;

// #define RAND_MAX 65536

// singleton accessors
int Random::rand() { return RNG.rand(); }
int Random::random() { return RNG.rand(); }
char Random::randomBool() { return RNG.randomBool(); }
uint64_t Random::randomUint64() { return RNG.randomUint64(); }
void Random::srand(unsigned int seed) { RNG.srand(seed); }
void Random::set_seed(unsigned int seed) { RNG.setSeed(seed); }
void Random::save_state() { RNG.saveState(); }
void Random::restore_state() { RNG.restoreState(); }
void Random::register_thread() { return RNG.registerRand(); }
void Random::check_future() { RNG.checkFuture(); }
void Random::set_termination_flag(atomic<bool> & tf) { RNG.setTerminationFlag(tf); }
