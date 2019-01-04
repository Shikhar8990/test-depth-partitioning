//===-- Searcher.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Searcher.h"

#include "CoreStats.h"
#include "Executor.h"
#include "PTree.h"
#include "StatsTracker.h"

#include "klee/ExecutionState.h"
#include "klee/MergeHandler.h"
#include "klee/Statistics.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/ADT/DiscretePDF.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#include <cassert>
#include <fstream>
#include <climits>
#include <iostream>

using namespace klee;
using namespace llvm;


namespace klee {
  extern RNG theRNG;
}

Searcher::~Searcher() {
}

///

ExecutionState &DFSSearcher::selectState() {
  return *states.back();
}

void DFSSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin(),
                                                     ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    if (es == states.back()) {
      states.pop_back();
    } else {
      bool ok = false;

      for (std::vector<ExecutionState*>::iterator it = states.begin(),
             ie = states.end(); it != ie; ++it) {
        if (es==*it) {
          states.erase(it);
          ok = true;
          break;
        }
      }

      (void) ok;
      assert(ok && "invalid state removed");
    }
  }
}

ExecutionState* DFSSearcher::getState2Offload2() {
  ExecutionState *ptr2State = states[theRNG.getInt32()%states.size()];
  ExecutionState retState = *ptr2State;
  return ptr2State;
}

ExecutionState &DFSSearcher::getState2Offload() {
  //need to have atleast two states in order to upload
  if(states.size() > 1) {
    //ExecutionState *retState = states.back();
    ExecutionState *retState = states[theRNG.getInt32()%states.size()];
    if(retState == states.back()) {
      states.pop_back();
    } else {
      for (std::vector<ExecutionState*>::iterator it = states.begin(),
            ie = states.end(); it != ie; ++it) {
        if (retState==*it) {
          states.erase(it);
          break;
        }
      }
    }
    return *retState;
  } else {
    return *(ExecutionState*)(NULL);
  }
}

///

BFSSearcher::BFSSearcher() {
  currentMinDepth = 0;
  depthStatesMap.clear();
  depthMap.clear();
}

BFSSearcher::~BFSSearcher() {
}


ExecutionState &BFSSearcher::getState2Offload() {
}

ExecutionState* BFSSearcher::getState2Offload2() {
  assert(depthStatesMap.find(currentMinDepth) != depthStatesMap.end());
  return (depthStatesMap[currentMinDepth][theRNG.getInt32()%depthStatesMap[currentMinDepth].size()]);
}

ExecutionState &BFSSearcher::selectState() {
  //std::cout<<"YT Calling Select State Minimum Depth: "<<currentMinDepth<<"\n";
  assert(depthStatesMap.find(currentMinDepth) != depthStatesMap.end());
  return *((depthStatesMap[currentMinDepth]).front());
}

//The switch statement adds all the states corresponding to each of the case
//statments in one go. Each case has an increasing depth. Now If say there are
//multiple switch statements, a state of depth 4 will be added before the
//a state of depth 2 in the following switch stament which breaks the BFS
//search, so I need to reimplement the BFS search again to accomodate this case
//There is map which maps the depth to the deque of states of that depth

void BFSSearcher::update(ExecutionState *current,
    const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {
    
  //std::cout << "SS_Searcher: Calling updatestate BFS \n";
  if(current != nullptr) { 
    auto mit = depthMap.find(current);
    if (mit == depthMap.end()) {
      //if the state doesnt exist for some reason just put it 
      //in and update it
      depthMap[current] = current->depth;
      insertIntoDepthStateMap(current);
      //std::cout << "YT Inserting State "<<current<<" at depth "<<current->depth<<"\n";
    } else {
      //if it exists and the depth has changed, if yes update it
      if (depthMap[current] != current->depth) {
        //std::cout << "YT Updating State "<<current<<" from depth "<<depthMap[current]
        //          << " to depth " << current->depth<<"\n";
        updateDepthStateMap(current, depthMap[current]);
        depthMap[current] = current->depth;
      } 
    } 
  } 
  
  //removing the removed states
  //std::cout << "SS_Searcher: Removing states BFS \n";
  for(auto it = removedStates.begin(); it != removedStates.end(); ++it) {
    removeFromDepthStateMap(*it);
  } 
  //adding the new states
  //std::cout << "SS_Searcher: Adding states BFS \n";
  for(auto it = addedStates.begin(); it != addedStates.end(); ++it) {
    insertIntoDepthStateMap(*it);
  } 
} 

void BFSSearcher::insertIntoDepthStateMap(ExecutionState* current) {
  int depth = current->depth;
  depthMap[current] = depth;
  if(depthStatesMap.find(depth) == depthStatesMap.end()) {
    std::deque<ExecutionState*> newListofStates;
    newListofStates.push_back(current);
    depthStatesMap[depth] = newListofStates;
    //std::cout << "YT Adding first state "<<current<<" depth "<<depth<<"\n";
  } else {
    auto listofStates= depthStatesMap[depth];
    listofStates.push_back(current);
    depthStatesMap[depth] = listofStates;
  }
}

void BFSSearcher::removeFromDepthStateMap(ExecutionState* current) {
  int depth = current->depth;
  assert(depthStatesMap.find(depth) != depthStatesMap.end());
  auto listofStates = depthStatesMap[depth];
  auto it = std::find(listofStates.begin(), listofStates.end(), current);
  assert(it!=listofStates.end());
  listofStates.erase(it);
  //here check if the list is empty
  if(listofStates.size() == 0) {
    depthStatesMap.erase(depth);
    //std::cout << "YT Removing last state "<<current<<" depth "<<depth<<"\n";
    if (depth == currentMinDepth) {
      currentMinDepth++;
    }
  } else {
    depthStatesMap[depth] = listofStates;
    //std::cout << "YT Removing state "<<current<<" depth "<<depth<<"\n";
  }
  assert(depthMap.find(current) != depthMap.end());
  depthMap.erase(current);
}

void BFSSearcher::updateDepthStateMap(ExecutionState* current, int oldDepth) {
  int newDepth = current->depth;
  assert(depthStatesMap.find(oldDepth) != depthStatesMap.end());
  //erase from the old list
  auto listofStates = depthStatesMap[oldDepth];
  auto it = std::find(listofStates.begin(), listofStates.end(), current);
  assert(it!=listofStates.end());
  listofStates.erase(it);
  if (listofStates.size() == 0) {
    depthStatesMap.erase(oldDepth);
    if (currentMinDepth <= oldDepth)
      //currentMinDepth = oldDepth+1;
      currentMinDepth = newDepth;
  } else {
    depthStatesMap[oldDepth] = listofStates;
  }
  insertIntoDepthStateMap(current);
}

///

ExecutionState &RandomSearcher::getState2Offload() {
  //need to have atleast two states in order to upload
  if(states.size() > 1) {
    ExecutionState *retState = states.back();
    states.pop_back();
    return *retState;
  } else {
    return *(ExecutionState*)(NULL);
  }
}

ExecutionState* RandomSearcher::getState2Offload2() {
  std::cout << "SS_Searcher: Random Calling Offload\n";
  return states[theRNG.getInt32()%states.size()];
}

ExecutionState &RandomSearcher::selectState() {
  //std::cout << "SS_Searcher: Random Calling Select State Active States\n";
  return *states[theRNG.getInt32()%states.size()];
}

void
RandomSearcher::update(ExecutionState *current,
                       const std::vector<ExecutionState *> &addedStates,
                       const std::vector<ExecutionState *> &removedStates) {
  states.insert(states.end(),
                addedStates.begin(),
                addedStates.end());
  for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin(),
                                                     ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    bool ok = false;

    for (std::vector<ExecutionState*>::iterator it = states.begin(),
           ie = states.end(); it != ie; ++it) {
      if (es==*it) {
        states.erase(it);
        ok = true;
        break;
      }
    }

    assert(ok && "invalid state removed");
  }
}

///

ExecutionState &WeightedRandomSearcher::getState2Offload() {
}

ExecutionState* WeightedRandomSearcher::getState2Offload2() {
}

WeightedRandomSearcher::WeightedRandomSearcher(WeightType _type)
  : states(new DiscretePDF<ExecutionState*>()),
    type(_type) {
  switch(type) {
  case Depth: 
    updateWeights = false;
    break;
  case InstCount:
  case CPInstCount:
  case QueryCost:
  case MinDistToUncovered:
  case CoveringNew:
    updateWeights = true;
    break;
  default:
    assert(0 && "invalid weight type");
  }
}

WeightedRandomSearcher::~WeightedRandomSearcher() {
  delete states;
}

ExecutionState &WeightedRandomSearcher::selectState() {
  return *states->choose(theRNG.getDoubleL());
}

double WeightedRandomSearcher::getWeight(ExecutionState *es) {
  switch(type) {
  default:
  case Depth: 
    return es->weight;
  case InstCount: {
    uint64_t count = theStatisticManager->getIndexedValue(stats::instructions,
                                                          es->pc->info->id);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv * inv;
  }
  case CPInstCount: {
    StackFrame &sf = es->stack.back();
    uint64_t count = sf.callPathNode->statistics.getValue(stats::instructions);
    double inv = 1. / std::max((uint64_t) 1, count);
    return inv;
  }
  case QueryCost:
    return (es->queryCost.toSeconds() < .1) ? 1. : 1./ es->queryCost.toSeconds();
  case CoveringNew:
  case MinDistToUncovered: {
    uint64_t md2u = computeMinDistToUncovered(es->pc,
                                              es->stack.back().minDistToUncoveredOnReturn);

    double invMD2U = 1. / (md2u ? md2u : 10000);
    if (type==CoveringNew) {
      double invCovNew = 0.;
      if (es->instsSinceCovNew)
        invCovNew = 1. / std::max(1, (int) es->instsSinceCovNew - 1000);
      return (invCovNew * invCovNew + invMD2U * invMD2U);
    } else {
      return invMD2U * invMD2U;
    }
  }
  }
}

void WeightedRandomSearcher::update(
    ExecutionState *current, const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {
  if (current && updateWeights &&
      std::find(removedStates.begin(), removedStates.end(), current) ==
          removedStates.end())
    states->update(current, getWeight(current));

  for (std::vector<ExecutionState *>::const_iterator it = addedStates.begin(),
                                                     ie = addedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    states->insert(es, getWeight(es));
  }

  for (std::vector<ExecutionState *>::const_iterator it = removedStates.begin(),
                                                     ie = removedStates.end();
       it != ie; ++it) {
    states->remove(*it);
  }
}

bool WeightedRandomSearcher::empty() { 
  return states->empty(); 
}

///

ExecutionState &RandomPathSearcher::getState2Offload() {
}

ExecutionState* RandomPathSearcher::getState2Offload2() {
}

RandomPathSearcher::RandomPathSearcher(Executor &_executor)
  : executor(_executor) {
}

RandomPathSearcher::~RandomPathSearcher() {
}

ExecutionState &RandomPathSearcher::selectState() {
  unsigned flips=0, bits=0;
  PTree::Node *n = executor.processTree->root;
  while (!n->data) {
    if (!n->left) {
      n = n->right;
    } else if (!n->right) {
      n = n->left;
    } else {
      if (bits==0) {
        flips = theRNG.getInt32();
        bits = 32;
      }
      --bits;
      n = (flips&(1<<bits)) ? n->left : n->right;
    }
  }

  return *n->data;
}

void
RandomPathSearcher::update(ExecutionState *current,
                           const std::vector<ExecutionState *> &addedStates,
                           const std::vector<ExecutionState *> &removedStates) {
}

bool RandomPathSearcher::empty() { 
  return executor.states.empty(); 
}

///

ExecutionState &MergingSearcher::getState2Offload() {
}
  
ExecutionState* MergingSearcher::getState2Offload2() {
}


MergingSearcher::MergingSearcher(Executor &_executor, Searcher *_baseSearcher)
  : executor(_executor),
  baseSearcher(_baseSearcher){}

MergingSearcher::~MergingSearcher() {
  delete baseSearcher;
}

ExecutionState& MergingSearcher::selectState() {
  assert(!baseSearcher->empty() && "base searcher is empty");

  // Iterate through all MergeHandlers
  for (auto cur_mergehandler: executor.mergeGroups) {
    // Find one that has states that could be released
    if (!cur_mergehandler->hasMergedStates()) {
      continue;
    }
    // Find a state that can be prioritized
    ExecutionState *es = cur_mergehandler->getPrioritizeState();
    if (es) {
      return *es;
    } else {
      if (DebugLogIncompleteMerge){
        llvm::errs() << "Preemptively releasing states\n";
      }
      // If no state can be prioritized, they all exceeded the amount of time we
      // are willing to wait for them. Release the states that already arrived at close_merge.
      cur_mergehandler->releaseStates();
    }
  }
  // If we were not able to prioritize a merging state, just return some state
  return baseSearcher->selectState();
}

///

ExecutionState &BatchingSearcher::getState2Offload() {
}

ExecutionState* BatchingSearcher::getState2Offload2() {
}

BatchingSearcher::BatchingSearcher(Searcher *_baseSearcher,
                                   time::Span _timeBudget,
                                   unsigned _instructionBudget) 
  : baseSearcher(_baseSearcher),
    timeBudget(_timeBudget),
    instructionBudget(_instructionBudget),
    lastState(0) {
  
}

BatchingSearcher::~BatchingSearcher() {
  delete baseSearcher;
}

ExecutionState &BatchingSearcher::selectState() {
  if (!lastState || 
      (time::getWallTime() - lastStartTime) > timeBudget ||
      (stats::instructions - lastStartInstructions) > instructionBudget) {
    if (lastState) {
      time::Span delta = time::getWallTime() - lastStartTime;
      auto t = timeBudget;
      t *= 1.1;
      if (delta > t) {
        klee_message("increased time budget from %f to %f\n", timeBudget.toSeconds(), delta.toSeconds());
        timeBudget = delta;
      }
    }
    lastState = &baseSearcher->selectState();
    lastStartTime = time::getWallTime();
    lastStartInstructions = stats::instructions;
    return *lastState;
  } else {
    return *lastState;
  }
}

void
BatchingSearcher::update(ExecutionState *current,
                         const std::vector<ExecutionState *> &addedStates,
                         const std::vector<ExecutionState *> &removedStates) {
  if (std::find(removedStates.begin(), removedStates.end(), lastState) !=
      removedStates.end())
    lastState = 0;
  baseSearcher->update(current, addedStates, removedStates);
}

/***/

ExecutionState &IterativeDeepeningTimeSearcher::getState2Offload() {
}

ExecutionState* IterativeDeepeningTimeSearcher::getState2Offload2() {
}

IterativeDeepeningTimeSearcher::IterativeDeepeningTimeSearcher(Searcher *_baseSearcher)
  : baseSearcher(_baseSearcher),
    time(time::seconds(1)) {
}

IterativeDeepeningTimeSearcher::~IterativeDeepeningTimeSearcher() {
  delete baseSearcher;
}

ExecutionState &IterativeDeepeningTimeSearcher::selectState() {
  ExecutionState &res = baseSearcher->selectState();
  startTime = time::getWallTime();
  return res;
}

void IterativeDeepeningTimeSearcher::update(
    ExecutionState *current, const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {

  const auto elapsed = time::getWallTime() - startTime;

  if (!removedStates.empty()) {
    std::vector<ExecutionState *> alt = removedStates;
    for (std::vector<ExecutionState *>::const_iterator
             it = removedStates.begin(),
             ie = removedStates.end();
         it != ie; ++it) {
      ExecutionState *es = *it;
      std::set<ExecutionState*>::const_iterator it2 = pausedStates.find(es);
      if (it2 != pausedStates.end()) {
        pausedStates.erase(it2);
        alt.erase(std::remove(alt.begin(), alt.end(), es), alt.end());
      }
    }    
    baseSearcher->update(current, addedStates, alt);
  } else {
    baseSearcher->update(current, addedStates, removedStates);
  }

  if (current &&
      std::find(removedStates.begin(), removedStates.end(), current) ==
          removedStates.end() &&
      elapsed > time) {
    pausedStates.insert(current);
    baseSearcher->removeState(current);
  }

  if (baseSearcher->empty()) {
    time *= 2;
    klee_message("increased time budget to %f\n", time.toSeconds());
    std::vector<ExecutionState *> ps(pausedStates.begin(), pausedStates.end());
    baseSearcher->update(0, ps, std::vector<ExecutionState *>());
    pausedStates.clear();
  }
}

/***/

ExecutionState &InterleavedSearcher::getState2Offload() {
}

ExecutionState* InterleavedSearcher::getState2Offload2() {
}

InterleavedSearcher::InterleavedSearcher(const std::vector<Searcher*> &_searchers)
  : searchers(_searchers),
    index(1) {
}

InterleavedSearcher::~InterleavedSearcher() {
  for (std::vector<Searcher*>::const_iterator it = searchers.begin(),
         ie = searchers.end(); it != ie; ++it)
    delete *it;
}

ExecutionState &InterleavedSearcher::selectState() {
  Searcher *s = searchers[--index];
  if (index==0) index = searchers.size();
  return s->selectState();
}

void InterleavedSearcher::update(
    ExecutionState *current, const std::vector<ExecutionState *> &addedStates,
    const std::vector<ExecutionState *> &removedStates) {
  for (std::vector<Searcher*>::const_iterator it = searchers.begin(),
         ie = searchers.end(); it != ie; ++it)
    (*it)->update(current, addedStates, removedStates);
}
