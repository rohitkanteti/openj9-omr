/*******************************************************************************
 * Copyright (c) 2000, 2022 IBM Corp. and others
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at http://eclipse.org/legal/epl-2.0
 * or the Apache License, Version 2.0 which accompanies this distribution
 * and is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following Secondary
 * Licenses when the conditions for such availability set forth in the
 * Eclipse Public License, v. 2.0 are satisfied: GNU General Public License,
 * version 2 with the GNU Classpath Exception [1] and GNU General Public
 * License, version 2 with the OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
 *******************************************************************************/

#include "optimizer/Optimizer.hpp"
#include <fstream>

#include "invariantparser/ptgparser/PointsToGraph.h"

#include <queue>
#include <iostream>

#include <omp.h>

#include "optimizer/Optimizer_inlines.hpp"
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "codegen/CodeGenerator.hpp"
#include "env/FrontEnd.hpp"
#include "compile/Compilation.hpp"
#include "compile/CompilationTypes.hpp"
#include "compile/Method.hpp"
#include "compile/SymbolReferenceTable.hpp"
#include "control/Options.hpp"
#include "control/Options_inlines.hpp"
#include "control/Recompilation.hpp"
#ifdef J9_PROJECT_SPECIFIC
#include "control/RecompilationInfo.hpp"
#endif
#include "env/CompilerEnv.hpp"
#include "env/IO.hpp"
#include "env/PersistentInfo.hpp"
#include "env/StackMemoryRegion.hpp"
#include "env/TRMemory.hpp"
#include "env/jittypes.h"
#include "il/Block.hpp"
#include "il/DataTypes.hpp"
#include "il/ILOpCodes.hpp"
#include "il/ILOps.hpp"
#include "il/Node.hpp"
#include "il/NodePool.hpp"
#include "il/Node_inlines.hpp"
#include "il/ResolvedMethodSymbol.hpp"
#include "il/Symbol.hpp"
#include "il/SymbolReference.hpp"
#include "il/TreeTop.hpp"
#include "il/TreeTop_inlines.hpp"
#include "il/ParameterSymbol.hpp"
#include "infra/Assert.hpp"
#include "infra/BitVector.hpp"
#include "infra/Cfg.hpp"
#include "infra/List.hpp"
#include "infra/SimpleRegex.hpp"
#include "infra/CfgNode.hpp"
#include "infra/Timer.hpp"
#include "optimizer/LoadExtensions.hpp"
#include "optimizer/Optimization.hpp"
#include "optimizer/OptimizationManager.hpp"
#include "optimizer/OptimizationStrategies.hpp"
#include "optimizer/Optimizations.hpp"
#include "optimizer/Structure.hpp"
#include "optimizer/StructuralAnalysis.hpp"
#include "optimizer/UseDefInfo.hpp"
#include "optimizer/ValueNumberInfo.hpp"
#include "optimizer/AsyncCheckInsertion.hpp"
#include "optimizer/DeadStoreElimination.hpp"
#include "optimizer/DeadTreesElimination.hpp"
#include "optimizer/CatchBlockRemover.hpp"
#include "optimizer/CFGSimplifier.hpp"
#include "optimizer/CompactLocals.hpp"
#include "optimizer/CopyPropagation.hpp"
#include "optimizer/ExpressionsSimplification.hpp"
#include "optimizer/GeneralLoopUnroller.hpp"
#include "optimizer/LocalCSE.hpp"
#include "optimizer/LocalDeadStoreElimination.hpp"
#include "optimizer/LocalLiveRangeReducer.hpp"
#include "optimizer/LocalOpts.hpp"
#include "optimizer/LocalReordering.hpp"
#include "optimizer/LoopCanonicalizer.hpp"
#include "optimizer/LoopReducer.hpp"
#include "optimizer/LoopReplicator.hpp"
#include "optimizer/LoopVersioner.hpp"
#include "optimizer/OrderBlocks.hpp"
#include "optimizer/RedundantAsyncCheckRemoval.hpp"
#include "optimizer/Simplifier.hpp"
#include "optimizer/VirtualGuardCoalescer.hpp"
#include "optimizer/VirtualGuardHeadMerger.hpp"
#include "optimizer/Inliner.hpp"
#include "ras/Debug.hpp"
#include "optimizer/InductionVariable.hpp"
#include "optimizer/GlobalValuePropagation.hpp"
#include "optimizer/LocalValuePropagation.hpp"
#include "optimizer/RegDepCopyRemoval.hpp"
#include "optimizer/SinkStores.hpp"
#include "optimizer/PartialRedundancy.hpp"
#include "optimizer/OSRDefAnalysis.hpp"
#include "optimizer/StripMiner.hpp"
#include "optimizer/FieldPrivatizer.hpp"
#include "optimizer/ReorderIndexExpr.hpp"
#include "optimizer/GlobalRegisterAllocator.hpp"
#include "optimizer/RecognizedCallTransformer.hpp"
#include "optimizer/SwitchAnalyzer.hpp"
#include "env/RegionProfiler.hpp"
#include "il/AutomaticSymbol.hpp"
#include "il/StaticSymbol.hpp"

#include <chrono>

namespace TR
{
   class AutomaticSymbol;
}

using namespace OMR; // Note: used here only to avoid having to prepend all opts in strategies with OMR::

#define MAX_LOCAL_OPTS_ITERS 5

// -------------------------------------------------------------------------------------------
// --------------------------- HELPER CLASSES START (HCS) ------------------------------------
// -------------------------------------------------------------------------------------------
template <typename T>
class UniqueDeque
{
public:
   // Adds an element to the deque if it's not already present
   void push_back(T value)
   {
      if (seen.find(value) == seen.end())
      {
         d.push_back(value);
         seen.insert(value);
      }
   }

   bool contains(T value)
   {
      if (seen.find(value) == seen.end())
      {
         return false;
      }
      return true;
   }

   // Removes an element from the front of the deque
   void pop_front()
   {
      if (!d.empty())
      {
         T front = d.front();
         d.pop_front();
         seen.erase(front);
      }
   }

   // Range insertion: Insert elements from another container
   template <typename InputIterator>
   void insert(InputIterator first, InputIterator last)
   {
      for (InputIterator it = first; it != last; ++it)
      {
         if (seen.find(*it) == seen.end())
         {
            d.push_back(*it);
            seen.insert(*it);
         }
      }
   }

   // Check if the deque is empty
   bool empty() const
   {
      return d.empty();
   }

   // Get the size of the deque
   size_t size() const
   {
      return d.size();
   }

   T &front()
   {
      if (d.empty())
      {
         std::cout << "ERROR: deque is empty\n";
      }
      return d.front();
   }

   typename std::deque<T>::iterator end()
   {
      if (d.empty())
      {
         d.begin();
      }
      return d.end();
   }

   typename std::deque<T>::iterator begin()
   {
      return d.begin();
   }

   T &operator[](size_t index)
   {
      if (index >= d.size())
      {
         std::cout << "ERROR: index out of range\n";
         throw std::out_of_range("Index out of range");
      }
      // Return the element at the given index
      return d[index]; // Using deque's operator[] to access elements by index
   }

private:
   std::deque<T> d;            // Deque to hold the elements
   std::unordered_set<T> seen; // Set to track unique elements
};

// A custom hash function for unordered_map with pair<int, int> as key
struct hash_pair
{
   template <class T1, class T2>
   size_t operator()(const pair<T1, T2> &pair) const
   {
      return hash<T1>()(pair.first) ^ hash<T2>()(pair.second);
   }
};

namespace std
{
   template <>
   struct hash<Entry>
   {
      std::size_t operator()(const Entry &e) const
      {
         // Combine hash values of members
         std::size_t h1 = std::hash<int>()(e.caller);
         std::size_t h2 = std::hash<int>()(e.bci);
         return h1 ^ (h2 << 1); // Combine hashes
      }
   };
}

class LinkCutTree
{
public:
   std::unordered_map<int, int> parent;
   std::unordered_map<int, std::unordered_set<int>> child;
   std::unordered_map<int, int> rank;

   int findRoot(int k)
   {
      if (parent.find(k) == parent.end())
      {
         parent[k] = k;
         rank[k] = 0;
      }
      if (parent[k] != k)
      {
         int root = findRoot(parent[k]);
         parent[k] = root;
      }
      return parent[k];
   }

   void link(int a, int b)
   {
      int x = findRoot(a);
      int y = findRoot(b);
      if (x == y)
      {
         return;
      }

      if (rank[x] > rank[y])
      {
         parent[y] = x;
         child[x].insert(y);
      }
      else
      {
         if (rank[x] < rank[y])
         {
            parent[x] = y;
            child[y].insert(x);
         }
         else
         {
            parent[x] = y;
            child[y].insert(x);
            rank[y] = rank[y] + 1;
         }
      }
   }

   std::unordered_set<int> getAllChildVars(int var)
   {
      std::unordered_set<int> result;
      std::deque<int> worklist;
      int root = findRoot(var);
      result.insert(root);
      worklist.push_back(root);
      while (!worklist.empty())
      {
         int current = worklist.front();
         worklist.pop_front();
         for (auto ch : child[current])
         {
            if (result.find(ch) == result.end())
            {
               result.insert(ch);
               worklist.push_back(ch);
            }
         }
      }
      return result;
   }
};

class MethodSet
{
public:
   LinkCutTree lct;
   std::unordered_map<int, std::unordered_set<int>> stmtMap;
};

class Counter
{
public:
   vcount_t visitCount;
   int retCount;
   int stmtCount;
   Counter(vcount_t v, int r)
   {
      visitCount = v;
      retCount = r;
      stmtCount = 0;
   }
};

class MapOfSet
{
public:
   // The data structure: map from TR_OpaqueMethodBlock* to a set of integers
   std::unordered_map<TR_OpaqueMethodBlock *, std::set<Entry *>> work;

   // Variable to maintain the total size of all sets
   size_t totalSize;

   // Constructor: initializes total size to 0
   MapOfSet() : totalSize(0) {}

   std::set<Entry *> &operator[](TR_OpaqueMethodBlock *key)
   {
      // Access work[method], and this will return a reference to the set.
      return work[key];
   }

   // Add an element to a specific set (identified by a key)
   bool addElement(TR_OpaqueMethodBlock *key, Entry *value)
   {
      // Insert the element into the set
      bool inserted = work[key].insert(value).second;

      // If the element was successfully inserted, update the total size
      if (inserted)
      {
         totalSize++;
         return inserted;
      }
      return inserted;
   }

   // Insert a range of elements into a specific set (identified by a key)
   bool insert(TR_OpaqueMethodBlock *key, typename std::set<Entry *>::iterator begin, typename std::set<Entry *>::iterator end)
   {
      auto &targetSet = work[key];

      // Remember the current size of the set before insertion
      size_t currentSize = targetSet.size();

      // Insert the entire range
      targetSet.insert(begin, end);

      // The number of elements inserted is the difference in size
      size_t newSize = targetSet.size();

      if (newSize > currentSize)
      {
         // Update the total size by how many new elements were inserted
         totalSize += (newSize - currentSize);
         return true;
      }

      return false;
   }

   // Get the total size (sum of sizes of all sets)
   size_t size() const
   {
      return totalSize;
   }

   // Get the size of the set for a specific key
   size_t getSetSize(TR_OpaqueMethodBlock *key) const
   {
      auto it = work.find(key);
      if (it != work.end())
      {
         return it->second.size();
      }
      return 0;
   }

   std::unordered_map<TR_OpaqueMethodBlock *, std::set<Entry *>>::iterator find(TR_OpaqueMethodBlock *key)
   {
      return work.find(key);
   }

   std::unordered_map<TR_OpaqueMethodBlock *, std::set<Entry *>>::iterator begin()
   {
      return work.begin();
   }

   std::unordered_map<TR_OpaqueMethodBlock *, std::set<Entry *>>::iterator end()
   {
      return work.end();
   }
};

class DeleteInfo
{
public:
   std::set<Entry *> heapDelta;
   MapOfSet stackDelta;
   std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> reanalyze;
   std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> workList;
};

// -------------------------------------------------------------------------------------------
// --------------------------- HELPER CLASSES END (HCE) --------------------------------------
// -------------------------------------------------------------------------------------------

// ************************ GLOBAL VARIABLES DECL START (GVS) ****************************************

// used to recognize thread type
static TR_OpaqueMethodBlock *_threadStartPersistentId;

static bool exhaustive = false;

static bool bruteForce = false;

static std::unordered_map<TR_OpaqueMethodBlock *, PointsToGraph *> methodPTG;

static std::unordered_map<TR_OpaqueMethodBlock *, PointsToGraph *> methodPTGout;

static std::unordered_map<TR_OpaqueMethodBlock *, PointsToGraph *> methodPTGcopy;
// ************************ GLOBAL VARIABLES DECL START (GVE) ****************************************

// ************************ GLOBAL DATA STRUCTURE DECL START (GDS) ****************************************
static std::unordered_map<std::string, int> _methodIndices;

static std::unordered_map<int, std::string> inverse_methodIndices;

static map<int, PointsToGraph> _indexPTG;

static std::unordered_map<int, std::string> _classIndices;

static std::unordered_map<TR_OpaqueClassBlock *, std::unordered_set<TR_OpaqueClassBlock *>> CHA;

static unordered_map<TR_OpaqueClassBlock *, int> classPtrToIndex;

// methods that were analyzed till now
static std::unordered_set<TR_OpaqueMethodBlock *> _methodsAnalyzed;

static std::unordered_set<TR_OpaqueMethodBlock *> _methodsBeingAnalyzed;

static std::unordered_map<TR_OpaqueMethodBlock *, int> methodPtrToIndex;

static std::unordered_map<int, std::map<int, std::set<int>>> _callsiteReceivers;

static std::unordered_map<std::string, TR_OpaqueMethodBlock *> methodNameIDmapping;

static std::unordered_map<TR_OpaqueMethodBlock *, string> inverseMethodNameIDmapping;

// (method, argument symref, argument number) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, int>> formalParMethod;

// (method, argument number, argument symref) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, int>> inverseFormalParMethod;

static std::unordered_map<TR::Node *, std::set<Entry *>> cachedValues; // affected and handled

// (method, variable symref, callnode, argument number) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, std::unordered_set<std::pair<TR::Node *, int>>>> argCallNode;

// (method, callnode, argument number, variable symref) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR::Node *, std::unordered_map<int, int>>> inverseArgCallNode;

// stmt number to stmt(node)
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, TR::Node *>> stmtNumber;

// (method, callnode, method) -update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR::Node *, std::unordered_set<TR_OpaqueMethodBlock *>>> myCallGraph;

// (method, callnode, method) -update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR::Node *, std::unordered_set<TR_OpaqueMethodBlock *>>> myCallGraphDelete;

// (method, method, callnode) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<TR::Node *>>> myInverseCallGraph;

// (method, method, callnode) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<TR::Node *>>> myInverseCallGraphDelete;

static std::unordered_map<TR::Node *, int> evaluatedNodeValues;

static std::unordered_set<TR_OpaqueMethodBlock *> topLevelMethods;

static std::unordered_set<TR_OpaqueMethodBlock *> topLevelVisited;

static std::unordered_map<TR::Node *, std::string> cachedMethodName;

static std::unordered_map<TR_OpaqueClassBlock *, std::unordered_map<std::string, TR_ResolvedMethod *>> cachedResolvedMethod;

static std::unordered_map<TR_OpaqueMethodBlock *, TR_ResolvedMethod *> cachedResolvedMethodFromPtr;

static std::unordered_map<TR_OpaqueClassBlock *, std::string> cachedClassSignature;

static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, TR_OpaqueClassBlock *>> cachedParameterType;

static std::unordered_map<TR::Node *, PointsToGraph *> callSiteStore;

static std::unordered_map<TR_OpaqueMethodBlock *, PointsToGraph *> returnSiteStore;

static std::unordered_map<Node *, Entry *> nodeAllocationMap;

static std::unordered_set<TR_OpaqueMethodBlock *> exhaustiveAnalyzed;

static std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> rootSetMap;

static std::unordered_set<TR_OpaqueMethodBlock *> cyclicMethods;

// ************************ GLOBAL DATA STRUCTURE DECL END (GDE) ******************************************

// ************************ EXTERN METHODS DECL START (EMS) ****************************************
extern std::map<int, std::set<int>> readReceivers(int methodIndex);

extern std::unordered_map<int, std::string> readClassIndices();

extern std::unordered_map<std::string, int> readMethodIndices();

extern std::unordered_set<std::string> readIgnoreMethodIndices();

extern map<int, PointsToGraph> readPTG(string fileName);

// ************************ EXTERN METHODS DECL END (EME) ******************************************

// ************************ EXTERN DS DECL START (EDS) ****************************************
extern std::unordered_map<int, std::unordered_map<int, Entry *>> entryMap;

// ************************ EXTERN DS DECL END (EDE) ******************************************

// ************************ PRIMARY METHODS DECL START (PMS) ****************************************

void initEngine(TR::Compilation *comp);

void benchmarkBuildIndependentSet(TR::Compilation *comp);

void computeMSetForMethod(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict);

int evaluateNode(TR::Node *node, Counter &counter, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp, bool fillCache, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict, std::unordered_set<TR::Node *> &nodeVisited);

void performPTA(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict, std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &reanalyze);

std::set<Entry *> processNode(TR::Node *node, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp,
                              Counter &counter, UniqueDeque<TR_OpaqueMethodBlock *> &workList,
                              std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &reanalyze, bool &flag,
                              std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict, std::unordered_set<TR::Node *> &nodeVisited);

void performDelete(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &delStmt,
                   std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict);

void deleteInit(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &delStmt,
                std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict,
                DeleteInfo &deleteInfo);

void findAffectedInfo(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict,
                      DeleteInfo &deleteInfo, std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<int>> &affectedVars);

std::set<Entry *> deletePointsToInfo(TR::Node *node, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp, Counter &counter, DeleteInfo &deleteInfo, std::unordered_set<TR::Node *> &nodeVisited);

void updateGlobalDS();

void performAddition(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &addStmt, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict);

void performExhaustivePTA(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict);

void analyzeNode(TR::Node *node, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp,
                 std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &visitedMap,
                 DeleteInfo &deleteInfo, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict);
// ************************ PRIMARY METHODS DECL END (PME) ******************************************

// ************************ SECONDARY METHODS DECL START (SMS) ****************************************

void constructCHA(TR::Compilation *comp);

int getOrInsertMethodIndex(TR::ResolvedMethodSymbol *methodSymbol, TR::Compilation *comp);

TR::Node *getUsefulNode(TR::Node *node);

void getVarSlots(TR::Node *node, TR::Compilation *comp, std::unordered_set<int> &evaluatedSymRef, TR_OpaqueMethodBlock *currentMethod);

std::set<Entry *> getCachedPointsTo(TR::Node *node);

PointsToGraph *buildCallsitePtg(TR::Node *callNode, PointsToGraph *in, TR_OpaqueMethodBlock *currentMethod,
                                TR::Compilation *comp, Counter &counter, UniqueDeque<TR_OpaqueMethodBlock *> &workList,
                                std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &reanalyze,
                                bool &flag, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict, std::unordered_set<TR::Node *> &nodeVisited);

Entry *evaluateAllocate(TR::Node *node, int methodIndex, int newType);

// ************************ SECONDARY METHODS DECL END (SME) ******************************************

// ************************ TERTIARY METHODS DEFN START (TMS) ******************************************

void printExhaustive();

std::string getMethodName(TR::ResolvedMethodSymbol *m);

char *substring(const char *str, size_t start, size_t length);

void pseudoTopoSort(TR::Block *currentBlock, std::vector<TR::Block *> &gray, std::vector<TR::Block *> &black, std::stack<TR::Block *> &sorted);

bool isLibraryMethod(std::string methodName);

std::string join(std::set<Entry *> const &entrySet, std::string delim);

std::string joinVec(std::vector<std::string> const &strings, std::string delim);

TR_ResolvedMethod *getCachedResolvedMethodFromPtr(TR::Compilation *comp, TR_OpaqueMethodBlock *methodPtr);

TR_ResolvedMethod *getCachedResolvedMethod(TR::Compilation *comp, TR_OpaqueClassBlock *classPointer, const char *methodName, const char *signature);

bool canCast(Entry *e, TR_OpaqueClassBlock *type, TR::Compilation *comp);

void checkCycles();

void cycleDFS(TR_OpaqueMethodBlock *currentMethod, std::deque<TR_OpaqueMethodBlock *> &myStack, std::unordered_set<TR_OpaqueMethodBlock *> &visited);

// ************************ TERTIARY METHODS DEFN END (TME) ******************************************

// ************************ DEBUG END (DBS) ******************************************
static TR_OpaqueMethodBlock *monitor1 = NULL;
static TR_OpaqueMethodBlock *monitor2 = NULL;
static TR_OpaqueMethodBlock *monitor3 = NULL;
static TR_OpaqueMethodBlock *monitor4 = NULL;
static TR_OpaqueMethodBlock *monitor5 = NULL;
bool debugFlag = false;
bool stopFlag = false;
// ************************ DEBUG END (DBE) ******************************************

const OptimizationStrategy localValuePropagationOpts[] =
    {
        {localCSE},
        {localValuePropagation},
        {localCSE, IfEnabled},
        {localValuePropagation, IfEnabled},
        {endGroup}};

const OptimizationStrategy arrayPrivatizationOpts[] =
    {
        {globalValuePropagation, IfMoreThanOneBlock},      // reduce # of null/bounds checks and setup iv info
        {veryCheapGlobalValuePropagationGroup, IfEnabled}, // enabled by blockVersioner
        {inductionVariableAnalysis, IfLoops},
        {loopCanonicalization, IfLoops}, // setup for any unrolling in arrayPrivatization
        {treeSimplification},            // get rid of null/bnd checks if possible
        {deadTreesElimination},
        {basicBlockOrdering, IfLoops}, // required for loop reduction
        {treesCleansing, IfLoops},
        {inductionVariableAnalysis, IfLoops},                   // required for array Privatization
        {basicBlockOrdering, IfEnabled},                        // cleanup if unrolling happened
        {globalValuePropagation, IfEnabledAndMoreThanOneBlock}, // ditto
        {endGroup}};

// To be run just before PRE
const OptimizationStrategy reorderArrayIndexOpts[] =
    {
        {inductionVariableAnalysis, IfLoops}, // need to id the primary IVs
        {reorderArrayIndexExpr, IfLoops},     // try to maximize loop invarient
                                              // expressions in index calculations and be hoisted
        {endGroup}};

const OptimizationStrategy cheapObjectAllocationOpts[] =
    {
        {eachEscapeAnalysisPassGroup, IfEAOpportunitiesAndNotOptServer},
        {explicitNewInitialization, IfNews}, // do before local dead store
                                             // basicBlockHoisting,                     // merge block into pred and prepare for local dead store
        {localDeadStoreElimination},         // remove local/parm/some field stores
        {endGroup}};

const OptimizationStrategy expensiveObjectAllocationOpts[] =
    {
        {eachEscapeAnalysisPassGroup, IfEAOpportunities},
        {explicitNewInitialization, IfNews}, // do before local dead store
        {endGroup}};

const OptimizationStrategy eachEscapeAnalysisPassOpts[] =
    {
        {preEscapeAnalysis, IfOSR},
        {escapeAnalysis},
        {postEscapeAnalysis, IfOSR},
        {eachEscapeAnalysisPassGroup, IfEnabled}, // if another pass requested
        {endGroup}};

const OptimizationStrategy veryCheapGlobalValuePropagationOpts[] =
    {
        {globalValuePropagation, IfMoreThanOneBlock},
        {endGroup}};

const OptimizationStrategy cheapGlobalValuePropagationOpts[] =
    {
        //{ catchBlockRemoval,                     },
        {CFGSimplification, IfOptServer},            // for WAS trace folding
        {treeSimplification, IfOptServer},           // for WAS trace folding
        {localCSE, IfEnabledAndOptServer},           // for WAS trace folding
        {treeSimplification, IfEnabledAndOptServer}, // for WAS trace folding
        {globalValuePropagation, IfMoreThanOneBlock},
        {localValuePropagation, IfOneBlock},
        {treeSimplification, IfEnabled},
        {cheapObjectAllocationGroup},
        {globalValuePropagation, IfEnabled}, // if inlined a call or an object
        {treeSimplification, IfEnabled},
        {catchBlockRemoval, IfEnabled},                                    // if checks were removed
        {osrExceptionEdgeRemoval},                                         // most inlining is done by now
        {redundantMonitorElimination, IfMonitors},                         // performed if method has monitors
        {redundantMonitorElimination, IfEnabledAndMonitors},               // performed if method has monitors
        {globalValuePropagation, IfEnabledAndMoreThanOneBlockMarkLastRun}, // mark monitors requiring sync
        {virtualGuardTailSplitter, IfEnabled},                             // merge virtual guards
        {CFGSimplification},
        {endGroup}};

const OptimizationStrategy expensiveGlobalValuePropagationOpts[] =
    {
        /////   { innerPreexistence                             },
        {CFGSimplification, IfOptServer},  // for WAS trace folding
        {treeSimplification, IfOptServer}, // for WAS trace folding
        {localCSE, IfEnabledAndOptServer}, // for WAS trace folding
        {treeSimplification, IfEnabled},   // may be enabled by inner prex
        {globalValuePropagation, IfMoreThanOneBlock},
        {treeSimplification, IfEnabled},
        {deadTreesElimination}, // clean up left-over accesses before escape analysis
#ifdef J9_PROJECT_SPECIFIC
        {expensiveObjectAllocationGroup},
#endif
        {globalValuePropagation, IfEnabledAndMoreThanOneBlock}, // if inlined a call or an object
        {treeSimplification, IfEnabled},
        {catchBlockRemoval, IfEnabled}, // if checks were removed
        {osrExceptionEdgeRemoval},      // most inlining is done by now
#ifdef J9_PROJECT_SPECIFIC
        {redundantMonitorElimination, IfEnabled}, // performed if method has monitors
        {redundantMonitorElimination, IfEnabled}, // performed if method has monitors
#endif
        {globalValuePropagation, IfEnabledAndMoreThanOneBlock}, // mark monitors requiring sync
        {virtualGuardTailSplitter, IfEnabled},                  // merge virtual guards
        {CFGSimplification},
        {endGroup}};

const OptimizationStrategy eachExpensiveGlobalValuePropagationOpts[] =
    {
        //{ blockSplitter                                        },
        ///   { innerPreexistence                                      },
        {globalValuePropagation, IfMoreThanOneBlock},
        {treeSimplification, IfEnabled},
        {veryCheapGlobalValuePropagationGroup, IfEnabled}, // enabled by blockversioner
        {deadTreesElimination},                            // clean up left-over accesses before escape analysis
#ifdef J9_PROJECT_SPECIFIC
        {expensiveObjectAllocationGroup},
#endif
        {eachExpensiveGlobalValuePropagationGroup, IfEnabled}, // if inlining was done
        {endGroup}};

const OptimizationStrategy veryExpensiveGlobalValuePropagationOpts[] =
    {
        {eachExpensiveGlobalValuePropagationGroup},
        //{ basicBlockHoisting,                           }, // merge block into pred and prepare for local dead store
        {localDeadStoreElimination}, // remove local/parm/some field stores
        {treeSimplification, IfEnabled},
        {catchBlockRemoval, IfEnabled}, // if checks were removed
        {osrExceptionEdgeRemoval},      // most inlining is done by now
#ifdef J9_PROJECT_SPECIFIC
        {redundantMonitorElimination, IfEnabled}, // performed if method has monitors
        {redundantMonitorElimination, IfEnabled}, // performed if method has monitors
#endif
        {globalValuePropagation, IfEnabledAndMoreThanOneBlock}, // mark monitors requiring syncs
        {virtualGuardTailSplitter, IfEnabled},                  // merge virtual guards
        {CFGSimplification},
        {endGroup}};

const OptimizationStrategy partialRedundancyEliminationOpts[] =
    {
        {globalValuePropagation, IfMoreThanOneBlock}, // GVP (before PRE)
        {deadTreesElimination},
        {treeSimplification, IfEnabled},
        {treeSimplification},               // might fold expressions created by versioning/induction variables
        {treeSimplification, IfEnabled},    // Array length simplification shd be followed by reassoc before PRE
        {reorderArrayExprGroup, IfEnabled}, // maximize opportunities hoisting of index array expressions
        {partialRedundancyElimination, IfMoreThanOneBlock},
        {
            localCSE,
        },                                                                 // common up expression which can benefit EA
        {catchBlockRemoval, IfEnabled},                                    // if checks were removed
        {deadTreesElimination, IfEnabled},                                 // if checks were removed
        {compactNullChecks, IfEnabled},                                    // PRE creates explicit null checks in large numbers
        {localReordering, IfEnabled},                                      // PRE may create temp stores that can be moved closer to uses
        {globalValuePropagation, IfEnabledAndMoreThanOneBlockMarkLastRun}, // GVP (after PRE)
#ifdef J9_PROJECT_SPECIFIC
        {preEscapeAnalysis, IfOSR},
        {escapeAnalysis, IfEAOpportunitiesMarkLastRun}, // to stack-allocate after loopversioner and localCSE
        {postEscapeAnalysis, IfOSR},
#endif
        {basicBlockOrdering, IfLoops},    // early ordering with no extension
        {globalCopyPropagation, IfLoops}, // for Loop Versioner

        {loopVersionerGroup, IfEnabledAndLoops},
        {treeSimplification, IfEnabled},                            // loop reduction block should be after PRE so that privatization
        {treesCleansing},                                           // clean up gotos in code and convert to fall-throughs for loop reducer
        {redundantGotoElimination, IfNotJitProfiling},              // clean up for loop reducer.  Note: NEVER run this before PRE
        {loopReduction, IfLoops},                                   // will have happened and it needs to be before loopStrider
        {localCSE, IfEnabled},                                      // so that it will not get confused with internal pointers.
        {globalDeadStoreElimination, IfEnabledAndMoreThanOneBlock}, // It may need to be run twice if deadstore elimination is required,
        {
            deadTreesElimination,
        }, // but this only happens for unsafe access (arraytranslate.twoToOne)
        {
            loopReduction,
        }, // and so is conditional
#ifdef J9_PROJECT_SPECIFIC
        {idiomRecognition, IfLoopsAndNotProfiling}, // after loopReduction!!
#endif
        {lastLoopVersionerGroup, IfLoops},
        {
            treeSimplification,
        }, // cleanup before AutoVectorization
        {
            deadTreesElimination,
        }, // cleanup before AutoVectorization
        {inductionVariableAnalysis, IfLoopsAndNotProfiling},
#ifdef J9_PROJECT_SPECIFIC
        {SPMDKernelParallelization, IfLoops},
#endif
        {loopStrider, IfLoops},
        {treeSimplification, IfEnabled},
        {lastLoopVersionerGroup, IfEnabledAndLoops},
        {
            treeSimplification,
        }, // cleanup before strider
        {
            localCSE,
        }, // cleanup before strider so it will not be confused by commoned nodes (mandatory to run local CSE before strider)
        {
            deadTreesElimination,
        }, // cleanup before strider so that dead stores can be eliminated more effcientlly (i.e. false uses are not seen)
        {loopStrider, IfLoops},

        {treeSimplification, IfEnabled}, // cleanup after strider
        {loopInversion, IfLoops},
        {endGroup}};

const OptimizationStrategy methodHandleInvokeInliningOpts[] =
    {
        {
            treeSimplification,
        }, // Supply some known-object info, and help CSE
        {
            localCSE,
        },                       // Especially copy propagation to replace temps with more descriptive trees
        {localValuePropagation}, // Propagate known-object info and derive more specific archetype specimen symbols for inlining
#ifdef J9_PROJECT_SPECIFIC
        {
            targetedInlining,
        },
#endif
        {deadTreesElimination},
        {methodHandleInvokeInliningGroup, IfEnabled}, // Repeat as required to inline all the MethodHandle.invoke calls we can afford
        {endGroup},
};

const OptimizationStrategy earlyGlobalOpts[] =
    {
        {methodHandleInvokeInliningGroup, IfMethodHandleInvokes},
#ifdef J9_PROJECT_SPECIFIC
        {inlining},
#endif
        {osrExceptionEdgeRemoval}, // most inlining is done by now
        //{ basicBlockOrdering,          IfLoops }, // early ordering with no extension
        {treeSimplification, IfEnabled},
        {compactNullChecks}, // cleans up after inlining; MUST be done before PRE
#ifdef J9_PROJECT_SPECIFIC
        {virtualGuardTailSplitter}, // merge virtual guards
        {treeSimplification},
        {CFGSimplification},
#endif
        {endGroup}};

const OptimizationStrategy earlyLocalOpts[] =
    {
        {localValuePropagation},
        //{ localValuePropagationGroup           },
        {localReordering},
        {
            switchAnalyzer,
        },
        {treeSimplification, IfEnabled}, // simplify any exprs created by LCP/LCSE
#ifdef J9_PROJECT_SPECIFIC
        {catchBlockRemoval}, // if all possible exceptions in a try were removed by inlining/LCP/LCSE
#endif
        {deadTreesElimination}, // remove any anchored dead loads
        {profiledNodeVersioning},
        {endGroup}};

const OptimizationStrategy isolatedStoreOpts[] =
    {
        {isolatedStoreElimination},
        {deadTreesElimination},
        {endGroup}};

const OptimizationStrategy globalDeadStoreOpts[] =
    {
        {globalDeadStoreElimination, IfMoreThanOneBlock},
        {deadTreesElimination},
        {endGroup}};

const OptimizationStrategy loopAliasRefinerOpts[] =
    {
        {inductionVariableAnalysis, IfLoops},
        {loopCanonicalization},
        {globalValuePropagation, IfMoreThanOneBlock}, // create ivs
        {loopAliasRefiner},
        {endGroup}};

const OptimizationStrategy loopSpecializerOpts[] =
    {
        {inductionVariableAnalysis, IfLoops},
        {loopCanonicalization},
        {loopSpecializer},
        {endGroup}};

const OptimizationStrategy loopVersionerOpts[] =
    {
        {basicBlockOrdering},
        {inductionVariableAnalysis, IfLoops},
        {loopCanonicalization},
        {loopVersioner},
        {endGroup}};

const OptimizationStrategy lastLoopVersionerOpts[] =
    {
        {inductionVariableAnalysis, IfLoops},
        {loopCanonicalization},
        {loopVersioner, MarkLastRun},
        {endGroup}};

const OptimizationStrategy loopCanonicalizationOpts[] =
    {
        {globalCopyPropagation, IfLoops}, // propagate copies to allow better invariance detection
        {loopVersionerGroup},
        {deadTreesElimination}, // remove dead anchors created by check removal (versioning)
        //{ loopStrider                        }, // use canonicalized loop to insert initializations
        {treeSimplification},                      // remove unreachable blocks (with nullchecks etc.) left by LoopVersioner
        {fieldPrivatization},                      // use canonicalized loop to privatize fields
        {treeSimplification},                      // might fold expressions created by versioning/induction variables
        {loopSpecializerGroup, IfEnabledAndLoops}, // specialize the versioned loop if possible
        {deadTreesElimination, IfEnabledAndLoops}, // remove dead anchors created by specialization
        {treeSimplification, IfEnabledAndLoops},   // might fold expressions created by specialization
        {endGroup}};

const OptimizationStrategy stripMiningOpts[] =
    {
        {inductionVariableAnalysis, IfLoops},
        {loopCanonicalization},
        {inductionVariableAnalysis},
        {stripMining},
        {endGroup}};

const OptimizationStrategy blockManipulationOpts[] =
    {
        //   { generalLoopUnroller,       IfLoops   }, //Unroll Loops
        {coldBlockOutlining},
        {CFGSimplification, IfNotJitProfiling},
        {basicBlockHoisting, IfNotJitProfiling},
        {treeSimplification},
        {redundantGotoElimination, IfNotJitProfiling}, // redundant gotos gone
        {treesCleansing},                              // maximize fall throughs
        {virtualGuardHeadMerger},
        {basicBlockExtension, MarkLastRun}, // extend blocks; move trees around if reqd
        {treeSimplification},               // revisit; not really required ?
        {basicBlockPeepHole, IfEnabled},
        {endGroup}};

const OptimizationStrategy eachLocalAnalysisPassOpts[] =
    {
        {localValuePropagationGroup, IfEnabled},
#ifdef J9_PROJECT_SPECIFIC
        {arraycopyTransformation},
#endif
        {treeSimplification, IfEnabled},
        {localCSE, IfEnabled},
        {localDeadStoreElimination, IfEnabled}, // after local copy/value propagation
        {rematerialization, IfEnabled},
        {compactNullChecks, IfEnabled},
        {deadTreesElimination, IfEnabled}, // remove dead anchors created by check/store removal
        //{ eachLocalAnalysisPassGroup, IfEnabled  }, // if another pass requested
        {endGroup}};

const OptimizationStrategy lateLocalOpts[] =
    {
        {OMR::eachLocalAnalysisPassGroup},
        {OMR::andSimplification}, // needs commoning across blocks to work well; must be done after versioning
        {OMR::treesCleansing},    // maximize fall throughs after LCP has converted some conditions to gotos
        {OMR::eachLocalAnalysisPassGroup},
        {OMR::localDeadStoreElimination}, // after latest copy propagation
        {OMR::deadTreesElimination},      // remove dead anchors created by check/store removal
        {
            OMR::globalDeadStoreGroup,
        },
        {OMR::eachLocalAnalysisPassGroup},
        {OMR::treeSimplification},
        {OMR::endGroup}};

static const OptimizationStrategy tacticalGlobalRegisterAllocatorOpts[] =
    {
        {OMR::inductionVariableAnalysis, OMR::IfLoops},
        {OMR::loopCanonicalization, OMR::IfLoops},
        {OMR::liveRangeSplitter, OMR::IfLoops},
        {OMR::redundantGotoElimination, OMR::IfNotJitProfiling}, // need to be run before global register allocator
        {OMR::treeSimplification, OMR::MarkLastRun},             // Cleanup the trees after redundantGotoElimination
        {OMR::tacticalGlobalRegisterAllocator, OMR::IfEnabled},
        {OMR::localCSE},
        // { isolatedStoreGroup,                    IfEnabled                    }, // if global register allocator created stores from registers
        {OMR::globalCopyPropagation, OMR::IfEnabledAndMoreThanOneBlock}, // if live range splitting created copies
        {OMR::localCSE},                                                 // localCSE after post-PRE + post-GRA globalCopyPropagation to clean up whole expression remat (rtc 64659)
        {OMR::globalDeadStoreGroup, OMR::IfEnabled},
        {OMR::redundantGotoElimination, OMR::IfEnabledAndNotJitProfiling}, // if global register allocator created new block
        {OMR::deadTreesElimination},                                       // remove dangling GlRegDeps
        {OMR::deadTreesElimination, OMR::IfEnabled},                       // remove dead RegStores produced by previous deadTrees pass
        {OMR::deadTreesElimination, OMR::IfEnabled},                       // remove dead RegStores produced by previous deadTrees pass
        {OMR::endGroup}};

const OptimizationStrategy finalGlobalOpts[] =
    {
        {rematerialization},
        {compactNullChecks, IfEnabled},
        {deadTreesElimination},
        //{ treeSimplification,       IfEnabled  },
        {localLiveRangeReduction},
        {compactLocals, IfNotJitProfiling}, // analysis results are invalidated by profilingGroup
#ifdef J9_PROJECT_SPECIFIC
        {globalLiveVariablesForGC},
#endif
        {endGroup}};

// **************************************************************************
//
// Strategy that is run for each non-peeking IlGeneration - this allows early
// optimizations to be run even before the IL is available to Inliner
//
// **************************************************************************
static const OptimizationStrategy ilgenStrategyOpts[] =
    {
#ifdef J9_PROJECT_SPECIFIC
        {osrLiveRangeAnalysis, IfOSR},
        {osrDefAnalysis, IfInvoluntaryOSR},
        {
            methodHandleTransformer,
        },
        {varHandleTransformer, MustBeDone},
        {handleRecompilationOps, MustBeDone},
        {unsafeFastPath},
        {recognizedCallTransformer},
        {coldBlockMarker},
        {CFGSimplification},
        {allocationSinking, IfNews},
        {invariantArgumentPreexistence, IfNotClassLoadPhaseAndNotProfiling}, // Should not run if a recompilation is possible
#endif
        {endOpts},
};

// **********************************************************
//
// OMR Strategies
//
// **********************************************************

static const OptimizationStrategy omrNoOptStrategyOpts[] =
    {
        {endOpts},
};

static const OptimizationStrategy omrColdStrategyOpts[] =
    {
        {basicBlockExtension},
        {localCSE},
        //{ localValuePropagation                },
        {treeSimplification},
        {localCSE},
        {endOpts},
};

static const OptimizationStrategy omrWarmStrategyOpts[] =
    {
        {basicBlockExtension},
        {localCSE},
        //{ localValuePropagation               },
        {treeSimplification},
        {localCSE},
        {localDeadStoreElimination},
        {globalDeadStoreGroup},
        {endOpts},
};

static const OptimizationStrategy omrHotStrategyOpts[] =
    {
        {OMR::coldBlockOutlining},
        {OMR::earlyGlobalGroup},
        {OMR::earlyLocalGroup},
        {OMR::andSimplification}, // needs commoning across blocks to work well; must be done after versioning
        {
            OMR::stripMiningGroup,
        }, // strip mining in loops
        {
            OMR::loopReplicator,
        }, // tail-duplication in loops
        {
            OMR::blockSplitter,
        }, // treeSimplification + blockSplitter + VP => opportunity for EA
        {
            OMR::arrayPrivatizationGroup,
        }, // must preceed escape analysis
        {OMR::veryExpensiveGlobalValuePropagationGroup},
        {
            OMR::globalDeadStoreGroup,
        },
        {
            OMR::globalCopyPropagation,
        },
        {
            OMR::loopCanonicalizationGroup,
        }, // canonicalize loops (improve fall throughs)
        {
            OMR::expressionsSimplification,
        },
        {OMR::partialRedundancyEliminationGroup},
        {
            OMR::globalDeadStoreElimination,
        },
        {
            OMR::inductionVariableAnalysis,
        },
        {
            OMR::loopSpecializerGroup,
        },
        {
            OMR::inductionVariableAnalysis,
        },
        {
            OMR::generalLoopUnroller,
        }, // unroll Loops
        {OMR::blockSplitter, OMR::MarkLastRun},
        {OMR::blockManipulationGroup},
        {OMR::lateLocalGroup},
        {OMR::redundantAsyncCheckRemoval}, // optimize async check placement
#ifdef J9_PROJECT_SPECIFIC
        {
            OMR::recompilationModifier,
        }, // do before GRA to avoid commoning of longs afterwards
#endif
        {
            OMR::globalCopyPropagation,
        }, // Can produce opportunities for store sinking
        {OMR::generalStoreSinking},
        {
            OMR::localCSE,
        }, // common up lit pool refs in the same block
        {
            OMR::treeSimplification,
        }, // cleanup the trees after sunk store and localCSE
        {OMR::trivialBlockExtension},
        {
            OMR::localDeadStoreElimination,
        }, // remove the astore if no literal pool is required
        {
            OMR::localCSE,
        }, // common up lit pool refs in the same block
        {OMR::arraysetStoreElimination},
        {OMR::localValuePropagation, OMR::MarkLastRun},
        {OMR::checkcastAndProfiledGuardCoalescer},
        {OMR::osrExceptionEdgeRemoval, OMR::MarkLastRun},
        {
            OMR::tacticalGlobalRegisterAllocatorGroup,
        },
        {
            OMR::globalDeadStoreElimination,
        },                           // global dead store removal
        {OMR::deadTreesElimination}, // cleanup after dead store removal
        {OMR::compactNullChecks},    // cleanup at the end
        {OMR::finalGlobalGroup},     // done just before codegen
        {OMR::regDepCopyRemoval},
        {endOpts},
};

// The following arrays of Optimization pointers are externally declared in OptimizerStrategies.hpp
// This allows frontends to assist in selection of optimizer strategies.
// (They cannot be made 'static const')

const OptimizationStrategy *omrCompilationStrategies[] =
    {
        omrNoOptStrategyOpts, // empty strategy
        omrColdStrategyOpts,  // <<  specialized
        omrWarmStrategyOpts,  // <<  specialized
        omrHotStrategyOpts,   // currently used to test available omr optimizations
};

#ifdef OPT_TIMING // provide statistics on time taken by individual optimizations
TR_Stats statOptTiming[OMR::numOpts];
TR_Stats statStructuralAnalysisTiming("Structural Analysis");
TR_Stats statUseDefsTiming("Use Defs");
TR_Stats statGlobalValNumTiming("Global Value Numbering");
#endif // OPT_TIMING

TR::Optimizer *OMR::Optimizer::createOptimizer(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol, bool isIlGen)
{
   // returns IL optimizer, performs tree-to-tree optimizing transformations.
   if (isIlGen)
      return new (comp->trHeapMemory()) TR::Optimizer(comp, methodSymbol, isIlGen, ilgenStrategyOpts);

   if (comp->getOptions()->getCustomStrategy())
   {
      if (comp->getOption(TR_TraceOptDetails))
         traceMsg(comp, "Using custom optimization strategy\n");

      // Reformat custom strategy as array of Optimization rather than array of int32_t
      //
      int32_t *srcStrategy = comp->getOptions()->getCustomStrategy();
      int32_t size = comp->getOptions()->getCustomStrategySize();
      OptimizationStrategy *customStrategy = (OptimizationStrategy *)comp->trMemory()->allocateHeapMemory(size * sizeof(customStrategy[0]));
      for (int32_t i = 0; i < size; i++)
      {
         OptimizationStrategy o = {(OMR::Optimizations)(srcStrategy[i] & TR::Options::OptNumMask)};
         if (srcStrategy[i] & TR::Options::MustBeDone)
            o._options = MustBeDone;
         customStrategy[i] = o;
      }

      return new (comp->trHeapMemory()) TR::Optimizer(comp, methodSymbol, isIlGen, customStrategy);
   }

   TR::Optimizer *optimizer = new (comp->trHeapMemory()) TR::Optimizer(
       comp,
       methodSymbol,
       isIlGen,
       TR::Optimizer::optimizationStrategy(comp),
       TR::Optimizer::valueNumberInfoBuildType());

   return optimizer;
}

// ************************************************************************
//
// Implementation of TR::Optimizer
//
// ************************************************************************

OMR::Optimizer::Optimizer(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol, bool isIlGen,
                          const OptimizationStrategy *strategy, uint16_t VNType)
    : _compilation(comp),
      _cg(comp->cg()),
      _trMemory(comp->trMemory()),
      _methodSymbol(methodSymbol),
      _isIlGen(isIlGen),
      _strategy(strategy),
      _vnInfoType(VNType),
      _symReferencesTable(NULL),
      _useDefInfo(NULL),
      _valueNumberInfo(NULL),
      _aliasSetsAreValid(false),
      _cantBuildGlobalsUseDefInfo(false),
      _cantBuildLocalsUseDefInfo(false),
      _cantBuildGlobalsValueNumberInfo(false),
      _cantBuildLocalsValueNumberInfo(false),
      _canRunBlockByBlockOptimizations(true),
      _cachedExtendedBBInfoValid(false),
      _inlineSynchronized(true),
      _enclosingFinallyBlock(NULL),
      _eliminatedCheckcastNodes(comp->trMemory()),
      _classPointerNodes(comp->trMemory()),
      _optMessageIndex(0),
      _seenBlocksGRA(NULL),
      _resetExitsGRA(NULL),
      _successorBitsGRA(NULL),
      _stackedOptimizer(false),
      _firstTimeStructureIsBuilt(true),
      _disableLoopOptsThatCanCreateLoops(false)
{
   // zero opts table
   memset(_opts, 0, sizeof(_opts));

/*
 * Allow downstream projects to disable the default initialization of optimizations
 * and allow them to take full control over this process.  This can be an advantage
 * if they don't use all of the optimizations initialized here as they can avoid
 * getting linked in to the binary in their entirety.
 */
#if !defined(TR_OVERRIDE_OPTIMIZATION_INITIALIZATION)
   // initialize OMR optimizations

   _opts[OMR::andSimplification] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_SimplifyAnds::create, OMR::andSimplification);
   _opts[OMR::arraysetStoreElimination] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_ArraysetStoreElimination::create, OMR::arraysetStoreElimination);
   _opts[OMR::asyncCheckInsertion] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_AsyncCheckInsertion::create, OMR::asyncCheckInsertion);
   _opts[OMR::basicBlockExtension] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_ExtendBasicBlocks::create, OMR::basicBlockExtension);
   _opts[OMR::basicBlockHoisting] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_HoistBlocks::create, OMR::basicBlockHoisting);
   _opts[OMR::basicBlockOrdering] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_OrderBlocks::create, OMR::basicBlockOrdering);
   _opts[OMR::basicBlockPeepHole] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_PeepHoleBasicBlocks::create, OMR::basicBlockPeepHole);
   _opts[OMR::blockShuffling] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_BlockShuffling::create, OMR::blockShuffling);
   _opts[OMR::blockSplitter] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_BlockSplitter::create, OMR::blockSplitter);
   _opts[OMR::catchBlockRemoval] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_CatchBlockRemover::create, OMR::catchBlockRemoval);
   _opts[OMR::CFGSimplification] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::CFGSimplifier::create, OMR::CFGSimplification);
   _opts[OMR::checkcastAndProfiledGuardCoalescer] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_CheckcastAndProfiledGuardCoalescer::create, OMR::checkcastAndProfiledGuardCoalescer);
   _opts[OMR::coldBlockMarker] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_ColdBlockMarker::create, OMR::coldBlockMarker);
   _opts[OMR::coldBlockOutlining] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_ColdBlockOutlining::create, OMR::coldBlockOutlining);
   _opts[OMR::compactLocals] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_CompactLocals::create, OMR::compactLocals);
   _opts[OMR::compactNullChecks] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_CompactNullChecks::create, OMR::compactNullChecks);
   _opts[OMR::deadTreesElimination] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::DeadTreesElimination::create, OMR::deadTreesElimination);
   _opts[OMR::expressionsSimplification] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_ExpressionsSimplification::create, OMR::expressionsSimplification);
   _opts[OMR::generalLoopUnroller] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_GeneralLoopUnroller::create, OMR::generalLoopUnroller);
   _opts[OMR::globalCopyPropagation] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_CopyPropagation::create, OMR::globalCopyPropagation);
   _opts[OMR::globalDeadStoreElimination] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_DeadStoreElimination::create, OMR::globalDeadStoreElimination);
   _opts[OMR::inlining] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_TrivialInliner::create, OMR::inlining);
   _opts[OMR::innerPreexistence] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_InnerPreexistence::create, OMR::innerPreexistence);
   _opts[OMR::invariantArgumentPreexistence] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_InvariantArgumentPreexistence::create, OMR::invariantArgumentPreexistence);
   _opts[OMR::loadExtensions] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoadExtensions::create, OMR::loadExtensions);
   _opts[OMR::localCSE] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::LocalCSE::create, OMR::localCSE);
   _opts[OMR::localDeadStoreElimination] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::LocalDeadStoreElimination::create, OMR::localDeadStoreElimination);
   _opts[OMR::localLiveRangeReduction] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LocalLiveRangeReduction::create, OMR::localLiveRangeReduction);
   _opts[OMR::localReordering] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LocalReordering::create, OMR::localReordering);
   _opts[OMR::loopCanonicalization] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoopCanonicalizer::create, OMR::loopCanonicalization);
   _opts[OMR::loopVersioner] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoopVersioner::create, OMR::loopVersioner);
   _opts[OMR::loopReduction] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoopReducer::create, OMR::loopReduction);
   _opts[OMR::loopReplicator] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoopReplicator::create, OMR::loopReplicator);
   _opts[OMR::profiledNodeVersioning] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_ProfiledNodeVersioning::create, OMR::profiledNodeVersioning);
   _opts[OMR::redundantAsyncCheckRemoval] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_RedundantAsyncCheckRemoval::create, OMR::redundantAsyncCheckRemoval);
   _opts[OMR::redundantGotoElimination] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_EliminateRedundantGotos::create, OMR::redundantGotoElimination);
   _opts[OMR::rematerialization] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_Rematerialization::create, OMR::rematerialization);
   _opts[OMR::treesCleansing] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_CleanseTrees::create, OMR::treesCleansing);
   _opts[OMR::treeSimplification] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::Simplifier::create, OMR::treeSimplification);
   _opts[OMR::trivialBlockExtension] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_TrivialBlockExtension::create, OMR::trivialBlockExtension);
   _opts[OMR::trivialDeadTreeRemoval] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_TrivialDeadTreeRemoval::create, OMR::trivialDeadTreeRemoval);
   _opts[OMR::virtualGuardHeadMerger] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_VirtualGuardHeadMerger::create, OMR::virtualGuardHeadMerger);
   _opts[OMR::virtualGuardTailSplitter] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_VirtualGuardTailSplitter::create, OMR::virtualGuardTailSplitter);
   _opts[OMR::generalStoreSinking] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_GeneralSinkStores::create, OMR::generalStoreSinking);
   _opts[OMR::globalValuePropagation] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::GlobalValuePropagation::create, OMR::globalValuePropagation);
   _opts[OMR::localValuePropagation] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::LocalValuePropagation::create, OMR::localValuePropagation);
   _opts[OMR::redundantInductionVarElimination] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_RedundantInductionVarElimination::create, OMR::redundantInductionVarElimination);
   _opts[OMR::partialRedundancyElimination] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_PartialRedundancy::create, OMR::partialRedundancyElimination);
   _opts[OMR::loopInversion] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoopInverter::create, OMR::loopInversion);
   _opts[OMR::inductionVariableAnalysis] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_InductionVariableAnalysis::create, OMR::inductionVariableAnalysis);
   _opts[OMR::osrExceptionEdgeRemoval] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_OSRExceptionEdgeRemoval::create, OMR::osrExceptionEdgeRemoval);
   _opts[OMR::regDepCopyRemoval] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::RegDepCopyRemoval::create, OMR::regDepCopyRemoval);
   _opts[OMR::stripMining] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_StripMiner::create, OMR::stripMining);
   _opts[OMR::fieldPrivatization] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_FieldPrivatizer::create, OMR::fieldPrivatization);
   _opts[OMR::reorderArrayIndexExpr] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_IndexExprManipulator::create, OMR::reorderArrayIndexExpr);
   _opts[OMR::loopStrider] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoopStrider::create, OMR::loopStrider);
   _opts[OMR::osrDefAnalysis] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_OSRDefAnalysis::create, OMR::osrDefAnalysis);
   _opts[OMR::osrLiveRangeAnalysis] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_OSRLiveRangeAnalysis::create, OMR::osrLiveRangeAnalysis);
   _opts[OMR::tacticalGlobalRegisterAllocator] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_GlobalRegisterAllocator::create, OMR::tacticalGlobalRegisterAllocator);
   _opts[OMR::liveRangeSplitter] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LiveRangeSplitter::create, OMR::liveRangeSplitter);
   _opts[OMR::loopSpecializer] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR_LoopSpecializer::create, OMR::loopSpecializer);
   _opts[OMR::recognizedCallTransformer] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::RecognizedCallTransformer::create, OMR::recognizedCallTransformer);
   _opts[OMR::switchAnalyzer] =
       new (comp->allocator()) TR::OptimizationManager(self(), TR::SwitchAnalyzer::create, OMR::switchAnalyzer);

   // NOTE: Please add new OMR optimizations here!

   // initialize OMR optimization groups

   _opts[OMR::globalDeadStoreGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::globalDeadStoreGroup, globalDeadStoreOpts);
   _opts[OMR::loopCanonicalizationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::loopCanonicalizationGroup, loopCanonicalizationOpts);
   _opts[OMR::loopVersionerGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::loopVersionerGroup, loopVersionerOpts);
   _opts[OMR::lastLoopVersionerGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::lastLoopVersionerGroup, lastLoopVersionerOpts);
   _opts[OMR::methodHandleInvokeInliningGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::methodHandleInvokeInliningGroup, methodHandleInvokeInliningOpts);
   _opts[OMR::earlyGlobalGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::earlyGlobalGroup, earlyGlobalOpts);
   _opts[OMR::earlyLocalGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::earlyLocalGroup, earlyLocalOpts);
   _opts[OMR::stripMiningGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::stripMiningGroup, stripMiningOpts);
   _opts[OMR::arrayPrivatizationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::arrayPrivatizationGroup, arrayPrivatizationOpts);
   _opts[OMR::veryCheapGlobalValuePropagationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::veryCheapGlobalValuePropagationGroup, veryCheapGlobalValuePropagationOpts);
   _opts[OMR::eachExpensiveGlobalValuePropagationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::eachExpensiveGlobalValuePropagationGroup, eachExpensiveGlobalValuePropagationOpts);
   _opts[OMR::veryExpensiveGlobalValuePropagationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::veryExpensiveGlobalValuePropagationGroup, veryExpensiveGlobalValuePropagationOpts);
   _opts[OMR::loopSpecializerGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::loopSpecializerGroup, loopSpecializerOpts);
   _opts[OMR::lateLocalGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::lateLocalGroup, lateLocalOpts);
   _opts[OMR::eachLocalAnalysisPassGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::eachLocalAnalysisPassGroup, eachLocalAnalysisPassOpts);
   _opts[OMR::tacticalGlobalRegisterAllocatorGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::tacticalGlobalRegisterAllocatorGroup, tacticalGlobalRegisterAllocatorOpts);
   _opts[OMR::partialRedundancyEliminationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::partialRedundancyEliminationGroup, partialRedundancyEliminationOpts);
   _opts[OMR::reorderArrayExprGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::reorderArrayExprGroup, reorderArrayIndexOpts);
   _opts[OMR::blockManipulationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::blockManipulationGroup, blockManipulationOpts);
   _opts[OMR::localValuePropagationGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::localValuePropagationGroup, localValuePropagationOpts);
   _opts[OMR::finalGlobalGroup] =
       new (comp->allocator()) TR::OptimizationManager(self(), NULL, OMR::finalGlobalGroup, finalGlobalOpts);

   // NOTE: Please add new OMR optimization groups here!
#endif
}

// Note: optimizer_name array needs to match Optimizations enum defined
// in compiler/optimizer/Optimizations.hpp
static const char *optimizer_name[] =
    {
#define OPTIMIZATION(name) #name,
#define OPTIMIZATION_ENUM_ONLY(entry) "****",
#include "optimizer/Optimizations.enum"
        OPTIMIZATION_ENUM_ONLY(numOpts)
#include "optimizer/OptimizationGroups.enum"
            OPTIMIZATION_ENUM_ONLY(numGroups)
#undef OPTIMIZATION
#undef OPTIMIZATION_ENUM_ONLY
};

const char *
OMR::Optimizer::getOptimizationName(OMR::Optimizations opt)
{
   return ::optimizer_name[opt];
}

bool OMR::Optimizer::isEnabled(OMR::Optimizations i)
{
   if (_opts[i] != NULL)
      return _opts[i]->enabled();
   return false;
}

TR_Debug *OMR::Optimizer::getDebug()
{
   return _compilation->getDebug();
}

void OMR::Optimizer::setCachedExtendedBBInfoValid(bool b)
{
   TR_ASSERT(!comp()->isPeekingMethod(), "ERROR: Should not modify _cachedExtendedBBInfoValid while peeking");
   _cachedExtendedBBInfoValid = b;
}

TR_UseDefInfo *OMR::Optimizer::setUseDefInfo(TR_UseDefInfo *u)
{
   if (_useDefInfo != NULL)
   {
      dumpOptDetails(comp(), "     (Invalidating use/def info)\n");
      delete _useDefInfo;
   }
   return (_useDefInfo = u);
}

TR_ValueNumberInfo *OMR::Optimizer::setValueNumberInfo(TR_ValueNumberInfo *v)
{
   if (_valueNumberInfo && !v)
      dumpOptDetails(comp(), "     (Invalidating value number info)\n");

   if (_valueNumberInfo)
      delete _valueNumberInfo;
   return (_valueNumberInfo = v);
}

TR_UseDefInfo *OMR::Optimizer::createUseDefInfo(TR::Compilation *comp,
                                                bool requiresGlobals, bool prefersGlobals, bool loadsShouldBeDefs, bool cannotOmitTrivialDefs,
                                                bool conversionRegsOnly, bool doCompletion)
{
   return new (comp->allocator()) TR_UseDefInfo(comp, comp->getFlowGraph(), self(), requiresGlobals, prefersGlobals, loadsShouldBeDefs,
                                                cannotOmitTrivialDefs, conversionRegsOnly, doCompletion, getCallsAsUses());
}

TR_ValueNumberInfo *OMR::Optimizer::createValueNumberInfo(bool requiresGlobals, bool preferGlobals, bool noUseDefInfo)
{
   LexicalTimer t("global value numbering (for globals definitely)", comp()->phaseTimer());
   TR::LexicalMemProfiler mp("global value numbering (for globals definitely)", comp()->phaseMemProfiler());

   TR_ValueNumberInfo *valueNumberInfo = NULL;
   switch (_vnInfoType)
   {
   case PrePartitionVN:
      valueNumberInfo = new (comp()->allocator()) TR_ValueNumberInfo(comp(), self(), requiresGlobals, preferGlobals, noUseDefInfo);
      break;
   case HashVN:
      valueNumberInfo = new (comp()->allocator()) TR_HashValueNumberInfo(comp(), self(), requiresGlobals, preferGlobals, noUseDefInfo);
      break;
   default:
      valueNumberInfo = new (comp()->allocator()) TR_ValueNumberInfo(comp(), self(), requiresGlobals, preferGlobals, noUseDefInfo);
      break;
   };

   TR_ASSERT(valueNumberInfo != NULL, "Failed to create ValueNumber Information");
   return valueNumberInfo;
}

void OMR::Optimizer::optimize()
{

   TR::Compilation::CompilationPhaseScope mainCompilationPhaseScope(comp());

   if (isIlGenOpt())
   {
      const OptimizationStrategy *opt = _strategy;
      while (opt->_num != endOpts)
      {
         TR::OptimizationManager *manager = getOptimization(opt->_num);
         TR_ASSERT(manager->getSupportsIlGenOptLevel(), "Optimization %s should support IlGen opt level", manager->name());
         opt++;
      }

      if (comp()->getOption(TR_TraceTrees) && (comp()->isOutermostMethod() || comp()->trace(inlining) || comp()->getOption(TR_DebugInliner)))
         comp()->dumpMethodTrees("Pre IlGenOpt Trees", getMethodSymbol());
   }

   LexicalTimer t("optimize", comp()->signature(), comp()->phaseTimer());
   TR::LexicalMemProfiler mp("optimize", comp()->signature(), comp()->phaseMemProfiler());
   TR::StackMemoryRegion stackMemoryRegion(*trMemory());

   // Sometimes the Compilation object needs to host more than one Optimizer
   // (over time).  This is because Symbol::genIL can be called, for example,
   // (indirectly) by addVeryRefinedCallAliasSets.  Under some circumstances,
   // genIL will instantiate a new Optimizer which must use the caller's
   // Compilation.  So, we need to push and pop the appropriate Optimizer.
   TR::Optimizer *stackedOptimizer = comp()->getOptimizer();
   _stackedOptimizer = (self() != stackedOptimizer);
   comp()->setOptimizer(self());

   if (comp()->getOption(TR_TraceOptDetails))
   {
      if (comp()->isOutermostMethod())
      {
         const char *hotnessString = comp()->getHotnessName(comp()->getMethodHotness());
         TR_ASSERT(hotnessString, "expected to have a hotness string");
         traceMsg(comp(), "<optimize\n"
                          "\tmethod=\"%s\"\n"
                          "\thotness=\"%s\">\n",
                  comp()->signature(), hotnessString);
      }
   }

   if (comp()->getOption(TR_TraceOpts))
   {
      if (comp()->isOutermostMethod())
      {
         const char *hotnessString = comp()->getHotnessName(comp()->getMethodHotness());
         TR_ASSERT(hotnessString, "expected to have a hotness string");
         traceMsg(comp(), "<strategy hotness=\"%s\">\n", hotnessString);
      }
   }

   int32_t firstOptIndex = comp()->getOptions()->getFirstOptIndex();
   int32_t lastOptIndex = comp()->getOptions()->getLastOptIndex();

   _firstDumpOptPhaseTrees = INT_MAX;
   _lastDumpOptPhaseTrees = INT_MAX;

   if (comp()->getOption(TR_TraceOptDetails))
      _firstDumpOptPhaseTrees = 0;

#ifdef DEBUG
   char *p;
   p = debug("dumpOptPhaseTrees");
   if (p)
   {
      _firstDumpOptPhaseTrees = 0;
      if (*p)
      {
         while (*p >= '0' && *p <= '9')
            _firstDumpOptPhaseTrees = _firstDumpOptPhaseTrees * 10 + *(p++) - '0';
         if (*(p++) == '-')
         {
            _lastDumpOptPhaseTrees = 0;
            while (*p >= '0' && *p <= '9')
               _lastDumpOptPhaseTrees = _lastDumpOptPhaseTrees * 10 + *(p++) - '0';
         }
         else
            _lastDumpOptPhaseTrees = _firstDumpOptPhaseTrees;
      }
   }

   static char *c3 = feGetEnv("TR_dumpGraphs");
   if (c3)
   {
      if (!debug("dumpGraphs"))
         addDebug("dumpGraphs");
      // Check if it is a number
      //
      if (*c3 >= '0' && *c3 <= '9')
         _dumpGraphsIndex = atoi(c3);
      else
         _dumpGraphsIndex = -1;
   }
#endif

   TR_SingleTimer myTimer;
   TR_FrontEnd *fe = comp()->fe();
   bool doTiming = comp()->getOption(TR_Timing);
   if (doTiming && comp()->getOutFile() != NULL)
   {
      myTimer.initialize("all optimizations", trMemory());
   }

   if (comp()->getOption(TR_Profile) && !comp()->isProfilingCompilation())
   {
      // These numbers are chosen to try to maximize the odds of finding bugs.
      // freq=2 means we'll switch to and from the profiling body often,
      // thus testing those transitions.
      // The low count value means we will try to recompile the method
      // fairly early, thus testing recomp.
      //
      self()->switchToProfiling(2, 30);
   }

   const OptimizationStrategy *opt = _strategy;
   while (opt->_num != endOpts)
   {
      int32_t actualCost = performOptimization(opt, firstOptIndex, lastOptIndex, doTiming);
      opt++;
      if (!isIlGenOpt() && comp()->getNodePool().removeDeadNodes())
      {
         setValueNumberInfo(NULL);
      }
   }

   if (comp()->getOption(TR_EnableDeterministicOrientedCompilation) &&
       comp()->isOutermostMethod() &&
       (comp()->getMethodHotness() > cold) &&
       (comp()->getMethodHotness() < scorching))
   {
      TR_Hotness nextHotness = checkMaxHotnessOfInlinedMethods(comp());
      if (nextHotness > comp()->getMethodHotness())
      {
         comp()->setNextOptLevel(nextHotness);
         comp()->failCompilation<TR::InsufficientlyAggressiveCompilation>("Method needs to be compiled at higher level");
      }
   }

   dumpPostOptTrees();

   if (comp()->getOption(TR_TraceOpts))
   {
      if (comp()->isOutermostMethod())
         traceMsg(comp(), "</strategy>\n");
   }

   if (comp()->getOption(TR_TraceOptDetails))
   {
      if (comp()->isOutermostMethod())
         traceMsg(comp(), "</optimize>\n");
   }

   comp()->setOptimizer(stackedOptimizer);
   _stackedOptimizer = false;
}

void OMR::Optimizer::dumpPostOptTrees()
{
   // do nothing for IlGen optimizer
   if (isIlGenOpt())
      return;

   TR::Method *method = comp()->getMethodSymbol()->getMethod();
   if ((debug("dumpPostLocalOptTrees") || comp()->getOption(TR_TraceTrees)))
      comp()->dumpMethodTrees("Post Optimization Trees");
}

void dumpName(TR::Optimizer *op, TR_FrontEnd *fe, TR::Compilation *comp, OMR::Optimizations optNum)
{
   static int level = 1;
   TR::OptimizationManager *manager = op->getOptimization(optNum);

   if (level > 6)
      return;

   if (optNum > endGroup && optNum < OMR::numGroups)
   {
      trfprintf(comp->getOutFile(), "%*s<%s>\n", level * 6, " ", manager->name());

      level++;

      const OptimizationStrategy *subGroup = ((TR::OptimizationManager *)manager)->groupOfOpts();

      while (subGroup->_num != endOpts && subGroup->_num != endGroup)
      {
         dumpName(op, fe, comp, subGroup->_num);
         subGroup++;
      }

      level--;

      trfprintf(comp->getOutFile(), "%*s</%s>", level * 6, " ", manager->name());
   }
   else if (optNum > endOpts && optNum < OMR::numOpts)
      trfprintf(comp->getOutFile(), "%*s%s", level * 6, " ", manager->name());
   else
      trfprintf(comp->getOutFile(), "%*s<%d>", level * 6, " ", optNum);

   trfprintf(comp->getOutFile(), "\n");
}

void OMR::Optimizer::dumpStrategy(const OptimizationStrategy *opt)
{
   TR_FrontEnd *fe = comp()->fe();

   trfprintf(comp()->getOutFile(), "endOpts:%d OMR::numOpts:%d endGroup:%d numGroups:%d\n", endOpts, OMR::numOpts, endGroup, OMR::numGroups);

   while (opt->_num != endOpts)
   {
      dumpName(self(), fe, comp(), opt->_num);
      opt++;
   }

   trfprintf(comp()->getOutFile(), "\n");
}

static bool hasMoreThanOneBlock(TR::Compilation *comp)
{
   return (comp->getStartBlock() && comp->getStartBlock()->getNextBlock());
}

static void breakForTesting(int index)
{
   static char *optimizerBreakLocationStr = feGetEnv("TR_optimizerBreakLocation");
   if (optimizerBreakLocationStr)
   {
      static int optimizerBreakLocation = atoi(optimizerBreakLocationStr);
      static char *optimizerBreakSkipCountStr = feGetEnv("TR_optimizerBreakSkipCount");
      static int optimizerBreakSkipCount = optimizerBreakSkipCountStr ? atoi(optimizerBreakSkipCountStr) : 0;
      if (index == optimizerBreakLocation)
      {
         if (optimizerBreakSkipCount == 0)
            TR::Compiler->debug.breakPoint();
         else
            --optimizerBreakSkipCount;
      }
   }
}

int32_t OMR::Optimizer::performOptimization(const OptimizationStrategy *optimization, int32_t firstOptIndex, int32_t lastOptIndex, int32_t doTiming)
{

   // omkar - initialized here
   initEngine(comp());

   OMR::Optimizations optNum = optimization->_num;
   TR::OptimizationManager *manager = getOptimization(optNum);
   TR_ASSERT(manager != NULL, "Optimization manager should have been initialized for %s.",
             getOptimizationName(optNum));

   comp()->reportAnalysisPhase(BEFORE_OPTIMIZATION);
   breakForTesting(1010);

   int32_t optIndex = comp()->getOptIndex() + 1; // +1 because we haven't incremented yet at this point, becuase we're not sure we should
   // Determine whether or not to do this optimization
   //
   bool doThisOptimization = false;
   bool doThisOptimizationIfEnabled = false;
   bool mustBeDone = false;
   bool justSetLastRun = false;
   switch (optimization->_options)
   {
   case Always:
      doThisOptimization = true;
      break;

   case IfLoops:
      if (comp()->mayHaveLoops())
         doThisOptimization = true;
      break;

   case IfMoreThanOneBlock:
      if (hasMoreThanOneBlock(comp()))
         doThisOptimization = true;
      break;

   case IfOneBlock:
      if (!hasMoreThanOneBlock(comp()))
         doThisOptimization = true;
      break;

   case IfLoopsMarkLastRun:
      if (comp()->mayHaveLoops())
         doThisOptimization = true;
      TR_ASSERT(optNum < OMR::numOpts, "No current support for marking groups as last (optNum=%d,numOpt=%d\n", optNum, OMR::numOpts); // make sure we didn't mark groups
      manager->setLastRun(true);
      justSetLastRun = true;
      break;

   case IfNoLoops:
      if (!comp()->mayHaveLoops())
         doThisOptimization = true;
      break;

   case IfProfiling:
      if (comp()->isProfilingCompilation())
         doThisOptimization = true;
      break;

   case IfNotProfiling:
      if (!comp()->isProfilingCompilation() || debug("ignoreIfNotProfiling"))
         doThisOptimization = true;
      break;

   case IfNotJitProfiling:
      if (comp()->getProfilingMode() != JitProfiling)
         doThisOptimization = true;
      break;

   case IfNews:
      if (comp()->hasNews())
         doThisOptimization = true;
      break;

   case IfOptServer:
      if (comp()->isOptServer())
         doThisOptimization = true;
      break;

   case IfMonitors:
      if (comp()->getMethodSymbol()->mayContainMonitors())
         doThisOptimization = true;
      break;

   case IfEnabledAndMonitors:
      if (manager->requested() && comp()->getMethodSymbol()->mayContainMonitors())
         doThisOptimization = true;
      break;

   case IfEnabledAndOptServer:
      if (manager->requested() &&
          comp()->isOptServer())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

#ifdef J9_PROJECT_SPECIFIC
   case IfNotClassLoadPhase:
      if (!comp()->getPersistentInfo()->isClassLoadingPhase() ||
          comp()->getOption(TR_DontDowngradeToCold))
         doThisOptimization = true;
      break;

   case IfNotClassLoadPhaseAndNotProfiling:
      if ((!comp()->getPersistentInfo()->isClassLoadingPhase() ||
           comp()->getOption(TR_DontDowngradeToCold)) &&
          (!comp()->isProfilingCompilation() || debug("ignoreIfNotProfiling")))
         doThisOptimization = true;
      break;
#endif

   case IfEnabledAndLoops:
      if (comp()->mayHaveLoops() && manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfEnabledAndMoreThanOneBlock:
      if (hasMoreThanOneBlock(comp()) && manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfEnabledAndMoreThanOneBlockMarkLastRun:
      if (hasMoreThanOneBlock(comp()) && manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      TR_ASSERT(optNum < OMR::numOpts, "No current support for marking groups as last (optNum=%d,numOpt=%d\n", optNum, OMR::numOpts); // make sure we didn't mark groups
      manager->setLastRun(true);
      justSetLastRun = true;
      break;

   case IfEnabledAndNoLoops:
      if (!comp()->mayHaveLoops() && manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfNoLoopsOREnabledAndLoops:
      if (!comp()->mayHaveLoops() || manager->requested())
      {
         if (comp()->mayHaveLoops())
            doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfEnabledAndProfiling:
      if (comp()->isProfilingCompilation() && manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfEnabledAndNotProfiling:
      if (!comp()->isProfilingCompilation() && manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfEnabledAndNotJitProfiling:
      if (comp()->getProfilingMode() != JitProfiling && manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfLoopsAndNotProfiling:
      if (comp()->mayHaveLoops() && !comp()->isProfilingCompilation())
         doThisOptimization = true;
      break;

   case MustBeDone:
      mustBeDone = doThisOptimization = true;
      break;

   case IfFullInliningUnderOSRDebug:
      if (comp()->getOption(TR_FullSpeedDebug) && comp()->getOption(TR_EnableOSR) && comp()->getOption(TR_FullInlineUnderOSRDebug))
         doThisOptimization = true;
      break;

   case IfNotFullInliningUnderOSRDebug:
      if (comp()->getOption(TR_FullSpeedDebug) && (!comp()->getOption(TR_EnableOSR) || !comp()->getOption(TR_FullInlineUnderOSRDebug)))
         doThisOptimization = true;
      break;

   case IfOSR:
      if (comp()->getOption(TR_EnableOSR))
         doThisOptimization = true;
      break;

   case IfVoluntaryOSR:
      if (comp()->getOption(TR_EnableOSR) && comp()->getOSRMode() == TR::voluntaryOSR)
         doThisOptimization = true;
      break;

   case IfInvoluntaryOSR:
      if (comp()->getOption(TR_EnableOSR) && comp()->getOSRMode() == TR::involuntaryOSR)
         doThisOptimization = true;
      break;

   case IfEnabled:
      if (manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      break;

   case IfEnabledMarkLastRun:
      if (manager->requested())
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
      TR_ASSERT(optNum < OMR::numOpts, "No current support for marking groups as last (optNum=%d,numOpt=%d\n", optNum, OMR::numOpts); // make sure we didn't mark groups
      manager->setLastRun(true);
      justSetLastRun = true;
      break;

   case IfAOTAndEnabled:
   {
      bool enableColdCheapTacticalGRA = comp()->getOption(TR_EnableColdCheapTacticalGRA);
      bool disableAOTColdCheapTacticalGRA = comp()->getOption(TR_DisableAOTColdCheapTacticalGRA);

      if ((comp()->compileRelocatableCode() || enableColdCheapTacticalGRA) && manager->requested() && !disableAOTColdCheapTacticalGRA)
      {
         doThisOptimizationIfEnabled = true;
         doThisOptimization = true;
      }
   }
   break;

   case IfMethodHandleInvokes:
   {
      if (comp()->getMethodSymbol()->hasMethodHandleInvokes() && !comp()->getOption(TR_DisableMethodHandleInvokeOpts))
         doThisOptimization = true;
   }
   break;

   case IfNotQuickStart:
   {
      if (!comp()->getOptions()->isQuickstartDetected())
      {
         doThisOptimization = true;
      }
      break;
   }

   case IfEAOpportunitiesMarkLastRun:
      getOptimization(optNum)->setLastRun(true);
      justSetLastRun = true;
      // fall through
   case IfEAOpportunities:
   case IfEAOpportunitiesAndNotOptServer:
   {
      if (comp()->getMethodSymbol()->hasEscapeAnalysisOpportunities())
      {
         if ((optimization->_options == IfEAOpportunitiesAndNotOptServer) && comp()->isOptServer())
         {
            // don't enable
         }
         else
         {
            doThisOptimization = true;
         }
      }
      break;
   }
   case IfAggressiveLiveness:
   {
      if (comp()->getOption(TR_EnableAggressiveLiveness))
      {
         doThisOptimization = true;
      }
      break;
   }
   case IfVectorAPI:
   {
      if (comp()->getMethodSymbol()->hasVectorAPI() &&
          !comp()->getOption(TR_DisableVectorAPIExpansion))
         doThisOptimization = true;
   }
   break;
   case MarkLastRun:
      doThisOptimization = true;
      TR_ASSERT(optNum < OMR::numOpts, "No current support for marking groups as last (optNum=%d,numOpt=%d\n", optNum, OMR::numOpts); // make sure we didn't mark groups
      manager->setLastRun(true);
      justSetLastRun = true;
      break;
   default:
      TR_ASSERT(0, "unexpection optimization flags");
   }

   if (doThisOptimizationIfEnabled && manager->getRequestedBlocks()->isEmpty())
      doThisOptimization = false;

   int32_t actualCost = 0;
   static int32_t optDepth = 1;

   TR_FrontEnd *fe = comp()->fe();

   // If this is the start of an optimization subGroup, perform the
   // optimizations in the subgroup.
   //
   if (optNum > OMR::numOpts && doThisOptimization)
   {
      if (comp()->getOption(TR_TraceOptDetails) || comp()->getOption(TR_TraceOpts))
      {
         if (comp()->isOutermostMethod())
            traceMsg(comp(), "%*s<optgroup name=%s>\n", optDepth * 3, " ", manager->name());
      }

      optDepth++;

      // Find the subgroup. It is either referenced directly from this
      // optimization or picked up from the table of groups using the
      // optimization number.
      //
      manager->setRequested(false);

      if (optNum == loopVersionerGroup && getOptimization(lastLoopVersionerGroup) != NULL)
         getOptimization(lastLoopVersionerGroup)->setRequested(false);

      const OptimizationStrategy *subGroup = ((TR::OptimizationManager *)manager)->groupOfOpts();
      const OptimizationStrategy *origSubGroup = subGroup;
      int32_t numIters = 0;

      while (1)
      {
         // Perform the optimizations in the subgroup
         //
         while (subGroup->_num != endGroup && subGroup->_num != endOpts)
         {
            actualCost += performOptimization(subGroup, firstOptIndex, lastOptIndex, doTiming);
            subGroup++;
         }

         numIters++;

         if (optNum == eachLocalAnalysisPassGroup)
         {
            const OptimizationStrategy *currSubGroup = subGroup;
            subGroup = origSubGroup;
            bool blocksArePending = false;
            while (subGroup->_num != endGroup && subGroup->_num != endOpts)
            {
               OMR::Optimizations optNum = subGroup->_num;
               if (!manager->getRequestedBlocks()->isEmpty())
               {
                  blocksArePending = true;
                  break;
               }
               subGroup++;
            }

            subGroup = currSubGroup;
            if (!blocksArePending ||
                (numIters >= MAX_LOCAL_OPTS_ITERS))
            {
               break;
            }
            else
               subGroup = origSubGroup;
         }
         else
            break;
      }

      optDepth--;

      if (comp()->getOption(TR_TraceOptDetails) || comp()->getOption(TR_TraceOpts))
      {
         if (comp()->isOutermostMethod())
            traceMsg(comp(), "%*s</optgroup>\n", optDepth * 3, " ");
      }

      return actualCost;
   }

   //
   // This is a real optimization.
   //
   TR::RegionProfiler rp(comp()->trMemory()->heapMemoryRegion(), *comp(), "opt/%s/%s", comp()->getHotnessName(comp()->getMethodHotness()),
                         getOptimizationName(optNum));

   if (comp()->isOutermostMethod())
      comp()->incOptIndex(); // Note that we count the opt even if we're not doing it, to keep the opt indexes more stable

   if (!doThisOptimization)
   {
      if (!manager->requested() &&
          !manager->getRequestedBlocks()->isEmpty())
      {
         TR_ASSERT(0, "Opt is disabled but blocks are still present\n");
      }
      return 0;
   }

   if (mustBeDone ||
       (optIndex >= firstOptIndex && optIndex <= lastOptIndex))
   {
      bool needTreeDump = false;
      bool needStructureDump = false;

      if (!isEnabled(optNum))
         return 0;

      TR::SimpleRegex *regex = comp()->getOptions()->getDisabledOpts();
      if (regex && TR::SimpleRegex::match(regex, optIndex))
         return 0;

      if (regex && TR::SimpleRegex::match(regex, manager->name()))
         return 0;

      // actually doing optimization
      regex = comp()->getOptions()->getBreakOnOpts();
      if (regex && TR::SimpleRegex::match(regex, optIndex))
         TR::Compiler->debug.breakPoint();

      TR::Optimization *opt = manager->factory()(manager);

      // Do any opt specific checks before analysis/opt is run
      if (!opt->shouldPerform())
      {
         delete opt;
         return 0;
      }

      if (comp()->getOption(TR_TraceOptDetails))
      {
         if (comp()->isOutermostMethod())
            getDebug()->printOptimizationHeader(comp()->signature(), manager->name(), optIndex, optimization->_options == MustBeDone);
      }

      if (comp()->getOption(TR_TraceOpts))
      {
         if (comp()->isOutermostMethod())
            traceMsg(comp(), "%*s%s\n", optDepth * 3, " ", manager->name());
      }

      if (!_aliasSetsAreValid && !manager->getDoesNotRequireAliasSets())
      {
         TR::Compilation::CompilationPhaseScope buildingAliases(comp());
         comp()->reportAnalysisPhase(BUILDING_ALIASES);
         breakForTesting(1020);
         dumpOptDetails(comp(), "   (Building alias info)\n");
         comp()->getSymRefTab()->aliasBuilder.createAliasInfo();
         _aliasSetsAreValid = true;
         ++actualCost;
      }
      breakForTesting(1021);

      if (manager->getRequiresUseDefInfo() || manager->getRequiresValueNumbering())
         manager->setRequiresStructure(true);

      if (manager->getRequiresStructure() && !comp()->getFlowGraph()->getStructure())
      {
         TR::Compilation::CompilationPhaseScope buildingStructure(comp());
         comp()->reportAnalysisPhase(BUILDING_STRUCTURE);
         breakForTesting(1030);
         dumpOptDetails(comp(), "   (Doing structural analysis)\n");

#ifdef OPT_TIMING
         TR_SingleTimer myTimer;
         if (doTiming)
         {
            myTimer.initialize("structural analysis", trMemory());
            myTimer.startTiming(comp());
         }
#endif

         actualCost += doStructuralAnalysis();

         if (_firstTimeStructureIsBuilt && comp()->getFlowGraph()->getStructure())
         {
            _firstTimeStructureIsBuilt = false;
            _numLoopsInMethod = 0;
            countNumberOfLoops(comp()->getFlowGraph()->getStructure());
            // dumpOptDetails(comp(), "Number of loops in the cfg = %d\n", _numLoopsInMethod);

            if (!comp()->getOption(TR_ProcessHugeMethods) && (_numLoopsInMethod >= (HIGH_LOOP_COUNT - 25)))
               _disableLoopOptsThatCanCreateLoops = true;
            _numLoopsInMethod = 0;
         }

         needStructureDump = true;

#ifdef OPT_TIMING
         if (doTiming)
         {
            myTimer.stopTiming(comp());
            statStructuralAnalysisTiming.update((double)myTimer.timeTaken() * 1000.0 / TR::Compiler->vm.getHighResClockResolution());
         }
#endif
      }
      breakForTesting(1031);

      if (manager->getStronglyPrefersGlobalsValueNumbering() &&
          getUseDefInfo() && !getUseDefInfo()->hasGlobalsUseDefs() &&
          !cantBuildGlobalsUseDefInfo())
      {
         // We would strongly prefer global usedef info, but we only have
         // local usedef info. We can build global usedef info so force a
         // rebuild.
         //
         setUseDefInfo(NULL);
      }

      if (manager->getDoesNotRequireLoadsAsDefsInUseDefs() &&
          getUseDefInfo() && getUseDefInfo()->hasLoadsAsDefs())
      {
         setUseDefInfo(NULL);
      }

      if (!manager->getDoesNotRequireLoadsAsDefsInUseDefs() &&
          getUseDefInfo() && !getUseDefInfo()->hasLoadsAsDefs())
      {
         setUseDefInfo(NULL);
      }

      TR_UseDefInfo *useDefInfo;
      if (manager->getRequiresGlobalsUseDefInfo() || manager->getRequiresGlobalsValueNumbering())
      {
         // We need global usedef info. If it doesn't exist but can be built,
         // build it.
         //
         if (!cantBuildGlobalsUseDefInfo() &&
             (!getUseDefInfo() || !getUseDefInfo()->hasGlobalsUseDefs()))
         {
            TR::Compilation::CompilationPhaseScope buildingUseDefs(comp());
            comp()->reportAnalysisPhase(BUILDING_USE_DEFS);
            breakForTesting(1040);
#ifdef OPT_TIMING
            TR_SingleTimer myTimer;
            if (doTiming)
            {
               myTimer.initialize("use defs (for globals definitely)", trMemory());
               myTimer.startTiming(comp());
            }
#endif

            LexicalTimer t("use defs (for globals definitely)", comp()->phaseTimer());
            TR::LexicalMemProfiler mp("use defs (for globals definitely)", comp()->phaseMemProfiler());
            useDefInfo = createUseDefInfo(comp(),
                                          true,  // requiresGlobals
                                          false, // prefersGlobals
                                          !manager->getDoesNotRequireLoadsAsDefsInUseDefs(),
                                          manager->getCannotOmitTrivialDefs(),
                                          false, // conversionRegsOnly
                                          true); // doCompletion

#ifdef OPT_TIMING
            if (doTiming)
            {
               myTimer.stopTiming(comp());
               statUseDefsTiming.update((double)myTimer.timeTaken() * 1000.0 / TR::Compiler->vm.getHighResClockResolution());
            }
#endif

            if (useDefInfo->infoIsValid())
            {
               setUseDefInfo(useDefInfo);
            }
            else
               // release storage for failed _useDefInfo
               delete useDefInfo;

            actualCost += 10;
            needTreeDump = true;
         }
      }

      else if (manager->getRequiresUseDefInfo() || manager->getRequiresValueNumbering())
      {
         if (!cantBuildLocalsUseDefInfo() && !getUseDefInfo())
         {
            TR::Compilation::CompilationPhaseScope buildingUseDefs(comp());
            comp()->reportAnalysisPhase(BUILDING_USE_DEFS);
            breakForTesting(1050);
#ifdef OPT_TIMING
            TR_SingleTimer myTimer;
            if (doTiming)
            {
               myTimer.initialize("use defs (for globals possibly)", trMemory());
               myTimer.startTiming(comp());
            }
#endif
            LexicalTimer t("use defs (for globals possibly)", comp()->phaseTimer());
            TR::LexicalMemProfiler mp("use defs (for globals possibly)", comp()->phaseMemProfiler());
            useDefInfo = createUseDefInfo(comp(),
                                          false, // requiresGlobals
                                          manager->getPrefersGlobalsUseDefInfo() || manager->getPrefersGlobalsValueNumbering(),
                                          !manager->getDoesNotRequireLoadsAsDefsInUseDefs(),
                                          manager->getCannotOmitTrivialDefs(),
                                          false, // conversionRegsOnly
                                          true); // doCompletion

#ifdef OPT_TIMING
            if (doTiming)
            {
               myTimer.stopTiming(comp());
               statUseDefsTiming.update((double)myTimer.timeTaken() * 1000.0 / TR::Compiler->vm.getHighResClockResolution());
            }
#endif

            if (useDefInfo->infoIsValid())
            {
               setUseDefInfo(useDefInfo);
            }
            else
               // release storage for failed _useDefInfo
               delete useDefInfo;

            actualCost += 10;
            needTreeDump = true;
         }
      }

      TR_ValueNumberInfo *valueNumberInfo;
      if (manager->getRequiresGlobalsValueNumbering())
      {
         // We need global value number info.
         // If it doesn't exist but can be built, build it.
         //
         if (!cantBuildGlobalsValueNumberInfo() &&
             (!getValueNumberInfo() || !getValueNumberInfo()->hasGlobalsValueNumbers()))
         {
            TR::Compilation::CompilationPhaseScope buildingValueNumbers(comp());
            comp()->reportAnalysisPhase(BUILDING_VALUE_NUMBERS);
            breakForTesting(1060);
#ifdef OPT_TIMING
            TR_SingleTimer myTimer;
            if (doTiming)
            {
               myTimer.initialize("global value numbering (for globals definitely)", trMemory());
               myTimer.startTiming(comp());
            }
#endif

            valueNumberInfo = createValueNumberInfo(true, false);

#ifdef OPT_TIMING
            if (doTiming)
            {
               myTimer.stopTiming(comp());
               statGlobalValNumTiming.update((double)myTimer.timeTaken() * 1000.0 / TR::Compiler->vm.getHighResClockResolution());
            }
#endif

            if (valueNumberInfo->infoIsValid())
               setValueNumberInfo(valueNumberInfo);
            actualCost += 10;
            needTreeDump = true;
         }
      }

      else if (manager->getRequiresValueNumbering())
      {
         if (!cantBuildLocalsValueNumberInfo() && !getValueNumberInfo())
         {
            TR::Compilation::CompilationPhaseScope buildingValueNumbers(comp());
            comp()->reportAnalysisPhase(BUILDING_VALUE_NUMBERS);
            breakForTesting(1070);
#ifdef OPT_TIMING
            TR_SingleTimer myTimer;
            if (doTiming)
            {
               myTimer.initialize("global value numbering (for globals possibly)", trMemory());
               myTimer.startTiming(comp());
            }
#endif

            valueNumberInfo = createValueNumberInfo(false, manager->getPrefersGlobalsValueNumbering());

#ifdef OPT_TIMING
            if (doTiming)
            {
               myTimer.stopTiming(comp());
               statGlobalValNumTiming.update((double)myTimer.timeTaken() * 1000.0 / TR::Compiler->vm.getHighResClockResolution());
            }
#endif
            if (valueNumberInfo->infoIsValid())
               setValueNumberInfo(valueNumberInfo);
            actualCost += 10;
            needTreeDump = true;
         }
      }

      if (manager->getRequiresAccurateNodeCount())
      {
         TR::Compilation::CompilationPhaseScope buildingAccurateNodeCount(comp());
         comp()->reportAnalysisPhase(BUILDING_ACCURATE_NODE_COUNT);
         breakForTesting(1080);
         comp()->generateAccurateNodeCount();
      }

      // dumpOptDetails(comp(), "\n");

#ifdef OPT_TIMING
      if (*(statOptTiming[optNum].getName()) == 0) // has no name yet
         statOptTiming[optNum].setName(manager->name());
#endif

#ifdef OPT_TIMING
      TR_SingleTimer myTimer;
      if (doTiming)
      {
         myTimer.initialize(manager->name(), trMemory());
         myTimer.startTiming(comp());
      }
#endif
      LexicalTimer t(manager->name(), comp()->phaseTimer());
      TR::LexicalMemProfiler mp(manager->name(), comp()->phaseMemProfiler());

      int32_t origSymRefCount = comp()->getSymRefCount();
      int32_t origNodeCount = comp()->getNodeCount();
      int32_t origCfgNodeCount = comp()->getFlowGraph()->getNextNodeNumber();
      int32_t origOptMsgIndex = self()->getOptMessageIndex();

      if (comp()->isOutermostMethod() && (comp()->getFlowGraph()->getMaxFrequency() < 0) && !manager->getDoNotSetFrequencies())
      {
         TR::Compilation::CompilationPhaseScope buildingFrequencies(comp());
         comp()->reportAnalysisPhase(BUILDING_FREQUENCIES);
         breakForTesting(1100);
         comp()->getFlowGraph()->setFrequencies();
      }

      bool origTraceSetting = manager->trace();

      regex = comp()->getOptions()->getOptsToTrace();
      if (regex && TR::SimpleRegex::match(regex, optIndex))
         manager->setTrace(true);

      if (doThisOptimizationIfEnabled)
         manager->setPerformOnlyOnEnabledBlocks(true);

      // check if method exceeds loop or basic block threshold
      if (manager->getRequiresStructure() && comp()->getFlowGraph()->getStructure())
      {
         if (checkNumberOfLoopsAndBasicBlocks(comp(), comp()->getFlowGraph()->getStructure()))
         {
            if (comp()->getOption(TR_ProcessHugeMethods))
            {
               dumpOptDetails(comp(), "Method is normally too large (%d blocks and %d loops) but limits overridden\n", _numBasicBlocksInMethod, _numLoopsInMethod);
            }
            else
            {
               if (comp()->getOption(TR_MimicInterpreterFrameShape))
               {
                  comp()->failCompilation<TR::ExcessiveComplexity>("complex method under MimicInterpreterFrameShape");
               }
               else
               {
                  comp()->failCompilation<TR::ExcessiveComplexity>("Method is too large");
               }
            }
         }
      }

      comp()->reportOptimizationPhase(optNum);
      breakForTesting(optNum);
      if (!doThisOptimizationIfEnabled ||
          manager->getRequestedBlocks()->find(toBlock(comp()->getFlowGraph()->getStart())) ||
          manager->getRequestedBlocks()->find(toBlock(comp()->getFlowGraph()->getEnd())))
      {

         TR_ASSERT((justSetLastRun || !manager->getLastRun()), "%s shouldn't be run after LastRun was set\n", manager->name());

         manager->setRequested(false);

         comp()->recordBegunOpt();
         if (comp()->getOption(TR_TraceLastOpt) && comp()->getOptIndex() == comp()->getOptions()->getLastOptIndex())
         {
            comp()->getOptions()->enableTracing(optNum);
            manager->setTrace(true);
         }

         comp()->reportAnalysisPhase(PERFORMING_OPTIMIZATION);

         {
            TR::StackMemoryRegion stackMemoryRegion(*trMemory());
            opt->prePerform();
            actualCost += opt->perform();
            opt->postPerform();
         }

         comp()->reportAnalysisPhase(AFTER_OPTIMIZATION);
      }
      else if (canRunBlockByBlockOptimizations())
      {
         TR::StackMemoryRegion stackMemoryRegion(*trMemory());

         opt->prePerformOnBlocks();
         ListIterator<TR::Block> blockIt(manager->getRequestedBlocks());
         manager->setRequested(false);
         manager->setPerformOnlyOnEnabledBlocks(false);
         for (TR::Block *block = blockIt.getFirst(); block != NULL; block = blockIt.getNext())
         {
            // if (!comp()->getFlowGraph()->getRemovedNodes().find(block))
            if (!block->nodeIsRemoved())
            {
               block = block->startOfExtendedBlock();
               TR_ASSERT((justSetLastRun || !manager->getLastRun()), "opt %d shouldn't be run after LastRun was set for this optimization\n", optNum);
               actualCost += opt->performOnBlock(block);
            }
         }
         opt->postPerformOnBlocks();
      }

      delete opt;
      // we cannot easily invalidate during IL gen since we could be peeking and we cannot destroy our
      // caller's alias sets
      if (!isIlGenOpt())
         comp()->invalidateAliasRegion();
      breakForTesting(-optNum);

      if (comp()->compilationShouldBeInterrupted((TR_CallingContext)optNum))
      {
         comp()->failCompilation<TR::CompilationInterrupted>("interrupted between optimizations");
      }

      manager->setTrace(origTraceSetting);

      int32_t finalOptMsgIndex = self()->getOptMessageIndex();
      if ((finalOptMsgIndex != origOptMsgIndex) && !manager->getDoesNotRequireTreeDumps())
         comp()->reportOptimizationPhaseForSnap(optNum);

      if (comp()->getNodeCount() > unsigned(origNodeCount))
      {
         // If nodes were added, invalidate
         //
         setValueNumberInfo(NULL);
         if (!manager->getMaintainsUseDefInfo())
            setUseDefInfo(NULL);
      }

      if ((comp()->getSymRefCount() != origSymRefCount) /* || manager->getCanAddSymbolReference()*/)
      {
         setSymReferencesTable(NULL);
         // invalidate any alias sets so that they are rebuilt
         // by the next optimization that needs them
         //
         setAliasSetsAreValid(false);
      }

      if (comp()->getVisitCount() > HIGH_VISIT_COUNT)
      {
         comp()->resetVisitCounts(1);
         dumpOptDetails(comp(), "\nResetting visit counts for this method after %s\n", manager->name());
      }

      if (comp()->getFlowGraph()->getMightHaveUnreachableBlocks())
         comp()->getFlowGraph()->removeUnreachableBlocks();

#ifdef OPT_TIMING
      if (doTiming)
      {
         myTimer.stopTiming(comp());
         statOptTiming[optNum].update((double)myTimer.timeTaken() * 1000.0 / TR::Compiler->vm.getHighResClockResolution());
      }
#endif

#ifdef DEBUG
      if (manager->getDumpStructure() && debug("dumpStructure"))
      {
         traceMsg(comp(), "\nStructures:\n");
         getDebug()->print(comp()->getOutFile(), comp()->getFlowGraph()->getStructure(), 6);
      }

#endif

      if ((optIndex >= _firstDumpOptPhaseTrees && optIndex <= _lastDumpOptPhaseTrees) &&
          comp()->isOutermostMethod())
      {
         if (manager->getDoesNotRequireTreeDumps())
         {
            dumpOptDetails(comp(), "Trivial opt -- omitting lisitings\n");
         }
         else if (needTreeDump || (finalOptMsgIndex != origOptMsgIndex))
            comp()->dumpMethodTrees("Trees after ", manager->name(), getMethodSymbol());
         else if (finalOptMsgIndex == origOptMsgIndex)
         {
            dumpOptDetails(comp(), "No transformations done by this pass -- omitting listings\n");
            if (needStructureDump && comp()->getDebug() && comp()->getFlowGraph()->getStructure())
            {
               comp()->getDebug()->print(comp()->getOutFile(), comp()->getFlowGraph()->getStructure(), 6);
            }
         }
      }

#ifdef DEBUG
      if (debug("dumpGraphs") &&
          (_dumpGraphsIndex == -1 || _dumpGraphsIndex == optIndex))
         comp()->dumpMethodGraph(optIndex);
#endif

      manager->performChecks();

      static const bool enableCountTemps = feGetEnv("TR_EnableCountTemps") != NULL;
      if (enableCountTemps)
      {
         int32_t tempCount = 0;

         traceMsg(comp(), "Temps seen (if any): ");

         for (TR::TreeTop *tt = getMethodSymbol()->getFirstTreeTop(); tt; tt = tt->getNextTreeTop())
         {
            TR::Node *ttNode = tt->getNode();

            if (ttNode->getOpCodeValue() == TR::treetop)
            {
               ttNode = ttNode->getFirstChild();
            }

            if (ttNode->getOpCode().isStore() && ttNode->getOpCode().hasSymbolReference())
            {
               TR::SymbolReference *symRef = ttNode->getSymbolReference();

               if ((symRef->getSymbol()->getKind() == TR::Symbol::IsAutomatic) &&
                   symRef->isTemporary(comp()))
               {
                  ++tempCount;
                  traceMsg(comp(), "%s ", comp()->getDebug()->getName(ttNode->getSymbolReference()));
               }
            }
         }

         traceMsg(comp(), "\nNumber of temps seen = %d\n", tempCount);
      }

      if (comp()->getOption(TR_TraceOptDetails))
      {
         if (comp()->isOutermostMethod())
            traceMsg(comp(), "</optimization>\n\n");
      }
   }

   return actualCost;
}

void OMR::Optimizer::enableAllLocalOpts()
{
   setRequestOptimization(lateLocalGroup, true);
   setRequestOptimization(localCSE, true);
   setRequestOptimization(localValuePropagationGroup, true);
   setRequestOptimization(treeSimplification, true);
   setRequestOptimization(localDeadStoreElimination, true);
   setRequestOptimization(deadTreesElimination, true);
   setRequestOptimization(catchBlockRemoval, true);
   setRequestOptimization(compactNullChecks, true);
   setRequestOptimization(localReordering, true);
   setRequestOptimization(andSimplification, true);
   setRequestOptimization(redundantGotoElimination, true);
}

int32_t OMR::Optimizer::doStructuralAnalysis()
{

   // Only perform structural analysis if there may be loops in the method
   //
   // TEMPORARY HACK - always do structural analysis
   //
   TR_Structure *rootStructure = NULL;
   /////if (comp()->mayHaveLoops())
   {
      LexicalTimer t("StructuralAnalysis", comp()->phaseTimer());
      rootStructure = TR_RegionAnalysis::getRegions(comp());
      comp()->getFlowGraph()->setStructure(rootStructure);

      if (debug("dumpStructure"))
      {
         traceMsg(comp(), "\nStructures:\n");
         getDebug()->print(comp()->getOutFile(), rootStructure, 6);
      }
   }

   return 10;
}

int32_t OMR::Optimizer::changeContinueLoopsToNestedLoops()
{
   TR_RegionStructure *rootStructure = comp()->getFlowGraph()->getStructure()->asRegion();
   if (rootStructure && rootStructure->changeContinueLoopsToNestedLoops(rootStructure))
   {
      comp()->getFlowGraph()->setStructure(NULL);
      doStructuralAnalysis();
   }

   return 10;
}

bool OMR::Optimizer::prepareForNodeRemoval(TR::Node *node, bool deferInvalidatingUseDefInfo)
{
   int32_t index;

   TR_UseDefInfo *udInfo = getUseDefInfo();
   bool useDefInfoAreInvalid = false;
   if (udInfo)
   {
      index = node->getUseDefIndex();
      if (udInfo->isUseIndex(index))
      {
         // udInfo->setUseDefInfoToNull(index);
         udInfo->resetDefUseInfo();

         // If the node is both a use and a def we can't repair the info, since
         // it is a def to other uses that we don't know about (it's an unresolved
         // load, which acts like a call def node).
         //
         if (udInfo->isDefIndex(index))
         {
            if (!deferInvalidatingUseDefInfo)
               setUseDefInfo(NULL);
            useDefInfoAreInvalid = true;
         }
      }
      node->setUseDefIndex(0);
   }

   TR_ValueNumberInfo *vnInfo = getValueNumberInfo();
   if (vnInfo)
   {
      vnInfo->removeNodeInfo(node);
   }

   for (int32_t i = node->getNumChildren() - 1; i >= 0; i--)
   {
      TR::Node *child = node->getChild(i);
      if (child != NULL && child->getReferenceCount() == 1)
         if (prepareForNodeRemoval(child))
            useDefInfoAreInvalid = true;
   }
   return useDefInfoAreInvalid;
}

void OMR::Optimizer::getStaticFrequency(TR::Block *block, int32_t *currentWeight)
{
   if (comp()->getUsesBlockFrequencyInGRA())
      *currentWeight = block->getFrequency();
   else
      block->getStructureOf()->calculateFrequencyOfExecution(currentWeight);
}

TR_Hotness OMR::Optimizer::checkMaxHotnessOfInlinedMethods(TR::Compilation *comp)
{
   TR_Hotness strategy = comp->getMethodHotness();
#ifdef J9_PROJECT_SPECIFIC
   if (comp->getNumInlinedCallSites() > 0)
   {
      for (uint32_t i = 0; i < comp->getNumInlinedCallSites(); ++i)
      {
         TR_InlinedCallSite &ics = comp->getInlinedCallSite(i);
         TR_OpaqueMethodBlock *method = comp->fe()->getInlinedCallSiteMethod(&ics);
         if (TR::Compiler->mtd.isCompiledMethod(method))
         {
            TR_PersistentJittedBodyInfo *bodyInfo = TR::Recompilation::getJittedBodyInfoFromPC((void *)TR::Compiler->mtd.startPC(method));
            if (bodyInfo &&
                bodyInfo->getHotness() > strategy)
            {
               strategy = bodyInfo->getHotness();
            }
            else if (!bodyInfo && TR::Options::getCmdLineOptions()->allowRecompilation()) // don't do it for fixed level
            {
               strategy = scorching;
               break;
            }
         }
      }
   }
#endif
   return strategy;
}

bool OMR::Optimizer::checkNumberOfLoopsAndBasicBlocks(TR::Compilation *comp, TR_Structure *rootStructure)
{
   TR::CFGNode *node;
   _numBasicBlocksInMethod = 0;
   for (node = comp->getFlowGraph()->getFirstNode(); node; node = node->getNext())
   {
      _numBasicBlocksInMethod++;
   }

   // dumpOptDetails(comp(), "Number of nodes in the cfg = %d\n", _numBasicBlocksInMethod);

   _numLoopsInMethod = 0;
   countNumberOfLoops(rootStructure);
   // dumpOptDetails(comp(), "Number of loops in the cfg = %d\n", _numLoopsInMethod);

   int32_t highBasicBlockCount = HIGH_BASIC_BLOCK_COUNT;
   int32_t highLoopCount = HIGH_LOOP_COUNT;
   // set loop count thershold to a higher value for now
   // TODO: find a better way to fix this by creating a check
   // about _disableLoopOptsThatCanCreateLoops
   if (comp->getMethodHotness() >= veryHot)
      highLoopCount = VERY_HOT_HIGH_LOOP_COUNT;
   if (comp->isOptServer())
   {
      highBasicBlockCount = highBasicBlockCount * 2;
      highLoopCount = highLoopCount * 2;
   }

   if ((_numBasicBlocksInMethod >= highBasicBlockCount) ||
       (_numLoopsInMethod >= highLoopCount))
   {
      return true;
   }
   return false;
}

void OMR::Optimizer::countNumberOfLoops(TR_Structure *rootStructure)
{
   TR_RegionStructure *regionStructure = rootStructure->asRegion();
   if (regionStructure)
   {
      if (regionStructure->isNaturalLoop())
         _numLoopsInMethod++;
      TR_StructureSubGraphNode *node;
      TR_RegionStructure::Cursor si(*regionStructure);
      for (node = si.getFirst(); node; node = si.getNext())
         countNumberOfLoops(node->getStructure());
   }
}

bool OMR::Optimizer::areNodesEquivalent(TR::Node *node1, TR::Node *node2, TR::Compilation *_comp, bool allowBCDSignPromotion)
{
   // WCodeLinkageFixup runs a version of LocalCSE that is not owned by
   // an optimizer, so it has to pass in a TR_Compilation

   if (node1 == node2)
      return true;

   if (!(node1->getOpCodeValue() == node2->getOpCodeValue()))
      return false;

   TR::ILOpCode &opCode1 = node1->getOpCode();
   if (opCode1.isSwitch() == 0)
   {
      if (opCode1.hasSymbolReference())
      {
         if (node1->getSymbolReference()->getReferenceNumber() != node2->getSymbolReference()->getReferenceNumber())
         {
            return false;
         }
         else if ((opCode1.isCall() && !node1->isPureCall()) ||
                  opCode1.isStore() ||
                  opCode1.getOpCodeValue() == TR::New ||
                  opCode1.getOpCodeValue() == TR::newarray ||
                  opCode1.getOpCodeValue() == TR::anewarray ||
                  opCode1.getOpCodeValue() == TR::multianewarray ||
                  opCode1.getOpCodeValue() == TR::monent ||
                  opCode1.getOpCodeValue() == TR::monexit)
         {
            if (!(node1 == node2))
               return false;
         }
      }
      else if (opCode1.isBranch())
      {
         if (!(node1->getBranchDestination()->getNode() == node2->getBranchDestination()->getNode()))
            return false;
      }

#ifdef J9_PROJECT_SPECIFIC
      if (node1->getOpCode().isSetSignOnNode() && node1->getSetSign() != node2->getSetSign())
         return false;
#endif

      if (opCode1.isLoadConst())
      {
         switch (node1->getDataType())
         {
         case TR::Int8:
            if (node1->getByte() != node2->getByte())
               return false;
            break;
         case TR::Int16:
            if (node1->getShortInt() != node2->getShortInt())
               return false;
            break;
         case TR::Int32:
            if (node1->getInt() != node2->getInt())
               return false;
            break;
         case TR::Int64:
            if (node1->getLongInt() != node2->getLongInt())
               return false;
            break;
         case TR::Float:
            if (node1->getFloatBits() != node2->getFloatBits())
               return false;
            break;
         case TR::Double:
            if (node1->getDoubleBits() != node2->getDoubleBits())
               return false;
            break;
         case TR::Address:
            if (node1->getAddress() != node2->getAddress())
               return false;
            break;
#ifdef J9_PROJECT_SPECIFIC
         case TR::Aggregate:
            if (!areBCDAggrConstantNodesEquivalent(node1, node2, _comp))
            {
               return false;
            }
#endif
            break;
         default:
         {
            if (node1->getDataType().isVector())
            {
               if (node1->getLiteralPoolOffset() != node2->getLiteralPoolOffset())
                  return false;
               break;
            }
#ifdef J9_PROJECT_SPECIFIC
            if (node1->getDataType().isBCD())
            {
               if (!areBCDAggrConstantNodesEquivalent(node1, node2, _comp))
                  return false;
            }
#endif
         }
         }
      }
      else if (opCode1.isArrayLength())
      {
         if (node1->getArrayStride() != node2->getArrayStride())
            return false;
      }
#ifdef J9_PROJECT_SPECIFIC
      else if (node1->getType().isBCD())
      {
         if (node1->isDecimalSizeAndShapeEquivalent(node2))
         {
            // LocalAnalysis temporarily changes store opcodes to load opcodes to enable matching up loads/stores
            // However since sign state is not tracked (and is not relevant) for stores this causes the equivalence
            // test to unnecessarily fail. The isBCDStoreTemporarilyALoad flag allow skipping of the sign state compare
            // for these cases.
            if (!(node1->getOpCode().isLoadVar() && node1->isBCDStoreTemporarilyALoad()) &&
                !(node2->getOpCode().isLoadVar() && node2->isBCDStoreTemporarilyALoad()) &&
                !node1->isSignStateEquivalent(node2))
            {
               if (allowBCDSignPromotion && node1->isSignStateAnImprovementOver(node2))
               {
                  if (_comp->cg()->traceBCDCodeGen())
                     traceMsg(_comp, "y^y : found sign state mismatch node1 %s (%p), node2 %s (%p) but node1 improves sign state over node2\n",
                              node1->getOpCode().getName(), node1, node2->getOpCode().getName(), node2);
                  return true;
               }
               else
               {
                  if (_comp->cg()->traceBCDCodeGen())
                     traceMsg(_comp, "x^x : found sign state mismatch node1 %s (%p), node2 %s (%p)\n",
                              node1->getOpCode().getName(), node1, node2->getOpCode().getName(), node2);
                  return false;
               }
            }
         }
         else
         {
            return false;
         }
      }
      else if (opCode1.isConversionWithFraction() &&
               node1->getDecimalFraction() != node2->getDecimalFraction())
      {
         return false;
      }
      else if (node1->chkOpsCastedToBCD() &&
               node1->castedToBCD() != node2->castedToBCD())
      {
         return false;
      }
      else if (opCode1.getOpCodeValue() == TR::loadaddr &&
               (node1->getSymbolReference()->isTempVariableSizeSymRef() && node2->getSymbolReference()->isTempVariableSizeSymRef()) &&
               (node1->getDecimalPrecision() != node2->getDecimalPrecision()))
      {
         return false;
      }
#endif
      else if (opCode1.isArrayRef())
      {
         // for some reason this tests hasPinningArrayPointer only when the node also is true on _flags.testAny(internalPointer)
         bool haveIPs = node1->isInternalPointer() && node2->isInternalPointer();
         bool haveNoIPs = !node1->isInternalPointer() && !node2->isInternalPointer();
         TR::AutomaticSymbol *pinning1 = node1->getOpCode().hasPinningArrayPointer() ? node1->getPinningArrayPointer() : NULL;
         TR::AutomaticSymbol *pinning2 = node2->getOpCode().hasPinningArrayPointer() ? node2->getPinningArrayPointer() : NULL;
         if ((haveIPs && (pinning1 == pinning2)) || haveNoIPs)
            return true;
         else
            return false;
      }
      else if (opCode1.getOpCodeValue() == TR::PassThrough)
      {
         return false;
      }
      else if (opCode1.isLoadReg())
      {
         if (!node2->getOpCode().isLoadReg())
         {
            return false;
         }

         if (node1->getGlobalRegisterNumber() != node2->getGlobalRegisterNumber())
         {
            return false;
         }
      } // IvanB
   }
   else
   {
      if (!(areNodesEquivalent(node1->getFirstChild(), node2->getFirstChild(), _comp)))
         return false;

      if (!(node1->getSecondChild()->getBranchDestination()->getNode() == node2->getSecondChild()->getBranchDestination()->getNode()))
         return false;

      if (opCode1.getOpCodeValue() == TR::lookup)
      {
         for (int i = node1->getCaseIndexUpperBound() - 1; i > 1; i--)
         {
            if (!(node1->getChild(i)->getBranchDestination()->getNode() == node2->getChild(i)->getBranchDestination()->getNode()))
               return false;
         }
      }
      else if (opCode1.getOpCodeValue() == TR::table)
      {
         for (int i = node1->getCaseIndexUpperBound() - 1; i > 1; i--)
         {
            if (!(node1->getChild(i)->getBranchDestination()->getNode() == node2->getChild(i)->getBranchDestination()->getNode()))
               return false;
         }
      }
   }

   return true;
}

#ifdef J9_PROJECT_SPECIFIC
bool OMR::Optimizer::areBCDAggrConstantNodesEquivalent(TR::Node *node1, TR::Node *node2, TR::Compilation *_comp)
{
   size_t size1 = (node1->getDataType().isBCD()) ? node1->getDecimalPrecision() : 0;
   size_t size2 = (node2->getDataType().isBCD()) ? node2->getDecimalPrecision() : 0;

   if (size1 != size2)
   {
      return false;
   }
   if (node1->getNumChildren() == 1 && node2->getNumChildren() == 1 && // if neither is a delayed literal,
       node1->getLiteralPoolOffset() != node2->getLiteralPoolOffset()) // compare their offsets in the literal pool.
   {
      return false;
   }
   return true;
}
#endif

bool OMR::Optimizer::areSyntacticallyEquivalent(TR::Node *node1, TR::Node *node2, vcount_t visitCount)
{
   if (node1->getVisitCount() == visitCount)
   {
      if (node2->getVisitCount() == visitCount)
         return true;
      else
         return false;
   }

   if (node2->getVisitCount() == visitCount)
   {
      if (node1->getVisitCount() == visitCount)
         return true;
      else
         return false;
   }

   bool equivalent = true;
   if (!areNodesEquivalent(node1, node2))
      equivalent = false;

   if (node1->getNumChildren() != node2->getNumChildren())
      equivalent = false;

   if (equivalent)
   {
      int32_t numChildren = node1->getNumChildren();
      int32_t i;
      for (i = numChildren - 1; i >= 0; i--)
      {
         TR::Node *child1 = node1->getChild(i);
         TR::Node *child2 = node2->getChild(i);

         if (!areSyntacticallyEquivalent(child1, child2, visitCount))
         {
            equivalent = false;
            break;
         }
      }
   }

   return equivalent;
}

/**
 * Build the table of corresponding symbol references for use by optimizations.
 * This table allows a fast determination of whether two symbol references
 * represent the same symbol.
 */
int32_t *OMR::Optimizer::getSymReferencesTable()
{
   if (_symReferencesTable == NULL)
   {
      int32_t symRefCount = comp()->getSymRefCount();
      _symReferencesTable = (int32_t *)trMemory()->allocateStackMemory(symRefCount * sizeof(int32_t));
      memset(_symReferencesTable, 0, symRefCount * sizeof(int32_t));
      TR::SymbolReferenceTable *symRefTab = comp()->getSymRefTab();
      for (int32_t symRefNumber = 0; symRefNumber < symRefCount; symRefNumber++)
      {
         bool newSymbol = true;
         if (symRefNumber >= comp()->getSymRefTab()->getIndexOfFirstSymRef())
         {
            TR::SymbolReference *symRef = symRefTab->getSymRef(symRefNumber);
            TR::Symbol *symbol = symRef ? symRef->getSymbol() : 0;
            if (symbol)
            {
               for (int32_t i = comp()->getSymRefTab()->getIndexOfFirstSymRef(); i < symRefNumber; ++i)
               {
                  if (_symReferencesTable[i] == i)
                  {
                     TR::SymbolReference *otherSymRef = symRefTab->getSymRef(i);
                     TR::Symbol *otherSymbol = otherSymRef ? otherSymRef->getSymbol() : 0;
                     if (otherSymbol && symbol == otherSymbol && symRef->getOffset() == otherSymRef->getOffset())
                     {
                        newSymbol = false;
                        _symReferencesTable[symRefNumber] = i;
                        break;
                     }
                  }
               }
            }
         }

         if (newSymbol)
            _symReferencesTable[symRefNumber] = symRefNumber;
      }
   }
   return _symReferencesTable;
}

#ifdef DEBUG
void OMR::Optimizer::doStructureChecks()
{
   TR::CFG *cfg = getMethodSymbol()->getFlowGraph();
   if (cfg)
   {
      TR_Structure *rootStructure = cfg->getStructure();
      if (rootStructure)
      {
         TR::StackMemoryRegion stackMemoryRegion(*trMemory());

         // Allocate bit vector of block numbers that have been seen
         //
         TR_BitVector blockNumbers(cfg->getNextNodeNumber(), comp()->trMemory(), stackAlloc);
         rootStructure->checkStructure(&blockNumbers);
      }
   }
}
#endif

bool OMR::Optimizer::getLastRun(OMR::Optimizations opt)
{
   if (!_opts[opt])
      return false;
   return _opts[opt]->getLastRun();
}

void OMR::Optimizer::setRequestOptimization(OMR::Optimizations opt, bool value, TR::Block *block)
{
   if (_opts[opt])
      _opts[opt]->setRequested(value, block);
}

void OMR::Optimizer::setAliasSetsAreValid(bool b, bool setForWCode)
{
   if (_aliasSetsAreValid && !b)
      dumpOptDetails(comp(), "     (Invalidating alias info)\n");

   _aliasSetsAreValid = b;
}

const OptimizationStrategy *OMR::Optimizer::_mockStrategy = NULL;

const OptimizationStrategy *
OMR::Optimizer::optimizationStrategy(TR::Compilation *c)
{
   // Mock strategies are used for testing, and override
   // the compilation strategy.
   if (NULL != OMR::Optimizer::_mockStrategy)
   {
      traceMsg(c, "Using mock optimization strategy %p\n", OMR::Optimizer::_mockStrategy);
      return OMR::Optimizer::_mockStrategy;
   }

   TR_Hotness strategy = c->getMethodHotness();
   TR_ASSERT(strategy <= lastOMRStrategy, "Invalid optimization strategy");

   // Downgrade strategy rather than crashing in prod.
   if (strategy > lastOMRStrategy)
      strategy = lastOMRStrategy;

   return omrCompilationStrategies[strategy];
}

ValueNumberInfoBuildType
OMR::Optimizer::valueNumberInfoBuildType()
{
   return PrePartitionVN;
}

TR::Optimizer *OMR::Optimizer::self()
{
   return (static_cast<TR::Optimizer *>(this));
}

OMR_InlinerPolicy *OMR::Optimizer::getInlinerPolicy()
{
   return new (comp()->allocator()) OMR_InlinerPolicy(comp());
}

OMR_InlinerUtil *OMR::Optimizer::getInlinerUtil()
{
   return new (comp()->allocator()) OMR_InlinerUtil(comp());
}

// ************************ PRIMARY METHODS DEFN START (PMS) ****************************************

void initEngine(TR::Compilation *comp)
{
   // temporarily commenting !exhaustive //todo - omkar -uncomment this
   if (!exhaustive && _methodIndices.empty())
   {
      _methodIndices = readMethodIndices();
      for (auto it : _methodIndices)
      {
         inverse_methodIndices[it.second] = it.first;
      }
   }

   if (_classIndices.empty())
   {
      _classIndices = readClassIndices();
   }

   if (!PointsToGraph::defaultEntriesInit)
   {
      PointsToGraph::defaultEntriesInit = true;
      PointsToGraph::initializeEntries();
   }

   if (!exhaustive && _indexPTG.empty())
   {
      _indexPTG = readPTG("ptg2.txt");
   }

   if (!_threadStartPersistentId)
   {
      // fetch method ptr for the thread.start method
      int len = strlen("java/lang/Thread");
      TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature("java/lang/Thread", len, comp->getCurrentMethod());
      TR_ASSERT_FATAL(type, "unable to get class pointer for receiver %s", "java/lang/Thread");
      TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, type, "start", "()V");
      TR_ASSERT_FATAL(targetMethod, "unable to find method for name and signature %s %s", "start", "()V");
      TR::ResolvedMethodSymbol *targetMethodSymbol = targetMethod->findOrCreateJittedMethodSymbol(comp);
      TR_ASSERT_FATAL(targetMethodSymbol, "unable to find method for name and signature %s %s", "start", "()V");
      _threadStartPersistentId = targetMethod->getPersistentIdentifier();
   }

   if (CHA.size() == 0)
   {
      constructCHA(comp);
   }

   benchmarkBuildIndependentSet(comp);
}

void benchmarkBuildIndependentSet(TR::Compilation *comp)
{

   static std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> methodDict;

   TR_OpaqueMethodBlock *methodPersistentId = comp->getMethodSymbol()->getResolvedMethod()->getPersistentIdentifier();
   if (_methodsAnalyzed.find(methodPersistentId) == _methodsAnalyzed.end())
   {
      _methodsBeingAnalyzed.insert(methodPersistentId);

      computeMSetForMethod(comp, comp->getMethodSymbol(), methodDict);

      // std::cout<<"method mset = "<<((std::string)(comp->getMethodSymbol()->getResolvedMethod()->nameChars())).substr(0, comp->getMethodSymbol()->getResolvedMethod()->nameLength())<<"\n";

      _methodsBeingAnalyzed.erase(methodPersistentId);
      _methodsAnalyzed.insert(methodPersistentId);

      if (_methodsBeingAnalyzed.empty())
      {
         if (exhaustive)
         {

            // TODO - omkar - check this

            performExhaustivePTA(comp, methodDict);
            printExhaustive();
         }
         else
         {

            checkCycles();

            // TODO - omkar - perform experiment
            bool allMethods = false;
            std::unordered_set<TR_OpaqueMethodBlock *> expMethod;
            std::unordered_set<std::string> ignoreMethods = readIgnoreMethodIndices();
            if (allMethods)
            {
               for (auto method : stmtNumber)
               {
                  if (methodPTG.find(method.first) != methodPTG.end() && methodPTGcopy.find(method.first) != methodPTGcopy.end() && ignoreMethods.find(inverseMethodNameIDmapping[method.first]) == ignoreMethods.end())
                  {
                     expMethod.insert(method.first);
                  }
               }
            }
            else
            {
               for (auto method : stmtNumber)
               {
                  if (method.first == monitor3 && methodPTG.find(method.first) != methodPTG.end() && methodPTGcopy.find(method.first) != methodPTGcopy.end())
                  {
                     expMethod.insert(method.first);
                  }
                  // if(method.first == monitor4 && methodPTG.find(method.first) != methodPTG.end() && methodPTGcopy.find(method.first) != methodPTGcopy.end()){
                  //    expMethod.insert(method.first);
                  // }
               }
            }

            bool breakFlag = false;
            for (auto hcrMethod : expMethod)
            {
               std::cout << "hcr method = " << inverseMethodNameIDmapping[hcrMethod] << "\n";
               std::cout.flush() << "\n";
               std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> delStmt;
               std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> addStmt;
               for (auto stmt : stmtNumber[hcrMethod])
               {
                  delStmt[hcrMethod].insert(stmt.first);
                  addStmt[hcrMethod].insert(stmt.first);
               }

               topLevelMethods.clear();
               topLevelVisited.clear();

               auto start1 = std::chrono::high_resolution_clock::now();

               performDelete(comp, delStmt, methodDict);

               auto end1 = std::chrono::high_resolution_clock::now();

               for (auto m : stmtNumber)
               {
                  if (methodPTG.find(m.first) != methodPTG.end() && methodPTGcopy.find(m.first) != methodPTGcopy.end())
                  {
                     if (methodPTG[m.first]->equals(methodPTGcopy[m.first]))
                     {
                        // std::cout<<"after addition equal\n";
                     }
                     else
                     {
                        std::cout << "after del unequal for " << inverseMethodNameIDmapping[m.first] << "\n";
                        // methodPTGcopy[m.first]->print();
                        // std::cout<<"after del "<<inverseMethodNameIDmapping[m.first]<<"\n";
                        // methodPTG[m.first]->print();
                     }
                  }
               }

               callSiteStore.clear();
               topLevelMethods.clear();
               topLevelVisited.clear();

               std::cout << "addition proc started\n";

               auto start2 = std::chrono::high_resolution_clock::now();

               performAddition(comp, addStmt, methodDict);

               auto end2 = std::chrono::high_resolution_clock::now();

               callSiteStore.clear();

               for (auto m : stmtNumber)
               {
                  if (methodPTG.find(m.first) != methodPTG.end() && methodPTGcopy.find(m.first) != methodPTGcopy.end())
                  {
                     if (methodPTG[m.first]->equals(methodPTGcopy[m.first]))
                     {
                        // std::cout<<"after addition equal\n";
                        // std::cout<<"after addition equal for "<<inverseMethodNameIDmapping[m.first]<<"\n";
                        // methodPTGcopy[m.first]->print();
                        // std::cout<<"after add "<<inverseMethodNameIDmapping[m.first]<<"\n";
                        // methodPTG[m.first]->print();
                     }
                     else
                     {
                        std::cout << "after addition unequal for " << inverseMethodNameIDmapping[m.first] << "\n";
                        methodPTGcopy[m.first]->print();
                        std::cout << "after add " << inverseMethodNameIDmapping[m.first] << "\n";
                        methodPTG[m.first]->print();
                        breakFlag = true;
                     }
                  }
               }

               std::chrono::duration<double> elapsed1 = end1 - start1;
               std::cout << "Time taken for delete: " << elapsed1.count() << " s\n";

               std::chrono::duration<double> elapsed2 = end2 - start2;
               std::cout << "Time taken for addition: " << elapsed2.count() << " s\n";

               std::cout << "Time taken for total: " << elapsed1.count() + elapsed2.count() << " s\n";

               if (breakFlag)
               {
                  std::cout.flush();
                  break;
               }
            }
         }
      }
   }
}

void computeMSetForMethod(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict)
{
   // std::cout<<"Mset computed for method = "<<getMethodName(methodSymbol)<<"\n";

   Counter counter(comp->getVisitCount() + 1, -10);

   std::unordered_set<TR::Node *> nodeVisited;

   // std::string methodSignature = methodSymbol->signature(comp->trMemory());

   TR_OpaqueMethodBlock *methodPersistentId = methodSymbol->getResolvedMethod()->getPersistentIdentifier();

   // storing data in helper data structures
   methodNameIDmapping[getMethodName(methodSymbol)] = methodPersistentId;
   inverseMethodNameIDmapping[methodPersistentId] = getMethodName(methodSymbol);

   if (inverseMethodNameIDmapping[methodPersistentId].find("Harness.main") != std::string::npos)
   {
      monitor1 = methodPersistentId;
   }

   if (inverseMethodNameIDmapping[methodPersistentId].find("org/sunflow/core/Geometry.build()V") != std::string::npos)
   {
      monitor2 = methodPersistentId;
   }

   if (inverseMethodNameIDmapping[methodPersistentId].find("org/sunflow/core/accel/KDTree.buildTree(FFFFFFLorg/sunflow/core/accel/KDTree$BuildTask;ILorg/sunflow/util/IntArray;ILorg/sunflow/util/IntArray;Lorg/sunflow/core/accel/KDTree$BuildStats;)V") != std::string::npos)
   {
      monitor3 = methodPersistentId;
   }

   if (inverseMethodNameIDmapping[methodPersistentId].find("org/dacapo/parser/TokenMgrError.<init>(ZIIILjava/lang/String;CI)V") != std::string::npos)
   {
      monitor4 = methodPersistentId;
   }

   if (inverseMethodNameIDmapping[methodPersistentId].find("org/sunflow/Benchmark$BenchmarkScene.buildCornellBox()V") != std::string::npos)
   {
      monitor5 = methodPersistentId;
   }

   int methodIndex = getOrInsertMethodIndex(methodSymbol, comp);
   methodPtrToIndex[methodPersistentId] = methodIndex;

   // create methodPTG here
   if (!exhaustive)
   {
      methodPTG[methodPersistentId] = &(_indexPTG[methodIndex]);
      std::map<int, std::set<Entry *>> myRho = methodPTG[methodPersistentId]->getRho();
      std::map<int, std::set<Entry *>>::iterator myIterator = myRho.begin();
      while (myIterator != myRho.end())
      {
         int slot = myIterator->first;
         if (slot > 400)
         {
            break;
         }
         if (slot == 0)
         {
            methodPTG[methodPersistentId]->assignReturn(myRho[slot]);
         }
         else
         {
            methodPTG[methodPersistentId]->setArg(slot - 1, myRho[slot]);
         }
         myIterator++;
      }

      methodPTGcopy[methodPersistentId] = new PointsToGraph(*methodPTG[methodPersistentId]);
      methodPTGout[methodPersistentId] = new PointsToGraph(*methodPTG[methodPersistentId]);
   }

   ListIterator<TR::ParameterSymbol> paramIterator(&(methodSymbol->getParameterList()));
   TR::ParameterSymbol *paramCursor = paramIterator.getFirst();
   TR::SymbolReference *symRef;

   int argIndex = 0;
   if (methodSymbol->isStatic())
   {
      // for static methods, our magic arg index begins from 1
      argIndex = 1;
   }
   for (; paramCursor != NULL; paramCursor = paramIterator.getNext())
   {
      int paramSlot = paramCursor->getSlot();
      // cout << "paramSlot = " << paramSlot << "\n";

      symRef = methodSymbol->getParmSymRef(paramSlot);
      if (!symRef)
         TR_ASSERT_FATAL(false, "param symref is null!");
      // cout << "param symRef is null!\n";
      if (symRef->getSymbol()->getType().isAddress())
      {
         int32_t symRefNumber = symRef->getReferenceNumber();
         formalParMethod[methodPersistentId][symRefNumber] = argIndex;
         inverseFormalParMethod[methodPersistentId][argIndex] = symRefNumber;
         argIndex++;
      }
      else
      {
         // cout << "not an address symref!\n";
         argIndex++;
      }
   }

   // we begin from the start node of the CFG
   // TODO: perform the topological sort of the CFG here, to identify the order in which the basic blocks are to be processed
   TR::CFG *cfg = methodSymbol->getFlowGraph();
   if (!cfg)
      std::cout << "cfg is null!" << std::endl;
   TR::Block *start = cfg->getStart()->asBlock();
   TR_LinkHead1<TR::CFGNode> nodeList = cfg->getNodes();

   // perform a topological sort of the CFG to determine the order in which the basic blocks are to be processed
   std::vector<TR::Block *> gray;
   std::vector<TR::Block *> black;
   std::stack<TR::Block *> blockProcessingOrder;
   std::stack<TR::Block *> bpo;
   pseudoTopoSort(start, gray, black, blockProcessingOrder);

   while (!nodeList.isEmpty())
   {
      TR::Block *tempBlock = nodeList.pop()->asBlock();
      pseudoTopoSort(tempBlock, gray, black, blockProcessingOrder);
   }

   while (!blockProcessingOrder.empty())
   {
      TR::Block *currentBB = blockProcessingOrder.top();
      blockProcessingOrder.pop();

      int currentBBNumber = currentBB->getNumber();

      TR::TreeTop *tt = currentBB->getEntry();
      // its possible that there are no entry treetops for certain basic blocks

      if (tt)
      {
         // now we iterate over the treetops in the basic block
         for (; tt; tt = tt->getNextRealTreeTop())
         {
            TR::Node *node = tt->getNode();

            int nodeBCI = node->getByteCodeInfo().getByteCodeIndex();
            // unfortunately it appears that the Start and End nodes are also valid treetops.

            if (node->getOpCodeValue() == TR::BBStart)
            {
               continue;
            }
            else
            {
               if (node->getOpCodeValue() == TR::BBEnd)
               {
                  break;
               }
            }

            bool fc = !exhaustive;

            int evaluatedValueForNode = evaluateNode(node, counter, methodPersistentId, comp, fc, methodDict, nodeVisited);
         }
      }
   }
}

int evaluateNode(TR::Node *node, Counter &counter, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp, bool fillCache, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict, std::unordered_set<TR::Node *> &nodeVisited)
{

   // default value of evaluatedSymref
   int evaluatedSymRef = -2;

   // get relevant node
   TR::Node *usefulNode = getUsefulNode(node);

   // if relevant node not present
   if (!usefulNode)
   {
      return evaluatedSymRef;
   }

   if (nodeVisited.find(usefulNode) != nodeVisited.end())
   {
      // std::cout<<"seen node = "<<usefulNode<<"\n";
      evaluatedSymRef = evaluatedNodeValues[usefulNode];
      return evaluatedSymRef;
   }
   else
   {
      // std::cout<<"eval node = "<<usefulNode<<"\n";

      // fetch the mset for this method

      // increment the visit count to denote that node is visited
      usefulNode->setVisitCount(counter.visitCount);
      nodeVisited.insert(usefulNode);

      // get the type of node
      TR::ILOpCodes opCode = usefulNode->getOpCodeValue();

      switch (opCode)
      {

      case TR::checkcast:
      {

         // actual values belong tofirst child
         evaluatedSymRef = evaluateNode(usefulNode->getFirstChild(), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

         // increment stmt count
         counter.stmtCount++;

         // update stmt number of this node
         usefulNode->stmtNumber = counter.stmtCount;

         // update stmt number to stmt map
         stmtNumber[currentMethod][usefulNode->stmtNumber] = usefulNode;

         methodDict[currentMethod].stmtMap[evaluatedSymRef].insert(usefulNode->stmtNumber);

         if (fillCache)
         {
            std::set<Entry *> childPts = getCachedPointsTo(usefulNode->getFirstChild());
            cachedValues[usefulNode].insert(childPts.begin(), childPts.end());
         }

         break;
      }
      case TR::aconst:
      {

         // this is needed for calls where the arg is null - it appears to map to aconst_null in bytecode
         evaluatedSymRef = -1;

         if (fillCache)
         {
            cachedValues[usefulNode].insert(PointsToGraph::nullEntry);
         }

         break;
      }
      case TR::aladd:
      {

         evaluatedSymRef = evaluateNode(usefulNode->getFirstChild(), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

         if (fillCache)
         {
            std::set<Entry *> childPts = getCachedPointsTo(usefulNode->getFirstChild());
            cachedValues[usefulNode].insert(childPts.begin(), childPts.end());
         }
         break;
      }
      case TR::New:
      {

         // process new here
         evaluatedSymRef = -1000 - (usefulNode->getByteCodeIndex());

         if (fillCache)
         {

            // create an entry object
            Entry *e = evaluateAllocate(usefulNode, methodPtrToIndex[currentMethod], 0);

            // get the type of object

            if (e->clazz == NULL)
            {
               std::cout << "figure out why type is null at " << methodPtrToIndex[currentMethod] << "-" << usefulNode->getByteCodeIndex() << "\n";
            }
            else
            {

               // cache the type name for class ptr
               if (cachedClassSignature.find(e->clazz) == cachedClassSignature.end())
               {
                  cachedClassSignature[e->clazz] = TR::Compiler->cls.classSignature(comp, e->clazz, comp->trMemory());
               }
               std::string className = cachedClassSignature[e->clazz];

               // special case if type is string
               if (className.find("Ljava/lang/String;") != std::string::npos)
               {
                  cachedValues[usefulNode].insert(PointsToGraph::stringEntry);
               }
               else
               { // standard case
                  cachedValues[usefulNode].insert(e);
               }
            }
         }
         break;
      }
      case TR::anewarray:
      {

         evaluatedSymRef = -1000 - (usefulNode->getByteCodeIndex());

         if (fillCache)
         {
            // create an entry object
            Entry *e = evaluateAllocate(usefulNode, methodPtrToIndex[currentMethod], 1);
            if (usefulNode->getSecondChild()->getOpCodeValue() == TR::loadaddr)
            {
               // get the type of object

               if (e->clazz == NULL)
               {
                  std::cout << "figure out why type is null at " << methodPtrToIndex[currentMethod] << "-" << usefulNode->getByteCodeIndex() << "\n";
               }
               else
               {
                  // caching
                  cachedValues[usefulNode].insert(e);
               }
            }
            else
            {
               // caching
               cachedValues[usefulNode].insert(e);
            }
         }
         break;
      }
      case TR::newarray:
      {

         // process newarray
         evaluatedSymRef = -1000 - (usefulNode->getByteCodeIndex());

         if (fillCache)
         {
            // create an entry object
            Entry *e = evaluateAllocate(usefulNode, methodPtrToIndex[currentMethod], 2);

            // cache points-to
            cachedValues[usefulNode].insert(e);
         }
         break;
      }

      case TR::multianewarray:
      {

         evaluatedSymRef = -1000 - (usefulNode->getByteCodeIndex());

         if (fillCache)
         {
            // we do not model multianewarray !! Be conservative
            cachedValues[usefulNode].insert(PointsToGraph::bottomEntry);
         }
         break;
      }

      case TR::astore:
      {

         // store child contains the actual values
         TR::Node *storeChild = usefulNode->getFirstChild();

         // evaluate the first child
         int loadSymRef = evaluateNode(storeChild, counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

         if (fillCache)
         {
            cachedValues[usefulNode] = cachedValues[storeChild];
         }

         // get the store var
         int storeSymRef = usefulNode->getSymbolReference()->getReferenceNumber();
         evaluatedSymRef = storeSymRef;

         // increment stmt count
         counter.stmtCount++;

         // update stmt number of this node
         usefulNode->stmtNumber = counter.stmtCount;

         // update stmt number to stmt map
         stmtNumber[currentMethod][usefulNode->stmtNumber] = usefulNode;

         // update mapping of var to stmt
         methodDict[currentMethod].stmtMap[storeSymRef].insert(usefulNode->stmtNumber);

         // in case loadsymref is not valid, we still want node for storesymref

         // if rhs contains valid variable then union of ds
         methodDict[currentMethod].lct.link(storeSymRef, loadSymRef);

         break;
      }

      case TR::aload:
      {

         // check if it's a static field load
         bool isStaticFieldRead = usefulNode->getSymbol()->isStaticField();
         if (isStaticFieldRead)
         {
            evaluatedSymRef = -1;
            if (fillCache)
            {
               cachedValues[usefulNode].insert(PointsToGraph::bottomEntry);
            }
         }
         else
         {
            // get rhs variablle
            int loadSymRef = usefulNode->getSymbolReference()->getReferenceNumber();
            evaluatedSymRef = loadSymRef;

            if (fillCache)
            {
               // special case for exception objects
               if (usefulNode->getSymbolReference()->getSymbol()->getKind() == TR::Symbol::IsMethodMetaData)
               {
                  std::string loadName = comp->getDebug()->getMetaDataName(usefulNode->getSymbolReference());
                  if (loadName.find("ExceptionMeta") != std::string::npos)
                  {
                     cachedValues[usefulNode].insert(PointsToGraph::bottomEntry);
                  }
               }
               else if (usefulNode->getSymbolReference()->getSymbol()->castToStaticSymbol()->isConstString())
               {
                  // special case for strings
                  cachedValues[usefulNode].insert(PointsToGraph::stringEntry);
               }
               else
               {
                  // standard case
                  set<Entry *> pointsToSet = methodPTG[currentMethod]->getPointsToSet(loadSymRef);
                  cachedValues[usefulNode].insert(pointsToSet.begin(), pointsToSet.end());
               }
            }
         }

         break;
      }

      case TR::aloadi:
      {

         std::string field;

         // check if it's an array load
         if (usefulNode->getSymbol()->isArrayShadowSymbol())
         {
            // get the array node
            TR::Node *receiverNode = usefulNode->getFirstChild()->getFirstChild();

            // retrieve the name of array
            evaluatedSymRef = evaluateNode(receiverNode, counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

            if (fillCache)
            {
               // get the cached points-to for array variable
               std::set<Entry *> receiverNodeVals = getCachedPointsTo(receiverNode);

               // abstract field fro array contents
               field = "_$";

               // union of points-to for abstract field of all array objects
               for (auto receiver : receiverNodeVals)
               {
                  // retrieve points-to for abstract field of points-to
                  set<Entry *> rhsPointees = methodPTG[currentMethod]->getPointsToSet(receiver, field);

                  // update the cached information for array load (implicit union)
                  cachedValues[usefulNode].insert(rhsPointees.begin(), rhsPointees.end());
               }
            }
         }
         else
         {

            // get the node ref
            TR::SymbolReference *symRef = usefulNode->getSymbolReference();

            // get extra info
            bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;
            int cpIndex = symRef->getCPIndex();

            if (/* !isUnresolved && */ isShadow && cpIndex > 0)
            {
               // this is most certainly a field access, until proven otherwise

               // get the base variable node
               TR::Node *receiverNode = usefulNode->getFirstChild();

               // get the base variable name
               evaluatedSymRef = evaluateNode(receiverNode, counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

               if (fillCache)
               {
                  // retrieve points-to of base variable
                  std::set<Entry *> receiverNodeVals = getCachedPointsTo(receiverNode);

                  // fetch the name of field
                  int32_t len;
                  const char *fieldName = usefulNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(usefulNode->getSymbolReference()->getCPIndex(), len);
                  field.assign(fieldName, fieldName + len);

                  // union of points-to for field of obj pointed by base var
                  for (auto receiver : receiverNodeVals)
                  {
                     // retrieve points-to for field of points-to
                     set<Entry *> rhsPointees = methodPTG[currentMethod]->getPointsToSet(receiver, field);

                     // update the cached information for field read (implicit union)
                     cachedValues[usefulNode].insert(rhsPointees.begin(), rhsPointees.end());
                  }
               }
            }
         }

         break;
      }

      case TR::awrtbar:
      {

         // increment stmt count
         counter.stmtCount++;

         // update stmt number of this node
         usefulNode->stmtNumber = counter.stmtCount;

         // update stmt number to stmt map
         stmtNumber[currentMethod][usefulNode->stmtNumber] = usefulNode;

         // get the variable on rhs
         evaluatedSymRef = evaluateNode(usefulNode->getFirstChild(), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

         if (fillCache)
         {
            cachedValues[usefulNode] = cachedValues[getUsefulNode(usefulNode->getFirstChild())];
         }

         // we are not checking if evaluated symRef < -10 and >= 0
         // bcoz if it is valid symref then the stmt will be stored appropriately as expected
         // however, if this is spl case, we still want the stmt number but don't want to merge with any set
         // as reanalyzing/adding/deleting in spl case won't lead to any new result
         // eg spl case : A.g = B.g

         methodDict[currentMethod].stmtMap[evaluatedSymRef].insert(usefulNode->stmtNumber);

         break;
      }

      case TR::awrtbari:
      {

         // awrtbari also performs array writes!

         // increment stmt count
         counter.stmtCount++;

         // update stmt number of this node
         usefulNode->stmtNumber = counter.stmtCount;

         // update stmt number to stmt map
         stmtNumber[currentMethod][usefulNode->stmtNumber] = usefulNode;

         // get rhs node
         TR::Node *valueNode = usefulNode->getSecondChild();

         if (valueNode->getDataType() == TR::Address)
         {

            // get rhs variable
            int loadSymRef = evaluateNode(valueNode, counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

            if (fillCache)
            {
               cachedValues[usefulNode] = cachedValues[getUsefulNode(valueNode)];
            }

            // if not an array store
            if (!usefulNode->getSymbol()->isArrayShadowSymbol())
            {

               // get symref for lhs node
               TR::SymbolReference *symRef = usefulNode->getSymbolReference();

               // get extra info
               bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;
               int cpIndex = symRef->getCPIndex();

               if (/* !isUnresolved && */ isShadow && cpIndex > 0)
               {
                  //    // this is most certainly a field access, until proven otherwise

                  // get base variable node for lhs
                  TR::Node *receiverNode = usefulNode->getFirstChild();

                  // get base variable name
                  int storeSymRef = evaluateNode(receiverNode, counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

                  evaluatedSymRef = storeSymRef;

                  // update mapping of var to stmt
                  methodDict[currentMethod].stmtMap[storeSymRef].insert(usefulNode->stmtNumber);
                  // std::cout<<"awrtbari store = "<<storeSymRef<<" node = "<<usefulNode<<" stmt nm = "<<usefulNode->stmtNumber<<"\n";

                  methodDict[currentMethod].lct.link(storeSymRef, loadSymRef);
               }
            }
            else
            {
               // array writes

               // get array node
               TR::Node *receiverNode = usefulNode->getThirdChild();

               // get array variable name
               int storeSymRef = evaluateNode(receiverNode, counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

               evaluatedSymRef = storeSymRef;

               // update mapping of var to stmt
               methodDict[currentMethod].stmtMap[storeSymRef].insert(usefulNode->stmtNumber);

               // if rhs contains valid variable then union of ds
               methodDict[currentMethod].lct.link(storeSymRef, loadSymRef);
            }
         }

         break;
      }

      case TR::icalli:
         // case TR::vcalli:
      case TR::lcalli:
      case TR::fcalli:
      case TR::dcalli:
      case TR::acalli:
      case TR::calli:
      case TR::icall:
      case TR::lcall:
      case TR::fcall:
      case TR::dcall:
      case TR::acall:
      case TR::call:
      case TR::vcall:
      {

         // increment stmt count
         counter.stmtCount++;

         // update stmt number of this node
         usefulNode->stmtNumber = counter.stmtCount;

         // update stmt number to stmt map
         stmtNumber[currentMethod][usefulNode->stmtNumber] = usefulNode;

         // check if method is a helper
         bool isHelperMethodCall = usefulNode->getSymbol()->castToMethodSymbol()->isHelper();

         // if not an helper, then fetch the name of method
         const char *methodName;
         if (!isHelperMethodCall)
         {
            methodName = usefulNode->getSymbolReference()->getName(comp->getDebug());

            // cache the name of method
            cachedMethodName[usefulNode] = methodName;
         }

         // we do not want to process helper method calls (prepareForOSR, potentialOSRPointHelper, for example)
         if (isHelperMethodCall) // || (usefulNode->getSymbolReference()->isUnresolved() && !usefulNode->getSymbol()->castToMethodSymbol()->isInterface()))
         {
            evaluatedSymRef = -1;
            break;
         }
         else if (isLibraryMethod(methodName) && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
         {
            evaluatedSymRef = -1;

            // populate cache with return pts of these method calls

            if (((std::string)methodName).find(")Ljava/lang/String;") != std::string::npos)
            {
               evaluatedSymRef = -4;
               if (fillCache)
               {
                  cachedValues[usefulNode].insert(PointsToGraph::stringEntry);
               }
            }
            else if (((std::string)methodName).find(")Ljava/lang/Class;") != std::string::npos)
            {
               evaluatedSymRef = -5;
               if (fillCache)
               {
                  cachedValues[usefulNode].insert(PointsToGraph::classEntry);
               }
            }
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0)
            {
               evaluatedSymRef = -6;
               if (fillCache)
               {
                  cachedValues[usefulNode].insert(PointsToGraph::bottomEntry);
               }
            }

            methodDict[currentMethod].stmtMap[evaluatedSymRef].insert(usefulNode->stmtNumber);

            // this is for thread creation with runnable parameter
            if (((std::string)methodName).find("java/lang/Thread.<init>(Ljava/lang/Runnable;)V") != std::string::npos)
            {
               int secChildNumber = evaluateNode(usefulNode->getSecondChild(), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);
               methodDict[currentMethod].stmtMap[secChildNumber].insert(usefulNode->stmtNumber);
               if (fillCache)
               {
                  cachedValues[usefulNode->getFirstChild()] = getCachedPointsTo(usefulNode->getSecondChild());
               }
            }

            // library methods that don't use reflection and are not constructors
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0 && ((std::string)methodName).find("<init>") == std::string::npos)
            {

               // first arg index points to receiver in case of non static
               int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
               int32_t numChildren = usefulNode->getNumChildren();

               // iterate over all arguments
               for (int32_t i = firstArgIndex; i < numChildren; i++)
               {
                  int tempNumber = evaluateNode(usefulNode->getChild(i), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);
                  // std::cout<<"tempNum is "<<tempNumber<<" for "<<usefulNode<<"\n";
                  methodDict[currentMethod].stmtMap[tempNumber].insert(usefulNode->stmtNumber);
               }
            }
            else
            {
               // first arg index points to receiver in case of non static
               int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
               int32_t numChildren = usefulNode->getNumChildren();

               // iterate over all arguments
               for (int32_t i = firstArgIndex; i < numChildren; i++)
               {
                  int tempNumber = evaluateNode(usefulNode->getChild(i), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);
                  // std::cout<<"tempNum is "<<tempNumber<<" for "<<usefulNode<<"\n";
                  // methodDict[currentMethod].stmtMap[tempNumber].insert(usefulNode->stmtNumber);
               }
            }

            break;
         }
         else
         {

            // checks to determine the type of method call
            bool isStatic = usefulNode->getSymbol()->castToMethodSymbol()->isStatic();
            bool isInterfaceInvoke = usefulNode->getSymbol()->castToMethodSymbol()->isInterface();

            // fetch the bci of method call
            int callsiteBCI = usefulNode->getByteCodeIndex();

            if (isInterfaceInvoke)
            {
               // in case of invokeinterface, J9 seems to increment the bci by 2. This causes a mismatch with static artifacts, so we adjust it back
               callsiteBCI -= 2;
            }

            // methods to be peeked
            std::unordered_set<TR_OpaqueMethodBlock *> methodsToPeek;

            int argIndex = 0;
            if (isStatic)
            {
               argIndex = 1;

               // if we are filling cache, populate callgraphs

               // there is no runtime polymorphism when it comes to static methods - so direct resolution of the static type at the callsite is just fine
               // fetch call node symbol
               TR::ResolvedMethodSymbol *callNodeSymbol = usefulNode->getSymbol()->getResolvedMethodSymbol();

               // get the target method from call node symbol
               methodsToPeek.insert(callNodeSymbol->getResolvedMethod()->getPersistentIdentifier());

               if (fillCache)
               {
                  // update the callgraph
                  myCallGraph[currentMethod][usefulNode].insert(callNodeSymbol->getResolvedMethod()->getPersistentIdentifier());
                  myInverseCallGraph[callNodeSymbol->getResolvedMethod()->getPersistentIdentifier()][currentMethod].insert(usefulNode);
               }
            }
            else
            {
               // fetch target method name
               int methodNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->nameLength();
               std::string methodNm;

               if (!isInterfaceInvoke && usefulNode->getSymbol()->getResolvedMethodSymbol()->getResolvedMethod()->getPersistentIdentifier() == _threadStartPersistentId)
               {
                  // if method is thread.start then short-circuit with run method
                  // std::cout<<"Thread1 run node = "<<usefulNode<<"\n";
                  methodNm = "run";
                  // std::cout << "short-circuit Thread.start with .run()\n";
               }
               else
               {

                  // fetch method name
                  methodNm = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->nameChars();
                  methodNm = methodNm.substr(0, methodNameLength);
               }

               // fetch target method signature
               int sigLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->signatureLength();
               std::string signatureChars = usefulNode->getSymbol()->getMethodSymbol()->getMethod()->signatureChars();
               std::string sig = signatureChars.substr(0, sigLength);

               if (!exhaustive)
               {
                  // read the receiver info for the callsite, lazily
                  std::map<int, std::set<int>> receiverInfoForMethod;

                  if (_callsiteReceivers.find(methodPtrToIndex[currentMethod]) == _callsiteReceivers.end())
                  {
                     // callsite receiver info has not been loaded yet, load it now
                     receiverInfoForMethod = readReceivers(methodPtrToIndex[currentMethod]);

                     // cache this information
                     _callsiteReceivers[methodPtrToIndex[currentMethod]] = receiverInfoForMethod;
                  }
                  else
                  {
                     // receiver info already read; retrieve from cache
                     receiverInfoForMethod = _callsiteReceivers[methodPtrToIndex[currentMethod]];
                  }

                  if (receiverInfoForMethod.find(callsiteBCI) == receiverInfoForMethod.end())
                  {
                     std::cout << "some issue at bci " << callsiteBCI << " in method " << methodName << "\n";
                  }
                  else
                  {
                     // fetch the class index from which target method has to be retrieved
                     std::set<int> receiverTypesForCallsite = receiverInfoForMethod[callsiteBCI];

                     // iterate over class index
                     for (int receiverType : receiverTypesForCallsite)
                     {
                        // get the name of class from class index

                        std::string receiverTypeName = _classIndices[receiverType];

                        // length of class name
                        int len = strlen(receiverTypeName.c_str());

                        // fetch class pointer from name
                        TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(receiverTypeName.c_str(), len, comp->getCurrentMethod());

                        TR_ASSERT_FATAL(type, "unable to get class pointer for receiver %s", inverseMethodNameIDmapping[currentMethod]);

                        // fetch resolved method
                        TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, type, methodNm.c_str(), sig.c_str());
                        TR_ASSERT_FATAL(targetMethod, "unable to find method for name and signature %s %s", methodNm.c_str(), sig.c_str());

                        // fetch resolved method symbol
                        TR::ResolvedMethodSymbol *targetMethodSymbol = targetMethod->findOrCreateJittedMethodSymbol(comp);
                        TR_ASSERT_FATAL(targetMethodSymbol, "unable to find method for name and signature %s %s", methodNm.c_str(), sig.c_str());

                        // get the method ptr
                        TR_OpaqueMethodBlock *targetMethodPtr = targetMethodSymbol->getResolvedMethod()->getPersistentIdentifier();

                        // add method pointer to methodsToPeek
                        methodsToPeek.insert(targetMethodPtr);

                        cachedParameterType[targetMethodPtr][0] = type;

                        // update the callgraph
                        myCallGraph[currentMethod][usefulNode].insert(targetMethodPtr);
                        myInverseCallGraph[targetMethodPtr][currentMethod].insert(usefulNode);
                     }
                  }
               }
               else
               {

                  if (cachedMethodName[usefulNode].find("java/lang/Object.<init>()V") != std::string::npos)
                  {

                     for (auto ci : _classIndices)
                     {
                        std::string className = ci.second;
                        int len = strlen(className.c_str());
                        TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), len, comp->getCurrentMethod());
                        if (type != NULL)
                        {
                           TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, type, methodNm.c_str(), sig.c_str());
                           if (targetMethod != NULL)
                           {
                              methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                              cachedParameterType[targetMethod->getPersistentIdentifier()][0] = type;
                           }
                        }
                     }
                  }
                  else
                  {
                     // CHA based
                     int classNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameLength();
                     string className = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameChars();
                     TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), classNameLength, comp->getCurrentMethod());

                     std::queue<TR_OpaqueClassBlock *> bfsList;
                     std::unordered_set<TR_OpaqueClassBlock *> visitedClass;
                     bfsList.push(type);
                     visitedClass.insert(type);

                     // std::string tpName = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());

                     while (!bfsList.empty())
                     {
                        TR_OpaqueClassBlock *currentClass = bfsList.front();
                        bfsList.pop();

                        char *currchild = TR::Compiler->cls.classSignature(comp, currentClass, comp->trMemory());
                        // std::cout<<"eval method target name = "<<currchild<<"\n";

                        TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, currentClass, methodNm.c_str(), sig.c_str());
                        if (targetMethod != NULL && !targetMethod->isAbstract())
                        { //! TR::Compiler->cls.isInterfaceClass(comp, currentClass)){
                           // std::cout<<"targetMethod in CHA is null\n";
                           if (classPtrToIndex[currentClass] == 0)
                           {
                              // std::cout<<"didid 4 = "<<methodName<<"\n";
                           }
                           // _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[currentClass]);

                           methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                           cachedParameterType[targetMethod->getPersistentIdentifier()][0] = currentClass;
                        }

                        for (auto rec : CHA[currentClass])
                        {
                           // std::string child = TR::Compiler->cls.classSignature(comp, rec, comp->trMemory());
                           // std::cout<<"child meth = "<<child<<"\n";

                           if (visitedClass.find(rec) == visitedClass.end())
                           {
                              // std::cout<<"adding to bfs\n";
                              visitedClass.insert(rec);
                              bfsList.push(rec);
                           }
                        }
                     }
                  }
               }
            }

            // go over methods that need to be peeked (JIT compiled)

            for (auto calleeMethodPtr : methodsToPeek)
            {
               if (_methodsAnalyzed.find(calleeMethodPtr) == _methodsAnalyzed.end() && _methodsBeingAnalyzed.find(calleeMethodPtr) == _methodsBeingAnalyzed.end())
               {
                  if (inverseMethodNameIDmapping[currentMethod].find("<init>()V") != std::string::npos && cachedMethodName[usefulNode].find("java/lang/Object.<init>()V") != std::string::npos)
                  {
                     continue;
                  }

                  // fetch the resolved method symbol

                  TR_ResolvedMethod *calleeMethod = getCachedResolvedMethodFromPtr(comp, calleeMethodPtr);

                  TR::ResolvedMethodSymbol *calleeResolvedMethodSymbol = calleeMethod->findOrCreateJittedMethodSymbol(comp);

                  _methodsBeingAnalyzed.insert(calleeMethodPtr);

                  // JIT compile
                  bool ilGenFailed = NULL == calleeMethod->genMethodILForPeekingEvenUnderMethodRedefinition(calleeResolvedMethodSymbol, comp, false);
                  TR_ASSERT_FATAL(!ilGenFailed, "IL Gen failed, cannot peek into method");

                  // dump the JIT compiled method tree to log
                  comp->dumpMethodTrees("Method tree about to peek", calleeResolvedMethodSymbol);

                  TR_MethodParameterIterator *parIterator = comp->getOwningMethodSymbol(calleeMethodPtr)->getResolvedMethod()->getParameterIterator(*comp);
                  for (int argNo = 1; !parIterator->atEnd(); parIterator->advanceCursor(), argNo++)
                  {
                     if (parIterator->isArray() || parIterator->isClass())
                     {
                        cachedParameterType[calleeMethodPtr][argNo] = parIterator->getOpaqueClass();
                     }
                  }
               }

               if (usefulNode->getDataType() == TR::Address && fillCache && methodPTG[calleeMethodPtr]->contains(-3))
               {
                  cachedValues[usefulNode].insert(methodPTG[calleeMethodPtr]->getReturnPointsTo().begin(), methodPTG[calleeMethodPtr]->getReturnPointsTo().end());
                  // std::cout<<"caching return for "<<usefulNode<<" size = "<<cachedValues[usefulNode].size()<<"\n";
               }
            }

            bool stmtSaved = false;
            if (usefulNode->getDataType() == TR::Address)
            {
               // generate a dummy variable number to represent return of this callnode
               counter.retCount--;

               // evaluated value of this callnode will be return variable
               evaluatedSymRef = counter.retCount;
               methodDict[currentMethod].stmtMap[evaluatedSymRef].insert(usefulNode->stmtNumber);
               stmtSaved = true;

               // update mappings of call node, ret, etc
               argCallNode[currentMethod][counter.retCount].insert(std::make_pair(usefulNode, -3));
               inverseArgCallNode[currentMethod][usefulNode][-3] = counter.retCount;
            }

            // first arg index points to receiver in case of non static
            int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
            int32_t numChildren = usefulNode->getNumChildren();

            for (int32_t i = firstArgIndex; i < numChildren; i++)
            {
               // get argument variable
               int temp = evaluateNode(usefulNode->getChild(i), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

               // update mapping of var to stmt
               // std::cout<<"temp = "<<temp<<"\n";
               methodDict[currentMethod].stmtMap[temp].insert(usefulNode->stmtNumber);
               stmtSaved = true;

               // update mappings of call node, arg, etc
               argCallNode[currentMethod][temp].insert(std::make_pair(usefulNode, argIndex));
               inverseArgCallNode[currentMethod][usefulNode][argIndex] = temp;

               // increment argument
               argIndex++;
            }

            if (!stmtSaved)
            {
               methodDict[currentMethod].stmtMap[-2].insert(usefulNode->stmtNumber);
            }
         }

         break;
      }

      case TR::Return:
      case TR::lreturn:
      case TR::ireturn:
      case TR::dreturn:
      case TR::freturn:
      case TR::areturn:
      case TR::vreturn:
      {

         if (opCode == TR::areturn)
         {
            // increment stmt count
            counter.stmtCount++;

            // update stmt number of this node
            usefulNode->stmtNumber = counter.stmtCount;

            // update stmt number to stmt map
            stmtNumber[currentMethod][usefulNode->stmtNumber] = usefulNode;

            // get the return variable
            int loadSymRef = evaluateNode(usefulNode->getFirstChild(), counter, currentMethod, comp, fillCache, methodDict, nodeVisited);

            if (fillCache)
            {
               cachedValues[usefulNode] = cachedValues[getUsefulNode(usefulNode->getFirstChild())];
            }

            evaluatedSymRef = loadSymRef;

            // update mapping of var to stmt
            methodDict[currentMethod].stmtMap[loadSymRef].insert(counter.stmtCount);

            // if rhs contains valid variable then union of ds
            // -r is special number to represent return of method

            methodDict[currentMethod].lct.link(loadSymRef, -3);

            formalParMethod[currentMethod][loadSymRef] = -3;
            inverseFormalParMethod[currentMethod][-3] = loadSymRef;
         }
         break;
      }

      default:
      {
         //         TR_ASSERT_FATAL(true, "opcode %s not recognized", usefulNode->getOpCode().getName());
         break;
      }
      }
   }
   evaluatedNodeValues[usefulNode] = evaluatedSymRef;
   return evaluatedSymRef;
}

void performExhaustivePTA(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict)
{

   auto setupStart = std::chrono::high_resolution_clock::now();

   std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> reanalyze;

   for (auto currentMethod : methodNameIDmapping)
   {

      if (methodPTG.find(currentMethod.second) == methodPTG.end())
      {
         methodPTG[currentMethod.second] = new PointsToGraph();
      }

      std::set<int> rootSet;
      for (const auto &stmt : stmtNumber[currentMethod.second])
      {
         std::unordered_set<int> varSlots;
         getVarSlots(stmt.second, comp, varSlots, currentMethod.second);

         for (auto slot : varSlots)
         {
            rootSet.insert(methodDict[currentMethod.second].lct.findRoot(slot));
            // std::cout<<"mm = "<<inverseMethodNameIDmapping[currentMethod.second]<<" slot = "<<slot<<" root = "<<methodDict[currentMethod.second].lct.findRoot(slot)<<"\n";
         }
      }

      rootSetMap[currentMethod.second] = rootSet;

      reanalyze[currentMethod.second].insert(rootSet.begin(), rootSet.end());

      if (currentMethod.first.find("Harness.main") != std::string::npos)
      {
         topLevelMethods.insert(currentMethod.second);
      }
   }

   auto setupEnd = std::chrono::high_resolution_clock::now();

   auto fixpointStart = std::chrono::high_resolution_clock::now();

   performPTA(comp, methodDict, reanalyze);

   auto fixpointEnd = std::chrono::high_resolution_clock::now();

   auto setupDurationMicro = std::chrono::duration_cast<std::chrono::microseconds>(setupEnd - setupStart);

   auto fixpointDurationMicro = std::chrono::duration_cast<std::chrono::microseconds>(fixpointEnd - fixpointStart);

   auto setupDurationSec = std::chrono::duration_cast<std::chrono::seconds>(setupEnd - setupStart);

   auto fixpointDurationSec = std::chrono::duration_cast<std::chrono::seconds>(fixpointEnd - fixpointStart);

   std::cout << "Time for setup = " << setupDurationMicro.count() << "   seconds = " << setupDurationSec.count() << "\n";

   std::cout << "Time for fixpoint = " << fixpointDurationMicro.count() << "   seconds = " << fixpointDurationSec.count() << "\n";
}

void performPTA(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict, std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &reanalyze)
{

   UniqueDeque<TR_OpaqueMethodBlock *> workList;
   std::unordered_set<TR_OpaqueMethodBlock *> analyzedAtLeastOnce;
   workList.insert(topLevelMethods.begin(), topLevelMethods.end());
   while (!workList.empty())
   {
      TR_OpaqueMethodBlock *currentMethod = workList.front();
      analyzedAtLeastOnce.insert(currentMethod);
      workList.pop_front();

      TR_ResolvedMethod *tempRm = getCachedResolvedMethodFromPtr(comp, currentMethod);

      // iterate over roots

      // move inside while loop if removing bruteforce
      std::set<int> processStmtSet;

      // //todo - omkar - make reanalyze <method, deque<int>>
      while (!reanalyze[currentMethod].empty())
      {
         while (!reanalyze[currentMethod].empty())
         {
            int currentRoot = reanalyze[currentMethod].front();
            reanalyze[currentMethod].pop_front();
            // get all variabls of same group

            if (debugFlag)
            {
               std::cout << "processing currentMethod = " << inverseMethodNameIDmapping[currentMethod] << "\n";
            }

            std::unordered_set<int> varSet = msetDict[currentMethod].lct.getAllChildVars(currentRoot);

            if (debugFlag)
            {
               std::cout << "current root = " << currentRoot << "\n";
            }

            for (auto var : varSet)
            {
               if (debugFlag)
               {
                  std::cout << "process var is " << var << "\n";
               }
               for (auto stmt : msetDict[currentMethod].stmtMap[var])
               {
                  if (debugFlag)
                  {
                     std::cout << "process sn is " << stmt << "\n";
                  }
                  processStmtSet.insert(stmt);
               }
               if (inverseMethodNameIDmapping[currentMethod].find("Harness.main([Ljava/lang/String;)V") != std::string::npos && var == 417)
               {
                  methodPTG[currentMethod]->extend(417, PointsToGraph::nullEntry);
               }
            }
         }

         // if(!bruteForce){
         // do fix point computation on group
         // bool flag = true;
         // while (flag)
         // {
         //    flag = false;
         //    for(auto stmt: processStmtSet){
         //       TR::Node* stmtNode = stmtNumber[currentMethod][stmt];
         //       Counter counter(stmtNode->getVisitCount() + 1, -10);
         //       processNode(stmtNode, currentMethod, comp, counter, workList, reanalyze, flag, msetDict);
         //    }

         // }
         // }

         // if(bruteForce){
         // do fix point computation on group
         bool flag = true;
         while (flag)
         {
            flag = false;
            std::unordered_set<TR::Node *> nodeVisited;
            for (auto stmt : processStmtSet)
            {
               TR::Node *stmtNode = stmtNumber[currentMethod][stmt];
               Counter counter(stmtNode->getVisitCount() + 1, -10);
               if (debugFlag)
               {
                  std::cout << "process stmtnode = " << stmtNode << " with stmt no = " << stmt << "\n";
               }

               processNode(stmtNode, currentMethod, comp, counter, workList, reanalyze, flag, msetDict, nodeVisited);
            }
         }
         // }
      }

      bool bruteForceAdded = false;
      // handling reachable heap from args
      for (auto arg : methodPTG[currentMethod]->getArgs())
      {
         std::vector<Entry *> tempWorklist;
         std::set<Entry *> tempVisited;
         tempWorklist.insert(tempWorklist.end(), arg.second.begin(), arg.second.end());
         tempVisited.insert(arg.second.begin(), arg.second.end());

         if (methodPTGout.find(currentMethod) == methodPTGout.end() || methodPTGout[currentMethod]->compareHeap(tempWorklist, tempVisited, methodPTG[currentMethod]))
         {
            if (bruteForce)
            {
               std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<TR::Node *>> callNodeSet = myInverseCallGraph[currentMethod];
               for (auto m : callNodeSet)
               {
                  for (auto root : rootSetMap[m.first])
                  {
                     reanalyze[m.first].push_back(root);
                  }
                  workList.push_back(m.first);
               }
               bruteForceAdded = true;
               break;
            }
            else
            {
               std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<TR::Node *>> callNodeSet = myInverseCallGraph[currentMethod];
               for (auto m : callNodeSet)
               {
                  for (auto callNode : callNodeSet[m.first])
                  {
                     int symRef = inverseArgCallNode[m.first][callNode][arg.first];
                     int rootSymRef = msetDict[m.first].lct.findRoot(symRef);
                     reanalyze[m.first].push_back(rootSymRef);
                     if (debugFlag)
                     {
                        std::cout << "process currentMethod = " << inverseMethodNameIDmapping[currentMethod] << " caller = " << inverseMethodNameIDmapping[m.first] << " root = " << symRef << " agindex = " << arg.first << "\n";
                     }
                  }

                  workList.push_back(m.first);
               }
            }
         }
      }

      if (tempRm->returnType() == TR::Address)
      {
         std::vector<Entry *> tempWorklist;
         std::set<Entry *> tempVisited;
         if (methodPTG[currentMethod]->contains(-3))
         {
            tempWorklist.insert(tempWorklist.end(), methodPTG[currentMethod]->getReturnPointsTo().begin(), methodPTG[currentMethod]->getReturnPointsTo().end());
            tempVisited.insert(methodPTG[currentMethod]->getReturnPointsTo().begin(), methodPTG[currentMethod]->getReturnPointsTo().end());
         }

         int oldSize = 0, newSize = 0;
         if (methodPTGout.find(currentMethod) != methodPTGout.end() && methodPTGout[currentMethod]->contains(-3))
         {
            oldSize = methodPTGout[currentMethod]->getReturnPointsTo().size();
         }
         if (methodPTG[currentMethod]->contains(-3))
         {
            newSize = methodPTG[currentMethod]->getReturnPointsTo().size();
         }

         if (methodPTGout.find(currentMethod) == methodPTGout.end() || oldSize < newSize || methodPTGout[currentMethod]->compareHeap(tempWorklist, tempVisited, methodPTG[currentMethod]))
         {
            for (auto m : myInverseCallGraph[currentMethod])
            {
               for (auto callNode : m.second)
               {
                  int symRef = inverseArgCallNode[m.first][callNode][-3];
                  int rootSymRef = msetDict[m.first].lct.findRoot(symRef);
                  reanalyze[m.first].push_back(rootSymRef);
                  if (debugFlag)
                  {
                     std::cout << "ret process currentMethod = " << inverseMethodNameIDmapping[currentMethod] << " caller = " << inverseMethodNameIDmapping[m.first] << " root = " << rootSymRef << " symref = " << symRef << "\n";
                  }
               }

               workList.push_back(m.first);
            }
         }
      }

      if (methodPTGout.find(currentMethod) != methodPTGout.end())
      {
         delete (methodPTGout[currentMethod]);
      }
      methodPTGout[currentMethod] = new PointsToGraph(*methodPTG[currentMethod]);

      // if(inverseMethodNameIDmapping[currentMethod].find("org/sunflow/Benchmark$BenchmarkScene.buildCornellBox()V") != std::string::npos){
      //    std::cout<<"debug print = "<<inverseMethodNameIDmapping[currentMethod]<<"\n";
      //    methodPTG[currentMethod]->print();
      // }
      // if(inverseMethodNameIDmapping[currentMethod].find("org/sunflow/core/renderer/BucketRenderer.access$300(Lorg/sunflow/core/renderer/BucketRenderer;Lorg/sunflow/core/Display;IIILorg/sunflow/core/IntersectionState;") != std::string::npos){
      //    std::cout<<"debug print = "<<inverseMethodNameIDmapping[currentMethod]<<"\n";
      //    methodPTG[currentMethod]->print();
      // }
      // if(inverseMethodNameIDmapping[currentMethod].find("org/sunflow/core/renderer/BucketRenderer.renderBucket(Lorg/sunflow/core/Display;IIILorg/sunflow/core/IntersectionState;)V") != std::string::npos){
      //    std::cout<<"debug print = "<<inverseMethodNameIDmapping[currentMethod]<<"\n";
      //    methodPTG[currentMethod]->print();
      // }
   }
}

std::set<Entry *> processNode(TR::Node *node, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp, Counter &counter,
                              UniqueDeque<TR_OpaqueMethodBlock *> &workList, std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &reanalyze,
                              bool &flag, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict, std::unordered_set<TR::Node *> &nodeVisited)
{

   // stores points to info for current node
   std::set<Entry *> evaluatedValues;

   // get useful node
   TR::Node *usefulNode = getUsefulNode(node);

   // if no useful node then return empty pts
   if (!usefulNode)
   {
      return evaluatedValues;
   }

   // if(currentMethod == monitor5 && !stopFlag){
   //    std::map <Entry*, std::map <string, set  <Entry*> > > ss2 = methodPTG[currentMethod]->getSigma();
   //    for(auto tt: ss2){
   //       if(tt.first->caller == 127 && tt.first->bci == 12){
   //          for(auto gg: tt.second){
   //             if(gg.first.find("filter") != std::string::npos){
   //                if(gg.second.find(PointsToGraph::bottomEntry) != gg.second.end()){
   //                   std::cout<<"prev inst resp for bot mon1\n";
   //                   stopFlag = true;
   //                }
   //             }
   //          }
   //       }
   //    }
   // }

   // std::set <Entry*> rr = methodPTG[monitor1]->getReturnPointsTo();
   // if(rr.find(PointsToGraph::bottomEntry) != rr.end()){
   //    std::cout<<"prev inst resp for str\n";
   // }

   // // safety check
   // if(methodPTG[currentMethod] == NULL){
   //    std::cout<<"ERROR: PTG must not be null\n";
   //    methodPTG[currentMethod] = new PointsToGraph();
   // }

   // the node's been visited before - fetch its evaluated value

   if (nodeVisited.find(usefulNode) != nodeVisited.end())
   {
      // std::cout<<"seen processing node = "<<usefulNode<<"\n";
      return cachedValues[usefulNode];
   }

   // std::cout<<"processing node = "<<usefulNode<<"\n";

   nodeVisited.insert(usefulNode);

   TR::ILOpCodes opCode = usefulNode->getOpCodeValue();

   switch (opCode)
   {

   case TR::checkcast:
   {
      std::set<Entry *> afterCast;

      // fetch pts-to info of child
      evaluatedValues = processNode(usefulNode->getFirstChild(), currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

      // get class
      TR_OpaqueClassBlock *tpSym = (TR_OpaqueClassBlock *)usefulNode->getSecondChild()->getSymbol()->castToStaticSymbol()->getStaticAddress();

      if (tpSym != NULL)
      {
         // if class not null then do type check to refine pts info
         for (auto e : evaluatedValues)
         {
            if (canCast(e, tpSym, comp))
            {
               afterCast.insert(e);
            }
         }
      }
      else
      {
         // std::cout<<"cannot fetch type cast class "<<usefulNode<<"\n";
         afterCast.insert(evaluatedValues.begin(), evaluatedValues.end());
      }

      evaluatedValues = afterCast;
      break;
   }

   case TR::aconst:
   {
      evaluatedValues.insert(PointsToGraph::nullEntry);

      break;
   }

   case TR::aladd:
   {
      evaluatedValues.insert(PointsToGraph::bottomEntry);
      break;
   }

   case TR::New:
   {
      Entry *e = evaluateAllocate(usefulNode, methodPtrToIndex[currentMethod], 0);

      if (e->clazz == NULL)
      {
         // e = PointsToGraph::bottomEntry;
         std::cout << "class null for " << e->caller << "-" << e->bci << "\n";
      }
      else
      {

         if (exhaustive)
         {
            if (cachedClassSignature.find(e->clazz) == cachedClassSignature.end())
            {
               cachedClassSignature[e->clazz] = TR::Compiler->cls.classSignature(comp, e->clazz, comp->trMemory());
            }
         }

         // check if class name contains string
         std::string className = cachedClassSignature[e->clazz];
         if (className.find("Ljava/lang/String;") != std::string::npos)
         {
            evaluatedValues.insert(PointsToGraph::stringEntry);
         }
         else
         {
            evaluatedValues.insert(e);
         }
      }

      break;
   }

   case TR::newarray:
   {
      Entry *e = evaluateAllocate(usefulNode, methodPtrToIndex[currentMethod], 2);

      evaluatedValues.insert(e);
      break;
   }

   case TR::anewarray:
   {
      Entry *e = evaluateAllocate(usefulNode, methodPtrToIndex[currentMethod], 1);

      if (usefulNode->getSecondChild()->getOpCodeValue() == TR::loadaddr)
      {
         if (e->clazz == NULL)
         {
            // e = PointsToGraph::bottomEntry;
            std::cout << "class null for " << e->caller << "-" << e->bci << "\n";
         }
         else
         {
            evaluatedValues.insert(e);
         }
      }
      else
      {
         evaluatedValues.insert(e);
      }

      break;
   }

   case TR::multianewarray:
   {
      evaluatedValues.insert(PointsToGraph::bottomEntry);
      break;
   }

   case TR::astore:
   {
      // get rhs node
      TR::Node *storeChild = usefulNode->getFirstChild();

      // get pts-to for rhs
      evaluatedValues = processNode(storeChild, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

      // get lhs var
      int storeSymRef = usefulNode->getSymbolReference()->getReferenceNumber();

      // update pts of lhs
      bool update = methodPTG[currentMethod]->extend(storeSymRef, evaluatedValues);

      // if pts changed then set the flag
      if (update)
      {
         flag = true;
      }

      break;
   }

   case TR::aload:
   {
      bool isStaticFieldRead = usefulNode->getSymbol()->isStaticField();

      if (isStaticFieldRead)
      {

         evaluatedValues.insert(PointsToGraph::bottomEntry);
      }
      else
      {
         TR::SymbolReference *symRef = usefulNode->getSymbolReference();
         if (symRef->getSymbol()->getKind() == TR::Symbol::IsMethodMetaData)
         {
            std::string loadName = comp->getDebug()->getMetaDataName(usefulNode->getSymbolReference());
            if (loadName.find("ExceptionMeta") != std::string::npos)
            {
               evaluatedValues.insert(PointsToGraph::bottomEntry);
            }
         }
         else if (symRef->getSymbol()->castToStaticSymbol()->isConstString())
         {

            int loadSymRef = symRef->getReferenceNumber();
            methodPTG[currentMethod]->extend(loadSymRef, PointsToGraph::stringEntry);
            evaluatedValues.insert(PointsToGraph::stringEntry);
         }
         else
         {
            int loadSymRef = symRef->getReferenceNumber();

            set<Entry *> pointsToSet = methodPTG[currentMethod]->getPointsToSet(loadSymRef);
            evaluatedValues.insert(pointsToSet.begin(), pointsToSet.end());
         }
      }

      break;
   }

   case TR::aloadi:
   {

      // std::cout<<"rec node is "<<receiverNode<<"\n";

      string field;

      if (usefulNode->getSymbol()->isArrayShadowSymbol())
      {
         TR::Node *receiverNode = usefulNode->getFirstChild()->getFirstChild();
         // std::cout<<"aloadi = "<<receiverNode<<" "<<usefulNode->getFirstChild()<<"\n";
         std::set<Entry *> receiverNodeVals = processNode(receiverNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);
         field = "_$";
         for (auto receiver : receiverNodeVals)
         {
            set<Entry *> rhsPointees = methodPTG[currentMethod]->getPointsToSet(receiver, field);
            evaluatedValues.insert(rhsPointees.begin(), rhsPointees.end());
         }
      }
      else
      {

         TR::SymbolReference *symRef = usefulNode->getSymbolReference();
         bool isUnresolved = symRef->isUnresolved();

         bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;

         int cpIndex = symRef->getCPIndex();
         if (isShadow && cpIndex > 0)
         {
            TR::Node *receiverNode = usefulNode->getFirstChild();

            std::set<Entry *> receiverNodeVals = processNode(receiverNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);
            int32_t len;
            const char *fieldName = usefulNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(usefulNode->getSymbolReference()->getCPIndex(), len);
            field.assign(fieldName, fieldName + len);
            for (auto receiver : receiverNodeVals)
            {
               set<Entry *> rhsPointees = methodPTG[currentMethod]->getPointsToSet(receiver, field);

               evaluatedValues.insert(rhsPointees.begin(), rhsPointees.end());
            }
         }
      }
      break;
   }

   case TR::awrtbar:
   {

      bool isStatic = usefulNode->getSymbol()->isStatic();
      TR_ASSERT_FATAL(isStatic, "found an awrtbar node that isn't Static!");

      TR::Node *storeNode = usefulNode->getFirstChild();
      evaluatedValues = processNode(storeNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

      for (auto pointee : evaluatedValues)
      {

         if (pointee == PointsToGraph::nullEntry || pointee == PointsToGraph::bottomEntry)
            continue;

         methodPTG[currentMethod]->summarizeReachableHeap(pointee);
      }
      break;
   }

   case TR::awrtbari:
   {
      bool mustSummarize = false;

      TR::SymbolReference *symRef = usefulNode->getSymbolReference();

      bool isUnresolved = symRef->isUnresolved();

      bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;

      int cpIndex = symRef->getCPIndex();

      if (usefulNode->getSymbol()->isArrayShadowSymbol())
      {

         TR::Node *valueNode = usefulNode->getSecondChild();
         if (valueNode->getDataType() == TR::Address)
         {

            TR::Node *receiverNode = usefulNode->getThirdChild();

            set<Entry *> receiverNodeVals = processNode(receiverNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

            evaluatedValues = processNode(valueNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

            std::string field = "_$";
            for (auto receiver : receiverNodeVals)
            {
               if (methodPTG[currentMethod]->getSigma().find(receiver) == methodPTG[currentMethod]->getSigma().end())
               {
                  std::cout << "rec not present" << "\n";
               }
               if (receiver == PointsToGraph::bottomEntry)
               {
                  mustSummarize = true;
               }

               bool update = methodPTG[currentMethod]->extend(receiver, field, evaluatedValues);

               if (update)
               {
                  flag = true;
               }
            }
         }
      }
      else if (isShadow && cpIndex > 0)
      {

         TR::Node *valueNode = usefulNode->getSecondChild();

         TR::Node *receiverNode = usefulNode->getFirstChild();

         set<Entry *> receiverNodeVals = processNode(receiverNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

         evaluatedValues = processNode(valueNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

         std::string field;

         int32_t len;

         const char *fieldName = usefulNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(usefulNode->getSymbolReference()->getCPIndex(), len);

         field.assign(fieldName, fieldName + len);

         if (valueNode->getDataType() == TR::Address)
         {
            for (auto receiver : receiverNodeVals)
            {
               if (methodPTG[currentMethod]->getSigma().find(receiver) == methodPTG[currentMethod]->getSigma().end())
               {
                  std::cout << "rec not present"
                            << "\n";
               }

               if (receiver == PointsToGraph::bottomEntry)
               {
                  mustSummarize = true;
               }

               bool update = methodPTG[currentMethod]->extend(receiver, field, evaluatedValues);

               if (update)
               {
                  flag = true;
               }
            }
         }
      }
      if (mustSummarize)
      {
         for (auto val : evaluatedValues)
         {
            methodPTG[currentMethod]->summarizeReachableHeap(val);
         }
      }
      break;
   }

   case TR::icalli:
   // case TR::vcalli:
   case TR::lcalli:
   case TR::fcalli:
   case TR::dcalli:
   case TR::acalli:
   case TR::calli:
   case TR::icall:
   case TR::lcall:
   case TR::fcall:
   case TR::dcall:
   case TR::acall:
   case TR::call:
   case TR::vcall:
   { // b1

      std::unordered_set<TR_OpaqueMethodBlock *> methodsToPeek;

      bool isHelperMethodCall = usefulNode->getSymbol()->castToMethodSymbol()->isHelper();

      // we do not want to process helper method calls (prepareForOSR, potentialOSRPointHelper, for example)
      if (isHelperMethodCall)
      {
         break;
      }
      else
      { // b2

         std::string methodName = cachedMethodName[usefulNode];
         // std::cout<<"method name is "<<methodName<<"\n";

         if (isLibraryMethod(methodName) && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
         { // b3

            if (((std::string)methodName).find(")Ljava/lang/String;") != std::string::npos)
            {
               evaluatedValues.insert(PointsToGraph::stringEntry);
            }
            else if (((std::string)methodName).find(")Ljava/lang/Class;") != std::string::npos)
            {
               evaluatedValues.insert(PointsToGraph::classEntry);
            }
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0)
            {
               evaluatedValues.insert(PointsToGraph::bottomEntry);
            }

            if (((std::string)methodName).find("java/lang/Thread.<init>(Ljava/lang/Runnable;)V") != std::string::npos)
            {
               // std::cout<<"first child of thread is "<<usefulNode->getFirstChild()<<"\n";

               std::set<Entry *> secChild = processNode(usefulNode->getSecondChild(), currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);
               for (auto pointee : secChild)
               {
                  methodPTG[currentMethod]->summarizeReachableHeap(pointee);
               }

               // this is superuseful bcoz it sets pts of thread obj to pts of runnable. When thread obj is accessed, this short-circuit will give correct pts
               cachedValues[usefulNode->getFirstChild()] = secChild;
               usefulNode->getFirstChild()->setVisitCount(counter.visitCount);
            }
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0 && ((std::string)methodName).find("<init>") == std::string::npos)
            {

               bool isStatic = usefulNode->getSymbol()->castToMethodSymbol()->isStatic();
               int argIndex = 0;
               if (isStatic)
               {
                  argIndex = 1;
               }

               int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
               int32_t numChildren = usefulNode->getNumChildren();

               for (int32_t i = firstArgIndex; i < numChildren; i++)
               {

                  if (usefulNode->getChild(i)->getDataType() == TR::Address)
                  {
                     std::set<Entry *> argPt = processNode(usefulNode->getChild(i), currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);
                     // methodPTG[currentMethod]->extend(argToSymRef[target][argIndex], processNode(getUsefulNode(usefulNode->getChild(i)), methodIndex, currentMethod, comp, worklist, counter, cachedValues));
                     for (auto pointee : argPt)
                     {
                        methodPTG[currentMethod]->summarizeReachableHeap(pointee);
                     }
                  }

                  argIndex++;
               }
            }

         } // b3
         else
         { // b4

            int callsiteBCI = usefulNode->getByteCodeIndex();
            bool isInterfaceInvoke = usefulNode->getSymbol()->castToMethodSymbol()->isInterface();
            if (isInterfaceInvoke)
            {
               callsiteBCI -= 2;
            }

            bool isStatic = usefulNode->getSymbol()->castToMethodSymbol()->isStatic();

            int methodNameLength = usefulNode->getSymbol()->castToMethodSymbol()->getMethod()->nameLength();

            int mClazzlen = usefulNode->getSymbol()->castToMethodSymbol()->getMethod()->classNameLength();

            std::string mClazzChars = usefulNode->getSymbol()->castToMethodSymbol()->getMethod()->classNameChars();

            std::string mClazzName = mClazzChars.substr(0, mClazzlen);

            TR_OpaqueClassBlock *mClazz = comp->fe()->getClassFromSignature(mClazzName.c_str(), mClazzlen, comp->getCurrentMethod());
            // fetch target method signature

            int sigLength = usefulNode->getSymbol()->castToMethodSymbol()->getMethod()->signatureLength();

            std::string signatureChars = usefulNode->getSymbol()->castToMethodSymbol()->getMethod()->signatureChars();

            std::string sig = signatureChars.substr(0, sigLength);

            std::string methodNm;

            if (mClazz == NULL && !isLibraryMethod(methodName))
            {

               std::cout << "mclazz is null for " << usefulNode << "\n";
            }
            else if (isStatic)
            { // b5

               TR::ResolvedMethodSymbol *callNodeSymbol;
               if (usefulNode->getSymbolReference()->isUnresolved())
               {
                  std::string methodNm = usefulNode->getSymbol()->castToMethodSymbol()->getMethod()->nameChars();
                  methodNm = methodNm.substr(0, methodNameLength);
                  TR_ResolvedMethod *yp = getCachedResolvedMethod(comp, mClazz, methodNm.c_str(), sig.c_str());

                  callNodeSymbol = yp->findOrCreateJittedMethodSymbol(comp);
               }
               else
               {
                  callNodeSymbol = usefulNode->getSymbol()->getResolvedMethodSymbol();
               }

               methodsToPeek.insert(callNodeSymbol->getResolvedMethod()->getPersistentIdentifier());
            } // b5
            else
            { // b6

               TR::Node *receiverNode = usefulNode->getFirstArgument();

               set<Entry *> receiverVals = processNode(receiverNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

               if (!usefulNode->getSymbolReference()->isUnresolved() && !isInterfaceInvoke && usefulNode->getSymbol()->getResolvedMethodSymbol()->getResolvedMethod()->getPersistentIdentifier() == _threadStartPersistentId)
               {
                  methodNm = "run";
                  // std::cout << "short-circuit Thread.start with  .run()\n";
               }
               else
               {
                  methodNm = usefulNode->getSymbol()->castToMethodSymbol()->getMethod()->nameChars();

                  methodNm = methodNm.substr(0, methodNameLength);
               }

               // if(methodNm.find("<init>") != std::string::npos && cmName.find("<init>") != std::string::npos){

               if (usefulNode->getSymbolReference()->getSymbol()->castToMethodSymbol()->getMethodKind() == TR::MethodSymbol::Special && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
               {
                  // std::cout<<"method name in b6 = "<<methodName<<"\n";

                  TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, mClazz, methodNm.c_str(), sig.c_str());
                  TR_ASSERT_FATAL(targetMethod, "target method for init not found");
                  if (classPtrToIndex[mClazz] == 0)
                  {
                     // std::cout<<"didid 8 = "<<methodName<<"\n";
                  }
                  _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[mClazz]);
                  methodsToPeek.insert(targetMethod->getPersistentIdentifier());
               }
               else if (receiverVals.find(PointsToGraph::bottomEntry) == receiverVals.end() && (methodName.find("java/lang/Object.<init>") == std::string::npos || receiverNode->getSymbolReference()->getSymbol()->getKind() != TR::Symbol::IsParameter || receiverNode->getSymbolReference()->getCPIndex() != 0))
               { // b7

                  // std::cout<<"method name in b7 = "<<methodName<<"\n";

                  for (auto rec : receiverVals)
                  {
                     TR_OpaqueClassBlock *clazz = rec->clazz;

                     if (rec->type == Null || rec->type == PrimitiveArray || rec->type == RefArray || rec->type == String)
                     {
                        continue;
                     }

                     TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, clazz, methodNm.c_str(), sig.c_str());

                     if (targetMethod == NULL)
                     {
                        // std::cout<<"method resolved based on static type " + methodNm + sig.c_str() + " \n";
                        targetMethod = getCachedResolvedMethod(comp, mClazz, methodNm.c_str(), sig.c_str());
                        if (targetMethod != NULL && exhaustive)
                        {
                           if (classPtrToIndex[mClazz] == 0)
                           {
                              // std::cout<<"didid 5 = "<<methodName<<"\n";
                           }
                           _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[mClazz]);
                        }
                     }
                     else
                     {
                        if (exhaustive)
                        {
                           if (classPtrToIndex[clazz] != 0)
                           {
                              _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[clazz]);
                           }
                        }
                     }

                     if (targetMethod == NULL)
                     {
                        std::cout << "didn't expect " << usefulNode << "\n";
                        int classNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameLength();
                        string className = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameChars();
                        TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), classNameLength, comp->getCurrentMethod());

                        std::queue<TR_OpaqueClassBlock *> bfsList;
                        std::unordered_set<TR_OpaqueClassBlock *> visitedClass;
                        bfsList.push(type);
                        visitedClass.insert(type);

                        // std::string tpName = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());

                        while (!bfsList.empty())
                        {
                           TR_OpaqueClassBlock *currentClass = bfsList.front();
                           bfsList.pop();
                           // char* currchild = TR::Compiler->cls.classSignature(comp, currentClass, comp->trMemory());

                           TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, currentClass, methodNm.c_str(), sig.c_str());
                           if (targetMethod != NULL && !targetMethod->isAbstract())
                           { //! TR::Compiler->cls.isInterfaceClass(comp, currentClass)){
                              // std::cout<<"targetMethod in CHA is null\n";
                              if (exhaustive)
                              {
                                 if (classPtrToIndex[currentClass] == 0)
                                 {
                                    // std::cout<<"didid 7 = "<<methodName<<"\n";
                                 }
                                 _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[currentClass]);
                              }
                              methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                           }

                           for (auto rec : CHA[currentClass])
                           {
                              // std::string child = TR::Compiler->cls.classSignature(comp, rec, comp->trMemory());

                              if (visitedClass.find(rec) == visitedClass.end())
                              {
                                 // std::cout<<"adding to bfs\n";
                                 visitedClass.insert(rec);
                                 bfsList.push(rec);
                              }
                           }
                        }
                     } //
                     else
                     {

                        TR_ASSERT_FATAL(targetMethod, "unable to find method for name and signature %s %s", methodNm.c_str(), sig.c_str());
                        // std::cout<<"here 8.5 \n";
                        // std::cout<<"here 8.5 "<<((std::string)(targetMethod->nameChars())).substr(0,targetMethod->nameLength())<<"\n";
                        methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                     }
                  }
               } // b7
               else if (methodName.find("java/lang/Object.<init>") == std::string::npos)
               {

                  // std::cout<<"method name in b8 = "<<methodName<<"\n";

                  int classNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameLength();
                  string className = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameChars();
                  TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), classNameLength, comp->getCurrentMethod());
                  TR_ASSERT_FATAL(type, "why is type null here");

                  std::queue<TR_OpaqueClassBlock *> bfsList;
                  std::unordered_set<TR_OpaqueClassBlock *> visitedClass;
                  bfsList.push(type);
                  visitedClass.insert(type);

                  // std::string tpName = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());

                  while (!bfsList.empty())
                  {
                     TR_OpaqueClassBlock *currentClass = bfsList.front();
                     bfsList.pop();

                     TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, currentClass, methodNm.c_str(), sig.c_str());

                     if (targetMethod != NULL && !targetMethod->isAbstract())
                     { //&& !TR::Compiler->cls.isInterfaceClass(comp, currentClass)){

                        if (exhaustive)
                        {
                           if (classPtrToIndex[currentClass] != 0)
                           {
                              // std::cout<<"didid 8 = "<<methodName<<"\n";
                              _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[currentClass]);
                           }
                        }

                        methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                     }

                     for (auto rec : CHA[currentClass])
                     {
                        if (visitedClass.find(rec) == visitedClass.end())
                        {
                           visitedClass.insert(rec);
                           bfsList.push(rec);
                        }
                     }
                  }
               }

               // std::cout<<"method name in b9 = "<<methodName<<"\n";

            } // b6 end handling non-statics

            if (methodsToPeek.size() == 0)
            {
               // std::cout << "WARNING - no resolved targets for callsitebci " << callsiteBCI << " caller " << methodPtrToIndex[currentMethod] << "\n";

               // methodPTG[currentMethod]->print();
               // std::cout<<"methods to peek empty\n";
            }
            else
            {

               PointsToGraph *callSitePtg = buildCallsitePtg(usefulNode, methodPTG[currentMethod], currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

               if (callSitePtg == NULL)
               {
                  std::cout << "!!!!!!! ptg null\n";
               }

               if (callSiteStore.find(usefulNode) == callSiteStore.end() || !(callSitePtg->equals(callSiteStore[usefulNode])))
               { // b8

                  // std::cout<<"callste ptg updated\n";

                  if (callSiteStore.find(usefulNode) != callSiteStore.end())
                  {
                     delete (callSiteStore[usefulNode]);
                  }
                  callSiteStore[usefulNode] = new PointsToGraph(*callSitePtg);

                  for (auto target : methodsToPeek)
                  { // b9

                     if (methodPTG.find(target) == methodPTG.end())
                     {
                        methodPTG[target] = new PointsToGraph();
                     }

                     if (_methodsAnalyzed.find(target) == _methodsAnalyzed.end())
                     {
                        _methodsAnalyzed.insert(target);

                        TR_ResolvedMethod *calleeMethod = getCachedResolvedMethodFromPtr(comp, target);
                        TR::ResolvedMethodSymbol *actCalleeSymbol = calleeMethod->findOrCreateJittedMethodSymbol(comp);
                        bool ilGenFailed = NULL == calleeMethod->genMethodILForPeekingEvenUnderMethodRedefinition(actCalleeSymbol, comp, false);
                        TR_ASSERT_FATAL(!ilGenFailed, "IL Gen failed, cannot peek into method");
                        comp->dumpMethodTrees("Method tree about to peek", actCalleeSymbol);
                        // todo - omkar - handle this properly - incomplete
                     }

                     myCallGraph[currentMethod][usefulNode].insert(target);
                     myCallGraphDelete[currentMethod][usefulNode].erase(target);

                     myInverseCallGraph[target][currentMethod].insert(usefulNode);
                     myInverseCallGraphDelete[target][currentMethod].erase(usefulNode);

                     std::set<Entry *> inArgEntries;
                     int argIndex = 0;

                     if (isStatic)
                     {
                        argIndex = 1;
                     }

                     TR_ResolvedMethod *tempRM = getCachedResolvedMethodFromPtr(comp, target);
                     TR_MethodParameterIterator *parIterator = tempRM->getParameterIterator(*comp);

                     int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
                     int32_t numChildren = usefulNode->getNumChildren();

                     bool targetArgUpdated = false;

                     for (int32_t i = firstArgIndex; i <= numChildren; i++, argIndex++)
                     {

                        std::set<Entry *> argEntries = processNode(usefulNode->getChild(i), currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);

                        std::set<Entry *> actEntries;
                        if (argEntries.size() == 0)
                        {
                           continue;
                        }
                        TR_OpaqueClassBlock *argtype;
                        if (cachedParameterType.find(target) != cachedParameterType.end() && cachedParameterType[target].find(argIndex) != cachedParameterType[target].end())
                        {
                           argtype = cachedParameterType[target][argIndex];
                        }
                        else
                        {
                           continue;
                        }

                        for (auto e : argEntries)
                        {
                           if (canCast(e, argtype, comp))
                           {
                              actEntries.insert(e);
                              inArgEntries.insert(e);
                           }
                        }

                        if (!actEntries.empty())
                        {
                           methodPTG[target]->extend(inverseFormalParMethod[target][argIndex], actEntries);
                           methodPTG[target]->extendArg(argIndex, actEntries);
                           int symRef = inverseFormalParMethod[target][argIndex];
                           int rootSymRef = methodDict[target].lct.findRoot(symRef);
                           reanalyze[target].push_back(rootSymRef);
                           // std::cout<<"reanalyze target "<<inverseMethodNameIDmapping[target]<<" for root = "<<rootSymRef<<"\n";
                           targetArgUpdated = true;
                        }

                        if (isStatic || i != firstArgIndex)
                        {
                           parIterator->advanceCursor();
                        }
                     }

                     if (usefulNode->getDataType() == TR::Address)
                     {
                        std::set<Entry *> retSet = getCachedPointsTo(usefulNode);
                        if (!retSet.empty())
                        {
                           inArgEntries.insert(retSet.begin(), retSet.end());
                           int rootSymRef = methodDict[target].lct.findRoot(-3);
                           reanalyze[target].push_back(rootSymRef);

                           targetArgUpdated = true;
                        }
                        int localRoot = methodDict[currentMethod].lct.findRoot(inverseArgCallNode[currentMethod][usefulNode][-3]);
                        reanalyze[currentMethod].push_back(localRoot);
                     }

                     // merging current with in of target

                     methodPTG[target]->mergeReachableHeapFrom(methodPTG[currentMethod], inArgEntries);

                     if (targetArgUpdated)
                     {

                        workList.push_back(target);
                        if (bruteForce)
                        {
                           for (auto root : rootSetMap[target])
                           {
                              reanalyze[target].push_back(root);
                           }
                        }
                     }

                     if (exhaustive && exhaustiveAnalyzed.find(target) == exhaustiveAnalyzed.end())
                     {
                        workList.push_back(target);
                     }
                  } // b9
               } // b8

               delete (callSitePtg);

               for (auto target : methodsToPeek)
               {

                  TR_ResolvedMethod *tempRM = getCachedResolvedMethodFromPtr(comp, target);
                  TR_MethodParameterIterator *parIterator = tempRM->getParameterIterator(*comp);

                  int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
                  int32_t numChildren = usefulNode->getNumChildren();

                  int argIndex = 0;
                  if (isStatic)
                  {
                     argIndex = 1;
                  }

                  for (int32_t i = firstArgIndex; i <= numChildren; i++, argIndex++)
                  {

                     std::set<Entry *> argEntries = processNode(usefulNode->getChild(i), currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);
                     std::set<Entry *> actEntries;

                     if (argEntries.size() == 0)
                     {
                        continue;
                     }
                     TR_OpaqueClassBlock *argtype;
                     if (cachedParameterType.find(target) != cachedParameterType.end() && cachedParameterType[target].find(argIndex) != cachedParameterType[target].end())
                     {
                        argtype = cachedParameterType[target][argIndex];
                     }
                     else
                     {
                        continue;
                     }

                     for (auto e : argEntries)
                     {
                        if (canCast(e, argtype, comp))
                        {
                           actEntries.insert(e);
                        }
                     }

                     bool update = false;
                     if (methodPTGout.find(target) != methodPTGout.end())
                     {
                        std::vector<Entry *> tempWorklist;
                        std::set<Entry *> tempVisited;
                        tempWorklist.insert(tempWorklist.end(), actEntries.begin(), actEntries.end());
                        tempVisited.insert(actEntries.begin(), actEntries.end());
                        if (callSiteStore[usefulNode]->compareHeap(tempWorklist, tempVisited, methodPTGout[target]))
                        {
                           methodPTG[currentMethod]->mergeReachableHeapFrom(methodPTGout[target], actEntries);
                           flag = true; // used for fixpoint
                           int localRoot = methodDict[currentMethod].lct.findRoot(inverseArgCallNode[currentMethod][usefulNode][argIndex]);
                           reanalyze[currentMethod].push_back(localRoot);
                        }
                     }

                     if (isStatic || i != firstArgIndex)
                     {
                        parIterator->advanceCursor();
                     }
                  }

                  if (usefulNode->getDataType() == TR::Address)
                  {

                     int oldSize = cachedValues[usefulNode].size();

                     if (methodPTGout.find(target) != methodPTGout.end() && methodPTGout[target]->contains(-3))
                     {
                        evaluatedValues.insert(methodPTGout[target]->getReturnPointsTo().begin(), methodPTGout[target]->getReturnPointsTo().end());
                     }

                     int newSize = evaluatedValues.size();
                     bool update1 = newSize > oldSize;
                     bool update2 = false;
                     if (methodPTGout.find(target) != methodPTGout.end() && methodPTGout[target]->contains(-3))
                     {
                        update2 = methodPTG[currentMethod]->mergeReachableHeapFromReturn(methodPTGout[target]);
                     }

                     if (update1 || update2)
                     {
                        int localRoot = methodDict[currentMethod].lct.findRoot(inverseArgCallNode[currentMethod][usefulNode][-3]);
                        reanalyze[currentMethod].push_back(localRoot);
                        // std::cout<<"adding root "<<localRoot<<" to current\n";
                        flag = true;
                     }
                  }
               }
            }

         } // b4 end not library method

      } // end NOT isHelper

      break;
   }

   case TR::Return:
   case TR::lreturn:
   case TR::ireturn:
   case TR::dreturn:
   case TR::freturn:
   case TR::areturn:
   case TR::vreturn:
   {
      // handle the return value. We use a magic number (-3) to represent the pseudo-symref of the return var
      // also, we only need to worry about the areturn. So why do we have the others here? Maybe want to process some cleanup
      //   actions on encountering a return op

      if (opCode == TR::areturn)
      {
         // the evaluated value of the first child (ie. the call node) will hold the respective call's return value - simply fetch and assign
         evaluatedValues = processNode(usefulNode->getFirstChild(), currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);
         if (!evaluatedValues.empty())
         {
            bool update = methodPTG[currentMethod]->extend(PointsToGraph::RETURNLOCAL, evaluatedValues);
            if (update)
            {
               flag = true;
            }
         }
      }
      break;
   }

   default:
   {
      //         TR_ASSERT_FATAL(true, "opcode %s not recognized", usefulNode->getOpCode().getName());
      break;
   }
   }

   cachedValues[usefulNode] = evaluatedValues;
   return evaluatedValues;
}

void performDelete(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &delStmt, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict)
{

   auto start1 = std::chrono::high_resolution_clock::now();

   DeleteInfo deleteInfo;

   deleteInit(comp, delStmt, msetDict, deleteInfo);

   std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<int>> affectedVars;
   findAffectedInfo(comp, msetDict, deleteInfo, affectedVars);

   // for(auto sd: deleteInfo.stackDelta){
   //    if(sd.second.size() > 0){
   //       std::cout<<"dirty method = "<<inverseMethodNameIDmapping[sd.first]<<"\n";
   //    }

   //    for(auto obj: sd.second){
   //       std::cout<<"stack dirty = "<<obj->getString()<<"\n";
   //    }
   // }
   // for(auto obj: deleteInfo.heapDelta){
   //    std::cout<<"heap dirty = "<<obj->getString()<<"\n";
   // }

   // deleting pts
   for (auto i : affectedVars)
   {

      TR_OpaqueMethodBlock *currentMethod = i.first;

      std::set<Entry *> objectsToBeDeleted;
      std::set_union(deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(objectsToBeDeleted, objectsToBeDeleted.end()));

      if (methodPTGout.find(currentMethod) != methodPTGout.end())
      {
         methodPTG[currentMethod]->deleteStartingFrom(i.second, objectsToBeDeleted);
         methodPTGout[currentMethod]->deleteStartingFrom(i.second, objectsToBeDeleted);
      }
      else
      {
         std::cout << "methodptg out missing for " << inverseMethodNameIDmapping[currentMethod] << "\n";
      }

      std::unordered_set<TR::Node *> nodeVisited;
      for (auto j : i.second)
      {
         if (deleteInfo.reanalyze[currentMethod].stmtMap.find(j) != deleteInfo.reanalyze[currentMethod].stmtMap.end())
         {
            for (auto sn : deleteInfo.reanalyze[currentMethod].stmtMap[j])
            {
               TR::Node *currentStmt = stmtNumber[currentMethod][sn];
               Counter counter(currentStmt->getVisitCount() + 1, -10);
               deletePointsToInfo(currentStmt, currentMethod, comp, counter, deleteInfo, nodeVisited);
            }
         }
      }
   }

   // updating lct of methods from which stmts were deleted
   for (auto i : delStmt)
   {
      if (deleteInfo.reanalyze.find(i.first) != deleteInfo.reanalyze.end())
      {
         deleteInfo.reanalyze[i.first] = msetDict[i.first];
      }
      methodPTG[i.first]->deleteVarInfoFromRho();
      methodPTGout[i.first]->deleteVarInfoFromRho();
   }

   auto end1 = std::chrono::high_resolution_clock::now();

   auto start2 = std::chrono::high_resolution_clock::now();
   performPTA(comp, deleteInfo.reanalyze, deleteInfo.workList);
   auto end2 = std::chrono::high_resolution_clock::now();

   std::chrono::duration<double> elapsed1 = end1 - start1;
   std::cout << "Time taken for delta compute: " << elapsed1.count() << " s\n";

   std::chrono::duration<double> elapsed2 = end2 - start2;
   std::cout << "Time taken for fixpoint: " << elapsed2.count() << " s\n";

   // deleting from other global datastructures
   updateGlobalDS();
}

void deleteInit(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &delStmt,
                std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict, DeleteInfo &deleteInfo)
{ // b1

   for (auto delM : delStmt)
   { // b2

      topLevelMethods.insert(delM.first);
      // newDeleteInfo.workList[currentMethod] = new UniqueDeque<int>();      // needed so that findaffected nodes can traverse through formal args

      std::unordered_set<int> evaluatedSymRef;

      for (auto delS : delM.second)
      { // b3

         TR::Node *stmtNode = stmtNumber[delM.first][delS];

         // std::cout<<"deleting stmt = "<<stmtNode<<"\n";

         TR::ILOpCodes opCode = stmtNode->getOpCodeValue();
         switch (opCode)
         { // b4
         case TR::awrtbar:
         {
            std::set<Entry *> rhsPts = getCachedPointsTo(stmtNode);
            addReachableBottomToDeleteMap(rhsPts, deleteInfo, delM.first);

            // static store, parent of rhs must be added to worklist.
            getVarSlots(stmtNode, comp, evaluatedSymRef, delM.first);

            break;
         }
         case TR::awrtbari:
         {
            bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;

            int cpIndex = symRef->getCPIndex();

            TR::Node *receiverNode;
            std::string field;
            if (stmtNode->getSymbol()->isArrayShadowSymbol())
            {
               receiverNode = stmtNode->getThirdChild();
               field = "_$";
            }
            else if (isShadow && cpIndex > 0)
            {
               receiverNode = stmtNode->getFirstChild();
               int32_t len;
               const char *fieldName = stmtNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(cpIndex, len);
               field.assign(fieldName, fieldName + len);
            }
            TR::Node *valueNode = stmtNode->getSecondChild();
            std::set<Entry *> recPts = getCachedPointsTo(receiverNode);
            std::set<Entry *> rhsPts = getCachedPointsTo(valueNode);

            for (auto rec : recPts)
            {
               if (rec == PointsToGraph::bottomEntry)
               {
                  addReachableBottomToDeleteMap(rhsPts, deleteInfo, delM.first);
               }
               else
               {
                  deleteInfo.deleteMap[rec][field].insert(rhsPts.begin(), rhsPts.end());
               }
            }

            getVarSlots(stmtNode, comp, evaluatedSymRef, delM.first);

            break;
         }
         case TR::icalli:
         // case TR::vcalli:
         case TR::lcalli:
         case TR::fcalli:
         case TR::dcalli:
         case TR::acalli:
         case TR::calli:
         case TR::icall:
         case TR::lcall:
         case TR::fcall:
         case TR::dcall:
         case TR::acall:
         case TR::call:
         case TR::vcall:
         {
            bool isHelperMethodCall = stmtNode->getSymbol()->castToMethodSymbol()->isHelper();
            // we do not want to process helper method calls (prepareForOSR, potentialOSRPointHelper, for example)
            if (isHelperMethodCall)
            {
               break;
            }
            else
            {
               std::string methodName = cachedMethodName[stmtNode];

               if (isLibraryMethod(methodName) && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
               {
                  if (((std::string)methodName).find("java/lang/Thread.<init>(Ljava/lang/Runnable;)V") != std::string::npos)
                  {
                     std::set<Entry *> rhsPts = getCachedPointsTo(stmtNode->getSecondChild())
                         addReachableBottomToDeleteMap(rhsPts, deleteInfo, delM.first);
                     std::unordered_set<int> varSlots;
                     getVarSlots(stmtNode, comp, evaluatedSymRef, delM.first);
                  }
                  else if (((std::string)methodName).rfind("java/lang/reflect/") != 0 && ((std::string)methodName).find("<init>") == std::string::npos)
                  {

                     int32_t firstArgIndex = stmtNode->getFirstArgumentIndex();
                     for (int32_t i = stmtNode->getNumChildren() - 1; i > firstArgIndex; --i)
                     {
                        TR::Node *child = stmtNode->getChild(i);
                        if (child->getDataType() == TR::Address)
                        {
                           std::set<Entry *> argPts = getCachedPointsTo(child);
                           addReachableBottomToDeleteMap(argPts, deleteInfo, delM.first);
                           std::unordered_set<int> varSlots;
                           getVarSlots(stmtNode, comp, varSlots, delM.first);
                        }
                     }
                  }
               }

               else
               {
                  getVarSlots(stmtNode, comp, evaluatedSymRef, delM.first);

                  bool isStatic = stmtNode->getSymbol()->castToMethodSymbol()->isStatic();

                  bool isCurrentMethodPartOfCycle = cyclicMethods.find(delM.first) != cyclicMethods.end();

                  for (TR_OpaqueMethodBlock *target : myCallGraph[delM.first][stmtNode])
                  {

                     // do not delete eagerly. Instead delete at the end after algo finishes
                     myCallGraphDelete[delM.first][stmtNode].insert(target);
                     myInverseCallGraphDelete[target][delM.first].insert(stmtNode);

                     // calculating Inflow
                     std::unordered_map<int, std::unordered_map<TR_OpaqueMethodBlock *, std::set<Entry *>>> inFlow;
                     for (auto caller : myInverseCallGraph[target])
                     {
                        if (caller.first != delM.first && (cyclicMethods.find(caller.first) == cyclicMethods.end() || cyclicMethods.find(delM.first) == cyclicMethods.end()))
                        {
                           for (auto callerNode : caller.second)
                           {
                              int argIndex = 0;
                              if (isStatic)
                              {
                                 argIndex = 1;
                              }
                              int32_t firstArgIndex = callerNode->getFirstArgumentIndex();
                              int32_t numChildren = callerNode->getNumChildren();
                              for (int32_t i = firstArgIndex; i < numChildren; i++, argIndex++)
                              {
                                 std::set<Entry *> argPointees = getCachedPointsTo(callerNode->getChild(i));

                                 TR_OpaqueClassBlock *argtype;
                                 if (cachedParameterType.find(caller.first) != cachedParameterType.end() && cachedParameterType[caller.first].find(argIndex) != cachedParameterType[caller.first].end())
                                 {
                                    argtype = cachedParameterType[caller.first][argIndex];
                                 }
                                 else
                                 {
                                    continue;
                                 }

                                 for (auto e : argPointees)
                                 {
                                    if (canCast(e, argtype, comp))
                                    {
                                       inFlow[argIndex][caller.first].insert(e);
                                    }
                                 }
                              }
                           }
                        }
                     }

                     int32_t firstArgIndex = stmtNode->getFirstArgumentIndex();
                     int32_t numChildren = stmtNode->getNumChildren();
                     int argIndex = 0;
                     TR_MethodParameterIterator *parIterator;

                     if (isStatic)
                     {
                        argIndex = 1;
                     }

                     for (int32_t i = firstArgIndex; i < numChildren; i++, argIndex++)
                     {
                        // std::cout<<"is par end = "<<parIterator->getOpaqueClass()<<"\n";
                        std::set<Entry *> currentFlow;

                        std::set<Entry *> argPointees = getCachedPointsTo(stmtNode->getChild(i));

                        TR_OpaqueClassBlock *argtype;
                        if (cachedParameterType.find(target) != cachedParameterType.end() && cachedParameterType[target].find(argIndex) != cachedParameterType[target].end())
                        {
                           argtype = cachedParameterType[target][argIndex];
                        }
                        else
                        {
                           continue;
                        }

                        std::set<Entry *> actEntries;
                        std::set<Entry *> unreachableObjects;

                        for (auto e : argPointees)
                        {
                           if (canCast(e, argtype, comp))
                           {
                              actEntries.insert(e);
                              unreachableObjects.insert(e);
                              currentFlow.insert(e);
                           }
                        }

                        unreachableObjects = methodPTG[currentMethod]->getReachable(unreachableObjects);

                        std::unordered_map<int, std::set<Entry *>> visited;
                        bool updated = calculateDirtyObjects(argIndex, delM.first, currentFlow, inFlow, deleteInfo, visited, target, unreachableObjects);
                        if (updated)
                        {
                           deleteInfo.track - set[target].insert(dirtyObjects.begin(), dirtyObjects.end());

                           int formalVar = inverseFormalParMethod[target][argIndex];
                           int formalParParent = msetDict[target].lct.findRoot(formalVar);

                           deleteInfo.workList[target].push_back(formalParParent);
                        }
                     }

                     if (stmtNode->getDataType() == TR::Address && methodPTG[target]->contains(-3))
                     {
                        std::set<Entry *> actEntries = methodPTG[target]->getReturnPointsTo();
                        std::set<Entry *> tempReachable = methodPTG[delM.first]->getReachable(actEntries);

                        bool propagate = false;
                        for (auto obj : tempReachable)
                        {
                           if (deleteInfo.delete -map.find(obj) != deleteInfo.delete -map.end() || deleteInfo.track - map.find(obj) != deleteInfo.track - map.end())
                           {
                              propagate = true;
                              break;
                           }
                        }

                        if (propagate)
                        {
                           int formalParParent = msetDict[target].lct.findRoot(-3);
                           deleteInfo.workList[target].push_back(formalParParent);
                        }
                     }
                  }

               } // end not library method

            } // end NOT isHelper

            break;
         }
         case TR::Return:
         case TR::lreturn:
         case TR::ireturn:
         case TR::dreturn:
         case TR::freturn:
         case TR::areturn:
         case TR::vreturn:
         {
            if (opCode == TR::areturn)
            {

               getVarSlots(stmtNode, comp, evaluatedSymRef, delM.first);

               std::set<Entry *> actEntries = getCachedPointsTo(stmtNode->getFirstChild());

               std::set<Entry *> tempReachable = methodPTG[delM.first]->getReachable(actEntries);

               for (auto t : myInverseCallGraph[delM.first])
               {

                  deleteInfo.unreachable - set[t.first].insert(tempReachable.begin(), tempReachable.end());
                  for (auto callStmt : t.second)
                  {
                     int var = inverseArgCallNode[t.first][callStmt][-3];
                     int varParent = msetDict[t.first].lct.findRoot(var);
                     deleteInfo.workList[t.first].push_back(varParent);
                     if (topLevelMethods.find(delM.first) != topLevelMethods.end())
                     {
                        topLevelVisited.insert(delM.first);
                        topLevelMethods.erase(delM.first);
                     }
                     if (topLevelVisited.find(t.first) == topLevelVisited.end())
                     {
                        topLevelMethods.insert(t.first);
                        if (debugFlag)
                        {
                           std::cout << "adding " << inverseMethodNameIDmapping[t.first] << " to toplevel\n";
                        }
                     }
                  }
               }
            }
            break;
         }
         default:
         {
            //         TR_ASSERT_FATAL(true, "opcode %s not recognized", usefulNode->getOpCode().getName());
            break;
         }

         } // b4

         // performing actual delete of stmt form mset
         for (auto var : evaluatedSymRef)
         {
            msetDict[delM.first].stmtMap[var].erase(stmtNode->stmtNumber);
         }

      } // b3

      for (auto par : inverseFormalParMethod[delM.first])
      {
         int formalParSymRef = par.second;

         std::set<Entry *> formalParPts = methodPTG[delM.first]->getPointsToSet(formalParSymRef);

         if (!formalParPts.empty())
         {

            bool propagate = false;
            std::set<Entry *> tempReachable = methodPTG[delM.first]->getReachable(formalParPts);

            for (auto obj : tempReachable)
            {
               if (deleteInfo.delete -map.find(obj) != deleteInfo.delete -map.end() || deleteInfo.track - map.find(obj) != deleteInfo.track - map.end())
               {
                  propagate = true;
                  break;
               }
            }

            if (propagate)
            {
               for (auto t : myInverseCallGraph[delM.first])
               {
                  for (auto callStmt : t.second)
                  {
                     int var = inverseArgCallNode[t.first][callStmt][par.first];
                     int varParent = msetDict[t.first].lct.findRoot(var);
                     deleteInfo.workList[t.first].push_back(varParent);
                     if (topLevelMethods.find(delM.first) != topLevelMethods.end())
                     {
                        topLevelVisited.insert(delM.first);
                        topLevelMethods.erase(delM.first);
                     }
                     if (topLevelVisited.find(t.first) == topLevelVisited.end())
                     {
                        topLevelMethods.insert(t.first);
                     }
                  }
               }
            }
         }
      }

   } // b2
} // b1

void findAffectedInfo(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict,
                      DeleteInfo &deleteInfo, std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<int>> &affectedVars)
{
   int i = 0;
   bool fixPoint = false;
   std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> baseState = deleteInfo.workList;
   do
   {

      deleteInfo.workList = baseState;
      std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> visitedMap = deleteInfo.workList;

      int oldSize = deleteInfo.stackDelta.size() + deleteInfo.heapDelta.size();

      std::cout << "iteration no = " << i++ << "\n";

      // init worklist using the initworklist passed as argument
      // worklist will only store root vars

      while (!deleteInfo.workList.empty())
      {
         // removing one method from list
         TR_OpaqueMethodBlock *currentMethod = deleteInfo.workList.begin()->first;

         // for reanalyzing we want to copy the lct as it is
         if (deleteInfo.reanalyze.find(currentMethod) == deleteInfo.reanalyze.end())
         {
            deleteInfo.reanalyze[currentMethod].lct = msetDict[currentMethod].lct;
         }

         UniqueDeque<int> varList = deleteInfo.workList[currentMethod];

         deleteInfo.workList.erase(currentMethod);

         // iterate over all var (their children) and collect relevant statements.
         while (!varList.empty())
         {
            int currentParentVar = varList.front(); // remove front element from queue
            varList.pop_front();
            // create inner worklist to traverse children

            if (debugFlag)
            {
               std::cout << "currentParentVar = " << currentParentVar << "\n";
            }

            std::unordered_set<int> varSet = msetDict[currentMethod].lct.getAllChildVars(currentParentVar);

            affectedVars[currentMethod].insert(varSet.begin(), varSet.end());

            for (auto currentVar : varSet)
            {

               if (debugFlag)
               {
                  std::cout << "current var = " << currentVar << " in method = " << inverseMethodNameIDmapping[currentMethod] << "\n";
               }

               for (auto sn : msetDict[currentMethod].stmtMap[currentVar])
               {

                  if (debugFlag)
                  {
                     std::cout << "sn = " << sn << "\n";
                     std::cout << "analyzing node = " << stmtNumber[currentMethod][sn] << "\n";
                  }

                  analyzeNode(stmtNumber[currentMethod][sn], currentMethod, comp, visitedMap, deleteInfo, msetDict);
               }

               // check if currentVar is formal par
               if (formalParMethod[currentMethod].find(currentVar) != formalParMethod[currentMethod].end() && formalParMethod[currentMethod][currentVar] >= 0)
               {
                  int argIndex = formalParMethod[currentMethod][currentVar];
                  if (debugFlag)
                  {
                     std::cout << "fai argindex = " << argIndex << "\n";
                  }

                  for (auto entry : myInverseCallGraph[currentMethod])
                  {
                     TR_OpaqueMethodBlock *callerMethod = entry.first;
                     for (auto cnptr : entry.second)
                     {
                        int callerVar = inverseArgCallNode[callerMethod][cnptr][argIndex];
                        if (debugFlag)
                        {
                           std::cout << "fai callerVar = " << callerVar << "\n";
                        }

                        // check pts of argument
                        int childIndex = cnptr->getFirstArgumentIndex();

                        childIndex += argIndex;

                        if (cnptr->getSymbol()->castToMethodSymbol()->isStatic())
                        {
                           childIndex--;
                           // we are doing this bcoz in static argindex starts from 1 and adding it to first arg index will give second argument.
                        }

                        std::set<Entry *> argPts = getCachedPointsTo(cnptr->getChild(childIndex));
                        std::set<Entry *> tempReachable = methodPTG[callerMethod]->getReachable(argPts);

                        bool propagate = false;
                        for (auto obj : tempReachable)
                        {
                           if (deleteInfo.delete -map.find(obj) != deleteInfo.delete -map.end() || deleteInfo.track - map.find(obj) != deleteInfo.track - map.end())
                           {
                              propagate = true;
                              break;
                           }
                        }

                        if (propagate)
                        {

                           // add var to worklist
                           int parParent = msetDict[callerMethod].lct.findRoot(callerVar);

                           if (debugFlag)
                           {
                              std::cout << "current = " << inverseMethodNameIDmapping[currentMethod] << "  caller = " << inverseMethodNameIDmapping[callerMethod] << "  parent = " << parParent << " for argindex = " << argIndex << "\n";
                           }

                           if (!visitedMap[callerMethod].contains(parParent))
                           {
                              visitedMap[callerMethod].push_back(parParent);
                              deleteInfo.workList[callerMethod].push_back(parParent);
                              if (topLevelMethods.find(currentMethod) != topLevelMethods.end())
                              {
                                 topLevelVisited.insert(currentMethod);
                                 topLevelMethods.erase(currentMethod);
                              }
                              if (topLevelVisited.find(callerMethod) == topLevelVisited.end())
                              {
                                 topLevelMethods.insert(callerMethod);
                              }
                           }
                        }
                     }
                  }
               }
            }
         }
      }
      deleteInfo.workList = visitedMap;
      int newSize = deleteInfo.stackDelta.size() + deleteInfo.heapDelta.size();
      fixPoint = newSize > oldSize;
   } while (fixPoint);
}

std::set<Entry *> deletePointsToInfo(TR::Node *node, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp, Counter &counter, DeleteInfo &deleteInfo, std::unordered_set<TR::Node *> &nodeVisited)
{

   std::set<Entry *> evaluatedValues;

   TR::Node *usefulNode = getUsefulNode(node);

   if (usefulNode == NULL)
   {
      // std::cout<<"inside del infor useful node = NULL node is "<<node<<"\n";
      return evaluatedValues;
   }

   if (debugFlag)
   {
      std::cout << "deleteing from " << usefulNode << "\n";
   }

   if (nodeVisited.find(usefulNode) != nodeVisited.end())
   {
      return cachedValues[usefulNode];
   }

   nodeVisited.insert(usefulNode);

   TR::ILOpCodes opCode = usefulNode->getOpCodeValue();

   switch (opCode)
   {

   case TR::checkcast:
   {
      std::set<Entry *> afterCast;

      // fetch pts-to info of child
      evaluatedValues = deletePointsToInfo(usefulNode->getFirstChild(), currentMethod, comp, counter, deleteInfo, nodeVisited);

      // get class
      TR_OpaqueClassBlock *tpSym = (TR_OpaqueClassBlock *)usefulNode->getSecondChild()->getSymbol()->castToStaticSymbol()->getStaticAddress();

      if (tpSym != NULL)
      {
         // if class not null then do type check to refine pts info
         for (auto e : evaluatedValues)
         {
            if (canCast(e, tpSym, comp))
            {
               afterCast.insert(e);
            }
         }
      }
      else
      {
         std::cout << "cannot fetch type cast class " << usefulNode << "\n";
         afterCast.insert(evaluatedValues.begin(), evaluatedValues.end());
      }

      evaluatedValues = afterCast;

      break;
   }

   case TR::aconst:
   {
      Entry *e = PointsToGraph::nullEntry;
      if (deleteInfo.stackDelta[currentMethod].find(e) == deleteInfo.stackDelta[currentMethod].end() && deleteInfo.heapDelta.find(e) == deleteInfo.heapDelta.end())
      {
         evaluatedValues.insert(e);
      }

      break;
   }

   case TR::aladd:
   {
      Entry *e = PointsToGraph::bottomEntry;
      if (deleteInfo.stackDelta[currentMethod].find(e) == deleteInfo.stackDelta[currentMethod].end() && deleteInfo.heapDelta.find(e) == deleteInfo.heapDelta.end())
      {
         evaluatedValues.insert(e);
      }
      break;
   }

   case TR::New:
   {
      std::set<Entry *> pointsToSet = getCachedPointsTo(usefulNode);
      std::set<Entry *> temp_0;
      std::set_difference(pointsToSet.begin(), pointsToSet.end(), deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
      std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));

      break;
   }

   case TR::newarray:
   {
      std::set<Entry *> pointsToSet = getCachedPointsTo(usefulNode);
      std::set<Entry *> temp_0;
      std::set_difference(pointsToSet.begin(), pointsToSet.end(), deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
      std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));

      break;
   }

   case TR::anewarray:
   {
      std::set<Entry *> pointsToSet = getCachedPointsTo(usefulNode);
      std::set<Entry *> temp_0;
      std::set_difference(pointsToSet.begin(), pointsToSet.end(), de leteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
      std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));

      break;
   }

   case TR::multianewarray:
   {
      if (deleteInfo.stackDelta[currentMethod].find(PointsToGraph::bottomEntry) == deleteInfo.stackDelta[currentMethod].end() && deleteInfo.heapDelta.find(PointsToGraph::bottomEntry) == deleteInfo.heapDelta.end())
      {
         evaluatedValues.insert(PointsToGraph::bottomEntry);
      }
      break;
   }

   case TR::astore:
   {
      // get rhs node
      TR::Node *storeChild = usefulNode->getFirstChild();

      // get pts-to for rhs
      evaluatedValues = deletePointsToInfo(storeChild, currentMethod, comp, counter, deleteInfo, nodeVisited);

      break;
   }

   case TR::aload:
   {

      set<Entry *> pointsToSet = getCachedPointsTo(usefulNode);
      std::set<Entry *> temp_0;
      std::set_difference(pointsToSet.begin(), pointsToSet.end(), deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
      std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));
      break;
   }

   case TR::aloadi:
   {

      set<Entry *> pointsToSet = getCachedPointsTo(usefulNode);
      std::set<Entry *> temp_0;
      std::set_difference(pointsToSet.begin(), pointsToSet.end(), deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
      std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));
      break;
   }

   case TR::awrtbari:
   {
      set<Entry *> pointsToSet = getCachedPointsTo(usefulNode);
      std::set<Entry *> temp_0;
      std::set_difference(pointsToSet.begin(), pointsToSet.end(), deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
      std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));
      break;
   }

   case TR::icalli:
   // case TR::vcalli:
   case TR::lcalli:
   case TR::fcalli:
   case TR::dcalli:
   case TR::acalli:
   case TR::calli:
   case TR::icall:
   case TR::lcall:
   case TR::fcall:
   case TR::dcall:
   case TR::acall:
   case TR::call:
   case TR::vcall:
   { // b1

      std::unordered_set<TR_OpaqueMethodBlock *> methodsToPeek;

      bool isHelperMethodCall = usefulNode->getSymbol()->castToMethodSymbol()->isHelper();

      // we do not want to process helper method calls (prepareForOSR, potentialOSRPointHelper, for example)
      if (isHelperMethodCall)
      {
         break;
      }
      else
      { // b2

         std::string methodName = cachedMethodName[usefulNode];
         if (isLibraryMethod(methodName) && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
         { // b3

            // std::cout<<"is library\n";

            if (((std::string)methodName).find(")Ljava/lang/String;") != std::string::npos)
            {
               if (deleteInfo.stackDelta[currentMethod].find(PointsToGraph::stringEntry) == deleteInfo.stackDelta[currentMethod].end() && deleteInfo.heapDelta.find(PointsToGraph::stringEntry) == deleteInfo.heapDelta.end())
               {
                  evaluatedValues.insert(PointsToGraph::stringEntry);
               }
            }
            else if (((std::string)methodName).find(")Ljava/lang/Class;") != std::string::npos)
            {
               if (deleteInfo.stackDelta[currentMethod].find(PointsToGraph::classEntry) == deleteInfo.stackDelta[currentMethod].end() && deleteInfo.heapDelta.find(PointsToGraph::classEntry) == deleteInfo.heapDelta.end())
               {
                  evaluatedValues.insert(PointsToGraph::classEntry);
               }
            }
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0)
            {
               if (deleteInfo.stackDelta[currentMethod].find(PointsToGraph::bottomEntry) == deleteInfo.stackDelta[currentMethod].end() && deleteInfo.heapDelta.find(PointsToGraph::bottomEntry) == deleteInfo.heapDelta.end())
               {
                  evaluatedValues.insert(PointsToGraph::bottomEntry);
               }
            }

            if (((std::string)methodName).find("java/lang/Thread.<init>(Ljava/lang/Runnable;)V") != std::string::npos)
            {
               // std::cout<<"first child of thread is "<<usefulNode->getFirstChild()<<"\n";

               std::set<Entry *> secChild = deletePointsToInfo(usefulNode->getSecondChild(), currentMethod, comp, counter, deleteInfo, nodeVisited);

               // this is superuseful bcoz it sets pts of thread obj to pts of runnable. When thread obj is accessed, this short-circuit will give correct pts
               cachedValues[usefulNode->getFirstChild()] = secChild;
               usefulNode->getFirstChild()->setVisitCount(counter.visitCount);
            }
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0 && ((std::string)methodName).find("<init>") == std::string::npos)
            {
               int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
               int32_t numChildren = usefulNode->getNumChildren();
               for (int32_t i = firstArgIndex; i < numChildren; i++)
               {
                  deletePointsToInfo(usefulNode->getChild(i), currentMethod, comp, counter, deleteInfo, nodeVisited);
               }
            }

         } // b3
         else
         { // b4

            bool isStatic = usefulNode->getSymbol()->castToMethodSymbol()->isStatic();

            int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
            int32_t numChildren = usefulNode->getNumChildren();
            int32_t i = firstArgIndex;

            if (!isStatic)
            {
               std::set<Entry *> recEntries = deletePointsToInfo(usefulNode->getChild(i), currentMethod, comp, counter, deleteInfo, nodeVisited);
               i++;
            }

            for (; i < numChildren; i++)
            {
               std::set<Entry *> argEntries = deletePointsToInfo(usefulNode->getChild(i), currentMethod, comp, counter, deleteInfo, nodeVisited);
            }

            std::set<Entry *> pointsToSet = getCachedPointsTo(usefulNode);
            std::set<Entry *> temp_0;
            std::set_difference(pointsToSet.begin(), pointsToSet.end(), deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
            std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));

         } // b4 end not library method

      } // end NOT isHelper

      break;
   }

   case TR::Return:
   case TR::lreturn:
   case TR::ireturn:
   case TR::dreturn:
   case TR::freturn:
   case TR::areturn:
   case TR::vreturn:
   {

      if (opCode == TR::areturn)
      {
         std::set<Entry *> pointsToSet = deletePointsToInfo(usefulNode->getFirstChild(), currentMethod, comp, counter, deleteInfo, nodeVisited);
         std::set<Entry *> temp_0;
         std::set_difference(pointsToSet.begin(), pointsToSet.end(), deleteInfo.heapDelta.begin(), deleteInfo.heapDelta.end(), inserter(temp_0, temp_0.end()));
         std::set_difference(temp_0.begin(), temp_0.end(), deleteInfo.stackDelta[currentMethod].begin(), deleteInfo.stackDelta[currentMethod].end(), inserter(evaluatedValues, evaluatedValues.end()));
      }
      break;
   }

   default:
   {
      //         TR_ASSERT_FATAL(true, "opcode %s not recognized", usefulNode->getOpCode().getName());
      break;
   }
   }
   cachedValues[usefulNode] = evaluatedValues;
   return evaluatedValues;
}

void updateGlobalDS()
{

   for (auto i : myCallGraphDelete)
   {
      for (auto j : i.second)
      {
         for (auto k : j.second)
         {
            myCallGraph[i.first][j.first].erase(k);
         }
      }
   }
   myCallGraphDelete.clear();

   for (auto i : myInverseCallGraphDelete)
   {
      for (auto j : i.second)
      {
         for (auto k : j.second)
         {
            myInverseCallGraph[i.first][j.first].erase(k);
         }
      }
   }
   myInverseCallGraphDelete.clear();
}

void performAddition(TR::Compilation *comp, std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &addStmt, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &msetDict)
{
   std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> workList;
   for (auto i : addStmt)
   {
      std::unordered_set<TR::Node *> nodeVisited;
      std::unordered_set<int> affectedVars;
      Counter counter(0, -10);
      for (auto j : i.second)
      {
         TR::Node *currentNode = stmtNumber[i.first][j];
         counter.visitCount = currentNode->getVisitCount() + 1;
         evaluateNode(currentNode, counter, i.first, comp, false, msetDict, nodeVisited);
         std::unordered_set<int> varSlots;
         getVarSlots(currentNode, comp, varSlots, i.first);
         affectedVars.insert(varSlots.begin(), varSlots.end());
      }
      for (auto var : affectedVars)
      {
         // std::cout<<"add method = "<<inverseMethodNameIDmapping[i.first]<<" var = "<<var<<" root = "<<msetDict[i.first].lct.findRoot(var)<<"\n";
         workList[i.first].push_back(msetDict[i.first].lct.findRoot(var));
      }

      topLevelMethods.insert(i.first);
      topLevelVisited.insert(i.first);
   }

   performPTA(comp, msetDict, workList);
}

void analyzeNode(TR::Node *node, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp,
                 std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &visitedMap,
                 DeleteInfo &deleteInfo, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict)
{

   node = getUsefulNode(node);

   if (node == NULL)
   {
      return;
   }

   TR::ILOpCodes opCode = node->getOpCodeValue();
   switch (opCode)
   {

   case TR::checkcast:
   case TR::astore:
   {
      std::set<Entry *> pointsToSet = getCachedPointsTo(node->getFirstChild());
      bool reanalyzeStmt = false;
      for (auto obj : pointsToSet)
      {
         if (deleteInfo.track - set[currentMethod].find(obj) != deleteInfo.track - set[currentMethod].end() || deleteInfo.unreachable - set[currentMethod].find(obj) != deleteInfo.unreachable - set[currentMethod].end())
         {
            reanalyzeStmt = true;
            break;
         }
      }
      if (reanalyzeStmt)
      {
         std::unordered_set<int> varSlots;
         getVarSlots(node, comp, varSlots, currentMethod);
         for (auto slot : varSlots)
         {
            // std::cout<<"adding astore stmt for slot "<<slot<<" node = "<<node->stmtNumber<<"\n";
            deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
         }
      }
   }

   case TR::awrtbar:
   {
      std::set<Entry *> pointsToSet = getCachedPointsTo(node->getFirstChild());
      std::set<Entry *> dirtyObjects;
      std::set_intersection(pointsToSet.begin(), pointsToSet.end(), deleteInfo.track - set[currentMethod].begin(), deleteInfo.track - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
      std::set_intersection(pointsToSet.begin(), pointsToSet.end(), deleteInfo.unreachable - set[currentMethod].begin(), deleteInfo.unreachable - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
      addReachableBottomToDeleteMap(dirtyObjects, deleteInfo, currentMethod);
      if (!dirtyObjects.empty())
      {
         std::unordered_set<int> varSlots;
         getVarSlots(node, comp, varSlots, currentMethod);
         for (auto slot : varSlots)
         {
            // std::cout<<"awrtbar slot = "<<slot<<"\n";
            deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
         }
      }
   }

   case TR::awrtbari:
   {

      TR::SymbolReference *symRef = node->getSymbolReference();

      bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;

      int cpIndex = symRef->getCPIndex();

      std::string field;

      if (node->getSymbol()->isArrayShadowSymbol())
      {
         field = "_$";
         TR::Node *receiverNode = node->getFirstChild();
         TR::Node *valueNode = node->getSecondChild();
      }
      else if (isShadow && cpIndex > 0)
      {
         int32_t len;
         const char *fieldName = node->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(cpIndex, len);
         field.assign(fieldName, fieldName + len);
         TR::Node *receiverNode = node->getThirdChild();
         TR::Node *valueNode = node->getSecondChild();
      }
      if (valueNode->getDataType() == TR::Address)
      {
         set<Entry *> lhs = getCachedPointsTo(receiverNode);
         set<Entry *> rhs = getCachedPointsTo(valueNode);

         std::set<Entry *> dirtyObjects;
         std::set_intersection(rhs.begin(), rhs.end(), deleteInfo.track - set[currentMethod].begin(), deleteInfo.track - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
         std::set_intersection(rhs.begin(), rhs.end(), deleteInfo.unreachable - set[currentMethod].begin(), deleteInfo.unreachable - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));

         bool reanalyzeStmt = false;

         if (!dirtyObjects.empty())
         {
            reanalyzeStmt = true;
            for (auto obj : lhs)
            {
               deleteInfo.dirty - map[obj][field].insert(dirtyObjects.begin(), dirtyObjects.end());
            }
         }

         for (auto obj : lhs)
         {
            if (deleteInfo.track - set[currentMethod].find(obj) != deleteInfo.track - set[currentMethod].end() || deleteInfo.unreachable - set[currentMethod].find(obj) != deleteInfo.unreachable - set[currentMethod].end())
            {
               if (obj == PointsToGraph::bottomEntry)
               {
                  addReachableBottomToDeleteMap(rhs, deleteInfo, currentMethod);
               }
               else
               {
                  deleteInfo.dirty - map[obj][field].insert(rhs.begin(), rhs.end());
               }

               reanalyzeStmt = true;
            }
         }

         if (reanayzeStmt)
         {
            std::unordered_set<int> varSlots;
            getVarSlots(node, comp, varSlots, currentMethod);
            for (auto slot : varSlots)
            {
               deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
            }
         }
      }
      break;
   }

   case TR::icalli:
   // case TR::vcalli:
   case TR::lcalli:
   case TR::fcalli:
   case TR::dcalli:
   case TR::acalli:
   case TR::calli:
   case TR::icall:
   case TR::lcall:
   case TR::fcall:
   case TR::dcall:
   case TR::acall:
   case TR::call:
   case TR::vcall:
   {
      bool isHelperMethodCall = node->getSymbol()->castToMethodSymbol()->isHelper();

      // we do not want to process helper method calls (prepareForOSR, potentialOSRPointHelper, for example)
      if (isHelperMethodCall)
      {
         break;
      }
      else
      {
         std::string methodName = cachedMethodName[node];

         if (isLibraryMethod(methodName) && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
         {
            if (((std::string)methodName).find(")Ljava/lang/String;") != std::string::npos)
            {
               if ((deleteInfo.stackDelta.find(currentMethod) != deleteInfo.stackDelta.end() && deleteInfo.stackDelta[currentMethod].find(PointsToGraph::stringEntry) != deleteInfo.stackDelta[currentMethod].end()) || deleteInfo.heapDelta.find(PointsToGraph::stringEntry) != deleteInfo.heapDelta.end())
               {

                  std::unordered_set<int> varSlots;
                  getVarSlots(node, comp, varSlots, currentMethod);
                  for (auto slot : varSlots)
                  {
                     deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                  }
               }
            }
            else if (((std::string)methodName).find(")Ljava/lang/Class;") != std::string::npos)
            {
               if ((deleteInfo.stackDelta.find(currentMethod) != deleteInfo.stackDelta.end() && deleteInfo.stackDelta[currentMethod].find(PointsToGraph::classEntry) != deleteInfo.stackDelta[currentMethod].end()) || deleteInfo.heapDelta.find(PointsToGraph::classEntry) != deleteInfo.heapDelta.end())
               {

                  std::unordered_set<int> varSlots;
                  getVarSlots(node, comp, varSlots, currentMethod);
                  for (auto slot : varSlots)
                  {
                     deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                  }
               }
            }
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0)
            {
               if ((deleteInfo.stackDelta.find(currentMethod) != deleteInfo.stackDelta.end() && deleteInfo.stackDelta[currentMethod].find(PointsToGraph::bottomEntry) != deleteInfo.stackDelta[currentMethod].end()) || deleteInfo.heapDelta.find(PointsToGraph::bottomEntry) != deleteInfo.heapDelta.end())
               {

                  std::unordered_set<int> varSlots;
                  getVarSlots(node, comp, varSlots, currentMethod);
                  for (auto slot : varSlots)
                  {
                     deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                  }
               }
            }
            if (((std::string)methodName).find("java/lang/Thread.<init>(Ljava/lang/Runnable;)V") != std::string::npos)
            {

               std::set<Entry *> childPts = getCachedPointsTo(node->getSecondChild());
               std::set<Entry *> dirtyObjects;
               std::set_intersection(childPts.begin(), childPts.end(), deleteInfo.track - set[currentMethod].begin(), deleteInfo.track - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
               std::set_intersection(childPts.begin(), childPts.end(), deleteInfo.unreachable - set[currentMethod].begin(), deleteInfo.unreachable - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
               if (!dirtyObjects.empty())
               {
                  addReachableBottomToDeleteMap(dirtyObjects, deleteInfo, currentMethod);
                  std::unordered_set<int> varSlots;
                  getVarSlots(node, comp, varSlots, currentMethod);
                  for (auto slot : varSlots)
                  {
                     deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                  }
               }
            }
            else if (((std::string)methodName).rfind("java/lang/reflect/") != 0 && ((std::string)methodName).find("<init>") == std::string::npos)
            {

               int32_t firstArgIndex = node->getFirstArgumentIndex();
               for (int32_t i = firstArgIndex; i < node->getNumChildren(); i++)
               {
                  std::set<Entry *> childPts = getCachedPointsTo(node->getChild(i));
                  std::set<Entry *> dirtyObjects;
                  std::set_intersection(childPts.begin(), childPts.end(), deleteInfo.track - set[currentMethod].begin(), deleteInfo.track - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
                  std::set_intersection(childPts.begin(), childPts.end(), deleteInfo.unreachable - set[currentMethod].begin(), deleteInfo.unreachable - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
                  if (!dirtyObjects.empty())
                  {
                     addReachableBottomToDeleteMap(dirtyObjects, deleteInfo, currentMethod);
                     std::unordered_set<int> varSlots;
                     getVarSlots(node, comp, varSlots, currentMethod);
                     for (auto slot : varSlots)
                     {
                        deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                     }
                  }
               }
            }
         }
         else
         {

            bool isStatic = node->getSymbol()->castToMethodSymbol()->isStatic();

            for (auto target : myCallGraph[currentMethod][node])
            {

               // calculating Inflow
               std::unordered_map<int, std::set<Entry *>> inFlow;
               for (auto caller : myInverseCallGraph[target])
               {
                  if (caller.first != currentMethod && (cyclicMethods.find(caller.first) == cyclicMethods.end() || cyclicMethods.find(currentMethod) == cyclicMethods.end()))
                  {
                     for (auto callNode : caller.second)
                     {
                        int argIndex = 0;
                        if (isStatic)
                        {
                           argIndex = 1;
                        }
                        int32_t firstArgIndex = callNode->getFirstArgumentIndex();
                        int32_t numChildren = callNode->getNumChildren();
                        for (int32_t i = firstArgIndex; i < numChildren; i++, argIndex++)
                        {
                           std::set<Entry *> argPointees = getCachedPointsTo(callNode->getChild(i));

                           TR_OpaqueClassBlock *argtype;
                           if (cachedParameterType.find(caller.first) != cachedParameterType.end() && cachedParameterType[caller.first].find(argIndex) != cachedParameterType[caller.first].end())
                           {
                              argtype = cachedParameterType[caller.first][argIndex];
                           }
                           else
                           {
                              continue;
                           }

                           std::set<Entry *> actEntries;
                           for (auto e : argPointees)
                           {
                              if (canCast(e, argtype, comp))
                              {
                                 actEntries.insert(e);
                                 inFlow[argIndex].insert(e);
                              }
                           }
                        }
                     }
                  }
               }

               // do not delete eagerly. Instead delete at the end after algo finishes
               std::set<Entry *> candidateNodes;
               bool isCallEdgeDeleted = false;

               int argIndex = 0;

               if (isStatic)
               {
                  argIndex = 1;
               }

               TR::ResolvedMethodSymbol *targetMethodSymbol = comp->getOwningMethodSymbol(target);

               TR_ResolvedMethod *tempRM = targetMethodSymbol->getResolvedMethod();

               int32_t firstArgIndex = node->getFirstArgumentIndex();
               int32_t numChildren = node->getNumChildren();
               int32_t i = firstArgIndex;
               if (!isStatic)
               {

                  std::set<Entry *> currentFlow;
                  std::set<Entry *> recEntries = getCachedPointsTo(node->getChild(i));
                  std::set<Entry *> actEntries;

                  TR_OpaqueClassBlock *rectype = comp->fe()->getClassFromSignature(tempRM->classNameChars(), tempRM->classNameLength(), comp->getCurrentMethod());
                  // TR_OpaqueClassBlock *rectype = NULL;

                  for (auto e : recEntries)
                  {
                     if (canCast(e, rectype, comp))
                     {
                        actEntries.insert(e);
                        currentFlow[argIndex][currentMethod].insert(e);
                     }
                  }

                  std::set<Entry *> dirtyObjects;
                  std::set_intersection(childPts.begin(), childPts.end(), deleteInfo.track - set[currentMethod].begin(), deleteInfo.track - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));
                  std::set_intersection(childPts.begin(), childPts.end(), deleteInfo.unreachable - set[currentMethod].begin(), deleteInfo.unreachable - set[currentMethod].end(), inserter(dirtyObjects, dirtyObjects.end()));

                  if (dirtyObjects.size() == actEntries.size())
                  {
                     isCallEdgeDeleted = true;
                     myCallGraphDelete[currentMethod][node].insert(target);
                     myInverseCallGraphDelete[target][currentMethod].insert(node);
                  }

                  std::unordered_map<int, std::set<Entry *>> visited;
                  std::set<Entry *> unreachableObjects;
                  bool updated = calculateDirtyObjects(argIndex, currentMethod, currentFlow, inFlow, deleteInfo, visited, target, unreachableObjects);

                  if (updated)
                  {

                     int formalVar = inverseFormalParMethod[target][argIndex];
                     int formalParParent = methodDict[target].lct.findRoot(formalVar);

                     if (!visitedMap[target].contains(formalParParent))
                     {
                        // std::cout<<formalParParent<<"  "<< inverseMethodNameIDmapping[target]<<" from method = "<<inverseMethodNameIDmapping[currentMethod]<<"\n";
                        visitedMap[target].push_back(formalParParent);
                        deleteInfo.workList[target].push_back(formalParParent);
                        if (debugFlag)
                        {
                           std::cout << "currentMethod = " << inverseMethodNameIDmapping[currentMethod] << " target = " << inverseMethodNameIDmapping[target] << " parent var = " << formalParParent << "\n";
                        }
                     }

                     std::unordered_set<int> varSlots;
                     getVarSlots(node->getChild(i), comp, varSlots, currentMethod);
                     for (auto slot : varSlots)
                     {
                        deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                        // also need to check if root of param variable is visited in currentmethod so that it is guaranteed to be present in worklist during reanalysis
                        int parentVar = methodDict[currentMethod].lct.findRoot(slot);
                        if (!visitedMap[currentMethod].contains(parentVar))
                        {
                           visitedMap[currentMethod].push_back(parentVar);
                           deleteInfo.workList[currentMethod].push_back(parentVar);
                        }
                     }
                  }

                  i++;
                  argIndex++;
               }

               TR_MethodParameterIterator *parIterator;
               for (; i < numChildren; i++, argIndex++)
               {
                  // std::cout<<"is par end = "<<parIterator->getOpaqueClass()<<"\n";
                  std::set<Entry *> currentFlow;

                  std::set<Entry *> argPointees = getCachedPointsTo(node->getChild(i));
                  TR_OpaqueClassBlock *argtype;
                  if (cachedParameterType.find(target) != cachedParameterType.end() && cachedParameterType[target].find(argIndex) != cachedParameterType[target].end())
                  {
                     argtype = cachedParameterType[target][argIndex];
                  }
                  else
                  {
                     continue;
                  }

                  std::set<Entry *> actEntries;

                  for (auto e : argPointees)
                  {
                     if (canCast(e, argtype, comp))
                     {
                        actEntries.insert(e);
                        currentFlow.insert(e);
                     }
                  }

                  std::unordered_map<int, std::set<Entry *>> visited;
                  std::set<Entry *> unreachableObjects;
                  if (isCallEdgeDeleted)
                  {
                     std::set<Entry *> tempReachable = methodPTG[currentMethod]->getReachable(actEntries);
                     unreachableObjects.insert(tempReachable.begin(), tempReachable.end());
                  }
                  bool updated = calculateDirtyObjects(argIndex, currentMethod, currentFlow, inFlow, deleteInfo, visited, target, unreachableObjects);

                  if (updated)
                  {

                     int formalVar = inverseFormalParMethod[target][argIndex];
                     int formalParParent = methodDict[target].lct.findRoot(formalVar);

                     if (!visitedMap[target].contains(formalParParent))
                     {
                        // std::cout<<formalParParent<<"  "<< inverseMethodNameIDmapping[target]<<" from method = "<<inverseMethodNameIDmapping[currentMethod]<<"\n";
                        visitedMap[target].push_back(formalParParent);
                        deleteInfo.workList[target].push_back(formalParParent);
                        if (debugFlag)
                        {
                           std::cout << "currentMethod = " << inverseMethodNameIDmapping[currentMethod] << " target = " << inverseMethodNameIDmapping[target] << " parent var = " << formalParParent << "\n";
                        }
                     }

                     std::unordered_set<int> varSlots;
                     getVarSlots(node->getChild(i), comp, varSlots, currentMethod);
                     for (auto slot : varSlots)
                     {
                        deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                        // also need to check if root of param variable is visited in currentmethod so that it is guaranteed to be present in worklist during reanalysis
                        int parentVar = methodDict[currentMethod].lct.findRoot(slot);
                        if (!visitedMap[currentMethod].contains(parentVar))
                        {
                           visitedMap[currentMethod].push_back(parentVar);
                           deleteInfo.workList[currentMethod].push_back(parentVar);
                        }
                     }
                  }
               }

               if (node->getDataType() == TR::Address && methodPTG[target]->contains(-3))
               {
                  std::set<Entry *> actEntries = methodPTG[target]->getReturnPointsTo();
                  std::set<Entry *> tempReachable = methodPTG[currentMethod]->getReachable(actEntries);

                  bool propagate = false;
                  for (auto obj : tempReachable)
                  {
                     if (deleteInfo.delete -map.find(obj) != deleteInfo.delete -map.end() || deleteInfo.track - map.find(obj) != deleteInfo.track - map.end())
                     {
                        propagate = true;
                        break;
                     }
                  }

                  if (propagate)
                  {
                     int slot = inverseArgCallNode[currentMethod][node][-3];
                     deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
                     int parentVar = methodDict[currentMethod].lct.findRoot(slot);
                     if (!visitedMap[currentMethod].contains(parentVar))
                     {
                        visitedMap[currentMethod].push_back(parentVar);
                        deleteInfo.workList[currentMethod].push_back(parentVar);
                     }

                     int formalParParent = methodDict[target].lct.findRoot(-3);
                     if (!visitedMap[target].contains(formalParParent))
                     {
                        visitedMap[target].push_back(formalParParent);
                        deleteInfo.workList[target].push_back(formalParParent);

                        // needed bcoz some stmts  my have to be reanalyzed from target method and there is no inflow
                        if (topLevelVisited.find(target) == topLevelVisited.end())
                        {
                           topLevelMethods.insert(target);
                        }
                     }
                  }
               }
            }

         } // end not library method

      } // end NOT isHelper

      // in->print();
      break;
   }

   case TR::Return:
   case TR::lreturn:
   case TR::ireturn:
   case TR::dreturn:
   case TR::freturn:
   case TR::areturn:
   case TR::vreturn:
   {

      if (opCode == TR::areturn)
      {

         std::set<Entry *> actEntries = getCachedPointsTo(node->getFirstChild());

         std::set<Entry *> tempReachable = methodPTG[currentMethod]->getReachable(actEntries);

         // reason to take diff for heapdelta is that we only need to propagate stackdelta
         std::set<Entry *> temp_1;
         std::set_intersection(tempReachable.begin(), tempReachable.end(), deleteInfo.track - set[currentMethod].begin(), deleteInfo.track - set[currentMethod].end(), inserter(temp_1, temp_1.end()));

         std::set<Entry *> temp_2;
         std::set_intersection(tempReachable.begin(), tempReachable.end(), deleteInfo.unreachable - set[currentMethod].begin(), deleteInfo.unreachable - set[currentMethod].end(), inserter(temp_2, temp_2.end()));

         bool propagate = false;
         for (auto obj : tempReachable)
         {
            if (deleteInfo.delete -map.find(obj) != deleteInfo.delete -map.end() || deleteInfo.track - map.find(obj) != deleteInfo.track - map.end())
            {
               propagate = true;
               break;
            }
         }

         if (!temp_1.empty() || !temp_2.empty() || propagate)
         {
            for (auto t : myInverseCallGraph[currentMethod])
            {
               for (auto callStmt : t.second)
               {
                  int var = inverseArgCallNode[t.first][callStmt][-3];
                  int varParent = methodDict[t.first].lct.findRoot(var);
                  if (!visitedMap[t.first].contains(varParent))
                  {
                     visitedMap[t.first].push_back(varParent);
                     deleteInfo.workList[t.first].push_back(varParent);
                     if (debugFlag)
                     {
                        std::cout << "currentMethod = " << inverseMethodNameIDmapping[currentMethod] << " caller = " << inverseMethodNameIDmapping[t.first] << " parent var = " << varParent << "\n";
                     }
                  }
                  if (deleteInfo.reanalyze.find(t.first) == deleteInfo.reanalyze.end())
                  {
                     // std::cout<<"analyzed -> "<<inverseMethodNameIDmapping[t.first]<<"\n";
                     deleteInfo.reanalyze[t.first].lct = methodDict[t.first].lct;
                  }
                  deleteInfo.reanalyze[t.first].stmtMap[var].insert(callStmt->stmtNumber);
               }
               deleteInfo.track - set[t.first].insert(temp_1.begin(), temp_1.end());
               deleteInfo.unreachable - set[t.first].insert(temp_2.begin(), temp_2.end());
            }
            std::unordered_set<int> varSlots;
            getVarSlots(node, comp, varSlots, currentMethod);
            for (auto slot : varSlots)
            {
               // std::cout<<"ret slot = "<<slot<<" and stmt num = "<<node->stmtNumber<<"\n";
               deleteInfo.reanalyze[currentMethod].stmtMap[slot].insert(node->stmtNumber);
            }
         }
      }

      break;
   }

   default:
   {
      //         TR_ASSERT_FATAL(true, "opcode %s not recognized", usefulNode->getOpCode().getName());
      break;
   }
   }
}
// ************************ PRIMARY METHODS DEFN END (PME) ******************************************

// ************************ SECONDARY METHODS DEFN END (SMS) ******************************************
void constructCHA(TR::Compilation *comp)
{
   std::unordered_set<TR_OpaqueClassBlock *> visited;
   for (auto &it : _classIndices)
   {

      std::string className = _classIndices[it.first];

      int len = strlen(className.c_str());

      TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), len, comp->getCurrentMethod());
      if (type == NULL)
      {
         continue;
      }
      classPtrToIndex[type] = it.first;
      TR_OpaqueClassBlock *prev = type;

      visited.insert(type);

      J9Class **superClasses = TR::Compiler->cls.superClassesOf(type);

      int classDepth = TR::Compiler->cls.classDepthOf(type);

      J9Class *superClass;
      while (classDepth != 0)
      {
         if (prev != type && visited.find(prev) != visited.end())
         {
            break;
         }
         classDepth--;
         *superClasses++;
         superClass = *superClasses;
         if (!superClass)
         {
            break;
         }
         else
         {
            if ((TR_OpaqueClassBlock *)superClass == prev)
            {
               continue;
            }
            CHA[(TR_OpaqueClassBlock *)superClass].insert(prev);
            prev = (TR_OpaqueClassBlock *)superClass;
         }
      }

      // std::string tpName = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());

      for (J9ITable *iTableCur = TR::Compiler->cls.iTableOf(type); iTableCur; iTableCur = iTableCur->next)
      {
         CHA[(TR_OpaqueClassBlock *)iTableCur->interfaceClass].insert(type);
      }
   }
}

int getOrInsertMethodIndex(TR::ResolvedMethodSymbol *methodSymbol, TR::Compilation *comp)
{
   TR_OpaqueMethodBlock *methodPersistentId = methodSymbol->getResolvedMethod()->getPersistentIdentifier();
   // no need of assert, guaranteed to be available

   if (methodPtrToIndex.find(methodPersistentId) != methodPtrToIndex.end())
   {
      return methodPtrToIndex[methodPersistentId];
   }
   else
   {
      std::string methodSignature = methodSymbol->signature(comp->trMemory());
      int index;
      if (_methodIndices.find(methodSignature) != _methodIndices.end())
      {
         // the id is available in the string map, add it to the pointer map for efficiency of later lookups
         index = _methodIndices[methodSignature];
      }
      else
      {
         // the index is in neither map, add it to both
         index = _methodIndices.size() + 1;
         _methodIndices[methodSignature] = index;
      }
      methodPtrToIndex[methodPersistentId] = index;
      return index;
   }
}

TR::Node *getUsefulNode(TR::Node *node)
{
   TR::Node *ret = NULL;
   if (node == NULL)
      return ret;
   else
   {
      TR::ILOpCodes opCode = node->getOpCodeValue();
      // if the opcodes is one of the following, we need to dig deeper
      if (opCode == TR::treetop || opCode == TR::ResolveAndNULLCHK || opCode == TR::ResolveCHK || opCode == TR::compressedRefs || opCode == TR::NULLCHK)
         return getUsefulNode(node->getFirstChild());

      else
      {
         // these are the interesting nodes
         if (opCode == TR::New ||     ///
             opCode == TR::astore ||  ///  refStore
             opCode == TR::astorei || ///   ????
             opCode == TR::Return ||
             opCode == TR::areturn ||
             opCode == TR::aload ||  ///  refLoad
             opCode == TR::aloadi || /// field and array read
             opCode == TR::call ||
             opCode == TR::calli ||
             opCode == TR::acalli ||
             opCode == TR::acall ||
             opCode == TR::calli ||
             opCode == TR::awrtbari ||  /// field and array write
             opCode == TR::awrtbar ||   // this should be only static   ///
             opCode == TR::ardbari ||   ///  ???
             opCode == TR::anewarray || ///
             opCode == TR::newarray ||  ///
             // this is needed for calls where the arg is null - it appears to map to aconst_null in bytecode
             opCode == TR::aconst || ///
             opCode == TR::aladd ||  ///
             opCode == TR::checkcast ||
             opCode == TR::multianewarray ||
             node->getOpCode().isCall())
         {
            // IFDIAGPRINT << "found useful node at n" << node->getGlobalIndex() << "n" << endl;
            ret = node;
         }
         else
         {
            // TODO: Shashin: insert an assert failure here - done
            // there are 41 "address" type nodes, out of those - some are handled above.
            //    create an assert fail for the rest of the address nodes,
            //    and let the other "safe" nodes trickle through - since they deal with non-ref types
            if (
                opCode == TR::ardbar ||
                opCode == TR::i2a ||
                opCode == TR::iu2a ||
                opCode == TR::l2a ||
                opCode == TR::lu2a ||
                opCode == TR::b2a ||
                opCode == TR::bu2a ||
                opCode == TR::s2a ||
                opCode == TR::su2a ||
                opCode == TR::aRegLoad ||
                opCode == TR::aRegStore ||
                opCode == TR::aselect ||
                opCode == TR::checkcastAndNULLCHK ||
                opCode == TR::newvalue ||
                opCode == TR::variableNew ||
                opCode == TR::variableNewArray ||
                opCode == TR::aiadd ||
                opCode == TR::ArrayCHK)
            {
               std::cout << "did not expect op code " << node->getOpCode().getName() << " node " << node->getGlobalIndex() << std::endl;
               TR_ASSERT_FATAL(false, "unexpected op codes");
            }
            else
            {
               // just let them go

               // below were encountered in tests and determined to be "safe" (i.e., not relevant to PTA)
               //  opCode == TR::loadaddr ||
               //  opCode == TR::ArrayStoreCHK || -- encountered in Harness.Main (avrora)
            }
         }
      }
   }

   return ret;
}

void getVarSlots(TR::Node *node, TR::Compilation *comp, std::unordered_set<int> &evaluatedSymRef, TR_OpaqueMethodBlock *currentMethod)
{

   TR::Node *usefulNode = getUsefulNode(node);

   if (!usefulNode)
   {
      evaluatedSymRef.insert(-2);
      return;
   }

   TR::ILOpCodes opCode = usefulNode->getOpCodeValue();

   switch (opCode)
   {
   case TR::aconst:
   {
      evaluatedSymRef.insert(-1);
      break;
   }
   case TR::New:
   case TR::anewarray:
   case TR::newarray:
   case TR::multianewarray:
   {
      evaluatedSymRef.insert(-1000 - (usefulNode->getByteCodeIndex()));
      break;
   }

   case TR::aladd:
   case TR::checkcast:
   {
      getVarSlots(usefulNode->getFirstChild(), comp, evaluatedSymRef, currentMethod);
      break;
   }

   case TR::astore:
   {
      int storeSymRef = usefulNode->getSymbolReference()->getReferenceNumber();
      evaluatedSymRef.insert(storeSymRef);
      break;
   }
   case TR::aload:
   {
      bool isStaticFieldRead = usefulNode->getSymbol()->isStaticField();

      if (!isStaticFieldRead)
      {

         int loadSymRef = usefulNode->getSymbolReference()->getReferenceNumber();
         evaluatedSymRef.insert(loadSymRef);
      }
      else
      {
         evaluatedSymRef.insert(-1);
      }

      break;
   }

   case TR::aloadi:
   {

      if (usefulNode->getSymbol()->isArrayShadowSymbol())
      {

         TR::Node *receiverNode = usefulNode->getFirstChild()->getFirstChild();
         getVarSlots(receiverNode, comp, evaluatedSymRef, currentMethod);
      }
      else
      {

         TR::SymbolReference *symRef = usefulNode->getSymbolReference();
         TR_ASSERT_FATAL(symRef, "aloadi fail 1");

         bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;

         int cpIndex = symRef->getCPIndex();

         if (/* !isUnresolved && */ isShadow && cpIndex > 0)
         {
            // this is most certainly a field access, until proven otherwise

            // receiver
            TR::Node *receiverNode = usefulNode->getFirstChild();
            TR_ASSERT_FATAL(receiverNode, "aloadi fail 2");
            getVarSlots(receiverNode, comp, evaluatedSymRef, currentMethod);
         }
      }

      break;
   }
   case TR::awrtbar:
   {
      getVarSlots(usefulNode->getFirstChild(), comp, evaluatedSymRef, currentMethod);
      break;
   }
   case TR::awrtbari:
   {

      // awrtbari also performs array writes
      TR::Node *valueNode = usefulNode->getSecondChild();
      TR_ASSERT_FATAL(valueNode, "awrtbari fail");

      if (valueNode->getDataType() == TR::Address)
      {
         TR::Node *receiverNode;
         if (!usefulNode->getSymbol()->isArrayShadowSymbol())
         {
            // receiver
            receiverNode = usefulNode->getFirstChild();
         }
         else
         {
            // array writes
            receiverNode = usefulNode->getThirdChild();
         }
         getVarSlots(receiverNode, comp, evaluatedSymRef, currentMethod);
      }

      break;
   }

   case TR::icalli:
   // case TR::vcalli:
   case TR::lcalli:
   case TR::fcalli:
   case TR::dcalli:
   case TR::acalli:
   case TR::calli:
   case TR::icall:
   case TR::lcall:
   case TR::fcall:
   case TR::dcall:
   case TR::acall:
   case TR::call:
   case TR::vcall:
   {

      bool isHelperMethodCall = usefulNode->getSymbol()->castToMethodSymbol()->isHelper();

      std::string methodName;
      if (!isHelperMethodCall)
      {
         methodName = cachedMethodName[usefulNode];
      }
      if (isHelperMethodCall)
      {
         break;
      }
      else if (isLibraryMethod(methodName) && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
      {
         evaluatedSymRef.insert(-1); // IMP - Required for return
         if (((std::string)methodName).find(")Ljava/lang/String;") != std::string::npos)
         {
            evaluatedSymRef.insert(-4);
         }
         else if (((std::string)methodName).find(")Ljava/lang/Class;") != std::string::npos)
         {
            evaluatedSymRef.insert(-5);
         }
         else if (((std::string)methodName).rfind("java/lang/reflect/") != 0)
         {
            evaluatedSymRef.insert(-6);
         }

         // this is for thread creation with runnable parameter
         if (((std::string)methodName).find("java/lang/Thread.<init>(Ljava/lang/Runnable;)V") != std::string::npos)
         {
            getVarSlots(usefulNode->getSecondChild(), comp, evaluatedSymRef, currentMethod);
         }

         // library methods that don't use reflection and are not constructors
         else if (((std::string)methodName).rfind("java/lang/reflect/") != 0 && ((std::string)methodName).find("<init>") == std::string::npos)
         {

            // checking if static
            bool isStatic = usefulNode->getSymbol()->castToMethodSymbol()->isStatic();

            int argIndex = 0;
            if (isStatic)
            {
               argIndex = 1;
            }

            // first arg index points to receiver in case of non static
            int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
            int32_t numChildren = usefulNode->getNumChildren();

            // iterate over all arguments
            for (int32_t i = firstArgIndex; i < numChildren; i++)
            {
               if (usefulNode->getChild(i)->getDataType() == TR::Address)
               {
                  getVarSlots(usefulNode->getChild(i), comp, evaluatedSymRef, currentMethod);
               }

               argIndex++;
            }
         }
         break;
      }
      else
      {
         int oldSize = evaluatedSymRef.size();
         int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
         int32_t numChildren = usefulNode->getNumChildren();
         for (int32_t i = firstArgIndex; i < numChildren; i++)
         {
            getVarSlots(usefulNode->getChild(i), comp, evaluatedSymRef, currentMethod);
         }

         if (usefulNode->getDataType() == TR::Address)
         {
            evaluatedSymRef.insert(inverseArgCallNode[currentMethod][usefulNode][-3]);
         }

         int newSize = evaluatedSymRef.size();
         if (newSize == oldSize)
         {
            evaluatedSymRef.insert(-2);
         }
      }

      break;
   }

   case TR::Return:
   case TR::lreturn:
   case TR::ireturn:
   case TR::dreturn:
   case TR::freturn:
   case TR::areturn:
   case TR::vreturn:
   {

      // also, we only need to worry about the areturn. So why do we have the others here? Maybe want to process some cleanup
      //   actions on encountering a return op

      if (opCode == TR::areturn)
      {
         // the evaluated value of the first child (ie. the call node) will hold the respective call's return value - simply fetch and assign
         getVarSlots(usefulNode->getFirstChild(), comp, evaluatedSymRef, currentMethod);
         evaluatedSymRef.insert(-3);
      }
      break;
   }

   default:
   {
      evaluatedSymRef.insert(-2);
      //         TR_ASSERT_FATAL(true, "opcode %s not recognized", usefulNode->getOpCode().getName());
      break;
   }
   }
}

std::set<Entry *> getCachedPointsTo(TR::Node *node)
{
   TR::Node *usefulNode = getUsefulNode(node);
   return cachedValues[usefulNode];
}

PointsToGraph *buildCallsitePtg(TR::Node *callNode, PointsToGraph *in, TR_OpaqueMethodBlock *currentMethod,
                                TR::Compilation *comp, Counter &counter,
                                UniqueDeque<TR_OpaqueMethodBlock *> &workList,
                                std::unordered_map<TR_OpaqueMethodBlock *, UniqueDeque<int>> &reanalyze,
                                bool &flag, std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> &methodDict, std::unordered_set<TR::Node *> &nodeVisited)
{

   int argIndex = 1;

   PointsToGraph *callSitePtg = new PointsToGraph();

   int32_t firstArgIndex = callNode->getFirstArgumentIndex();
   int32_t numChildren = callNode->getNumChildren();
   for (int32_t i = firstArgIndex; i < numChildren; i++, argIndex++)
   {
      TR::Node *argNode = callNode->getChild(i);

      set<Entry *> argValues = processNode(argNode, currentMethod, comp, counter, workList, reanalyze, flag, methodDict, nodeVisited);
      if (argValues.size() == 0)
      {
         continue;
      }

      callSitePtg->setArg(argIndex, argValues);
   }

   callSitePtg->mergeReachableHeapFromOwnArgs(in);

   if (cachedValues.find(callNode) != cachedValues.end())
   {
      std::set<Entry *> retVal = cachedValues[callNode];
      callSitePtg->extend(inverseArgCallNode[currentMethod][callNode][-3], retVal);
      callSitePtg->setArg(0, retVal);
      callSitePtg->mergeReachableHeapFrom(methodPTG[currentMethod], retVal);
   }

   return callSitePtg;
}

Entry *evaluateAllocate(TR::Node *node, int methodIndex, int newType)
{
   if (nodeAllocationMap.find(node) != nodeAllocationMap.end())
   {
      return nodeAllocationMap[node];
   }

   int allocationBCI = node->getByteCodeIndex();
   int callerIndex = methodIndex;

   // check the loadaddr child node to ensure that the instantiated type is resolved
   TR::Node *loadaddrNode;
   if (newType == 0)
   {
      loadaddrNode = node->getFirstChild();
   }
   else
   {
      loadaddrNode = node->getSecondChild();
   }
   // std::cout<<"loadaddr node is "<<loadaddrNode<<"\n";
   // TR_ASSERT_FATAL(loadaddrNode->getOpCodeValue() == TR::loadaddr, "expected first child of jitnewobject to be loadaddr op");
   Entry *obj;

   if (loadaddrNode->getOpCodeValue() == TR::loadaddr && loadaddrNode->getSymbolReference()->isUnresolved())
   {
      /*
       * the instantiated type is unresolved, we interpret that as "not on classpath and/or unresolved"
       *
       * assign an empty set at the allocation site and call it a day
       */

      // return null as a stopgap, we do't have an object to represent "empty" yet. This is fine since we ignore nulls anyway
      std::cout << "loaddr null for " << methodIndex << "-" << node->getByteCodeIndex() << "\n";
      obj = PointsToGraph::nullEntry;
   }
   else
   {
      if (exhaustive)
      {
         if (entryMap.find(methodIndex) == entryMap.end() || entryMap[methodIndex].find(allocationBCI) == entryMap[methodIndex].end())
         {
            entryMap[methodIndex][allocationBCI] = new Entry();
         }

         obj = entryMap[methodIndex][allocationBCI];
         obj->bci = allocationBCI;
         obj->caller = methodIndex;
      }
      else
      {
         if (entryMap.find(methodIndex) == entryMap.end() || entryMap[methodIndex].find(allocationBCI) == entryMap[methodIndex].end())
         {
            std::cout << "some error " << methodIndex << "-" << allocationBCI << " must be present in duped info\n";
            entryMap[methodIndex][allocationBCI] = new Entry();
            obj = entryMap[methodIndex][allocationBCI];
            obj->bci = allocationBCI;
            obj->caller = methodIndex;
         }
         else
         {
            obj = entryMap[methodIndex][allocationBCI];
         }
      }

      if (newType != 2)
      {
         obj->clazz = (TR_OpaqueClassBlock *)loadaddrNode->getSymbol()->castToStaticSymbol()->getStaticAddress();
         if (newType == 0)
         {
            obj->type = Reference;
         }
         else
         {
            obj->type = RefArray;
         }
      }
      else
      {
         obj->type = PrimitiveArray;
         obj->clazz = NULL;
      }
   }

   nodeAllocationMap[node] = obj;

   return nodeAllocationMap[node];
}

// ************************ SECONDARY METHODS DEFN END (SME) ******************************************

// ************************ TERTIARY METHODS DEFN START (TMS) ******************************************
void printExhaustive()
{
   std::map<int, std::string> methodMap;
   ofstream ptgFile("ptg2.txt");
   int i = 0;
   int ptgCount = methodPTG.size();
   for (auto m : methodPTG)
   {
      i++;
      PointsToGraph *currentPTG = m.second;
      std::map<int, std::set<Entry *>> argSet = currentPTG->getArgs();
      std::map<int, std::set<Entry *>> rhoSet = currentPTG->getRho();
      std::map<Entry *, std::map<std::string, std::set<Entry *>>> sigmaSet = currentPTG->getSigma();
      int mi = methodPtrToIndex[m.first];
      if (mi == 0)
      {
         std::cout << "method not analyzed " << inverseMethodNameIDmapping[m.first] << "\n";
      }
      std::vector<std::string> rhoVector;

      ptgFile << mi << ":(";
      for (auto arg : argSet)
      {
         if (arg.second.size() > 0)
         {
            rhoVector.push_back(to_string(arg.first + 1) + ":" + join(arg.second, " "));
         }
      }
      for (auto r : rhoSet)
      {
         if (r.second.size() > 0)
         {
            if (r.first == -3)
            {
               rhoVector.push_back(to_string(0) + ":" + join(r.second, " "));
            }
            else
            {
               rhoVector.push_back(to_string(r.first) + ":" + join(r.second, " "));
            }
         }
      }
      ptgFile << joinVec(rhoVector, ",");
      ptgFile << ")(";

      bool commaFlag = false;
      int sigmaCount = sigmaSet.size();
      for (auto sig : sigmaSet)
      {
         if (sig.second.size() > 0)
         {
            Entry *et = sig.first;
            if (commaFlag)
            {
               ptgFile << "," << et->getString() << "(";
            }
            else
            {
               ptgFile << et->getString() << "(";
            }
            vector<std::string> sigmaVector;
            for (auto field : sig.second)
            {
               if (field.second.size() > 0)
               {
                  sigmaVector.push_back(field.first + ":" + join(field.second, " "));
               }
            }
            ptgFile << joinVec(sigmaVector, ",");
            ptgFile << ")";
            commaFlag = true;
         }
      }

      if (i != ptgCount)
      {
         ptgFile << ");";
      }
      else
      {
         ptgFile << ")";
      }
   }

   ptgFile.close();

   ofstream miFile("mi2.txt");
   map<int, std::string> inverseMethodIndices;
   for (auto m : _methodIndices)
   {
      inverseMethodIndices[m.second] = m.first;
   }
   for (auto m : inverseMethodIndices)
   {
      miFile << m.second << "\n";
      ofstream crFile("crr" + to_string(m.first) + ".txt");
      for (auto r : _callsiteReceivers[m.first])
      {
         crFile << r.first;
         for (auto s : r.second)
         {
            crFile << " " << s;
         }
         crFile << ";";
      }
      crFile.close();
   }

   miFile.close();
}

std::string getMethodName(TR::ResolvedMethodSymbol *m)
{
   char *methodNm = substring(m->getMethod()->nameChars(), 0, m->getMethod()->nameLength());
   char *clazz = substring(m->getMethod()->classNameChars(), 0, m->getMethod()->classNameLength());
   char *sig = substring(m->getMethod()->signatureChars(), 0, m->getMethod()->signatureLength());
   return std::string(clazz) + "." + methodNm + sig;
}

char *substring(const char *str, size_t start, size_t length)
{
   // Allocate memory for the new substring
   char *result = new char[length + 1];      // +1 for the null terminator
   std::memcpy(result, str + start, length); // Copy substring
   result[length] = '\0';                    // Null-terminate the result
   return result;
}

void pseudoTopoSort(TR::Block *currentBlock, std::vector<TR::Block *> &gray, std::vector<TR::Block *> &black, std::stack<TR::Block *> &sorted)
{
   if (find(gray.begin(), gray.end(), currentBlock) != gray.end())
   {
      return;
   }
   else
   {
      gray.push_back(currentBlock);
   }

   TR::CFGEdgeList successors = currentBlock->getSuccessors();
   for (TR::CFGEdgeList::iterator successorIt = successors.begin(); successorIt != successors.end(); ++successorIt)
   {
      TR::Block *successorBlock = toBlock((*successorIt)->getTo());

      if (find(black.begin(), black.end(), successorBlock) != black.end())
      {
         continue;
      }
      else
      {
         pseudoTopoSort(successorBlock, gray, black, sorted);
      }
   }

   gray.erase(find(gray.begin(), gray.end(), currentBlock));
   black.push_back(currentBlock);
   sorted.push(currentBlock);
}

bool isLibraryMethod(std::string methodName)
{

   bool isLibraryMethod = false;
   if (methodName.rfind("java/lang/Thread.start") == 0 || methodName.rfind("soot/rtlib/tamiflex/ReflectiveCallsWrapper", 0) == 0)
   {
      isLibraryMethod = false;
      return isLibraryMethod;
   }

   if (methodName.rfind("org/apache/lucene", 0) == 0 || methodName.rfind("org/apache/xalan", 0) == 0)
   {
      return false;
   }
   else
      isLibraryMethod = methodName.rfind("java/lang/Thread.start") != 0 &&
                            methodName.rfind("java", 0) == 0 ||
                        methodName.rfind("com/ibm/", 0) == 0 || methodName.rfind("sun/", 0) == 0 ||
                        methodName.rfind("openj9/", 0) == 0 || methodName.rfind("jdk/", 0) == 0 || methodName.find("org/apache", 0) == 0 || methodName.find("org/slf4j", 0) == 0 ||
                        methodName.rfind("soot", 0) == 0 || methodName.rfind("org/jfree", 0) == 0 || methodName.rfind("org/codehaus", 0) == 0;

   return isLibraryMethod;
}

std::string join(std::set<Entry *> const &entrySet, std::string delim)
{
   std::vector<std::string> strings;
   for (auto e : entrySet)
   {
      strings.push_back(e->getString());
   }
   std::stringstream ss;
   std::copy(strings.begin(), strings.end(), std::ostream_iterator<std::string>(ss, delim.c_str()));
   return ss.str().substr(0, ss.str().size() - 1);
}

std::string joinVec(std::vector<std::string> const &strings, std::string delim)
{
   std::stringstream ss;
   std::copy(strings.begin(), strings.end(), std::ostream_iterator<std::string>(ss, delim.c_str()));
   return ss.str().substr(0, ss.str().size() - 1);
}

TR_ResolvedMethod *getCachedResolvedMethodFromPtr(TR::Compilation *comp, TR_OpaqueMethodBlock *methodPtr)
{
   if (cachedResolvedMethodFromPtr.find(methodPtr) == cachedResolvedMethodFromPtr.end())
   {
      cachedResolvedMethodFromPtr[methodPtr] = comp->fej9()->createResolvedMethod(comp->trMemory(), methodPtr, 0);
   }
   return cachedResolvedMethodFromPtr[methodPtr];
}

TR_ResolvedMethod *getCachedResolvedMethod(TR::Compilation *comp, TR_OpaqueClassBlock *classPointer, const char *methodName, const char *signature)
{
   std::string meth = ((std::string)methodName) + ((std::string)signature);
   if (cachedResolvedMethod[classPointer].find(meth) == cachedResolvedMethod[classPointer].end())
   {
      TR_ResolvedMethod *rm = comp->fej9()->getResolvedMethodForNameAndSignature(comp->trMemory(), classPointer, methodName, signature);
      if (rm == NULL)
      {
         return NULL;
      }
      cachedResolvedMethod[classPointer][meth] = rm;
   }
   return cachedResolvedMethod[classPointer][meth];
}

bool canCast(Entry *e, TR_OpaqueClassBlock *type, TR::Compilation *comp)
{

   queue<TR_OpaqueClassBlock *> q;
   if (type == NULL)
   {
      // think thrice before changing this !!!!
      // std::cout<<"type checking found null "<<e.caller<<"-"<<e.bci<<"\n";
      // std::cout<<"method = "<<inverse_methodIndices[e.caller]<<"\n";
      if (e->caller == 249 && e->bci == 20)
      {
         // std::cout<<"reasonod1\n";
      }
      return true;
   }
   if (e->type == Global || e->type == Null || (e->clazz == NULL && e->type != PrimitiveArray && e->type != RefArray))
   {
      // if(cachedClassSignature.find(type) == cachedClassSignature.end()){
      //    cachedClassSignature[type] = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());
      // }
      // std::string typeName = cachedClassSignature[type];
      // std::cout<<"type name = "<<typeName<<"\n";

      if (e->caller == 249 && e->bci == 20)
      {
         // std::cout<<"reasonod2\n";
      }
      return true;
   }

   // std::cout<<"handling cast 1 \n";

   if (cachedClassSignature.find(type) == cachedClassSignature.end())
   {
      cachedClassSignature[type] = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());
   }
   std::string typeName = cachedClassSignature[type];

   // std::cout<<"type name = "<<typeName<<"\n";

   if ((typeName.find("java/") != std::string::npos || typeName.rfind("[", 0) == 0))
   {
      if (typeName.rfind("[Ljava/lang/String", 0) == 0 && e->type == PrimitiveArray)
      {
         return false;
      }
      return true;
   }
   TR_OpaqueClassBlock *current;
   // std::cout<<"handling cast 2\n";
   q.push(type);
   while (!q.empty())
   {
      // std::cout<<"handling cast 3\n";
      current = q.front();
      if (current == e->clazz)
      {
         return true;
      }
      q.pop();
      if (CHA.find(current) != CHA.end())
      {
         std::unordered_set<TR_OpaqueClassBlock *> child = CHA[current];
         for (auto c : child)
         {
            q.push(c);
         }
      }
   }

   return false;
}

void checkCycles()
{
   std::unordered_map<std::string, int> cycleFreeMethods(_methodIndices);
   std::deque<TR_OpaqueMethodBlock *> myStack;
   std::unordered_set<TR_OpaqueMethodBlock *> visited;
   cycleDFS(monitor1, myStack, visited);
}

void cycleDFS(TR_OpaqueMethodBlock *currentMethod, std::deque<TR_OpaqueMethodBlock *> &myStack, std::unordered_set<TR_OpaqueMethodBlock *> &visited)
{
   auto it = std::find(myStack.begin(), myStack.end(), currentMethod);
   if (it != myStack.end())
   {
      while (it != myStack.end())
      {
         cyclicMethods.insert(currentMethod);
         it++;
      }
   }
   else
   {
      if (visited.find(currentMethod) != visited.end())
      {
         return;
      }
      visited.insert(currentMethod);
      myStack.push_back(currentMethod);
      for (auto cc : myCallGraph[currentMethod])
      {
         for (auto target : cc.second)
         {
            cycleDFS(target, myStack, visited);
         }
      }
      myStack.pop_back();
   }
}

void calculateDirtyObjects(int argIndex, TR_OpaqueMethodBlock *currentMethod, std::set<Entry *> currentFlow, std::unordered_map<int, std::unordered_map<TR_OpaqueMethodBlock *, std::set<Entry *>>> inFlow, DeleteInfo &deleteInfo, std::unordered_map<int, std::set<Entry *>> &visited, TR_OpaqueMethodBlock *target, std::set<Entry *> &unreachableObjects)
{
   bool update1 = false;
   bool update2 = false;
   bool update3 = false;

   std::set<Entry *> safeInFlow;
   for (auto it2 : inFlow[argIndex])
   {
      TR_OpaqueMethodBlock *caller = it2->first;
      std::set<Entry *> unsafeObj;
      std::set_union(deleteInfo.track - set[caller].begin(), deleteInfo.track - set[caller].end(), deleteInfo.unreachable - set[caller].begin(), deleteInfo.unreachable - set[caller].end(), inserter(unsafeObj, unsafeObj.end()));
      std::set_difference(it2->second.begin(), it2->second.end(), unsafeObj.begin(), unsafeObj.end(), inserter(safeInFlow, safeInFlow.end()));
   }

   std::set<Entry *> temp_1;
   std::set<Entry *> temp_2;
   std::set<Entry *> temp_3;
   std::set<Entry *> temp_4;

   std::set_intersection(currentFlow.begin(), currentFlow.end(), deleteInfo.track - set[currentMethod].begin(), deleteInfo.track - set[currentMethod].end(), inserter(temp_1, temp_1.end()));
   std::set_difference(temp_1.begin(), temp_1.end(), safeInFlow.begin(), safeInFlow.end(), inserter(temp_2, temp_2.end()));
   if (!temp_2.empty())
   {
      deleteInfo.track - set[target].insert(temp_2.begin(), temp_2.end());
      update1 = true;
   }
   std::set_intersection(currentFlow.begin(), currentFlow.end(), deleteInfo.unreachable - set[currentMethod].begin(), deleteInfo.unreachable - set[currentMethod].end(), inserter(temp_3, temp_3.end()));
   std::set_intersection(currentFlow.begin(), currentFlow.end(), unreachableObjects.begin(), unreachableObjects.end(), inserter(temp_3, temp_3.end()));
   std::set_difference(temp_3.begin(), temp_3.end(), safeInFlow.begin(), safeInFlow.end(), inserter(temp_4, temp_4.end()));
   if (!temp_4.empty())
   {
      deleteInfo.unreachable - set[target].insert(temp_4.begin(), temp_4.end());
      update2 = true;
   }

   std::set_differenc

       for (auto e : currentFlow)
   {
      if (visited[argIndex].find(e) == visited[argIndex].end())
      {
         visited[argIndex].insert(e);
         std::set<Entry *> recCurrentFlow;
         std::unordered_map<int, std::unordered_map<TR_OpaqueMethodBlock *, std::set<Entry *>>> recInFlow;
         for (auto f : methodPTG[currentMethod]->getFieldMap(e))
         {
            recCurrentFlow.insert(f.second.begin(), f.second.end());
            for (auto it2 : inFlow[argIndex])
            {
               TR_OpaqueMethodBlock *caller = it2->first;
               std::set<Entry *> temp_2 = methodPTG[caller]->getPointsToSet(e, f.first);
               recInFlow[argIndex][caller].insert(temp_2.begin(), temp_2.end());
            }
         }
         update3 = calculateDirtyObjects(argIndex, currentMethod, recCurrentFlow, recInFlow, deleteInfo, visited, target, unreachableObjects);
      }
   }

   for (auto it1 : currentFlow)
   {
   }

   return (update1 || update2 || update3);
}

void addReachableBottomToDeleteMap(std::set<Entry *> &source, DeleteInfo &deleteInfo, TR_OpaqueMethodBlock *currentMethod)
{
   std::deque<Entry *> workList;
   std::unordered_set<Entry *> visited;
   workList.insert(workList.end(), source.begin(), source.end());
   visited.insert(source.begin(), source.end());
   while (!workList.empty())
   {
      Entry *currEntry = workList.front();
      workList.pop_front();
      if (currEntry == PointsToGraph::nullEntry || currEntry == PointsToGraph::bottomEntry || currEntry == PointsToGraph::stringEntry || currEntry == PointsToGraph::classEntry)
      {
         continue;
      }

      std::map<std::string, std::set<Entry *>> fieldMap = methodPTG[currentMethod]->getFieldMap(currEntry);
      for (auto f : fieldMap)
      {
         for (auto e : f.second)
         {
            if (visited.find(e) == visited.end())
            {
               visited.insert(e);
            }
         }
         deleteInfo.deleteMap[currEntry][f.first].insert(PointsToGraph::bottomEntry);
      }
   }
}

bool hasCommonElement(std::set<Entry *> &source, DeleteInfo &deleteInfo)
{
   for (auto e : source)
   {
      if (deleteInfo.deleteMap.find(e) != deleteInfo.deleteMap.end() || deleteInfo.trackMap.find(e) != deleteInfo.trackMap.end())
      {
         return true
      }
   }
   return false;
}

// ************************ TERTIARY METHODS DEFN END (TME) ******************************************

// omkar -todo - print mi2.txt and crr.txt - right now it is commented.
// omkar -todo - deleteInfo.worklist gets empty , so fixpoint won't happen in second iteration. prevent from getting empty

// issue - when reachable return changes, ccaller gets called only when return stmt is analyzed. update it so that it happens everytime.

// java/security/MessageDigest
// java/security/Security
// java/security/MessageDigest$Delegate
// java/security/MessageDigestSpi
// java/security/Provider
// java/security/NoSuchAlgorithmException
// java/security/GeneralSecurityException
// java/security/ProtectionDomain
// java/security/CodeSource

// new strategy
// 2 global maps - track-map and dirty-map
// 1 local set - track-set -> propagated only through method args and return var

// in hcr method
// x.f = y
// for obj in pts(x):
//    dirty-map[obj][f].insert(pts(y))

// in findAffectedInfo
//
// y = x.f
// for obj in pts(x):
// if track-map.contains(obj, f):
//    track-set.insert(track-map[obj][f])
//    reanalyze.insert(stmt)
// elif dirty-map.contains(obj, f):
//    track-set.insert(dirty-map[obj][f])
//    reanalyze.insert(stmt)
// elif track-set.contains(obj):
//    track-set.insert(pts(obj, f))
//    reanalyze.insert(stmt)

// y.f = x
// for obj in pts(y):
//    if obj in track-set:
//       dirty-map[rec][f].insert(pts(x))
//       reanalyze.insert(stmt)
//    else:
//       for entry in pts(x):
//          if entry in track-set:
//             track-map[obj][f].insert(entry)
//             reanalyze.insert(stmt)
//
//    if dirty-map.contains(obj,f) AND !reanalyze.contains(stmt):
//       reanalyze.insert(stmt)