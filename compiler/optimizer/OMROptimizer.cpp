/*******************************************************************************
 * Copyright IBM Corp. and others 2000
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at https://www.eclipse.org/legal/epl-2.0/
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
 * [2] https://openjdk.org/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0-only WITH Classpath-exception-2.0 OR GPL-2.0-only WITH OpenJDK-assembly-exception-1.0
 *******************************************************************************/

#include "optimizer/Optimizer.hpp"

#include "optimizer/Optimizer_inlines.hpp"

#include <bits/stdc++.h>

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
//
#include "il/ParameterSymbol.hpp"
#ifndef PAG_POINTER_ASSIGNMENT_GRAPH_CPP
#define PAG_POINTER_ASSIGNMENT_GRAPH_CPP
#include "optimizer/PAG/PointerAssignmentGraph.hpp"
#endif

#ifndef PAG_COMPONENTS_CPP
#define PAG_COMPONENTS_CPP
#include "optimizer/PAG/PAG_Components.hpp"
#endif

#include "env/VMAccessCriticalSection.hpp"
#include "../../gc/structs/PoolIterator.hpp"
#include "../../gc/structs/PoolIterator.cpp"
// #include "../../../openj9/runtime/compiler/runtime/Recompilation_test/recompilation_test.cpp"
#include "methodSet.cpp"
#include <regex>
namespace TR
{
   class AutomaticSymbol;
}

using namespace OMR; // Note: used here only to avoid having to prepend all opts in strategies with OMR::

#define MAX_LOCAL_OPTS_ITERS 5

// ******start****]

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

//

static PointerAssignmentGraph *pag = nullptr;
extern PointerAssignmentGraph *pag_to_use;

//(method name, symbol ref, PAGNode*)
static unordered_map<TR_OpaqueMethodBlock *, unordered_map<int32_t, PAGNode *>> symRefNumToPAGNode;
static unordered_map<int32_t, TR::Node *> symRefNumToNode;
static bool done = false;
static std::unordered_map<TR_OpaqueClassBlock *, std::unordered_set<std::string>> clazz_to_fields;
static std::unordered_map<std::string, std::unordered_set<std::string>> className_to_fields;
static std::unordered_map<std::string, PAGNode *> staticField_to_Node;
static std::unordered_map<TR::Node *, int> nodeToLineNumber;
static std::unordered_map<int,PAGNode*> symref_PAGNode;
static std::unordered_map<TR_OpaqueMethodBlock *,TR::ResolvedMethodSymbol *> methodBlock_to_ResolvedMethodSymbol;
int getCachedLineNumber(TR::Node *node, TR::Compilation *comp);
//
TR::ResolvedMethodSymbol * getCachedResolvedMethodSymbol(TR::Compilation* comp,TR_OpaqueMethodBlock * method_block);
bool exhaustive = false;
static std::unordered_map<TR_OpaqueClassBlock *, int> classPtrToIndex;

void printMatch();
void calculateMatch();
void updateMatchEdges();
// std::string join(std::set<Entry> const &entrySet, std::string delim);
std::string joinVec(std::vector<std::string> const &strings, std::string delim);
// bool canCast(Entry e, TR_OpaqueClassBlock* type, TR::Compilation* comp);
void constructCHA(TR::Compilation *comp);
void getResolvedReflectiveCalls();
void buildIndependentSet(TR::Compilation *comp);
void benchmarkBuildIndependentSet(TR::Compilation *comp);
int evaluateNode(TR::Node *node, std::map<TR::Node *, int> &evaluatedNodeValues, Counter &counter, int methodIndex, MethodSet &mSet, TR_OpaqueMethodBlock *currentMethodSymbol, TR::Compilation *comp, bool populatePTA);
void collectStmt(TR_OpaqueMethodBlock *HCRmethod, TR::Compilation *comp, bool addStmt);
TR_ResolvedMethod *getCachedResolvedMethod(TR::Compilation *comp, TR_OpaqueClassBlock *classPointer, const char *methodName, const char *signature);
TR_ResolvedMethod *getCachedResolvedMethodFromPtr(TR::Compilation *comp, TR_OpaqueMethodBlock *methodPtr);
TR_MethodParameterIterator *getCachedIterFromRM(TR::Compilation *comp, TR_ResolvedMethod *tempRM);
std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<int>> getVarMapping(TR_OpaqueMethodBlock *currentMethod, int currentVar, TR_OpaqueMethodBlock *HCRmethod);
TR::Node *getUsefulNode(TR::Node *node);
std::unordered_set<std::string> getClassFields(J9Class *clazz, J9VMThread *vmThread);
void performDelete(TR::Compilation *comp, std::map<TR_OpaqueMethodBlock *, std::set<int>> delStmt);
void finalReanalyze(TR::Node *usefulNode, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp);
void refineCollect(TR::Compilation *comp);
bool isTransparentMethod(std::string methodName);
void printPAG(TR::Compilation *);
void printLPAG(PointerAssignmentGraph *lpag);
extern std::map<int, std::set<int>> readReceivers(int methodIndex);
extern std::unordered_map<int, std::string> readClassIndices();
std::unordered_map<std::string, int> readMethodIndices();
extern std::unordered_set<int> readPartiallyAnalysedMethodIndices();
// extern map<int, PointsToGraph> readPTG(string fileName);
// extern std::unordered_map<std::string, Entry> rawNode;
std::string getMethodName(TR::ResolvedMethodSymbol *m);
int getOrInsertMethodIndex(TR::ResolvedMethodSymbol *methodSymbol, TR::Compilation *comp);
void performRuntimePTA(TR::Compilation *comp);
MethodSet computeMSetForMethod(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol);
bool isLibraryMethod(std::string methodName);
void writeNodesToFile(TR::Compilation *, PointerAssignmentGraph *p);
void printExhaustive();
void getAlreadyAnalyzedMethodNames();
std::unordered_set<std::string> getReflectiveTargets(std::string &caller, int lineNumber);
// std::set<Entry> processNode(TR::Node *node, int methodIndex, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp,
//                               Counter &counter, std::unordered_map<TR_OpaqueMethodBlock*,
//                                  std::set<int>> &reanalyzeStmt, std::unordered_map<TR_OpaqueMethodBlock*, std::set<int>> &parentVisited,
//                                  std::unordered_map<TR_OpaqueMethodBlock*, std::set<int>> &work, deque<TR_OpaqueMethodBlock*> &mainWorklist,
//                                  std::unordered_set<TR_OpaqueMethodBlock*> &presentInWorklist);

// PointsToGraph *buildCallsitePtg(TR::Node *callNode, PointsToGraph *in, int methodIndex, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp,
//                                  Counter &counter, std::unordered_map<TR_OpaqueMethodBlock*,
//                                     std::set<int>> &reanalyzeStmt, std::unordered_map<TR_OpaqueMethodBlock*, std::set<int>> &parentVisited,
//                                        std::unordered_map<TR_OpaqueMethodBlock*, std::set<int>> &work, deque<TR_OpaqueMethodBlock*> &mainWorklist,
//                                           std::unordered_set<TR_OpaqueMethodBlock*> &presentInWorklist);

void addReachableVariable(int argNum, TR::Node *callStmt, TR_OpaqueMethodBlock *currentMethod, std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &parentVisited,
                          std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> &work, std::deque<TR_OpaqueMethodBlock *> &mainWorklist,
                          std::unordered_set<TR_OpaqueMethodBlock *> &presentInWorklist, bool isCaller);
void pseudoTopoSort(TR::Block *currentBlock, std::vector<TR::Block *> &gray, std::vector<TR::Block *> &black, std::stack<TR::Block *> &sorted);

PAGNode *evaluateAllocate(TR::Node *node, int methodIndex, bool isArray, TR::Compilation *);

struct CallInfo
{
   std::string callee;
   int lineNumber;

   CallInfo(const std::string &callee, int line)
       : callee(callee), lineNumber(line) {}
};

static std::unordered_map<std::string, std::vector<CallInfo>> reflectiveCallGraph;

// bool isEqual(PointsToGraph *ptg1, PointsToGraph *ptg2);

// void printExhaustive();

// (method name, int)
// static std::unordered_map<std::string, int> _methodIndices;

// static map<int, PointsToGraph> _indexPTG;

static std::unordered_set<int> _partiallyAnalysedMethodIndices;

// (int, classname)
static std::unordered_map<int, std::string> _classIndices;

// methods that were analyzed till now
static std::unordered_set<TR_OpaqueMethodBlock *> _methodsAnalyzed;

// do we need this ?
static std::unordered_set<TR_OpaqueMethodBlock *> _methodsBeingAnalyzed;

// (method, callsiteBCI, class indice)
static std::unordered_map<int, std::map<int, std::set<int>>> _callsiteReceivers;

// (method, mset)
static std::unordered_map<TR_OpaqueMethodBlock *, MethodSet> methodDict;

// (method, callnode, method) -update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR::Node *, std::unordered_set<TR_OpaqueMethodBlock *>>> myCallGraph;

// edges that need to be deleted
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR::Node *, std::unordered_set<TR_OpaqueMethodBlock *>>> myCallGraphDelete;

// (method, method, callnode) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<TR::Node *>>> myInverseCallGraph;

// edges that need to be deleted
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<TR::Node *>>> myInverseCallGraphDelete;

// used to recognize thread type
TR_OpaqueMethodBlock *_threadStartPersistentId;

// methods analyzed
std::unordered_set<std::string> alreadyAnalyzedMethods;

// (method, int)
static std::unordered_map<TR_OpaqueMethodBlock *, int> _methodIndicesPtr;

// (method, callnode)
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_set<TR::Node *>> callNodeMap;

// (callnode, argument_list)
static std::unordered_map<TR::Node *, std::vector<int>> callNodeArgumentList;

// static std::unordered_map<TR::Node*, std::map<int, std::set<Entry>>> callNodeArgs;

// (method, variable symref, callnode, argument number) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, std::unordered_set<std::pair<TR::Node *, int>>>> argCallNode;

// (method, callnode, argument number, variable symref) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<TR::Node *, std::unordered_map<int, int>>> inverseArgCallNode;

// (method, argument symref, argument number) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, int>> formalParMethod;

// (method, argument number, argument symref) - update - done
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, int>> inverseFormalParMethod;

// (methodName, method)
static std::unordered_map<std::string, TR_OpaqueMethodBlock *> methodNameIDmapping;
static std::unordered_map<TR_OpaqueMethodBlock *, std::string> inverseMethodNameIDmapping;

// (method, PTG) //readptg
// static std::unordered_map<TR_OpaqueMethodBlock *, PointsToGraph *> methodPTG;

// exhaustive ptg
// static std::unordered_map<TR_OpaqueMethodBlock *, PointsToGraph *> methodPTG1;

// (method, set(nodes))
static std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> reanalyze;

// (method, set(nodes))
static std::unordered_map<TR_OpaqueMethodBlock *, std::set<int>> refineReanalyze;

// (callsiteBCI, class Indice)

// (class, set(child Class))
static std::unordered_map<TR_OpaqueClassBlock *, std::unordered_set<TR_OpaqueClassBlock *>> CHA;

// stmt number to stmt(node)
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, TR::Node *>> stmtNumber;

static std::unordered_set<TR_OpaqueMethodBlock *> topLevelMethods;

static std::unordered_set<TR_OpaqueMethodBlock *> topLevelVisited;

static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, int>> argToSymRef;

static std::unordered_map<Node *, PAGNode *> nodeAllocationMap;
static std::unordered_map<TR_OpaqueMethodBlock *, std::unordered_map<int, TR_OpaqueClassBlock *>> cachedParameterType;

// static std::unordered_map<TR::Node*, std::set<Entry>> processNodeValues;

// static std::unordered_map<TR::Node*, PointsToGraph*> callSiteStore;

static std::unordered_map<TR_OpaqueClassBlock *, std::unordered_map<std::string, TR_ResolvedMethod *>> cachedResolvedMethod;

static std::unordered_map<TR_OpaqueMethodBlock *, TR_ResolvedMethod *> cachedResolvedMethodFromPtr;

static std::unordered_map<TR_ResolvedMethod *, TR_MethodParameterIterator *> cachedIter;

static std::unordered_map<TR::Node *, std::string> cachedMethodName;

static std::unordered_map<TR_OpaqueClassBlock *, std::string> cachedClassSignature;

static std::unordered_map<TR_OpaqueMethodBlock *, int> methodPtrToIndex;

static std::unordered_map<TR_OpaqueClassBlock *, string> classPtrToName;

static std::unordered_map<int, std::unordered_set<PAGNode *>> callsite_to_ActualParamPAGNodes; // [callsiteBCI->[actual param PAG nodes]]
static std::unordered_map<TR::Node *, std::unordered_set<TR_OpaqueMethodBlock *>> callsite_to_targets;
static std::unordered_map<PAGNode *, PAGNode *> abstractNode_to_assignedVar; // o1 --new--> b then (o1,b)
static std::unordered_map<string, PAGNode *> class_to_staticPAGNode;
static std::unordered_map<int, PAGNode *> callsite_to_storeNode;

#define STATIC_FIELD_READ -10866 // unique negative code for static field read.
#define RETURN_NODE_NAME -56765  // UNIQUE NAME for return node

// static std::set<Entry> removeDelta;
// static std::map<TR_OpaqueMethodBlock*, std::set<Entry>> interestingNodes;
// static std::map<TR_OpaqueMethodBlock*, std::set<Entry>> simpleDelete;

static std::set<Node *> affectedNodes;

static bool change = false;
static bool flag = true;
static bool mostImpFlag = false;

static bool hotCodeReplaceFlag = false;

// static std::unordered_map<TR_OpaqueMethodBlock*, std::unordered_set<TR::Node *>> methodBody;
// store all stmts of method

// stats
static std::vector<float> collectStmtResult;
static std::vector<float> flowTime;
static std::vector<float> refineResult;
static std::vector<float> propTime;
static std::vector<float> refTime;
static std::vector<float> totalTime;
static std::vector<TR_OpaqueMethodBlock *> expMethod;
// **** end ****

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
        {explicitNewInitialization, IfNews}, // do before local dead store
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
        {globalValuePropagation, IfLoopsMarkLastRun},
        {treeSimplification, IfEnabled},
        {cheapObjectAllocationGroup},
        {treeSimplification, IfEnabled},
        {catchBlockRemoval, IfEnabled},                                    // if checks were removed
        {osrExceptionEdgeRemoval},                                         // most inlining is done by now
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
        {localDeadStoreElimination, IfOneBlock},
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
        {compactLocals, IfNotJitProfiling}, // analysis results are invalidated by jitProfilingGroup
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

static int optimize_count = 0;
void OMR::Optimizer::optimize()
{
   optimize_count++;
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
   //---------END OF EXISTING CODE--------------
   if (comp()->getOption(TR_RunMyAnalysis))// /*&& comp()->getOption(TR_DumpPAG)*/ && optimize_count == 1 && !done)
   {
   //    done = true;
   //    if (comp()->getOption(TR_DumpPAG))
   //       printPAG(comp());

      // writeNodesToFile(comp(), pag);
   }

   //    std::ofstream outFile("analyzedMethods.txt");

   //    for (auto *omb : _methodsAnalyzed)
   //    {
   //       if (omb == nullptr)
   //          continue;

   //       TR_ResolvedMethod *Method = getCachedResolvedMethodFromPtr(comp(), omb);
   //       TR::ResolvedMethodSymbol *ResolvedMethodSymbol = Method->findOrCreateJittedMethodSymbol(comp());

   //       std::string methodName = getMethodName(ResolvedMethodSymbol);
   //       outFile << methodName << std::endl;
   //    }

   //    outFile.close();

   //    // std::string nodeFile = "nodes.txt";
   //    // std::string edgeFile = "PAGEdges.txt";
   //    // std::string methodNodeMappingFile = "methods_to_PAGNodes.txt";

   //    // LoadPAG loader(nodeFile, edgeFile, methodNodeMappingFile);
   //    // PointerAssignmentGraph *loaded_pag = loader.getPAG();
   //    // std::cout << "-----Printing Loaded PAG-----" << std::endl;
   //    // if (loaded_pag)
   //    //    printLPAG(loaded_pag);
   //    // for(auto* node:loaded_pag->PAG_nodes)
   //    // {
   //    //    if(node->type == VARIABLE)
   //    //    {
   //    //       std::unordered_set<PAGNode*> pts =  regularPT(node);
   //    //       std::cout << "PTS of " << *node << "&& \n";
   //    //       for(auto o : pts)
   //    //       {
   //    //          std::cout << "[ \n " << *o << " \n ]\n";
   //    //       }
   //    //    }
   //    // }
   // }

   optimize_count--;
}
std::vector<pair<int, vector<PAGNode *>>> sortMethodsByIndex(const unordered_map<int, vector<PAGNode *>> &methods_to_formalNodes, TR::Compilation *comp)
{
   vector<pair<int, vector<PAGNode *>>> sorted_entries(methods_to_formalNodes.begin(), methods_to_formalNodes.end());

   sort(sorted_entries.begin(), sorted_entries.end(),
        [comp](const pair<int, vector<PAGNode *>> &a, const pair<int, vector<PAGNode *>> &b)
        {
           int indexA = a.first;
           int indexB = b.first;
           return indexA < indexB;
        });

   return sorted_entries;
}

int getNodeIndex(PAGNode *node, std::unordered_map<string, int> nodeIndices)
{
   return nodeIndices[std::to_string(node->bci) + "," + std::to_string(node->methodIndex) + "," + std::to_string(node->type) + "," + std::to_string(node->name)];
}

void writeNodesToFile(TR::Compilation *comp, PointerAssignmentGraph *pag)
{
   std::ofstream outfile("nodes.txt");
   std::ofstream edgesfile("PAGEdges.txt");

   if (!outfile.is_open() || !edgesfile.is_open())
   {
      std::cerr << "Failed to open file for writing.\n";
      return;
   }
   int index = 1;
   std::unordered_map<string, int> nodeIndices;
   for (const auto &node : pag->PAG_nodes)
   {
      outfile << "["
              << node->bci << ","
              << node->methodIndex << ","
              << node->type << ","
              << node->name << ",";

      if (pag->LeakyNodes.find(node) != pag->LeakyNodes.end())
      {
         outfile << "1,";
      }
      else
         outfile << "0,";
      for (std::string cname : node->pointee_class_names)
      {
         outfile << cname << ",";
      }
      outfile << "]\n";

      std::string nodeKey = std::to_string(node->bci) + "," + std::to_string(node->methodIndex) + "," + std::to_string(node->type) + "," + std::to_string(node->name);
      nodeIndices[nodeKey] = index++;
   }
   outfile.close();

   for (const auto &node : pag->PAG_nodes)
   {
      int srcNodeIndex = getNodeIndex(node, nodeIndices);
      edgesfile << srcNodeIndex << ":";
      for (auto *edge : node->outgoing)
      {
         auto *dest = edge->dest;

         std::string indexkey = std::to_string(dest->bci) + "," + std::to_string(_methodIndicesPtr[dest->caller]) + "," +
                                std::to_string(dest->type) + "," +
                                std::to_string(dest->name);

         // std::cout << "Index key is " << indexkey << std::endl;
         int destNodeIndex = nodeIndices[indexkey];
         if (destNodeIndex == 0 && pag->staticFields.find(edge->field) != pag->staticFields.end())
         {
            destNodeIndex = getNodeIndex(staticField_to_Node[edge->field], nodeIndices);
         }
         edgesfile << "["
                   << destNodeIndex << ","
                   << edge->type << ","
                   << edge->field << ","
                   << edge->callsiteBCI << "];";
      }
      edgesfile << "\n";
   }
   edgesfile.close();
   // outfile.close();
   // sort the node mappings
   std::vector<pair<int, vector<PAGNode *>>> sortedMappings = sortMethodsByIndex(pag->methods_to_allMethodNodes, comp);

   // dump, method to node maps
   std::ofstream mToNodesfile("methods_to_PAGNodes.txt"); // methodIndex: [nodeIndex,formalNode=1/non-formal=0]*
   for (const auto &entry : sortedMappings)
   {
      // TR_OpaqueMethodBlock *omb = entry.first;
      // TR_ResolvedMethod *resolvedMethod = getCachedResolvedMethodFromPtr(comp, omb);
      // TR::ResolvedMethodSymbol *resolvedMethodSymbol = resolvedMethod->findOrCreateJittedMethodSymbol(comp);

      mToNodesfile << entry.first << ":";

      const std::vector<PAGNode *> &allNodes = entry.second;
      const std::vector<PAGNode *> &formalNodes = pag->methods_to_formalNodes[entry.first];

      for (PAGNode *node : allNodes)
      {
         mToNodesfile << "[" << getNodeIndex(node, nodeIndices) << ",";
         int isFormalNode = 0;

         for (PAGNode *n : formalNodes)
         {
            if (node == n)
            {
               isFormalNode = 1;
               break;
            }
         }

         mToNodesfile << std::to_string(isFormalNode) << "];";
      }

      mToNodesfile << "\n";
   }

   mToNodesfile.close();

   std::ofstream callgraphfile("callgraph.txt"); // (CallsiteBCI,receiverIndex):[methodIndex1,comma seperated list of actual paramter PAGNode*,];[methodIndex2,comma seperated list of actual paramter PAGNode*,]

   for (auto entry = callsite_to_targets.begin(); entry != callsite_to_targets.end(); entry++)
   {
      TR::Node *callsite = entry->first;
      const std::unordered_set<TR_OpaqueMethodBlock *> &targets = entry->second;
      int callsite_bci = callsite->getByteCodeIndex();
      int nodeindex = callsite_to_storeNode[callsite_bci] ? getNodeIndex(callsite_to_storeNode[callsite_bci], nodeIndices) : -90898;
      callgraphfile << "(" << callsite_bci << "," << nodeindex << "):";
      for (auto *target : targets)
      {
         int targetIndex = getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,target), comp);
         callgraphfile << "[" << targetIndex << ",";
         for (auto *actual_param : callsite_to_ActualParamPAGNodes[callsite_bci])
         {
            int node_index = getNodeIndex(actual_param, nodeIndices);
            callgraphfile << node_index << ",";
         }
         callgraphfile << "];";
      }
      callgraphfile << "\n";
   }

   callgraphfile.close();

   std::ofstream tf("threadAccesible.txt");
   for (auto field : pag->threadAccessibleFields)
   {
      tf << field << std::endl;
   }
   tf.close();

   std::ofstream sf("staticFields.txt");
   for (auto field : pag->staticFields)
   {
      sf << field << std::endl;
   }
   sf.close();
   // std::ofstream returnNodesfile("methods_to_returnPAGNodes.txt"); //methodIndex:nodeIndex
   // for(auto entry:pag->methods_to_returnNode)
   // {
   //    TR_OpaqueMethodBlock* omb = entry.first;
   //    TR_ResolvedMethod *resolvedMethod = getCachedResolvedMethodFromPtr(comp, omb);
   //    TR::ResolvedMethodSymbol *ResolvedMethodSymbol = resolvedMethod->findOrCreateJittedMethodSymbol(comp);

   //    returnNodesfile  << getOrInsertMethodIndex(ResolvedMethodSymbol,comp) <<":" << getNodeIndex(entry.second,nodeIndices) << "\n";
   // }

   // returnNodesfile.close();
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

void printPAG(TR::Compilation *comp)
{
   // Mycode

   if (!isLibraryMethod(getMethodName(comp->getMethodSymbol())))
   {
      std::cout << "*******PRINTING PAG********" << std::endl;
      for (PAGNode *node : pag->PAG_nodes)
      {
         std::cout << " [\n ";
         std::cout << (*node);
         std::cout << "]\n";
      }
   }
}

void printLPAG(PointerAssignmentGraph *lpag)
{
   // Mycode

   // if (!isLibraryMethod(getMethodName(comp->getMethodSymbol())))
   // {
   //    std::cout << "*******PRINTING PAG********" << std::endl;
   for (PAGNode *node : lpag->PAG_nodes)
   {
      std::cout << " [\n ";
      std::cout << (*node);
      std::cout << "]\n";
   }
   // }
}

int32_t OMR::Optimizer::performOptimization(const OptimizationStrategy *optimization, int32_t firstOptIndex, int32_t lastOptIndex, int32_t doTiming)
{

   //******** My code start********

   // if (_classIndices.empty())
   // {

   //    _classIndices = readClassIndices();
   //    // cout << "reading class indices" << endl;

   // }

   // if (!exhaustive && _indexPTG.empty())
   // {
   //    _indexPTG = readPTG("ptg1.txt");
   //    // std::cout<<"ptg reading done\n";
   // }

   // string env_flag = std::getenv("RUN_MY_PASS");
   // if(env_flag.find("True")!=string::npos)
   if (pag == nullptr && pag_to_use != nullptr)
   {
      pag = pag_to_use;
   }
   else if (pag == nullptr)
   {
      pag = new PointerAssignmentGraph();
   }

   if (!isLibraryMethod(getMethodName(comp()->getMethodSymbol())))
   {

      if (comp()->getOption(TR_RunMyAnalysis))
      {
         if (/*!exhaustive &&*/ pag->_methodIndices.empty())
         {
            // cout << "reading method indices" << endl;
            pag->_methodIndices = readMethodIndices();

            // _partiallyAnalysedMethodIndices = readPartiallyAnalysedMethodIndices();
         }
         if (!_threadStartPersistentId)
         {
            // fetch a persistent oject for the thread.start method
            int len = strlen("java/lang/Thread");
            TR_OpaqueClassBlock *type = comp()->fe()->getClassFromSignature("java/lang/Thread", len, comp()->getCurrentMethod(), true);
            TR_ASSERT_FATAL(type, "unable to get class pointer for receiver %s", "java/lang/Thread");
            // std::cout<<"thread ptr success"<< type <<std::endl;
            TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp(), type, "start", "()V");
            TR_ASSERT_FATAL(targetMethod, "unable to find method for name and signature %s %s", "start", "()V");
            TR::ResolvedMethodSymbol *targetMethodSymbol = targetMethod->findOrCreateJittedMethodSymbol(comp());
            TR_ASSERT_FATAL(targetMethodSymbol, "unable to find method for name and signature %s %s", "start", "()V");
            _threadStartPersistentId = targetMethod->getPersistentIdentifier();

            // std::cout << "Thread start id: " << _threadStartPersistentId << std::endl;
         }

         benchmarkBuildIndependentSet(comp());
         // if (comp()->getOption(TR_PrintPAG)) //&& !done)
         // {
         //    done = true;
         //    printPAG(comp());
         // }
      }
   }
   // ********my code ends********
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

   case IfJitProfiling:
      if (comp()->getProfilingMode() == JitProfiling)
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
   case IfExceptionHandlers:
   {
      if (comp()->hasExceptionHandlers())
         doThisOptimization = true;
   }
   break;
   case IfLoopsAndNotCompileTimeSensitive:
   {
      if (comp()->mayHaveLoops() && comp()->getOption(TR_NotCompileTimeSensitive))
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
            TR_ASSERT_FATAL(!node1->getDataType().isMask(), "OMR does not support mask constants\n");

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
         TR::AutomaticSymbol *pinning1 = node1->hasPinningArrayPointer() ? node1->getPinningArrayPointer() : NULL;
         TR::AutomaticSymbol *pinning2 = node2->hasPinningArrayPointer() ? node2->getPinningArrayPointer() : NULL;
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

/***** The newly added methods begins below *****/

// (performOptimization) -> benchmarkBuildIndependentSet -> computeMSetForMethod -> evaluateNode
//       ^                                                                             ^
//       |                                                                             |
//    Existing code                                                           Opcode wise evaluation

void benchmarkBuildIndependentSet(TR::Compilation *comp)
{

   // std::cout<<"**************************************************************"<<std::endl;
   // printSet();
   // std::cout<< sig <<std::endl;

   if (isLibraryMethod(getMethodName(comp->getMethodSymbol())))
      return;

   if (CHA.size() == 0)
   {
      constructCHA(comp);
      getAlreadyAnalyzedMethodNames();
      getResolvedReflectiveCalls();
      // printf("=== Class Hierarchy Analysis (CHA) ===\n");
      // printf("Total parent classes: %zu\n", CHA.size());

      // for (auto &entry : CHA)
      // {
      //    TR_OpaqueClassBlock *parentClass = entry.first;
      //    const std::unordered_set<TR_OpaqueClassBlock *> &childClasses = entry.second;

      //    std::string parentClassName = "Unknown";
      //    char *classSignature = TR::Compiler->cls.classSignature(comp, parentClass, comp->trMemory());
      //    if (classSignature)
      //    {
      //       parentClassName = std::string(classSignature);
      //    }

      //    printf("\n-----Parent Class: %s (ptr: %p)-----\n", parentClassName.c_str(), parentClass);
      //    printf(" Child classes (%zu):\n", childClasses.size());

      //    for (TR_OpaqueClassBlock *childClass : childClasses)
      //    {
      //       std::string childClassName = "Unknown";

      //       char *childClassSignature = TR::Compiler->cls.classSignature(comp, childClass, comp->trMemory());
      //       if (childClassSignature)
      //       {
      //          childClassName = std::string(childClassSignature);
      //       }

      //       printf("    %s\n", childClassName.c_str());
      //    }
      // }

      // printf("\n=== End CHA ===\n");
   }

   TR_OpaqueMethodBlock *methodPersistentId = comp->getMethodSymbol()->getResolvedMethod()->getPersistentIdentifier();
   std::string tempCName = comp->getMethodSymbol()->getResolvedMethod()->classNameChars();
   std::string actCName = tempCName.substr(0, comp->getMethodSymbol()->getResolvedMethod()->classNameLength());
   if (_methodsAnalyzed.find(methodPersistentId) == _methodsAnalyzed.end())
   {
      std::cout << "**************************************************************analyzing " << getMethodName(comp->getMethodSymbol()) << " in OMROptimizer.cpp**************************************************************" << std::endl;

      _methodsAnalyzed.insert(methodPersistentId);
      _methodsBeingAnalyzed.insert(methodPersistentId);
      //  std::cout << "Compiling : " << getMethodName(comp->getMethodSymbol()) << std::endl;

      //  return;
      methodDict[methodPersistentId] = computeMSetForMethod(comp, comp->getMethodSymbol());

      std::cout << "**************************************************************Done analyzing " << getMethodName(comp->getMethodSymbol()) << " in OMROptimizer.cpp**************************************************************" << std::endl;

      // methodDict[methodPersistentId] =
      // recompilation_test* rec = new recompilation_test();
      // J9Method* curr = (J9Method *)comp->getMethodBeingCompiled()->getPersistentIdentifier();
      // rec->traverse_bytecode(curr, pag, getOrInsertMethodIndex(comp->getMethodSymbol(),comp),comp);
      _methodsBeingAnalyzed.erase(methodPersistentId);

      if (_methodsBeingAnalyzed.empty())
      {
         printExhaustive();
         writeNodesToFile(comp, pag);
      }

      //    //std::cout<<"method mset = "<<((std::string)(comp->getMethodSymbol()->getResolvedMethod()->nameChars())).substr(0, comp->getMethodSymbol()->getResolvedMethod()->nameLength())<<"\n";

      //    _methodsBeingAnalyzed.erase(methodPersistentId);

      //    if (_methodsBeingAnalyzed.empty() && !hotCodeReplaceFlag)
      //    {
      //       if(exhaustive){
      //          unordered_map<std::string, TR_OpaqueMethodBlock *>::iterator it;
      //          for (it = methodNameIDmapping.begin(); it != methodNameIDmapping.end(); it++)
      //          {
      //             for (const auto &stmt : stmtNumber[methodNameIDmapping[it->first]])
      //             {
      //                // call evaluate
      //                reanalyze[methodNameIDmapping[it->first]].insert(stmt.first);
      //             }
      //             if (it->first.find("Harness.main") != std::string::npos)
      //             {
      //                topLevelMethods.insert(methodNameIDmapping[it->first]);
      //             }
      //          }

      //          performRuntimePTA(comp);

      //          printExhaustive();
      //       }else{

      //          // for(auto ptg: methodPTG){
      //          //    std::cout<<"method = "<<inverseMethodNameIDmapping[ptg.first]<<"\n";
      //          //    ptg.second->print();
      //          // }
      //          // perform delete here for mi 240
      //          TR_OpaqueMethodBlock* delMethod;
      //          for(auto tt: stmtNumber){
      //             if(true){
      //                delMethod = tt.first;
      //                expMethod.push_back(delMethod);
      //                std::map<TR_OpaqueMethodBlock*, std::set<int>> delStmt;
      //                for(auto d: stmtNumber[delMethod]){
      //                   delStmt[delMethod].insert(d.first);
      //                }

      //                // collect stmt using control flow

      //                // auto t1 = std::chrono::high_resolution_clock::now();

      //                // collectStmt(delMethod, comp, false);

      //                // auto t2 = std::chrono::high_resolution_clock::now();

      //                // std::chrono::duration<double, std::milli> ms_double = t2 - t1;

      //                // flowTime.push_back(ms_double.count()/1000);
      //                // std::cout<<"Time taken for stmt collection = "<<ms_double.count()/1000<<"\n" ;
      //                std::cout<<"deleting = "<<inverseMethodNameIDmapping[delMethod]<<"\n";
      //                performDelete(comp, delStmt);

      //                topLevelMethods.clear();
      //                topLevelVisited.clear();
      //                reanalyze.clear();
      //                refineReanalyze.clear();
      //             }
      //          }

      //          int maxRefineStmtIndex = max_element(refineResult.begin(), refineResult.end()) - refineResult.begin();
      //          std::cout<<"maxm refine stmt = "<<refineResult[maxRefineStmtIndex]<<" for method = "<<inverseMethodNameIDmapping[expMethod[maxRefineStmtIndex]]<<"\n";

      //          int maxPropTimeIndex = max_element(propTime.begin(), propTime.end()) - propTime.begin();
      //          std::cout<<"maxm propagation time = "<<propTime[maxPropTimeIndex]<<" for method = "<<inverseMethodNameIDmapping[expMethod[maxPropTimeIndex]]<<"\n";

      //          // int maxTotalTimeIndex = max_element(totalTime.begin(), totalTime.end()) - totalTime.begin();
      //          // std::cout<<"maxm total time = "<<totalTime[maxTotalTimeIndex]<<" for method = "<<inverseMethodNameIDmapping[expMethod[maxTotalTimeIndex]]<<"\n";

      //          double cumTime = 0;
      //          double refStmt = 0;
      //          double reduction = 0;
      //          for(int i = 0; i < expMethod.size(); i++){
      //             cumTime += propTime[i];
      //             // if(collectStmtResult[i] != 0){
      //             //    reduction += (collectStmtResult[i] - refineResult[i])/collectStmtResult[i];
      //             // }
      // }

      //          std::cout<<"Average time per method = "<<cumTime/expMethod.size()<<"\n";
      //          // std::cout<<"Average reduction per method = "<<reduction*100/expMethod.size()<<"\n";

      //          // for(int i = 0; i < expMethod.size(); i++){
      //          //    std::cout<< collectStmtResult[i]<<" ";
      //          // }
      //          // std::cout<<"\n--------------------------------\n";
      //          for(int i = 0; i < expMethod.size(); i++){
      //             std::cout<< refineResult[i]<<" ";
      //          }
      //          // std::cout<<"\n--------------------------------\n";
      //          // for(int i = 0; i < expMethod.size(); i++){
      //          //    std::cout<< flowTime[i]*1000<<" ";
      //          // }
      //          std::cout<<"\n--------------------------------\n";
      //          for(int i = 0; i < expMethod.size(); i++){
      //             std::cout<< propTime[i]*1000<<" ";
      //          }
      //          // std::cout<<"\n--------------------------------\n";
      //          // for(int i = 0; i < expMethod.size(); i++){
      //          //    std::cout<< refTime[i]*1000<<" ";
      //          // }
      //          // std::cout<<"\n--------------------------------\n";
      //          // for(int i = 0; i < expMethod.size(); i++){
      //          //    std::cout<< totalTime[i]*1000<<" ";
      //          // }

      //       }

      //    }
   }
}

void printInheritedInterfaces(J9Class *clazz, J9VMThread *vmThread)
{
   if (!clazz || !clazz->superclasses)
      return;

   // Walk up the inheritance hierarchy
   J9Class *currentClass = clazz;
   int level = 0;

   while (currentClass && currentClass->superclasses)
   {
      J9Class *superClass = currentClass->superclasses[0];
      if (!superClass)
         break;

      level++;
      J9ROMClass *superRomClass = superClass->romClass;
      if (!superRomClass)
      {
         currentClass = superClass;
         continue;
      }

      U_32 superInterfaceCount = superRomClass->interfaceCount;
      if (superInterfaceCount > 0)
      {
         J9UTF8 *superClassName = J9ROMCLASS_CLASSNAME(superRomClass);
         printf("  From superclass %.*s (level %d):\n",
                J9UTF8_LENGTH(superClassName),
                J9UTF8_DATA(superClassName),
                level);

         J9SRP *superInterfaces = J9ROMCLASS_INTERFACES(superRomClass);
         for (U_32 i = 0; i < superInterfaceCount; i++)
         {
            J9UTF8 *interfaceName = NNSRP_GET(superInterfaces[i], J9UTF8 *);
            if (interfaceName)
            {
               printf("    Interface[%d]: %.*s\n",
                      i,
                      J9UTF8_LENGTH(interfaceName),
                      J9UTF8_DATA(interfaceName));
            }
         }
      }

      currentClass = superClass;
      // Avoid infinite loops
      if (currentClass == clazz)
         break;
   }
}

std::unordered_set<std::string> getClassFields(J9Class *clazz, J9VMThread *vmThread)
{

   std::unordered_set<std::string> fields;
   if (!clazz)
      return fields;

   J9ROMClass *romClass = clazz->romClass;
   if (!romClass)
      return fields;

   //  printf("Fields for class: %.*s\n",
   //         J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(romClass)),
   //         J9UTF8_DATA(J9ROMCLASS_CLASSNAME(romClass)));
   J9UTF8 *className = J9ROMCLASS_CLASSNAME(romClass);
   std::string classNameStr(reinterpret_cast<const char *>(J9UTF8_DATA(className)), J9UTF8_LENGTH(className));
   // std::cout << "The fields for class : " << classNameStr << std::endl;

   J9ROMFieldWalkState fieldWalkState;
   J9ROMFieldShape *field = romFieldsStartDo(romClass, &fieldWalkState);

   while (field)
   {
      J9UTF8 *fieldName = J9ROMFIELDSHAPE_NAME(field);
      J9UTF8 *fieldSignature = J9ROMFIELDSHAPE_SIGNATURE(field);
      U_32 modifiers = field->modifiers;

      //   printf("  Field: %.*s, Signature: %.*s, Modifiers: 0x%x",
      //          J9UTF8_LENGTH(fieldName), J9UTF8_DATA(fieldName),
      //          J9UTF8_LENGTH(fieldSignature), J9UTF8_DATA(fieldSignature),
      //          modifiers);

      if (fieldSignature && J9UTF8_LENGTH(fieldSignature) > 0)
      {
         char sigChar = *J9UTF8_DATA(fieldSignature);

         // Reference types start with 'L' (objects) or '[' (arrays)
         // Primitive types: B C D F I J S Z
         if (sigChar == 'L' || sigChar == '[')
         {
            std::string fieldNameStr(reinterpret_cast<const char *>(J9UTF8_DATA(fieldName)), J9UTF8_LENGTH(fieldName));

            fields.insert(classNameStr + "." + fieldNameStr);
            // printf("   Reference field: %s\n", fieldNameStr.c_str());
            if (modifiers & J9AccStatic)
            {
               if (pag)
                  pag->staticFields.insert(classNameStr + "." + fieldNameStr);
            }
         }
      }

      //   if (modifiers & J9AccPrivate) {
      //       printf(" (private)");
      //   }
      //   if (modifiers & J9AccPublic) {
      //       printf(" (public)");
      //   }
      //   if (modifiers & J9AccProtected) {
      //       printf(" (protected)");
      //   }

      //   printf("\n");

      field = romFieldsNextDo(&fieldWalkState);
   }

   //  std::cout << "=================";

   return fields;
}

// void checkForRunnableInterface(J9Class* clazz, J9VMThread* vmThread)
// {

//    if (!clazz) return;

//     J9ROMClass* romClass = clazz->romClass;
//     if (!romClass) return;

//    U_32 interfaceCount = romClass->interfaceCount;
//    //  printf("Number of interfaces: %d\n", interfaceCount);

//     if (interfaceCount == 0) {
//       //   printf("No interfaces implemented.\n");
//       //   printf("\nInherited Interfaces:\n");
//     printInheritedInterfaces(clazz, vmThread);
//         return;
//     }

//     // Get interface names from ROM class
//     J9SRP* interfaces = J9ROMCLASS_INTERFACES(romClass);

//     for (U_32 i = 0; i < interfaceCount; i++) {
//         J9UTF8* interfaceName = NNSRP_GET(interfaces[i], J9UTF8*);
//         if (interfaceName) {
//             printf("  Interface[%d]: %.*s\n",
//                    i,
//                    J9UTF8_LENGTH(interfaceName),
//                    J9UTF8_DATA(interfaceName));

//             std::string interfaceNameStr(reinterpret_cast<const char*>(J9UTF8_DATA(fieldName)),J9UTF8_LENGTH(fieldName));
//             fields.insert(classNameStr+"."+fieldNameStr);
//         }
//     }

//     // Also check superclass interfaces (inherited interfaces)
//     printf("\nInherited Interfaces:\n");
//     printInheritedInterfaces(clazz, vmThread);
// }

void constructCHA(TR::Compilation *comp)
{
   std::vector<TR_OpaqueClassBlock *> classes;
   J9VMThread *vmThread = ((TR_J9VMBase *)comp->fe())->getCurrentVMThread();
   J9JavaVM *javaVM = vmThread->javaVM;
   TR::VMAccessCriticalSection criticalSection(comp);

   J9ClassLoader *classLoader = NULL;
   GC_PoolIterator classLoaderIterator(javaVM->classLoaderBlocks);
   while (NULL != (classLoader = (J9ClassLoader *)classLoaderIterator.nextSlot()))
   {
      J9HashTableState walkState;
      J9Class *clazz = javaVM->internalVMFunctions->hashClassTableStartDo(classLoader, &walkState, 0);
      while (clazz)
      {
         if (!J9ROMCLASS_IS_ARRAY(clazz->romClass))
         {
            // std::string className1 = TR::Compiler->cls.classSignature(comp, reinterpret_cast<TR_OpaqueClassBlock *>(clazz), comp->trMemory());
            // TR_ASSERT_FATAL(className.size() != 0, "unable to get class name for type");

            J9Class *j9clazz = (J9Class *)clazz;
            J9UTF8 *nameUTF8 = J9ROMCLASS_CLASSNAME(j9clazz->romClass);
            std::string className((char *)J9UTF8_DATA(nameUTF8), J9UTF8_LENGTH(nameUTF8));

            // std :: cout << className <<std::endl;
            if (!(className.rfind("java/") == 0 || className.rfind("sun") == 0 || className.rfind("jdk") == 0 || className.rfind("openj9") == 0 || className.rfind("com") == 0))
            {
               classes.push_back(reinterpret_cast<TR_OpaqueClassBlock *>(clazz));
               clazz_to_fields[(TR_OpaqueClassBlock *)clazz] = getClassFields(clazz, comp->j9VMThread());
            }
         }
         clazz = javaVM->internalVMFunctions->hashClassTableNextDo(&walkState);
      }
   }
   ///////
   std::unordered_set<TR_OpaqueClassBlock *> visited;
   // std::cout<<"size:"<<CHA.size()<<"CLASSES size:"<<classes.size();
   for (auto type : classes)
   {
      // std::cout<<it.first<<"----"<<it.second<<std::endl;

      // std::string className = _classIndices[it.first];
      // std::cout<< "Class Name: "<<className<<std::endl;

      // int len = strlen(className.c_str());

      // std::cout<<"class name: "<< tpName <<std::endl;

      // classPtrToIndex[type] = it.first;
      TR_OpaqueClassBlock *prev = type;

      visited.insert(type);

      J9Class **superClasses = TR::Compiler->cls.superClassesOf(type);

      int classDepth = TR::Compiler->cls.classDepthOf(type);
      // printf("Superclasses of %s:\n", TR::Compiler->cls.classSignature(comp, type, comp->trMemory()));

      // ignore java/lang/Object (at index i=0)
      for (int32_t i = 1; i < classDepth; ++i)
      {
         J9Class *superClass = superClasses[i];
         CHA[(TR_OpaqueClassBlock *)superClass].insert(type);

         std::string superClassName = TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)superClass, comp->trMemory());
         if (superClassName.rfind("Ljava/lang/Thread;") == 0)
         {
            pag->threadAccessibleFields.insert(clazz_to_fields[type].begin(), clazz_to_fields[type].end());
         }
      }

      // J9Class *superClass;
      // while (classDepth != 0)
      // {
      //    if (prev != type && visited.find(prev) != visited.end())
      //    {
      //       break;
      //    }
      //    classDepth--;
      //    // *superClasses++;
      //    superClass = *++superClasses;
      //    if (!superClass)
      //    {
      //       break;
      //    }
      //    else
      //    {
      //       if ((TR_OpaqueClassBlock *)superClass == prev)
      //       {
      //          continue;
      //       }
      //       CHA[(TR_OpaqueClassBlock *)superClass].insert(prev);
      //       prev = (TR_OpaqueClassBlock *)superClass;
      //    }
      // }

      std::string tpName = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());
      // std::cout<< "tpName: "<<tpName<<std::endl;
      for (J9ITable *iTableCur = TR::Compiler->cls.iTableOf(type); iTableCur; iTableCur = iTableCur->next)
      {
         CHA[(TR_OpaqueClassBlock *)iTableCur->interfaceClass].insert(type);
         // std::cout << TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)iTableCur->interfaceClass, comp->trMemory()) << "---->" << TR::Compiler->cls.classSignature(comp, type, comp->trMemory()) << std::endl;
         std::string superClassName = TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)iTableCur->interfaceClass, comp->trMemory());
         if (superClassName.rfind("Ljava/lang/Runnable") == 0)
         {
            pag->threadAccessibleFields.insert(clazz_to_fields[type].begin(), clazz_to_fields[type].end());
         }
      }
   }
}

std::string getMethodName(TR::ResolvedMethodSymbol *m)
{

   int methodNameLength = m->getMethod()->nameLength();
   std::string methodNm = m->getMethod()->nameChars();
   methodNm = methodNm.substr(0, methodNameLength);
   int classLength = m->getMethod()->classNameLength();
   std::string classChars = m->getMethod()->classNameChars();
   std::string clazz = classChars.substr(0, classLength);
   int sigLength = m->getMethod()->signatureLength();
   std::string sigChars = m->getMethod()->signatureChars();
   std::string sig = sigChars.substr(0, sigLength);
   return clazz + "." + methodNm + sig;
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
void print(TR::Node *node, int indent, TR_Debug *de)
{
   if (node == nullptr)
      return;

   string opcode = node->getOpCode().getName();

   std::cout << "n" << node->getGlobalIndex() << "n \t";
   std::cout << string(indent, ' ');

   if (node->getOpCode().hasSymbolReference() && node->getSymbolReference())
   {
      std::cout << opcode;
      std::cout << " " << node->getSymbolReference()->getName(de); //<< std::endl;

      std::cout << "\t[" << node->getSymbolReference()->getReferenceNumber() << "]";
   }
   else if (node->getOpCode().isBranch())
   {
      TR::TreeTop *tree_top = node->getBranchDestination();
      TR::Node *tree_top_node = tree_top->getNode();
      TR::Block *block = tree_top_node->getBlock();
      std::cout << opcode;
      printf(" --> ");
      if (block->getNumber() >= 0)
         printf("block_%d", block->getNumber());
      printf(" BBStart at n%dn", tree_top_node->getGlobalIndex());
   }
   else if (node->getOpCodeValue() == TR::BBStart)
   {
      TR::Block *block = node->getBlock();
      if (block->getNumber() >= 0)
      {
         printf("BBStart <block_%d>", block->getNumber());
      }
   }
   else if (node->getOpCodeValue() == TR::BBEnd)
   {
      TR::Block *block = node->getBlock();

      printf("BBEnd </block_%d>\n", block->getNumber());
   }
   else
   {
      std::cout << opcode;
      if (node->getOpCodeValue() == TR::iconst)
      {
         std::cout << " " << node->getInt();
      }
      else if (node->getOpCodeValue() == TR::fconst)
      {
         std::cout << " " << node->getFloat();
      }
      else if (node->getOpCodeValue() == TR::dconst)
      {
         std::cout << " " << node->getDouble();
      }
   }

   if (node->getOpCode().isNullCheck())
   {
      if (node->getNullCheckReference())
         printf(" on n%dn", node->getNullCheckReference()->getGlobalIndex());
      else
         printf(" on null NullCheckReference ----- INVALID tree!!");
   }
   else if (node->getOpCodeValue() == TR::allocationFence)
   {
      if (node->getAllocation())
         printf(" on n%dn ", node->getAllocation()->getGlobalIndex());
      else
         printf(" on ALL");
   }
   printf("\n");
   if (node->getNumChildren() > 0)
      print(node->getFirstChild(), indent + 1, de);
   if (node->getNumChildren() > 1)
      print(node->getSecondChild(), indent + 1, de);
   if (node->getNumChildren() > 2)
      print(node->getThirdChild(), indent + 1, de);
}

bool returnsObject(const std::string &methodSignature)
{
   int pos = methodSignature.find(')');
   if (pos == std::string::npos || pos + 1 >= methodSignature.length())
      return false;

   char returnTypeStart = methodSignature[pos + 1];

   // 'L' = object, '[' = array (both reference types), we are concerned only with objects returned and not any of the primitive types.
   return returnTypeStart == 'L' || returnTypeStart == '[';
}

MethodSet computeMSetForMethod(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol)
{

   std::cout << "-----Computing Mset for method = " << getMethodName(methodSymbol) << " " << methodSymbol->getResolvedMethod()->getPersistentIdentifier() << "-----\n";

   Counter counter(comp->getVisitCount(), -10);

   std::string methodSignature = methodSymbol->signature(comp->trMemory());
   bool hasReturnType = returnsObject(methodSignature);
   TR_OpaqueMethodBlock *methodBlock = methodSymbol->getResolvedMethod()->getPersistentIdentifier();
   int method = getOrInsertMethodIndex(methodSymbol, comp);
   if (hasReturnType)
   {
      pag->methods_to_returnNode[method] = new PAGNode(RETURN, RETURN_NODE_NAME, NULL, methodBlock, -1, getOrInsertMethodIndex(methodSymbol, comp));
      pag->PAG_nodes.insert(pag->methods_to_returnNode[method]);
      pag->methods_to_allMethodNodes[method].push_back(pag->methods_to_returnNode[method]);
   }
   int methodIndex = method;

   // TR_OpaqueMethodBlock *methodPersistentId = methodSymbol->getResolvedMethod()->getPersistentIdentifier();

   // create methodPTG here
   // if(!exhaustive){
   //    methodPTG[methodPersistentId] = &(_indexPTG[methodIndex]);
   // }
   // printing ptg after read
   //_indexPTG[methodIndex].print();

   MethodSet mSet;

   // we begin from the start node of the CFG
   // TODO: perform the topological sort of the CFG here, to identify the order in which the basic blocks are to be processed
   TR::CFG *cfg = methodSymbol->getFlowGraph();
   if (!cfg)
      std::cout << "cfg is null!" << std::endl;
   TR::Block *start = cfg->getStart()->asBlock();
   TR_LinkHead1<TR::CFGNode> nodeList = cfg->getNodes();

   if (comp->getOption(TR_PrintCFG))
   {
      // printing the CFGNodes
      std::cout << "####" << getMethodName(methodSymbol) << "####" << std::endl;
      while (!nodeList.isEmpty())
      {
         TR::CFGNode *cfg_node = nodeList.pop();
         TR::Block *block = cfg_node->asBlock();

         TR::TreeTop *tt = block->getEntry();
         while (tt)
         {
            TR::Node *node = tt->getNode();

            TR::FILE *file = new TR::FILE(stdout);
            TR_Debug de(comp);
            // de.print(file, node, 0,false);
            print(node, 0, &de);

            tt = tt->getNextRealTreeTop();
         }
      }

      std::cout << "###### Printing CFG Done!! #####" << std::endl;
   }

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

   std::map<TR::Node *, int> evaluatedNodeValues;

   while (!blockProcessingOrder.empty())
   {

      ListIterator<TR::ParameterSymbol> paramIterator(&(methodSymbol->getParameterList()));
      TR::ParameterSymbol *paramCursor = paramIterator.getFirst();
      TR::SymbolReference *symRef;

      int argIndex = 0;
      if (methodSymbol->isStatic())
      {
         // for static methods, our magic arg index begins from 1
         argIndex = 1;
         pag->methods_to_formalNodes[method].push_back(NULL);
      }
      // std::cout << "Iterating for: "<<getMethodName(methodSymbol) <<" paramCursor is: "<<paramCursor <<std::endl;
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

            argToSymRef[methodBlock][argIndex] = symRefNumber;
            formalParMethod[methodBlock][symRefNumber] = argIndex;
            formalParMethod[methodBlock][-3] = -3;
            inverseFormalParMethod[methodBlock][argIndex] = symRefNumber;
            inverseFormalParMethod[methodBlock][-3] = -3;

            // if(getMethodName(methodSymbol) == "org/dacapo/parser/Token.<init>(ILjava/lang/String;)V")
            // {
            //    printf("%s\n",getMethodName(methodSymbol).c_str());
            // }
            if (symRefNumToPAGNode[methodBlock].find(symRefNumber) == symRefNumToPAGNode[methodBlock].end())
            {
               PAGNode *param_node_ptr = new PAGNode(VARIABLE, symRefNumber, nullptr, methodBlock, -1, getOrInsertMethodIndex(methodSymbol, comp));
               pag->methods_to_allMethodNodes[method].push_back(param_node_ptr);
               pag->PAG_nodes.insert(param_node_ptr);
               // nodeAllocationMap[] = null_node_ptr;
               // std::cout << "Iterating for: "<<getMethodName(methodSymbol) <<" created formal param node: "<< symRefNumber <<std::endl;
               symRefNumToPAGNode[methodBlock][symRefNumber] = param_node_ptr;
               pag->methods_to_formalNodes[method].push_back(param_node_ptr);
            }

            // cout << "symref num = " << symRefNumber << "\n";

            // std::cout << "the symref number corresponding to param " << paramCursor->getSlot() << " is " << symRefNumber << " will be mapped to arg " << argIndex <<" in method name: "<< getMethodName(comp->getMethodSymbol())<< endl;
            // std::cout<< paramCursor->getName() << std::endl;
            // set<Entry> argsPointsTo = in->getArgPointsToSet(argIndex);
            // std::set<Entry> argsPointsTo = in->getPointsToSet(argIndex);
            // cout << "the argspointsto for arg " << argIndex << " is\n" ;
            // for (Entry e : argsPointsTo) {
            //    cout << e.getString()  << " ";
            // } cout << "\n";
            // in->assign(symRefNumber, argsPointsTo);

            argIndex++;
         }
         else
         {
            // cout << "not an address symref!\n";
            pag->methods_to_formalNodes[method].push_back(pag->bottom_node);
            argIndex++;
         }
      }

      TR::Block *currentBB = blockProcessingOrder.top();
      blockProcessingOrder.pop();

      int currentBBNumber = currentBB->getNumber();

      // if (_runtimeVerifierDiagnostics || methodIndex == 229)
      //    cout << "popped BB" << currentBBNumber << " from the worklist" << endl;

      TR::TreeTop *tt = currentBB->getEntry();
      // its possible that there are no entry treetops for certain basic blocks
      // TODO: DOCUMENT THIS
      if (tt)
      {
         // now we iterate over the treetops in the basic block
         for (; tt; tt = tt->getNextRealTreeTop())
         {
            TR::Node *node = tt->getNode();

            // std::cout<<"node visitCount = "<<node->getVisitCount()<<std::endl;
            // IFDIAGPRINT << "*** now processing node n" << node->getGlobalIndex() << "n, with opcode " << node->getOpCode().getName() << endl;
            int nodeBCI = node->getByteCodeInfo().getByteCodeIndex();
            // unfortunately it appears that the Start and End nodes are also valid treetops.
            // TODO: is there a way around this check?

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

            // std::cout<< "hahahahahah "<<nodeBCI<<"   "<< tt <<"        "<< tt->getNode()<< " " << node->getOpCode().getName() <<std::endl;

            bool ft = !exhaustive;

            int evaluatedValueForNode = evaluateNode(node, evaluatedNodeValues, counter, methodIndex, mSet, methodSymbol->getResolvedMethod()->getPersistentIdentifier(), comp, ft);
         }
      }
   }

   // std::map<int, std::set<Entry>>myRho = methodPTG[methodPersistentId]->getRho();
   // std::map<int, std::set<Entry>>::iterator myIterator = myRho.begin();
   // while(myIterator != myRho.end()){
   //    int slot = myIterator->first;
   //    if(slot > 400){
   //       break;
   //    }
   //    if(slot == 0){
   //       // methodPTG[methodPersistentId]->assignReturn(myRho[slot]);
   //    }else{
   //       // methodPTG[methodPersistentId]->setArg(slot-1, myRho[slot]);
   //    }
   //    myIterator++;
   // }

   // mapping stack slot to symref
   // std::map<int, std::set<Entry>> myRho = methodPTG[methodPersistentId]->getRho();
   // map<int, set<Entry>>::iterator myIterator = myRho.begin();
   // while (myIterator != myRho.end())
   // {
   //    int slot = myIterator->first;

   //    ListIterator<TR::SymbolReference> autos(&methodSymbol->getAutoSymRefs(slot));
   //    // TODO: assert autos.size == 1 -- this is a sanity check to make sure there is no sharing of auto symbols
   //    for (TR::SymbolReference *sr = autos.getFirst(); sr; sr = autos.getNext())
   //    {
   //       methodPTG[methodPersistentId]->assign(sr->getReferenceNumber(), methodPTG[methodPersistentId]->getPointsToSet(slot));
   //    }
   //    methodPTG[methodPersistentId]->killFromRho(slot);

   //    myIterator++;
   // }

   // save this away as the summary for this method!

   // if (_runtimeVerifierDiagnostics)
   // {
   //    cout << "completed runtime PTA for " << methodSignature << endl;
   //    cout << "out-PTG:" << endl;
   //    outForMethod->print();
   // }

   return mSet;
}
int getOrInsertMethodIndex(TR::ResolvedMethodSymbol *methodSymbol, TR::Compilation *comp)
{
   TR_OpaqueMethodBlock *methodPersistentId = methodSymbol->getResolvedMethod()->getPersistentIdentifier();
   // no need of assert, guaranteed to be available

   if (_methodIndicesPtr.find(methodPersistentId) != _methodIndicesPtr.end())
   {
      return _methodIndicesPtr[methodPersistentId];
   }
   else
   {
      std::string methodSignature = methodSymbol->signature(comp->trMemory());
      int index;
      if (pag->_methodIndices.find(methodSignature) != pag->_methodIndices.end())
      {
         // the id is available in the string map, add it to the pointer map for efficiency of later lookups
         index = pag->_methodIndices[methodSignature];
      }
      else
      {
         // the index is in neither map, add it to both
         index = pag->_methodIndices.size() + 1;
         pag->_methodIndices[methodSignature] = index;
      }
      _methodIndicesPtr[methodPersistentId] = index;
      return index;
   }
}
void getTargetsToPeek(std::queue<TR_OpaqueClassBlock *> &bfsList, std::unordered_set<TR_OpaqueClassBlock *> &visitedClass, std::unordered_set<TR_OpaqueMethodBlock *> &methodsToPeek, TR::Compilation *comp, std::string methodNm, std::string sig)
{

   while (!bfsList.empty())
   {
      TR_OpaqueClassBlock *currentClass = bfsList.front();
      bfsList.pop();

      // char *currchild = TR::Compiler->cls.classSignature(comp, currentClass, comp->trMemory());
      // std::cout<<"target class name = "<< currchild <<"\n";

      TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, currentClass, methodNm.c_str(), sig.c_str());
      // if(!targetMethod) continue;

      // std::cout <<"Target method "<<getMethodName(targetMethod->findOrCreateJittedMethodSymbol(comp))<<std::endl;
      std::cout << targetMethod << std::endl;
      if (targetMethod && !targetMethod->isAbstract())
      {

         //! TR::Compiler->cls.isInterfaceClass(comp, currentClass)){
         // std::cout<<"targetMethod in CHA is null\n";
         // if (classPtrToIndex[currentClass] == 0)
         // {
         //    // std::cout<<"didid 4 = "<<methodName<<"\n";
         // }
         // _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[currentClass]);
         if (!isLibraryMethod(getMethodName(targetMethod->findOrCreateJittedMethodSymbol(comp))))
         {
            methodsToPeek.insert(targetMethod->getPersistentIdentifier());
            std::cout << "Added to peek: " << getMethodName(targetMethod->findOrCreateJittedMethodSymbol(comp)) << " called  method: " << methodNm << sig << std::endl;
            cachedParameterType[targetMethod->getPersistentIdentifier()][0] = currentClass;
         }
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

int evaluateNode(TR::Node *node, std::map<TR::Node *, int> &evaluatedNodeValues, Counter &counter, int methodIndex, MethodSet &mSet, TR_OpaqueMethodBlock *currentMethod, TR::Compilation *comp, bool populatePTA)
{

   std::unordered_set<TR_OpaqueMethodBlock *> methodsToPeek;
   int current_method_index = methodIndex;
   int evaluatedSymRef = -2;

   TR_OpaqueMethodBlock *methodPersistentId = currentMethod;

   methodNameIDmapping[getMethodName(getCachedResolvedMethodSymbol(comp,currentMethod))] = methodPersistentId;
   inverseMethodNameIDmapping[methodPersistentId] = getMethodName(getCachedResolvedMethodSymbol(comp,currentMethod));

   TR::Node *usefulNode = getUsefulNode(node);

   if (!usefulNode)
      return evaluatedSymRef;

   if (usefulNode->getVisitCount() >= counter.visitCount)
   {
      evaluatedSymRef = evaluatedNodeValues[usefulNode];
      return evaluatedSymRef;
   }
   else
   {

      usefulNode->setVisitCount(counter.visitCount);

      TR::ILOpCodes opCode = usefulNode->getOpCodeValue();
      if (usefulNode->getOpCode().hasSymbolReference())
         std::cout << usefulNode->getOpCode().getName() << " " << usefulNode->getSymbolReference()->getName(comp->getDebug())  << "\t[" << usefulNode->getSymbolReference()->getReferenceNumber() << "]"<< std::endl;

      if (usefulNode->getNumChildren() > 0 && usefulNode->getFirstChild()->getOpCode().hasSymbolReference())
         std::cout << " --> CHILD 1. " << usefulNode->getFirstChild()->getOpCode().getName() << " " << usefulNode->getFirstChild()->getSymbolReference()->getName(comp->getDebug()) << "\t[" << usefulNode->getFirstChild()->getSymbolReference()->getReferenceNumber() << "]"<< std::endl;
     
      if (usefulNode->getNumChildren() > 1 && (usefulNode->getSecondChild()->getOpCode().hasSymbolReference()))
         std::cout << " --> CHILD 2. " << usefulNode->getSecondChild()->getOpCode().getName() << " " << usefulNode->getSecondChild()->getSymbolReference()->getName(comp->getDebug()) << "\t[" << usefulNode->getSecondChild()->getSymbolReference()->getReferenceNumber() << "]"<< std::endl;
      
      if (usefulNode->getNumChildren() > 2 && usefulNode->getThirdChild()->getOpCode().hasSymbolReference())
         std::cout << " --> CHILD 3. " << usefulNode->getThirdChild()->getOpCode().getName() << " " << usefulNode->getThirdChild()->getSymbolReference()->getName(comp->getDebug())<< "\t[" << usefulNode->getThirdChild()->getSymbolReference()->getReferenceNumber() << "]" << std::endl;

      switch (opCode)
      {

      case TR::checkcast:
      {
         // evaluatedSymRef = evaluateNode(usefulNode->getFirstChild(), evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);
         // if (usefulNode->stmtNumber == 0)
         // {
         //    counter.stmtCount++;
         //    usefulNode->stmtNumber = counter.stmtCount;
         // }
         // stmtNumber[methodPersistentId][usefulNode->stmtNumber] = usefulNode;

         // if (evaluatedSymRef <= -10 || evaluatedSymRef >= 0)
         // {
         //    mSet.stmtMap[evaluatedSymRef].insert(usefulNode->stmtNumber);
         // }

         break;
      }
      case TR::aconst:
      {
         // // this is needed for calls where the arg is null - it appears to map to aconst_null in bytecode
         evaluatedSymRef = -1;
         PAGNode *null_node_ptr;

         if (nodeAllocationMap.find(usefulNode) != nodeAllocationMap.end())
         {
            null_node_ptr = nodeAllocationMap[usefulNode];
         }
         else
         {
            null_node_ptr = new PAGNode(NULL_OBJ, -1, nullptr, methodPersistentId, usefulNode->getByteCodeIndex(), methodIndex);
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(null_node_ptr);
            pag->PAG_nodes.insert(null_node_ptr);
            nodeAllocationMap[usefulNode] = null_node_ptr;
         }

         // if(populatePTA){
         //    processNodeValues[usefulNode].insert(PointsToGraph::nullEntry);
         // }

         break;
      }
      case TR::aladd: // OD : how to handle this ?
      {
         // if(populatePTA){
         //    processNodeValues[usefulNode].insert(PointsToGraph::bottomEntry);
         // }
         break;
      }
      case TR::New:
      { // add edge : abstractObj -> global_index
         // process new here
         evaluatedSymRef = usefulNode->getGlobalIndex();

         PAGNode *alloc_node_ptr;

         if (nodeAllocationMap.find(usefulNode) != nodeAllocationMap.end())
         {
            alloc_node_ptr = nodeAllocationMap[usefulNode];
         }
         else
         {
            alloc_node_ptr = evaluateAllocate(usefulNode, methodIndex, false, comp);
            std::cout << "Alloc at global index = " << evaluatedSymRef << " MethodPersistent id = " << methodPersistentId << std::endl;
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(alloc_node_ptr);
         }

         PAGNode *global_index_ptr = new PAGNode(VARIABLE, evaluatedSymRef, nullptr, methodPersistentId, usefulNode->getByteCodeIndex(), methodIndex);
         pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(global_index_ptr);
         pag->PAG_nodes.insert(global_index_ptr);
         nodeAllocationMap[usefulNode] = global_index_ptr;
         symRefNumToPAGNode[methodPersistentId][evaluatedSymRef] = global_index_ptr;

         pag->addEdge(alloc_node_ptr, global_index_ptr, NEW);
         global_index_ptr->pointee_class_names.insert(alloc_node_ptr->pointee_class_names.begin(), alloc_node_ptr->pointee_class_names.end());

         // if(populatePTA){
         //    Entry e = evaluateAllocate(usefulNode, methodIndex, false);

         // TR_OpaqueClassBlock *tpSym = (TR_OpaqueClassBlock *)usefulNode->getFirstChild()->getSymbol()->castToStaticSymbol()->getStaticAddress();
         // alloc_node_ptr->clazz_ptr = tpSym;
         //    if(tpSym == NULL){
         //       //e = PointsToGraph::bottomEntry;
         //       //std::cout<<"tpsym null for "<<e.caller<<"-"<<e.bci<<"\n";
         //    }
         //    else{
         //       e.clazz = tpSym;
         //       if(cachedClassSignature.find(e.clazz) == cachedClassSignature.end()){
         //          cachedClassSignature[e.clazz] = TR::Compiler->cls.classSignature(comp, e.clazz, comp->trMemory());
         //       }
         //       std::string className = cachedClassSignature[e.clazz];
         //       if(className.find("Ljava/lang/String;") != std::string::npos ){
         //          processNodeValues[usefulNode].insert(PointsToGraph::stringEntry);
         //       }else{
         //          processNodeValues[usefulNode].insert(e);
         //       }
         //    }

         // }
         break;
      }

      case TR::anewarray:
      {
         evaluatedSymRef = -1;

         PAGNode *alloc_node_ptr;

         if (nodeAllocationMap.find(usefulNode) != nodeAllocationMap.end())
         {
            alloc_node_ptr = nodeAllocationMap[usefulNode];
         }
         else
         {
            alloc_node_ptr = evaluateAllocate(usefulNode, methodIndex, true, comp);
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(alloc_node_ptr);
         }

         // if(populatePTA){
         //    Entry e = evaluateAllocate(usefulNode, methodIndex, true);
         //    TR_OpaqueClassBlock *tpSym;
         //    if(usefulNode->getSecondChild()->getOpCodeValue() == TR::loadaddr){

         //       tpSym = (TR_OpaqueClassBlock *)usefulNode->getSecondChild()->getSymbol()->castToStaticSymbol()->getStaticAddress();
         //       if(tpSym == NULL){
         //          //e = PointsToGraph::bottomEntry;
         //       }
         //       else{
         //          e.clazz = tpSym;
         //          e.type = RefArray;
         //          processNodeValues[usefulNode].insert(e);

         //       }
         //    }else{
         //       e.type = RefArray;
         //       e.clazz = NULL;
         //       processNodeValues[usefulNode].insert(e);
         //    }
         // }
         break;
      }
      case TR::newarray:
      {
         // process anewarray
         // evaluatedSymRef = -1;

         // if(populatePTA){
         //    Entry e = evaluateAllocate(usefulNode, methodIndex, true,comp);
         //    e.type = PrimitiveArray;
         //    e.clazz = NULL;
         //    processNodeValues[usefulNode].insert(e);
         // }

         break;
      }

      case TR::multianewarray:
      {
         // evaluatedSymRef = -1;

         // if(populatePTA){
         //    processNodeValues[usefulNode].insert(PointsToGraph::bottomEntry);
         // }
         break;
      }

      case TR::astore:
      {
         /*
           child of astore could be
                            EDGETYPE
           1. new            ASSIGN (from globalIndex node to the var slot)
           2. acalli         ASSIGN
           3. aload          ASSIGN [GETFIELD for static field read]
           4. aloadi         GETFIELD => use symRef
           5. anewarray      NEW

         */

         TR::Node *storeChild = usefulNode->getFirstChild();
         TR::ILOpCodes storeChild_opcode = storeChild->getOpCodeValue();
         // std::cout << storeChild->getOpCodeValue()<< endl;
         TR_ASSERT_FATAL(storeChild, "astore failed");

         // IGNORE STMTS like these -> astore <temp slot 4 holds monitoredObject syncMethod>
         const std::regex rx(R"(^<temp slot \d+ holds monitoredObject syncMethod>$)");
         std::string node_name = usefulNode->getSymbolReference()->getName(comp->getDebug());
         if (std::regex_match(node_name, rx))
         {
            return -238933;
         }
         // std::cout << usefulNode->getFirstChild()->getOpCode().getName() << " " << usefulNode->getFirstChild()->getSymbolReference()->getName(comp->getDebug()) << std::endl;
         // std::cout << getMethodName(comp->getOwningMethodSymbol(currentMethod)) << std::endl;

         int loadSymRef = evaluateNode(storeChild, evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);
         int storeSymRef = usefulNode->getSymbolReference()->getReferenceNumber();
         PAGNode *storeChild_pagNode_ptr;

         int32_t storeChildSymRef = -78765; // some random negative number
         if (storeChild->getOpCode().hasSymbolReference() && storeChild->getSymbolReference())
         {
            storeChildSymRef = storeChild->getSymbolReference()->getReferenceNumber();
         }

         if (loadSymRef == STATIC_FIELD_READ)
         {
            std::string class_name = storeChild->getSymbolReference()->getName(comp->getDebug());
            int dot_index = class_name.rfind(".");
            class_name = class_name.substr(0, dot_index);

            storeChild_pagNode_ptr = class_to_staticPAGNode[class_name];
         }
         else if (storeChild_opcode == TR::New)
         {
            int globalIndex = storeChild->getGlobalIndex();
            storeChild_pagNode_ptr = symRefNumToPAGNode[methodPersistentId][globalIndex];
            symref_PAGNode[usefulNode->getSymbolReference()->getReferenceNumber()] = storeChild_pagNode_ptr;
         }
         else if (storeChildSymRef >= 0 && storeChild->getSymbolReference() && symRefNumToPAGNode[methodPersistentId].find(storeChildSymRef) != symRefNumToPAGNode[methodPersistentId].end())
         {
            storeChild_pagNode_ptr = symRefNumToPAGNode[methodPersistentId][storeChildSymRef];
            nodeAllocationMap[storeChild] = storeChild_pagNode_ptr;
         }
         else if (nodeAllocationMap.find(storeChild) != nodeAllocationMap.end())
         {
            storeChild_pagNode_ptr = nodeAllocationMap[storeChild];
            // std::cout << storeChild->getOpCode().getName()<<"2"<<std::endl;
         }
         else
         {
            storeChild_pagNode_ptr = new PAGNode(VARIABLE, storeSymRef, nullptr, methodPersistentId, storeChild->getByteCodeIndex(), methodIndex);
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(storeChild_pagNode_ptr);
            pag->PAG_nodes.insert(storeChild_pagNode_ptr);
            nodeAllocationMap[storeChild] = storeChild_pagNode_ptr;
            if (storeChildSymRef >= 0 && storeChild->getSymbolReference())
            {
               symRefNumToPAGNode[methodPersistentId][storeChildSymRef] = storeChild_pagNode_ptr;
               symRefNumToNode[storeChildSymRef] = storeChild;
            }
         }

         // TODO get clazz_ptr

         PAGNode *lhs_node_ptr;
         int32_t astore_lhs_symRef = usefulNode->getSymbolReference()->getReferenceNumber();

         if (symRefNumToPAGNode[methodPersistentId].find(astore_lhs_symRef) != symRefNumToPAGNode[methodPersistentId].end())
         {
            lhs_node_ptr = symRefNumToPAGNode[methodPersistentId][astore_lhs_symRef];
            nodeAllocationMap[usefulNode] = lhs_node_ptr;
         }
         else if (nodeAllocationMap.find(usefulNode) != nodeAllocationMap.end())
         {
            lhs_node_ptr = nodeAllocationMap[usefulNode];
         }
         else
         {
            lhs_node_ptr = new PAGNode(VARIABLE, storeSymRef, nullptr, methodPersistentId, usefulNode->getByteCodeIndex(), methodIndex);
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(lhs_node_ptr);

            pag->PAG_nodes.insert(lhs_node_ptr);
            nodeAllocationMap[usefulNode] = lhs_node_ptr;

            symRefNumToPAGNode[methodPersistentId][storeSymRef] = lhs_node_ptr;
            symRefNumToNode[storeSymRef] = usefulNode;
         }

         EdgeType e_type;
         if (storeChild_opcode == TR::New)
         {
            e_type = ASSIGN;
            abstractNode_to_assignedVar[storeChild_pagNode_ptr] = lhs_node_ptr;
         }
         else if (storeChild_opcode == TR::aloadi)
         {
            // for stmt like `x= y.f`,
            // usefulnode = x
            // usefulnode.child = y.f
            // usefulnode.child.child = y

            e_type = GETFIELD;
            TR::Node *y_node = storeChild->getFirstChild();
            if (storeChild->getSymbol()->isArrayShadowSymbol())
            {
               *y_node = storeChild->getFirstChild()->getFirstChild();
            }
            PAGNode *y_PAGnode_ptr;
            int32_t y_node_symRef = -78765; // some random negative number
            if (y_node->getOpCode().hasSymbolReference() && y_node->getSymbolReference())
            {
               y_node_symRef = y_node->getSymbolReference()->getReferenceNumber();
            }

            if (y_node_symRef >= 0 && symRefNumToPAGNode[methodPersistentId].find(y_node_symRef) != symRefNumToPAGNode[methodPersistentId].end())
            {
               y_PAGnode_ptr = symRefNumToPAGNode[methodPersistentId][y_node_symRef];
               y_node = symRefNumToNode[y_node_symRef];
               nodeAllocationMap[y_node] = y_PAGnode_ptr;
            }
            else if (nodeAllocationMap.find(y_node) != nodeAllocationMap.end())
            {
               y_PAGnode_ptr = nodeAllocationMap[y_node];
            }
            else
            {
               y_PAGnode_ptr = new PAGNode(VARIABLE, y_node->getSymbolReference()->getReferenceNumber(), nullptr, methodPersistentId, y_node->getByteCodeIndex(), methodIndex);
               pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(y_PAGnode_ptr);

               pag->PAG_nodes.insert(y_PAGnode_ptr);
               nodeAllocationMap[y_node] = y_PAGnode_ptr;

               symRefNumToPAGNode[methodPersistentId][y_node_symRef] = y_PAGnode_ptr;
               symRefNumToNode[y_node_symRef] = y_node;
            }

            // Add edge:  y --Getfield--> x
            //            y_PAGnode_ptr --Getfield--> lhs_node_ptr
            int32_t len;
            string field_name = "$";

            if (!storeChild->getSymbol()->isArrayShadowSymbol())
            {
               field_name = storeChild->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(storeChild->getSymbolReference()->getCPIndex(), len);
            }
            field_name = field_name.substr(0, len);
            // std::cout <<"Y_node: " << y_node->getOpCodeValue() << std::endl;
            // std::cout << "In astore:field is "<<field_name<<" len = "<< len << std::endl;

            // PAGEdge *new_edge = new PAGEdge(y_PAGnode_ptr, lhs_node_ptr, e_type, field_name);

            // lhs_node_ptr->incoming.insert(new_edge);
            // y_PAGnode_ptr->outgoing.insert(new_edge);
            updateMatchEdges();
            pag->addEdge(y_PAGnode_ptr, lhs_node_ptr, e_type, field_name);
            for (auto *edge : pag->getMatchEdgesEndingAt(lhs_node_ptr))
            {
               PAGNode *src = edge->src;
               lhs_node_ptr->pointee_class_names.insert(src->pointee_class_names.begin(), src->pointee_class_names.end());
            }
            evaluatedSymRef = storeSymRef;
            break;
         }
         else if (storeChild_opcode == TR::anewarray)
         {
            e_type = NEW;
         }
         else if (storeChild_opcode == TR::aload && loadSymRef == STATIC_FIELD_READ)
         {
            e_type = GETFIELD;
         }
         else
         {
            e_type = ASSIGN;
         }

         if (storeChild_opcode == TR::acalli || storeChild_opcode == TR::acall)
         {
            // Add edge from return node of the called method to lhs_node_ptr
            PAGNode *return_pag_node;
            for (auto target : callsite_to_targets[storeChild])
            {
               return_pag_node = pag->methods_to_returnNode[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,target), comp)];
               // PAGEdge *new_edge = new PAGEdge(return_pag_node, lhs_node_ptr, ASSIGN, storeChild->getByteCodeIndex());
               // lhs_node_ptr->incoming.insert(new_edge);
               // return_pag_node->outgoing.insert(new_edge);
               if (!return_pag_node)
               {
                  TR::ResolvedMethodSymbol *methodSymbol = getCachedResolvedMethodFromPtr(comp, currentMethod)->findOrCreateJittedMethodSymbol(comp);
                  int methodInd = getOrInsertMethodIndex(methodSymbol, comp);
                  pag->methods_to_returnNode[methodInd] = new PAGNode(RETURN, RETURN_NODE_NAME, NULL, currentMethod, -1, methodInd);
                  pag->PAG_nodes.insert(pag->methods_to_returnNode[methodInd]);
                  pag->methods_to_allMethodNodes[methodInd].push_back(pag->methods_to_returnNode[methodInd]);
                  return_pag_node = pag->methods_to_returnNode[methodInd];
               }

               pag->addEdge(return_pag_node, lhs_node_ptr, ASSIGN, storeChild->getByteCodeIndex());
               callsite_to_storeNode[storeChild->getByteCodeIndex()] = lhs_node_ptr;
               lhs_node_ptr->pointee_class_names.insert(return_pag_node->pointee_class_names.begin(), return_pag_node->pointee_class_names.end());
            }
         }
         else
         {
            // PAGEdge *new_edge = new PAGEdge(storeChild_pagNode_ptr, lhs_node_ptr, e_type);

            // std::cout<<"e_type: "<<e_type<<" storeChild_pagNode_ptr: "<<storeChild_pagNode_ptr->bci<<storeChild_pagNode_ptr->name<<std::endl;

            // lhs_node_ptr->incoming.insert(new_edge);
            // storeChild_pagNode_ptr->outgoing.insert(new_edge);

            pag->addEdge(storeChild_pagNode_ptr, lhs_node_ptr, e_type);
            if (e_type == GETFIELD)
            {
               updateMatchEdges();
               for (auto *edge : pag->getMatchEdgesEndingAt(lhs_node_ptr))
               {
                  PAGNode *src = edge->src;
                  lhs_node_ptr->pointee_class_names.insert(src->pointee_class_names.begin(), src->pointee_class_names.end());
               }
            }
            else if (e_type == ASSIGN)
            {
               lhs_node_ptr->pointee_class_names.insert(storeChild_pagNode_ptr->pointee_class_names.begin(), storeChild_pagNode_ptr->pointee_class_names.end());
            }
         }

         // if (usefulNode->stmtNumber == 0)
         // {
         //    counter.stmtCount++;
         //    usefulNode->stmtNumber = counter.stmtCount;
         // }
         // stmtNumber[methodPersistentId][usefulNode->stmtNumber] = usefulNode;

         // if (loadSymRef <= -10 || loadSymRef >= 0)
         // {
         //    mSet.ds.unionDS(storeSymRef, loadSymRef);
         //    mSet.stmtMap[storeSymRef].insert(usefulNode->stmtNumber);
         //    // std::cout<<storeSymRef<< " " <<loadSymRef<<std::endl;
         // }
         // else
         // {
         //    if (loadSymRef == -1)
         //    {
         //       mSet.stmtMap[storeSymRef].insert(usefulNode->stmtNumber);
         //    }
         // }

         evaluatedSymRef = storeSymRef;

         break;
      }
      case TR::aload:
      {
         // // process load here

         // // TODO - static field reads appear as follows:
         // //         n1n       BBStart <block_2>
         // //         n4n       astore  <auto slot 1>[#357  Auto] [flags 0x7 0x0 ]
         // //         n3n         aload  B.a LA;[#356  notAccessed Static] [flags 0x307 0x0 ]
         // //         n5n       return
         // //         n2n       BBEnd </block_2> =====
         // // we need a way to identify if the symref is a static or no

         // Regex explanation: FOR entries like "aload <callSite entry @0        0x1212ef4a0>" -> SKIP THEM
         // ^<callSite entry @  → must start with this
         // \\d+               → one or more digits
         // \\s+               → one or more spaces
         // 0x[0-9a-fA-F]+     → hex address
         // >$                 → must end with '>'
         std::regex pattern("^<callSite entry @\\d+\\s+0x[0-9a-fA-F]+>$");
         std::string nm = usefulNode->getSymbolReference()->getName(comp->getDebug());
         bool isNotFieldNode = std::regex_match(nm, pattern);

         if (isNotFieldNode)
         {
            return -344565;
         }

         bool isStaticFieldRead = usefulNode->getSymbol()->isStaticField();
         int loadSymRef = usefulNode->getSymbolReference()->getReferenceNumber();

         PAGNode *pag_node_ptr;
         if (symRefNumToPAGNode[methodPersistentId].find(loadSymRef) != symRefNumToPAGNode[methodPersistentId].end())
         {
            pag_node_ptr = symRefNumToPAGNode[methodPersistentId][loadSymRef];
            nodeAllocationMap[usefulNode] = pag_node_ptr;
         }
         else if (nodeAllocationMap.find(usefulNode) == nodeAllocationMap.end())
         {
            pag_node_ptr = new PAGNode(VARIABLE, loadSymRef, nullptr, methodPersistentId, usefulNode->getByteCodeIndex(), methodIndex);
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(pag_node_ptr);

            pag->PAG_nodes.insert(pag_node_ptr);
            nodeAllocationMap[usefulNode] = pag_node_ptr;

            symRefNumToPAGNode[methodPersistentId][loadSymRef] = pag_node_ptr;
            symRefNumToNode[loadSymRef] = usefulNode;

            // std::cout<<"Inside aload 1\n ";
            // std::cout << node->getSymbolReference()->getName(comp->getDebug())<< node->getByteCodeIndex()<<"\n";
         }
         // else
         // {
         //      pag_node_ptr = nodeAllocationMap[usefulNode];
         // }

         if (isStaticFieldRead)
         {

            evaluatedSymRef = STATIC_FIELD_READ;

            // if(!exhaustive){
            //    processNodeValues[usefulNode].insert(PointsToGraph::bottomEntry);
            // }
            int len;
            // std::cout << usefulNode->getGlobalIndex() <<" " << usefulNode->getSymbolReference()->getReferenceNumber() << " " <<  << std::endl;
            std::string field_name = usefulNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(usefulNode->getSymbolReference()->getCPIndex(), len);
            field_name = field_name.substr(0, len);

            std::string class_name = usefulNode->getSymbolReference()->getName(comp->getDebug());
            int dot_index = class_name.rfind(".");
            class_name = class_name.substr(0, dot_index);
            field_name = class_name + "." + field_name;
            if (class_to_staticPAGNode.find(class_name) == class_to_staticPAGNode.end())
            {
               class_to_staticPAGNode[class_name] = new PAGNode(STATIC, class_name, methodIndex);
               pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(class_to_staticPAGNode[class_name]);

               pag->PAG_nodes.insert(class_to_staticPAGNode[class_name]);
               nodeAllocationMap[usefulNode] = class_to_staticPAGNode[class_name];
            }
         }
         else
         {
            int loadSymRef = usefulNode->getSymbolReference()->getReferenceNumber();

            evaluatedSymRef = loadSymRef;

            // if(populatePTA){
            //    if(usefulNode->getSymbolReference()->getSymbol()->getKind() == TR::Symbol::IsMethodMetaData){
            //       std::string loadName = comp->getDebug()->getMetaDataName(usefulNode->getSymbolReference());
            //       if(loadName.find("ExceptionMeta") != std::string::npos){
            //          processNodeValues[usefulNode].insert(PointsToGraph::bottomEntry);
            //       }
            //    }else if (usefulNode->getSymbolReference()->getSymbol()->castToStaticSymbol()->isConstString()){
            //       processNodeValues[usefulNode].insert(PointsToGraph::stringEntry);
            //    }else{

            //       set<Entry> pointsToSet = methodPTG[currentMethod]->getPointsToSet(loadSymRef);
            //       processNodeValues[usefulNode].insert(pointsToSet.begin(), pointsToSet.end());
            //    }
            // }
         }
         // std::cout<<"evaluatedSymRef: in aload"<<evaluatedSymRef<<std::endl;

         break;
      }

      case TR::aloadi:
      {

         /*
           A statement `x = y.f` is broken down as:

            1. aload y -> Load the reference of y from a local variable.
            2. aloadi f -> Load the field f from the object y.
            3. astore x -> Store the result in x.

            //NOTE: child of aloadi is only aload and not astore
            // child of aloadi could be "==> acalli"
         */

         // std::cout<<"inside aloadi 2\n";
         // std::cout << node->getSymbolReference()->getName(comp->getDebug()) << node->getByteCodeIndex()<<"\n";

         // // TODO:
         // // array subs look like this:
         // //         n21n      compressedRefs
         // //         n19n        aloadi  <array-shadow>[#232  Shadow] [flags 0x80000607 0x0 ]
         // //         n18n          aladd (internalPtr sharedMemory )
         // //         n8n             ==>aload
         // //         n17n            ladd
         // //         n15n              lshl
         // //         n14n                i2l (X>=0 )
         // //         n9n                   ==>iconst 9
         // //         n13n                iconst 2
         // //         n16n              lconst 16
         // //         n20n        lconst 0

         std::string field;
         if (usefulNode->getSymbol()->isArrayShadowSymbol()) // handle array load
         {

            TR::Node *receiverNode = usefulNode->getFirstChild()->getFirstChild();
            evaluatedSymRef = evaluateNode(receiverNode, evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);

            //    if(populatePTA){
            //       // std::cout<<"array read "<<receiverNode<<"\n";
            //       std::set<Entry> receiverNodeVals = processNodeValues[receiverNode];
            //       field = "_$";
            //       //std::cout<<"is this issue or no ?\n";
            //       for (Entry receiver : receiverNodeVals)
            //       {
            //          set<Entry> rhsPointees = methodPTG[currentMethod]->getPointsToSet(receiver, field);
            //          processNodeValues[usefulNode].insert(rhsPointees.begin(), rhsPointees.end());
            //       }
            //    }
         }
         else
         {

            TR::SymbolReference *symRef = usefulNode->getSymbolReference();
            TR_ASSERT_FATAL(symRef, "aloadi fail 1");

            // bool isUnresolved = symRef->isUnresolved();
            // IFDIAGPRINT << "isUnresolved = " << isUnresolved << endl;

            bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;
            // IFDIAGPRINT << "isShadow = " << isShadow << endl;

            int cpIndex = symRef->getCPIndex();
            // IFDIAGPRINT << "cp index = " << cpIndex << endl;

            if (/* !isUnresolved && */ isShadow && cpIndex > 0)
            {
               // this is most certainly a field access, until proven otherwise

               // receiver,
               TR::Node *receiverNode = usefulNode->getFirstChild();
               TR_ASSERT_FATAL(receiverNode, "aloadi fail 2");

               evaluatedSymRef = evaluateNode(receiverNode, evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);
               // std::cout<<"evaluatedSymRef: in aloadi"<<evaluatedSymRef<<std::endl;
               // if(populatePTA){
               // std::set<Entry> receiverNodeVals = processNodeValues[receiverNode];
               int32_t len;
               const char *fieldName = usefulNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(usefulNode->getSymbolReference()->getCPIndex(), len);
               field.assign(fieldName, fieldName + len);
               // for (Entry receiver : receiverNodeVals)
               // {
               //    set<Entry> rhsPointees = methodPTG[currentMethod]->getPointsToSet(receiver, field);
               //    processNodeValues[usefulNode].insert(rhsPointees.begin(), rhsPointees.end());
               // }
               // }

               PAGNode *receiver_pag_ptr;
               int32_t receiver_symRef = -78765; // random negative number
               if (receiverNode->getOpCode().hasSymbolReference() && receiverNode->getSymbolReference())
               {
                  receiver_symRef = receiverNode->getSymbolReference()->getReferenceNumber();
               }

               if (symRefNumToPAGNode[methodPersistentId].find(receiver_symRef) != symRefNumToPAGNode[methodPersistentId].end())
               {
                  receiver_pag_ptr = symRefNumToPAGNode[methodPersistentId][receiver_symRef];
                  nodeAllocationMap[receiverNode] = receiver_pag_ptr;
               }
               else if (nodeAllocationMap.find(receiverNode) != nodeAllocationMap.end())
               {
                  receiver_pag_ptr = nodeAllocationMap[receiverNode];
               }
               else
               {
                  receiver_pag_ptr = new PAGNode(VARIABLE, receiverNode->getSymbolReference()->getReferenceNumber(), nullptr, methodPersistentId, receiverNode->getByteCodeIndex(), methodIndex);
                  pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(receiver_pag_ptr);
                  pag->PAG_nodes.insert(receiver_pag_ptr);
                  nodeAllocationMap[receiverNode] = receiver_pag_ptr;
                  if (receiver_symRef >= 0)
                  {
                     symRefNumToPAGNode[methodPersistentId][receiver_symRef] = receiver_pag_ptr;
                     symRefNumToNode[receiver_symRef] = receiverNode;
                  }
               }
            }
         }

         break;
      }
      case TR::awrtbar:
      {
         // the structure of the awrtbar node for a static store is as follows. We are interested only in the first child (corresponds to the rhs in A.f = x)

         //   awrtbar  A.f LA;[#356  notAccessed Static] [flags 0x307 0x0 ]
         //     aload  <auto slot 1>[#363  Auto] [flags 0x7 0x0 ]
         //     aloadi  <javaLangClassFromClass>[#275  Shadow +48] [flags 0x607 0x0 ]
         //       ==>loadaddr

         // if (usefulNode->stmtNumber == 0)
         // {
         //    counter.stmtCount++;
         //    usefulNode->stmtNumber = counter.stmtCount;

         // }

         evaluatedSymRef = evaluateNode(usefulNode->getFirstChild(), evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);

         int len;
         std::string field_name = usefulNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(usefulNode->getSymbolReference()->getCPIndex(), len);
         field_name = field_name.substr(0, len);

         std::string class_name = usefulNode->getSymbolReference()->getName(comp->getDebug());
         int dot_index = class_name.rfind(".");
         class_name = class_name.substr(0, dot_index);
         field_name = class_name + "." + field_name; // A.f
         if (class_to_staticPAGNode.find(class_name) == class_to_staticPAGNode.end())
         {
            class_to_staticPAGNode[class_name] = new PAGNode(STATIC, class_name, methodIndex);
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(class_to_staticPAGNode[class_name]);

            pag->PAG_nodes.insert(class_to_staticPAGNode[class_name]);
         }
         // A.f1 = b1;   b1 --putf--> A
         PAGNode *static_pag_ptr = class_to_staticPAGNode[class_name];

         PAGNode *rhs_pag_ptr;
         if (symRefNumToPAGNode[methodPersistentId].find(evaluatedSymRef) != symRefNumToPAGNode[methodPersistentId].end())
         {

            rhs_pag_ptr = symRefNumToPAGNode[methodPersistentId][evaluatedSymRef];
            nodeAllocationMap[usefulNode->getFirstChild()] = rhs_pag_ptr;
         }
         else if (nodeAllocationMap.find(usefulNode->getFirstChild()) != nodeAllocationMap.end())
         {

            rhs_pag_ptr = nodeAllocationMap[usefulNode->getFirstChild()];
         }
         else
         {

            rhs_pag_ptr = new PAGNode(VARIABLE, evaluatedSymRef, nullptr, methodPersistentId, usefulNode->getFirstChild()->getByteCodeIndex(), methodIndex);
            pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(rhs_pag_ptr);

            pag->PAG_nodes.insert(rhs_pag_ptr);
            nodeAllocationMap[usefulNode->getFirstChild()] = rhs_pag_ptr;
            // if (rhs_node_symRef >= 0)
            // {
            symRefNumToPAGNode[methodPersistentId][evaluatedSymRef] = rhs_pag_ptr;
            symRefNumToNode[evaluatedSymRef] = usefulNode->getFirstChild();
            // }
         }

         // PAGEdge *new_edge = new PAGEdge(rhs_pag_ptr, static_pag_ptr, PUTFIELD, field_name);

         // rhs_pag_ptr->outgoing.insert(new_edge);

         // static_pag_ptr->incoming.insert(new_edge);

         pag->addEdge(rhs_pag_ptr, static_pag_ptr, PUTFIELD, field_name);
         updateMatchEdges();
         pag->LeakyNodes.insert(rhs_pag_ptr);
         staticField_to_Node[field_name] = static_pag_ptr;
         // stmtNumber[methodPersistentId][usefulNode->stmtNumber] = usefulNode;
         // mSet.stmtMap[evaluatedSymRef].insert(usefulNode->stmtNumber);

         break;
      }
      case TR::awrtbari:
      {
         /*
           The first child is the address being written to.
           The second child is the object being stored (or the source object) -> acalli,aload,aconst
           The third child is the object being stored into (or the destination object).
         */
         // process field store
         // first we obtain the children of awrtbari
         // obviously we only process if the RHS of the field write is a ref type

         // awrtbari also performs array writes!

         // if (usefulNode->stmtNumber == 0)
         // {
         //    counter.stmtCount++;
         //    usefulNode->stmtNumber = counter.stmtCount;

         // }

         // stmtNumber[methodPersistentId][usefulNode->stmtNumber] = usefulNode;

         // std::cout << getMethodName(comp->getOwningMethodSymbol(currentMethod)) << " is the method name in awrtbari$$$$\n";

         TR::Node *rhsNode = usefulNode->getSecondChild();

         TR_ASSERT_FATAL(rhsNode, "awrtbari fail");
         TR::Node *receiverNode = usefulNode->getFirstChild();
         TR_ASSERT_FATAL(receiverNode, "awrtbari fail 2");

         if (rhsNode->getDataType() == TR::Address) // only process if the RHS of the field write is a ref type
         {

            int32_t rhs_node_symRef = -9876;
            PAGNode *rhs_pag_ptr = nullptr;
            rhs_node_symRef = evaluateNode(rhsNode, evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);
            // std::cout << "rhs_node_symRef: " << rhs_node_symRef << std::endl;
            // if (!usefulNode->getSymbol()->isArrayShadowSymbol())
            // {
            if (rhsNode->getOpCode().hasSymbolReference() && rhsNode->getOpCodeValue() != TR::New)
            {
               rhs_node_symRef = rhsNode->getSymbolReference()->getReferenceNumber();
            }

            if (usefulNode->getSymbol()->isArrayShadowSymbol())
               receiverNode = usefulNode->getThirdChild();

            // receiver
            int32_t receiver_node_symRef = receiverNode->getSymbolReference()->getReferenceNumber();

            if (symRefNumToPAGNode[methodPersistentId].find(rhs_node_symRef) != symRefNumToPAGNode[methodPersistentId].end())
            {

               rhs_pag_ptr = symRefNumToPAGNode[methodPersistentId][rhs_node_symRef];
               nodeAllocationMap[rhsNode] = rhs_pag_ptr;
            }
            else if (nodeAllocationMap.find(rhsNode) != nodeAllocationMap.end())
            {

               rhs_pag_ptr = nodeAllocationMap[rhsNode];
            }
            else
            {
               rhs_pag_ptr = new PAGNode(VARIABLE, rhs_node_symRef, nullptr, methodPersistentId, rhsNode->getByteCodeIndex(), methodIndex);
               pag->methods_to_allMethodNodes[current_method_index].push_back(rhs_pag_ptr);

               pag->PAG_nodes.insert(rhs_pag_ptr);
               nodeAllocationMap[rhsNode] = rhs_pag_ptr;
               if (rhs_node_symRef >= 0)
               {
                  symRefNumToPAGNode[methodPersistentId][rhs_node_symRef] = rhs_pag_ptr;
                  symRefNumToNode[rhs_node_symRef] = rhsNode;
               }
            }

            PAGNode *receiver_pag_ptr;
            if (symRefNumToPAGNode[methodPersistentId].find(receiver_node_symRef) != symRefNumToPAGNode[methodPersistentId].end())
            {
               receiver_pag_ptr = symRefNumToPAGNode[methodPersistentId][receiver_node_symRef];
               nodeAllocationMap[receiverNode] = receiver_pag_ptr;
            }
            else if (nodeAllocationMap.find(receiverNode) != nodeAllocationMap.end())
            {
               receiver_pag_ptr = nodeAllocationMap[receiverNode];
            }
            else
            {
               receiver_pag_ptr = new PAGNode(VARIABLE, receiverNode->getSymbolReference()->getReferenceNumber(), nullptr, methodPersistentId, receiverNode->getByteCodeIndex(), methodIndex);
               pag->PAG_nodes.insert(receiver_pag_ptr);
               pag->methods_to_allMethodNodes[current_method_index].push_back(receiver_pag_ptr);

               nodeAllocationMap[receiverNode] = receiver_pag_ptr;
               if (rhs_node_symRef >= 0)
               {
                  symRefNumToPAGNode[methodPersistentId][receiver_node_symRef] = receiver_pag_ptr;
                  symRefNumToNode[receiver_node_symRef] = receiverNode;
               }
            }
            int len;
            string field_name;
            if (usefulNode->getSymbol()->isArrayShadowSymbol())
            {
               field_name = "$";
            }
            else
            {
               field_name = usefulNode->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(usefulNode->getSymbolReference()->getCPIndex(), len);
               field_name = field_name.substr(0, len);
            }
            // PAGEdge *new_edge = new PAGEdge(rhs_pag_ptr, receiver_pag_ptr, PUTFIELD, field_name);

            // rhs_pag_ptr->outgoing.insert(new_edge);

            // receiver_pag_ptr->incoming.insert(new_edge);
            // TR_OpaqueMethodBlock *clazz = usefulNode->getSymbol()->getResolvedMethodSymbol()->getResolvedMethod()->getPersistentIdentifier();
            // TR::SymbolReference *fieldSymRef = usefulNode->getSymbolReference();

            // TR_OpaqueClassBlock *declaringClassBlock = fieldSymRef->getOwningMethod(comp)->getDeclaringClassFromFieldOrStatic(comp, fieldSymRef->getCPIndex());
            // J9Class *resolvedClass = (J9Class *)declaringClassBlock;

            // J9UTF8 *classNameutf8 = J9ROMCLASS_CLASSNAME(resolvedClass->romClass);
            // const char *classNameData = (const char *)J9UTF8_DATA(classNameutf8);
            // uint16_t classNameLength = J9UTF8_LENGTH(classNameutf8);
            // std::string className(classNameData,classNameLength);

            // field_name = className + "." + field_name;
            std::string name = usefulNode->getSymbolReference()->getName(comp->getDebug());
            std::string full_name = name.substr(0, name.find(' '));
            ;
            std::cout << full_name << std::endl;
            pag->addEdge(rhs_pag_ptr, receiver_pag_ptr, PUTFIELD, field_name);
            if (pag->threadAccessibleFields.find(full_name) != pag->threadAccessibleFields.end())
            {
               pag->LeakyNodes.insert(rhs_pag_ptr);
            }

            //       TR::SymbolReference *symRef = usefulNode->getSymbolReference();
            //       // bool isUnresolved = symRef->isUnresolved();
            //       bool isShadow = symRef->getSymbol()->getKind() == TR::Symbol::IsShadow;
            //       int cpIndex = symRef->getCPIndex();

            //       if (/* !isUnresolved && */ isShadow && cpIndex > 0)
            //       {
            //          //    // this is most certainly a field access, until proven otherwise

            //          if (loadSymRef <= -10 || loadSymRef >= 0)
            //          {
            //             mSet.ds.unionDS(storeSymRef, loadSymRef);
            //             mSet.stmtMap[storeSymRef].insert(usefulNode->stmtNumber);
            //          }
            //          else
            //          {
            //             if (loadSymRef == -1)
            //             {
            //                mSet.stmtMap[storeSymRef].insert(usefulNode->stmtNumber);
            //             }
            //          }
            //       }

            //       evaluatedSymRef = storeSymRef;
            //    }
            //    else{
            //          //array writes

            //          TR::Node *receiverNode = usefulNode->getThirdChild();

            //          // value
            //          int storeSymRef = evaluateNode(receiverNode, evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);

            //          // add edge rhsNode --putfield[$]--> receiverNode
            //          PAGNode *receiver_pag_ptr;
            //          if (symRefNumToPAGNode[methodPersistentId].find(receiver_node_symRef) != symRefNumToPAGNode[methodPersistentId].end())
            //          {
            //             receiver_pag_ptr = symRefNumToPAGNode[methodPersistentId][receiver_node_symRef];
            //             nodeAllocationMap[receiverNode] = receiver_pag_ptr;
            //          }
            //          else if (nodeAllocationMap.find(receiverNode) != nodeAllocationMap.end())
            //          {
            //             receiver_pag_ptr = nodeAllocationMap[receiverNode];
            //          }
            //          else
            //          {
            //             receiver_pag_ptr = new PAGNode(VARIABLE, receiverNode->getSymbolReference()->getReferenceNumber(), nullptr, methodPersistentId, receiverNode->getByteCodeIndex());
            //             pag->PAG_nodes.insert(receiver_pag_ptr);
            // pag->methods_to_allMethodNodes[currentMethod].push_back(receiver_pag_ptr);

            //             nodeAllocationMap[receiverNode] = receiver_pag_ptr;
            //             if (rhs_node_symRef >= 0)
            //             {
            //                symRefNumToPAGNode[methodPersistentId][receiver_node_symRef] = receiver_pag_ptr;
            //                symRefNumToNode[receiver_node_symRef] = receiverNode;
            //             }
            //          }

            //          // if ((storeSymRef <= -10 || storeSymRef >= 0) && (loadSymRef <= -10 || loadSymRef >= 0))
            //          // {
            //          //    mSet.ds.unionDS(storeSymRef, loadSymRef);
            //          //    mSet.stmtMap[storeSymRef].insert(usefulNode->stmtNumber);
            //          //    // std::cout<<storeSymRef<< " " <<loadSymRef<<std::endl;
            //          // }
            //          // else
            //          // {
            //          //    if ((storeSymRef <= -10 || storeSymRef >= 0) && loadSymRef == -1)
            //          //    {
            //          //       mSet.stmtMap[storeSymRef].insert(usefulNode->stmtNumber);
            //          //    }
            //          // }

            //          evaluatedSymRef = storeSymRef;
         }

         //    //
         // }

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

         // check if method is a helper
         bool isHelperMethodCall = usefulNode->getSymbol()->castToMethodSymbol()->isHelper();
         const char *methodName;
         if (!isHelperMethodCall)
         {
            methodName = usefulNode->getSymbolReference()->getName(comp->getDebug());
            // cache the name of method
            cachedMethodName[usefulNode] = methodName;

            std::cout << "Called method: " << cachedMethodName[usefulNode] << " usefull node " << usefulNode << std::endl;
         }

         // we do not want to process helper method calls (prepareForOSR, potentialOSRPointHelper, for example)
         if (isHelperMethodCall) // || (usefulNode->getSymbolReference()->isUnresolved() && !usefulNode->getSymbol()->castToMethodSymbol()->isInterface()))
         {
            evaluatedSymRef = -1;
            break;
         }
         else if (isLibraryMethod(methodName) && ((std::string)methodName).find("java/lang/Object.<init>") == std::string::npos)
         {
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

            //  // methods to be peeked
            //  std::unordered_set<TR_OpaqueMethodBlock *> methodsToPeek;
            int argIndex = 0;
            if (isStatic)
            {
               argIndex = 1;
               int classNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameLength();
               string className = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameChars();
               className = className.substr(0, classNameLength);

               TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), classNameLength, comp->getCurrentMethod(), true);
               TR_ASSERT_FATAL(type, "unable to get class pointer for receiver %s", className.c_str());
               int methodNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->nameLength();
               std::string methodNm;
               methodNm = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->nameChars();
               methodNm = methodNm.substr(0, methodNameLength);
               int sigLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->signatureLength();
               std::string signatureChars = usefulNode->getSymbol()->getMethodSymbol()->getMethod()->signatureChars();
               std::string sig = signatureChars.substr(0, sigLength);

               std::cout << "In isStatic :: Class name: " << className << " method_name: " << methodNm << " Signature " << sig << std::endl;

               if (type != NULL)
               {
                  TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, type, methodNm.c_str(), sig.c_str());
                  if (targetMethod != NULL)
                  {
                     methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                     // cachedParameterType[targetMethod->getPersistentIdentifier()][0] = type;
                  }
               }
            }
            else
            {
               int methodNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->nameLength();
               std::string methodNm;

               // std::cout<<"Failing after here: " << usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->nameChars() << std::endl;
               // TR_OpaqueMethodBlock* persistentIdentifier = usefulNode->getSymbol()->getResolvedMethodSymbol()->getResolvedMethod()->getPersistentIdentifier();
               std::cout << usefulNode->getOpCode().getName() << " " << usefulNode->getSymbolReference()->getName(comp->getDebug()) << std::endl;

               if (!usefulNode->getSymbolReference()->isUnresolved() && !isInterfaceInvoke && usefulNode->getSymbol()->getResolvedMethodSymbol()->getResolvedMethod()->getPersistentIdentifier() == _threadStartPersistentId)
               {
                  methodNm = "run";
                  // std::cout << "short-circuit Thread.start with  .run()\n";
               }
               else
               {

                  // fetch method name
                  methodNm = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->nameChars();
                  methodNm = methodNm.substr(0, methodNameLength);
               }
               // if(methodNm.rfind("<init>")!=string::npos) break;

               // fetch target method signature
               int sigLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->signatureLength();
               std::string signatureChars = usefulNode->getSymbol()->getMethodSymbol()->getMethod()->signatureChars();
               std::string sig = signatureChars.substr(0, sigLength);

               if (cachedMethodName[usefulNode].find("java/lang/Object.<init>()V") != std::string::npos)
               {

                  // for (auto ci : _classIndices)
                  // {
                  //    std::string className = ci.second;
                  //    int len = strlen(className.c_str());
                  //    TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), len, comp->getCurrentMethod(),true);
                  //    if (type != NULL)
                  //    {
                  //       TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, type, methodNm.c_str(), sig.c_str());
                  //       if (targetMethod != NULL)
                  //       {
                  //          methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                  //          cachedParameterType[targetMethod->getPersistentIdentifier()][0] = type;
                  //       }
                  //    }
                  // }
               }
               else if (cachedMethodName[usefulNode].find("java/lang/reflect/Constructor.newInstance([Ljava/lang/Object;)Ljava/lang/Object") != std::string::npos || cachedMethodName[usefulNode].find("java/lang/reflect/Method.invoke(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;") != std::string::npos)
               // reflective calls
               {

                  int lineNumber = getCachedLineNumber(usefulNode, comp);
                  std::unordered_set<std::string> targets = getReflectiveTargets(inverseMethodNameIDmapping[methodPersistentId], lineNumber);
                  for (std::string fullName : targets)
                  {
                     auto dotPos = fullName.find('.');
                     auto parenPos = fullName.find('(');

                     std::string className = fullName.substr(0, dotPos);
                     std::string methodName = fullName.substr(dotPos + 1, parenPos - dotPos - 1);
                     std::string signature = fullName.substr(parenPos);

                     TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), className.size(), comp->getCurrentMethod(), true);
                     TR_ResolvedMethod *targetMethod = getCachedResolvedMethod(comp, type, methodName.c_str(), signature.c_str());

                     // std::cout <<"Target method "<<getMethodName(targetMethod->findOrCreateJittedMethodSymbol(comp))<<std::endl;
                     // if(!targetMethod) continue;

                     if (targetMethod && !targetMethod->isAbstract())
                     {

                        //! TR::Compiler->cls.isInterfaceClass(comp, currentClass)){
                        // std::cout<<"targetMethod in CHA is null\n";
                        // if (classPtrToIndex[currentClass] == 0)
                        // {
                        //    // std::cout<<"didid 4 = "<<methodName<<"\n";
                        // }
                        // _callsiteReceivers[methodPtrToIndex[currentMethod]][callsiteBCI].insert(classPtrToIndex[currentClass]);
                        if (!isLibraryMethod(getMethodName(targetMethod->findOrCreateJittedMethodSymbol(comp))))
                        {
                           methodsToPeek.insert(targetMethod->getPersistentIdentifier());
                           std::cout << "Added to peek (in reflective block): " << getMethodName(targetMethod->findOrCreateJittedMethodSymbol(comp)) << " called  method: " << methodNm << sig << std::endl;
                           cachedParameterType[targetMethod->getPersistentIdentifier()][0] = type;
                        }
                     }
                  }
               }
               else
               {
                  // CHA based
                  int classNameLength = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameLength();
                  char *classNameChars = usefulNode->getSymbol()->castToResolvedMethodSymbol()->getMethod()->classNameChars();
                  string className(classNameChars, classNameLength);

                  TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), classNameLength, comp->getCurrentMethod(), true);
                  TR_ASSERT_FATAL(type, "unable to get class pointer for receiver %s", className.c_str());

                  std::queue<TR_OpaqueClassBlock *> bfsList;
                  std::unordered_set<TR_OpaqueClassBlock *> visitedClass;

                  bfsList.push(type);
                  visitedClass.insert(type);

                  // std::string tpName = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());
                  // std::cout <<"Tyepc class name: "<<className << std::endl;

                  // std::cout << methodNm << std::endl;
                  std::cout << "type class name = " << className << " where method name = " << methodNm << "\n";

                  if (cachedMethodName[usefulNode].find(".<init>") != std::string::npos) //&& cachedMethodName[usefulNode].find("java/lang/Object.<init>()V") == std::string::npos) // if this is a constructor call then directly peek
                  {
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
                  else
                     getTargetsToPeek(bfsList, visitedClass, methodsToPeek, comp, methodNm, sig);
               }
            }
            // std::cout<<"-------Methods to peek size-------"<<methodsToPeek.size()<<std::endl;
            callsite_to_targets[usefulNode] = methodsToPeek;

            for (auto calleeMethodPtr : methodsToPeek)
            {

               std::string calleeName = getMethodName(getCachedResolvedMethodFromPtr(comp, calleeMethodPtr)->findOrCreateJittedMethodSymbol(comp));
               if (_methodsAnalyzed.find(calleeMethodPtr) == _methodsAnalyzed.end() && _methodsBeingAnalyzed.find(calleeMethodPtr) == _methodsBeingAnalyzed.end() && alreadyAnalyzedMethods.find(calleeName) == alreadyAnalyzedMethods.end())
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

                  TR_MethodParameterIterator *parIterator = getCachedResolvedMethodSymbol(comp,calleeMethodPtr)->getResolvedMethod()->getParameterIterator(*comp);
                  for (int argNo = 1; !parIterator->atEnd(); parIterator->advanceCursor(), argNo++)
                  {
                     if (parIterator->isArray() || parIterator->isClass())
                     {
                        cachedParameterType[calleeMethodPtr][argNo] = parIterator->getOpaqueClass();
                     }
                  }
               }

               // if (usefulNode->getDataType() == TR::Address && fillCache && methodPTG[calleeMethodPtr]->contains(-3))
               // {
               //    cachedValues[usefulNode].insert(methodPTG[calleeMethodPtr]->getReturnPointsTo().begin(), methodPTG[calleeMethodPtr]->getReturnPointsTo().end());
               //    // std::cout<<"caching return for "<<usefulNode<<" size = "<<cachedValues[usefulNode].size()<<"\n";
               // }
            }

            // bool stmtSaved = false;
            // if (usefulNode->getDataType() == TR::Address)
            // {
            //    // generate a dummy variable number to represent return of this callnode
            //    counter.retCount--;

            //    // evaluated value of this callnode will be return variable
            //    evaluatedSymRef = counter.retCount;
            //    methodDict[currentMethod].stmtMap[evaluatedSymRef].insert(usefulNode->stmtNumber);
            //    stmtSaved = true;

            //    // update mappings of call node, ret, etc
            //    argCallNode[currentMethod][counter.retCount].insert(std::make_pair(usefulNode, -3));
            //    inverseArgCallNode[currentMethod][usefulNode][-3] = counter.retCount;
            // }

            // first arg index points to receiver in case of non static
            int32_t firstArgIndex = usefulNode->getFirstArgumentIndex();
            int32_t numChildren = usefulNode->getNumChildren();
            for (int32_t i = firstArgIndex; i < numChildren; i++)
            {
               TR::Node *actual_param_node = usefulNode->getChild(i);
               if (actual_param_node->getDataType() != TR::Address)
               {
                  argIndex++;
                  continue;
               }
               // get argument variable
               int temp = evaluateNode(actual_param_node, evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);

               // update mapping of var to stmt
               // std::cout<<"temp = "<<temp<<"\n";
               // methodDict[currentMethod].stmtMap[temp].insert(usefulNode->stmtNumber);
               // stmtSaved = true;

               // update mappings of call node, arg, etc
               argCallNode[currentMethod][temp].insert(std::make_pair(usefulNode, argIndex));
               inverseArgCallNode[currentMethod][usefulNode][argIndex] = temp;
               EdgeType e_type = ASSIGN;
               PAGNode *actual_param_pag_ptr = NULL;
               std::string methodBeingComp = getMethodName(comp->getMethodSymbol());
               // std::cout << "methodBeingComp" << methodBeingComp << std::endl;

               if (cachedMethodName[usefulNode].find(".<init>") != std::string::npos && argIndex == 0 && methodBeingComp.find(".<init>") == std::string::npos)
               {
                  int globalIndex = usefulNode->getFirstChild()->getGlobalIndex();
                  actual_param_pag_ptr = symRefNumToPAGNode[currentMethod][globalIndex];
                  if(!actual_param_pag_ptr)
                  {
                     actual_param_pag_ptr = symref_PAGNode[usefulNode->getFirstChild()->getSymbolReference()->getReferenceNumber()];
                  }
                  e_type = ASSIGN;
               }
               else if (symRefNumToPAGNode[methodPersistentId].find(temp) != symRefNumToPAGNode[methodPersistentId].end())
               {
                  actual_param_pag_ptr = symRefNumToPAGNode[methodPersistentId][temp];
                  nodeAllocationMap[actual_param_node] = actual_param_pag_ptr;
               }
               else if (nodeAllocationMap.find(actual_param_node) == nodeAllocationMap.end())
               {
                  actual_param_pag_ptr = nodeAllocationMap[actual_param_node];
                  if (!actual_param_pag_ptr)
                  {
                     // printf("%s -- %s\n",cachedMethodName[usefulNode].c_str(),inverseMethodNameIDmapping[methodPersistentId].c_str());
                     // std::cout << usefulNode->getSymbolReference()->getName(comp->getDebug()) << std::endl;
                     // std::cout << usefulNode->getFirstChild()->getSymbolReference()->getName(comp->getDebug()) << std::endl;
                     actual_param_pag_ptr = pag->bottom_node;
                  }
               }
               else
               {
                  int ref_no = -238933;
                  if (actual_param_node->getOpCode().hasSymbolReference())
                     ref_no = actual_param_node->getSymbolReference()->getReferenceNumber();
                  actual_param_pag_ptr = new PAGNode(VARIABLE, ref_no, nullptr, methodPersistentId, actual_param_node->getByteCodeIndex(), methodIndex);
                  pag->PAG_nodes.insert(actual_param_pag_ptr);
                  pag->methods_to_allMethodNodes[current_method_index].push_back(actual_param_pag_ptr);

                  nodeAllocationMap[actual_param_node] = actual_param_pag_ptr;

                  symRefNumToPAGNode[methodPersistentId][temp] = actual_param_pag_ptr;
                  symRefNumToNode[temp] = actual_param_node;
               }

               for (auto target : callsite_to_targets[usefulNode])
               {
                  // std::cout << "IIIIformal_param_pag_ptr: " << " CURRENT Method: " << getMethodName(comp->getOwningMethodSymbol(currentMethod)) << " target " << target << " " << getMethodName(comp->getOwningMethodSymbol(target)) << std::endl;
                  vector<PAGNode *> formal_nodes = pag->methods_to_formalNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,target), comp)];

                  PAGNode *formal_param_pag_ptr = formal_nodes.empty() ? pag->bottom_node : formal_nodes[argIndex];

                  // Add edge from actual to formal pag node
                  // PAGEdge *call_edge = new PAGEdge(actual_param_pag_ptr, formal_param_pag_ptr, e_type, usefulNode->getByteCodeIndex());
                  // actual_param_pag_ptr->outgoing.insert(call_edge);
                  // formal_param_pag_ptr->incoming.insert(call_edge);
                  // std::cout << "$$$$TArg index " << argIndex << std::endl;
                  pag->addEdge(actual_param_pag_ptr, formal_param_pag_ptr, e_type, usefulNode->getByteCodeIndex());
                  if (e_type == GETFIELD)
                  {
                     updateMatchEdges();
                     for (auto *edge : pag->getMatchEdgesEndingAt(formal_param_pag_ptr))
                     {
                        PAGNode *src = edge->src;
                        formal_param_pag_ptr->pointee_class_names.insert(src->pointee_class_names.begin(), src->pointee_class_names.end());
                     }
                  }
                  else if (e_type == ASSIGN)
                  {
                     formal_param_pag_ptr->pointee_class_names.insert(actual_param_pag_ptr->pointee_class_names.begin(), actual_param_pag_ptr->pointee_class_names.end());
                  }

                  callsite_to_ActualParamPAGNodes[usefulNode->getByteCodeIndex()].insert(actual_param_pag_ptr);
               }
               // increment argument
               argIndex++;
            }

            // if (!stmtSaved)
            // {
            //    methodDict[currentMethod].stmtMap[-2].insert(usefulNode->stmtNumber);
            // }
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
         // handle the return value. We use a magic number (-99) to represent the pseudo-symref of the return var
         // also, we only need to worry about the areturn. So why do we have the others here? Maybe want to process some cleanup
         //   actions on encountering a return op

         if (opCode == TR::areturn)
         {
            TR::Node *child_node = usefulNode->getFirstChild();
            // the evaluated value of the first child (ie. the call node) will hold the respective call's return value - simply fetch and assign
            int loadSymRef = evaluateNode(child_node, evaluatedNodeValues, counter, methodIndex, mSet, currentMethod, comp, populatePTA);

            // Add edge from the child of the useful node(loadSymRef) to return_pag_node_ptr;
            PAGNode *return_pag_node_ptr = pag->methods_to_returnNode[current_method_index];
            if (!return_pag_node_ptr)
            {
               TR::ResolvedMethodSymbol *methodSymbol = getCachedResolvedMethodFromPtr(comp, currentMethod)->findOrCreateJittedMethodSymbol(comp);
               int methodInd = getOrInsertMethodIndex(methodSymbol, comp);
               pag->methods_to_returnNode[methodInd] = new PAGNode(RETURN, RETURN_NODE_NAME, NULL, currentMethod, -1, methodInd);
               pag->PAG_nodes.insert(pag->methods_to_returnNode[methodInd]);
               pag->methods_to_allMethodNodes[methodInd].push_back(pag->methods_to_returnNode[methodInd]);
               return_pag_node_ptr = pag->methods_to_returnNode[methodInd];
            }
           
            int symref = -238933;
            if (child_node->getOpCode().hasSymbolReference())
               symref = child_node->getSymbolReference()->getReferenceNumber();
            // std::cout<< symref << std::endl;
            if (child_node->getOpCodeValue() == TR::aloadi)
            {

               TR::Node *y_node = child_node->getFirstChild();
               PAGNode *y_PAGnode_ptr;
               int32_t y_node_symRef = -78765; // some random negative number
               int y_ref_no = -238933;
               if(y_node->getOpCode().hasSymbolReference())
                  y_ref_no = y_node->getSymbolReference()->getReferenceNumber();

               if (y_node->getOpCode().hasSymbolReference() && y_node->getSymbolReference())
               {
                  y_node_symRef = y_node->getSymbolReference()->getReferenceNumber();
               }

               if (y_node_symRef >= 0 && symRefNumToPAGNode[methodPersistentId].find(y_node_symRef) != symRefNumToPAGNode[methodPersistentId].end())
               {
                  y_PAGnode_ptr = symRefNumToPAGNode[methodPersistentId][y_node_symRef];
                  y_node = symRefNumToNode[y_node_symRef];
               }
               else if (nodeAllocationMap.find(y_node) != nodeAllocationMap.end())
               {
                  y_PAGnode_ptr = nodeAllocationMap[y_node];
               }
               else
               {
                  y_PAGnode_ptr = new PAGNode(VARIABLE,y_ref_no, nullptr, methodPersistentId, y_node->getByteCodeIndex(), methodIndex);
                  pag->PAG_nodes.insert(y_PAGnode_ptr);
                  pag->methods_to_allMethodNodes[current_method_index].push_back(y_PAGnode_ptr);

                  nodeAllocationMap[y_node] = y_PAGnode_ptr;

                  symRefNumToPAGNode[methodPersistentId][y_node_symRef] = y_PAGnode_ptr;
                  symRefNumToNode[y_node_symRef] = y_node;
               }

               // Add edge:  y --Getfield--> x
               //            y_PAGnode_ptr --Getfield--> lhs_node_ptr
               int32_t len;
               string field_name ;
               if (child_node->getSymbol()->isArrayShadowSymbol())
               {
                  field_name = "$";
               }
               else
               {
                  field_name = child_node->getSymbolReference()->getOwningMethod(comp)->fieldNameChars(child_node->getSymbolReference()->getCPIndex(), len);
                  field_name = field_name.substr(0, len);
               }
              
               // std::cout <<"Y_node: " << y_node->getOpCodeValue() << std::endl;
               // std::cout << "In astore:field is "<<field_name<<" len = "<< len << std::endl;

               // PAGEdge *new_edge = new PAGEdge(y_PAGnode_ptr, return_pag_node_ptr, GETFIELD, field_name);

               // return_pag_node_ptr->incoming.insert(new_edge);
               // y_PAGnode_ptr->outgoing.insert(new_edge);
               pag->addEdge(y_PAGnode_ptr, return_pag_node_ptr, GETFIELD, field_name);

               updateMatchEdges();
               for (auto *edge : pag->getMatchEdgesEndingAt(return_pag_node_ptr))
               {
                  PAGNode *src = edge->src;
                  return_pag_node_ptr->pointee_class_names.insert(src->pointee_class_names.begin(), src->pointee_class_names.end());
               }
            }
            else if (child_node->getOpCodeValue() == TR::New)
            {

               int globalIndex = child_node->getGlobalIndex();

               // PAGEdge *new_edge = new PAGEdge(symRefNumToPAGNode[methodPersistentId][globalIndex], return_pag_node_ptr, ASSIGN);
               // symRefNumToPAGNode[methodPersistentId][globalIndex]->outgoing.insert(new_edge);
               // return_pag_node_ptr->incoming.insert(new_edge);
               pag->addEdge(symRefNumToPAGNode[methodPersistentId][globalIndex], return_pag_node_ptr, ASSIGN);
               return_pag_node_ptr->pointee_class_names.insert(symRefNumToPAGNode[methodPersistentId][globalIndex]->pointee_class_names.begin(), symRefNumToPAGNode[methodPersistentId][globalIndex]->pointee_class_names.end());
            }
            else if (callsite_to_targets.find(child_node) != callsite_to_targets.end()) // return b.foo() type of stmts => add edge from return node of foo to the current method's return node
            {
               std::unordered_set<TR_OpaqueMethodBlock *> targets = callsite_to_targets[child_node];
               for (auto target : targets)
               {
                  PAGNode *child_pag_ptr = pag->methods_to_returnNode[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,target), comp)];

                  // PAGEdge *new_edge = new PAGEdge(child_pag_ptr, return_pag_node_ptr, ASSIGN);

                  // return_pag_node_ptr->incoming.insert(new_edge);
                  // child_pag_ptr->outgoing.insert(new_edge);
                  pag->addEdge(child_pag_ptr, return_pag_node_ptr, ASSIGN);
                  return_pag_node_ptr->pointee_class_names.insert(child_pag_ptr->pointee_class_names.begin(), child_pag_ptr->pointee_class_names.end());
               }
            }
            else
            {
               PAGNode *child_pag_ptr;
               if (symRefNumToPAGNode[methodPersistentId].find(symref) != symRefNumToPAGNode[methodPersistentId].end())
               {
                  child_pag_ptr = symRefNumToPAGNode[methodPersistentId][symref];
                  nodeAllocationMap[child_node] = child_pag_ptr;
               }
               else
               {
                  child_pag_ptr = new PAGNode(VARIABLE, symref, nullptr, methodPersistentId, child_node->getByteCodeIndex(), methodIndex);
                  pag->PAG_nodes.insert(child_pag_ptr);
                  pag->methods_to_allMethodNodes[getOrInsertMethodIndex(getCachedResolvedMethodSymbol(comp,currentMethod), comp)].push_back(child_pag_ptr);

                  nodeAllocationMap[child_node] = child_pag_ptr;

                  symRefNumToPAGNode[methodPersistentId][symref] = child_pag_ptr;
                  symRefNumToNode[symref] = child_node;
               }
               // std::cout<< child_pag_ptr << "Is the child"<<std::endl;
               // PAGEdge *new_edge = new PAGEdge(child_pag_ptr, return_pag_node_ptr, ASSIGN);

               // return_pag_node_ptr->incoming.insert(new_edge);
               // child_pag_ptr->outgoing.insert(new_edge);
               pag->addEdge(child_pag_ptr, return_pag_node_ptr, ASSIGN);
               return_pag_node_ptr->pointee_class_names.insert(child_pag_ptr->pointee_class_names.begin(), child_pag_ptr->pointee_class_names.end());
            }

            evaluatedSymRef = loadSymRef;
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

   // TODO: update the evaluated values here, or in the caller? Lets do it here, for now
   evaluatedNodeValues[usefulNode] = evaluatedSymRef;
   return evaluatedSymRef;
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
      if (opCode == TR::treetop || opCode == TR::ResolveAndNULLCHK || opCode == TR::ResolveCHK || opCode == TR::compressedRefs || opCode == TR::NULLCHK || opCode == TR::ArrayStoreCHK)
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

PAGNode *evaluateAllocate(TR::Node *node, int methodIndex, bool isArray, TR::Compilation *comp)
{
   int allocationBCI = node->getByteCodeIndex();
   int callerIndex = methodIndex;
   // if(exhaustive)
   // {
   if (nodeAllocationMap.find(node) != nodeAllocationMap.end())
   {
      return nodeAllocationMap[node];
   }

   PAGNode *obj_ptr = new PAGNode(OBJECT, -1, nullptr, comp->getMethodSymbol()->getResolvedMethod()->getPersistentIdentifier(), allocationBCI, methodIndex);
   int32_t node_symRef = -7675;
   if (node->getOpCode().hasSymbolReference() && node->getSymbolReference())
      node_symRef = node->getSymbolReference()->getReferenceNumber();

   if (node_symRef >= 0)
   {
      symRefNumToPAGNode[comp->getMethodSymbol()->getResolvedMethod()->getPersistentIdentifier()][node_symRef] = obj_ptr;
      symRefNumToNode[node_symRef] = node;
   }
   pag->PAG_nodes.insert(obj_ptr);

   // if (_runtimeVerifierDiagnostics)
   //    cout << "evaluated an allocation node at n" << node->getGlobalIndex() << "n" << endl;

   // check the loadaddr child node to ensure that the instantiated type is resolved
   TR::Node *loadaddrNode;
   if (isArray)
   {
      loadaddrNode = node->getSecondChild();
   }
   else
   {
      loadaddrNode = node->getFirstChild();
   }

   nodeAllocationMap[node] = obj_ptr;
   // TR_Debug de(comp);
   // TR_Debug *deb = &de;
   // std::string obj_type = loadaddrNode->getSymbolReference()->getName(comp->getDebug());
   int len;
   TR::SymbolReference *symRef = loadaddrNode->getSymbolReference();
   std::cout << symRef << std::endl;

   // std::cout << "NAME IS " << loadaddrNode->getSymbolReference()->getName(comp->getDebug()) << std::endl;
   char *objc = TR::Compiler->cls.classNameChars(comp, symRef, len);
   std::string obj_type(objc, len);
   std::cout << "Allocate object type: " << obj_type << std::endl;
   nodeAllocationMap[node]->pointee_class_names.insert(obj_type);
   // std::cout<<"loadaddr node is "<<loadaddrNode<<"\n";
   // TR_ASSERT_FATAL(loadaddrNode->getOpCodeValue() == TR::loadaddr, "expected first child of jitnewobject to be loadaddr op");
   // if (loadaddrNode->getOpCodeValue() == TR::loadaddr && loadaddrNode->getSymbolReference()->isUnresolved())
   // {
   //    /*
   //    * the instantiated type is unresolved, we interpret that as "not on classpath and/or unresolved"
   //    *
   //    * assign an empty set at the allocation site and call it a day
   //    */

   //    // return null as a stopgap, we do't have an object to represent "empty" yet. This is fine since we ignore nulls anyway
   //    std::cout<<"loaddr null for "<<methodIndex<<"-"<<node->getByteCodeIndex()<<"\n";
   //    // std::cout<<"bci of null entry is "<<node->getByteCodeIndex()<<"\n";
   //    obj = PointsToGraph::nullEntry;
   //    //obj.bci = node->getByteCodeIndex();

   //    //org/dacapo/parser/TokenMgrError.addEscapes(Ljava/lang/String;)Ljava/lang/String;
   // }
   // else
   // {

   //    PAGNode node;
   //    node.bci = allocationBCI;
   //    node.caller = methodIndex;
   //    node.type = Reference;
   //    node.clazz = NULL;

   //    obj = node;
   // // }

   // nodeAllocationMap[node] = obj;
   // }else{
   //    Entry e = rawNode[to_string(callerIndex) + "-" + to_string(allocationBCI)];
   //    nodeAllocationMap[node] = e;
   // }
   return nodeAllocationMap[node];
}
bool isLibraryMethod(std::string methodName)
{

   bool isLibraryMethod = false;

   // if(methodName.rfind("java/lang/Thread.run") == 0)  return true;
   if (methodName.rfind("java/lang/Thread.start()V") == 0 || methodName.rfind("soot/rtlib/tamiflex/ReflectiveCallsWrapper", 0) == 0 /*|| methodName.rfind("java/security", 0) == 0*/ ||
       methodName.rfind("javax/crypto", 0) == 0)
   {
      isLibraryMethod = false;
      return isLibraryMethod;
   }

   if (methodName.rfind("org/apache/lucene", 0) == 0 || methodName.rfind("org/apache/xalan", 0) == 0)
   {
      return false;
   }
   else
      isLibraryMethod = methodName.rfind("java/lang/Thread.start()V") != 0 &&
                            methodName.rfind("java", 0) == 0 ||
                        methodName.rfind("com/ibm/", 0) == 0 ||
                        methodName.rfind("sun/", 0) == 0 ||
                        methodName.rfind("openj9/", 0) == 0 ||
                        methodName.rfind("jdk/", 0) == 0 ||
                        methodName.find("org/apache", 0) == 0 ||
                        methodName.find("org/slf4j", 0) == 0 ||
                        methodName.rfind("soot", 0) == 0 ||
                        methodName.rfind("org/jfree", 0) == 0 ||
                        methodName.rfind("org/codehaus", 0) == 0;

   return isLibraryMethod;
}

bool isTransparentMethod(std::string methodName)
{

   // omkar - ignore the concept of transparent methods for now.
   bool isTransparentMethod = false;
   /*
    * there are certain library methods that are known to have no effect on the reachable heap at a call site,
    * we cannot treat such library methods as opaque, and end up summarizing the reachable heap. This will cause
    * issues in later verification sites
    */
   isTransparentMethod = methodName.rfind("java/lang/Object", 0) == 0;

   // TODO: remove hardcode
   isTransparentMethod = false;

   return isTransparentMethod;
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
      if (!rm)
      {
         int len;
         // std::cout << TR::Compiler->cls.classNameChars(comp, classPointer,len) << std::endl;
         // std::cout<<"rm was null at: "<<meth<<" class pointer "<<TR::Compiler->cls.classSignature(comp, classPointer, comp->trMemory())<<std::endl;
      }
      cachedResolvedMethod[classPointer][meth] = rm;
   }
   return cachedResolvedMethod[classPointer][meth];
}
void printExhaustive()
{
   std::map<int, std::string> methodMap;
   int i = 0;
   ofstream miFile("mi.txt");
   map<int, std::string> inverseMethodIndices;
   for (auto m : pag->_methodIndices)
   {
      inverseMethodIndices[m.second] = m.first;
   }
   for (auto m : inverseMethodIndices)
   {
      miFile /*<<std::to_string(i)<<":"*/ << m.second << "\n";
      i++;
      // ofstream crFile("crr" + to_string(m.first) + ".txt");
      // for (auto r : _callsiteReceivers[m.first])
      // {
      //    crFile << r.first;
      //    for (auto s : r.second)
      //    {
      //       crFile << " " << s;
      //    }
      //    crFile << ";";
      // }
      // crFile.close();
   }

   miFile.close();
}

std::unordered_map<std::string, int> readMethodIndices()
{
   std::unordered_map<string, int> ret;
   char *methodIndicesFileName = "mi.txt";

   ifstream file(methodIndicesFileName);
   string methodName;
   int index = 1;
   while (file >> methodName)
   {
      // cout << methodName << ":" << index << endl;

      ret[methodName] = index;
      index++;
   }
   file.close();
   return ret;
}

void getAlreadyAnalyzedMethodNames()
{
   std::ifstream file("analyzedMethods.txt");
   std::string line;
   int index = 1;

   while (std::getline(file, line))
   {
      alreadyAnalyzedMethods.insert(line);
   }
   file.close();
}

void updateMatchEdges()
{
   for (PAGEdge *e1 : pag->getStoreEdges())
   {
      for (PAGEdge *e2 : pag->getLoadEdges())
      {
         if (e1->field == e2->field)
         {
            bool exists = false;
            for (PAGEdge *outEdge : e1->src->outgoing)
            {
               if (outEdge->dest == e2->dest && outEdge->type == MATCH)
               {
                  exists = true;
                  break;
               }
            }
            if (!exists)
            {
               pag->addEdge(e1->src, e2->dest, MATCH);
            }
         }
      }
   }
}

void getResolvedReflectiveCalls()
{
   std::ifstream file("transformedRefLog.txt");
   std::string line;

   while (std::getline(file, line))
   {
      if (line.empty())
         continue;

      std::istringstream iss(line);
      std::string caller, lineNumStr, callee;

      if (iss >> caller >> lineNumStr)
      {
         int lineNumber = std::stoi(lineNumStr);
         std::getline(iss, callee);

         if (!callee.empty() && callee[0] == ' ')
         {
            callee = callee.substr(1);
         }

         reflectiveCallGraph[caller].emplace_back(callee, lineNumber);
      }
   }
   file.close();
}

std::unordered_set<std::string> getReflectiveTargets(std::string &caller, int lineNumber)
{
   auto it = reflectiveCallGraph.find(caller);
   std::unordered_set<std::string> targets;
   if (it != reflectiveCallGraph.end())
   {
      // std::cout << caller << " calls:" << std::endl;
      for (const auto &call : it->second)
      {
         //  std::cout << "  - " << call.callee << " (line " << call.lineNumber << ")" << std::endl;
         if (call.lineNumber == lineNumber)
            targets.insert(call.callee);
      }
   }
   else
   {
      std::cout << "No calls found for " << caller << std::endl;
   }

   return targets;
}

int getCachedLineNumber(TR::Node *node, TR::Compilation *comp)
{
   if (nodeToLineNumber.find(node) == nodeToLineNumber.end())
   {
      nodeToLineNumber[node] = comp->getLineNumber(node);
   }

   return nodeToLineNumber[node];
}

TR::ResolvedMethodSymbol * getCachedResolvedMethodSymbol(TR::Compilation* comp,TR_OpaqueMethodBlock * method_block)
{
   if(methodBlock_to_ResolvedMethodSymbol.find(method_block) == methodBlock_to_ResolvedMethodSymbol.end())
   {
      methodBlock_to_ResolvedMethodSymbol[method_block] = comp->getOwningMethodSymbol(method_block);
   }

   return methodBlock_to_ResolvedMethodSymbol[method_block];
}