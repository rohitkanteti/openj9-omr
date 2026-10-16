#ifndef CALLGRAPH_HPP
#define CALLGRAPH_HPP
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#pragma once
#include "PAG_Components.hpp" 

class CallGraph {
public:
    
    // Maps callee to set of callers
    std::unordered_map<int, std::unordered_set<int>> calleeToCallers;

    // Maps caller -> callee -> set of BCIs
    std::unordered_map<int, std::unordered_map<int, std::unordered_set<int>>> callerCalleeSites;

    // Maps (caller, callee, bci) to actual parameters
    std::unordered_map<std::string, std::vector<PAGNode*>> callsiteParams;

    // SmartAOT: receiver ('this') nodes of instance call sites, keyed "caller callee bci" (callee -1 when no target
    // was resolved). A call site has an entry here iff it is an instance call with a resolved receiver.
    std::unordered_map<std::string, std::vector<PAGNode*>> callsiteReceivers;

    // Instance call sites ("caller callee bci") whose receiver could not be resolved when loading the PAG (no
    // receiver node, or a receiver node that is not part of the dumped PAG); their receiver types are unknown
    std::unordered_set<std::string> unresolvedReceiverCallsites;
    
    // Maps "methodIndex_bci" to locked PAGNodes for synchronization sites (SyncSites)
    std::unordered_map<std::string, std::vector<PAGNode*>> syncSites;

    // Maps a caller method index to the set of method indices that were inlined into it
    std::unordered_map<int, std::unordered_set<int>> inlinedMethods;

    // Maps a caller method index to the set of method indices that were peeked into (not inlined) while compiling it
    std::unordered_map<int, std::unordered_set<int>> peekedMethods;

    // Maps a caller signature to the signatures inlined into it (kept by name so that the structural
    // check does not depend on the inlined method having a PAG method index)
    std::unordered_map<std::string, std::unordered_set<std::string>> inlinedMethodNames;

    // Maps a caller signature to the signatures of all its dependencies (inlined and peeked)
    std::unordered_map<std::string, std::unordered_set<std::string>> dependencyNames;

    std::unordered_set<int> getCallers(int calleeMethodIndex) ;

    std::unordered_set<int> getCallSites(int callerMethodIndex, int calleeMethodIndex) ;

    std::vector<PAGNode*> getActualParams(int callerMethodIndex, int calleeMethodIndex, int bci) ;
};

#endif  