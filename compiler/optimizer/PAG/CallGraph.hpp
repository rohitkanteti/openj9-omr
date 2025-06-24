#ifndef CALLGRAPH_HPP
#define CALLGRAPH_HPP
#include <sstream>
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

    std::unordered_set<int> getCallers(int calleeMethodIndex) ;

    std::unordered_set<int> getCallSites(int callerMethodIndex, int calleeMethodIndex) ;

    std::vector<PAGNode*> getActualParams(int callerMethodIndex, int calleeMethodIndex, int bci) ;
};
#endif  