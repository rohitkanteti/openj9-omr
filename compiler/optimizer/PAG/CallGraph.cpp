
#include <unordered_set>
#pragma once
#include "PAG_Components.cpp" 

class CallGraph {
public:
    std::unordered_set<int> getCallers(int calleeMethodIndex) {
        return calleeToCallers[calleeMethodIndex];
    }

    std::unordered_set<int> getCallSites(int callerMethodIndex, int calleeMethodIndex) {
        return callerCalleeSites[callerMethodIndex][calleeMethodIndex];
    }

    std::vector<PAGNode*> getActualParams(int callerMethodIndex, int calleeMethodIndex, int bci) {
        auto key = std::make_tuple(callerMethodIndex, calleeMethodIndex, bci);
        return callsiteParams[key];
    }

    // Maps callee to set of callers
    std::unordered_map<int, std::unordered_set<int>> calleeToCallers;

    // Maps caller -> callee -> set of BCIs
    std::unordered_map<int, std::unordered_map<int, std::unordered_set<int>>> callerCalleeSites;

    // Maps (caller, callee, bci) to actual parameters
    std::unordered_map<std::tuple<int, int, int>, std::vector<PAGNode*>> callsiteParams;
};
