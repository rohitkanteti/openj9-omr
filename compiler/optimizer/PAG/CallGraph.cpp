#include <sstream>
#include <unordered_set>
#include "PAG_Components.hpp"
#include "CallGraph.hpp"

std::unordered_set<int> CallGraph::getCallers(int calleeMethodIndex)
{
    return calleeToCallers[calleeMethodIndex];
}

std::unordered_set<int> CallGraph::getCallSites(int callerMethodIndex, int calleeMethodIndex)
{
    return callerCalleeSites[callerMethodIndex][calleeMethodIndex];
}

std::vector<PAGNode *> CallGraph::getActualParams(int callerMethodIndex, int calleeMethodIndex, int bci)
{
    std::ostringstream oss;
    oss << callerMethodIndex << ' ' << calleeMethodIndex << ' ' << bci;
    std::string key = oss.str();
    return callsiteParams[key];
}