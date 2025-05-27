#pragma once 
#include <unordered_map>
#include <unordered_set>
class MethodSet
{
public:
   std::unordered_map<int, std::unordered_set<int>> stmtMap;
   // DisjointSet ds;
};