
#ifndef PAG_COMPONENTS_HPP
#define PAG_COMPONENTS_HPP

#include <iostream>
#include <unordered_set>
#include "env/jittypes.h"
#include "../il/Node.hpp"
#include "enums.h"
#include "../il/ResolvedMethodSymbol.hpp"

class PAGNode;
// class PAGEdge;

 
class PAGEdge {
public:
    PAGNode* src;
    PAGNode* dest;
    EdgeType type;
    std::string field;
    int callsiteBCI;

    PAGEdge();
    PAGEdge(PAGNode* src, PAGNode* dest, EdgeType type);
    PAGEdge(PAGNode* s, PAGNode* d, EdgeType t,int callsiteBCI);
    PAGEdge(PAGNode* src, PAGNode* dest, EdgeType type, std::string field_name);
    PAGEdge(PAGNode* s, PAGNode* d, EdgeType t,std::string field_name,int callsiteBCI);

    friend std::ostream& operator<<(std::ostream& os, const PAGEdge& obj);
};

 
class PAGNode {
public:
    NodeType type;
    int name;
    TR_OpaqueMethodBlock* caller;
    int methodIndex;
    int bci;
    std::unordered_set<PAGEdge*> incoming;
    std::unordered_set<PAGEdge*> outgoing;
    TR_OpaqueClassBlock* clazz_ptr;
    std::string class_name;
    std::unordered_set<std::string> pointee_class_names;
    // class_name.varname , For a putfield stmt like `x.f = z` if the class in which f is present is A then store "A.f"
    std::unordered_set<std::string> variableNames;

    int formal_param_index = -924305;

    PAGNode();
    PAGNode(NodeType type,std::string c,int mi);
    PAGNode(NodeType type, int name, TR_OpaqueClassBlock* clazz_ptr, TR_OpaqueMethodBlock* caller, int bci, int mi);
    void printNode();

    friend std::ostream& operator<<(std::ostream& os, const PAGNode& obj);
};
#endif