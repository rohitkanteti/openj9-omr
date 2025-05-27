#ifndef PAG_EDGE_NODE_HPP
#define PAG_EDGE_NODE_HPP

#include <iostream>
#include <unordered_set>
#include "env/jittypes.h"
#include "../il/Node.hpp"
#include "enums.h"
#include "../il/ResolvedMethodSymbol.hpp"

class PAGNode;
class PAGEdge;

 
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

    PAGNode();
    PAGNode(NodeType type,std::string c,int mi);
    PAGNode(NodeType type, int name, TR_OpaqueClassBlock* clazz_ptr, TR_OpaqueMethodBlock* caller, int bci, int mi);
    void printNode() {
  
        std::cout << "[ Nodetype = " << type ;
        std::cout << ", caller = " << caller;
        std::cout << ", name = " << name ;
        std::cout << ", bci = " << bci << " ]" ;
        std::cout << std::endl;
    }

    friend std::ostream& operator<<(std::ostream& os, const PAGNode& obj);
};

PAGEdge::PAGEdge() : src(nullptr), dest(nullptr), type(ASSIGN), field("<N/A>"),callsiteBCI(-9999) {}

PAGEdge::PAGEdge(PAGNode* s, PAGNode* d, EdgeType t)
    : src(s), dest(d), type(t), field("<N/A>"),callsiteBCI(-9999) {}

PAGEdge::PAGEdge(PAGNode* s, PAGNode* d, EdgeType t,int callsiteBCI)
    : src(s), dest(d), type(t), field("<N/A>") ,callsiteBCI(callsiteBCI) {}

    PAGEdge::PAGEdge(PAGNode* s, PAGNode* d, EdgeType t,std::string field_name,int callsiteBCI)
    : src(s), dest(d), type(t), field(field_name) ,callsiteBCI(callsiteBCI) {}

PAGEdge::PAGEdge(PAGNode* s, PAGNode* d, EdgeType t,std::string field_name)
    : src(s), dest(d), type(t), field(field_name),callsiteBCI(-9999) {}

std::ostream& operator<<(std::ostream& os, const PAGEdge& obj) {
    os << " PAGEdge: edge_type=" << obj.type 
        << " field = " << obj.field 
       << " src_bci= " << obj.src->bci 
       << " src_name= " <<  obj.src->name
       << " src_type="<< obj.src->type
       << " src_caller="<< obj.src->caller
       << " dest_bci: " << obj.dest->bci
       << " dest_name= " <<  obj.dest->name
       << " dest_type="<< obj.dest->type
       << " dest_caller="<< obj.dest->caller
       << " callsite: "<< obj.callsiteBCI;
    return os;
}

PAGNode::PAGNode() : type(NONTYPE), name(0), caller(0), bci(0), clazz_ptr(nullptr) {}

PAGNode::PAGNode(NodeType t, int n, TR_OpaqueClassBlock* clazz_p, TR_OpaqueMethodBlock* m, int b,int mi)
    : type(t), name(n), clazz_ptr(clazz_p), caller(m), bci(b),methodIndex(mi) {}

PAGNode::PAGNode(NodeType t,std::string c,int mi): type(t),class_name(c),methodIndex(mi) {}

std::ostream& operator<<(std::ostream& os, const PAGNode& obj) {
    os << "{ \n PAGNode: bci=" << obj.bci 
       << " caller= " << obj.caller 
       << " nodeType= "<< obj.type
       << " name= "<< obj.name
       << "\n Incoming edges follows:" << std::endl;
    // if(obj.incoming.size() > 0)
    // {   
        // os<<"obj.incoming size="<<obj.incoming.size()<<std::endl;
        for(auto* edge : obj.incoming) 
        {   
            // os<<"here 2"<<std::endl;
            if (edge) 
            {   
                os << *edge << std::endl;
            } 
            else 
            {
                os << "[Null Edge]" << std::endl;  
            }
        }
    // }
    os << " Outgoing edges follows:" << std::endl;
    // os<<"obj.outgoing size="<<obj.outgoing.size()<<std::endl;

    // if(obj.outgoing.size() > 0)
    // {
        for(auto* edge : obj.outgoing) 
        {   

            if (edge) 
            {   
                os << *edge << std::endl;
            } 
            else 
            {
                os << "[Null Edge]" << std::endl;  
            }
        }
    // }
    os << "}" << std::endl;
    return os;
}

#endif  
