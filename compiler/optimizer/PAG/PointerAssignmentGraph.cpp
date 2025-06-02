#include "PAG_Components.cpp"
#include "il/ResolvedMethodSymbol.hpp"
#include "CallGraph.cpp"
#include "optimizer/PAG/regularPT.cpp"
#define METHOD_INDEX int
#define CALLSITE_BCI int
#define INVALID_BCI -9999
using namespace std;

extern std::string getMethodName(TR::ResolvedMethodSymbol *m);

class PointerAssignmentGraph
{
public:
    
    //******PAG****** 
    unordered_set<PAGNode*> PAG_nodes; 
    //******PAG****** 

    PAGNode* bottom_node;
    CallGraph CG;
    unordered_map<string,PAGNode*> nodes;
    unordered_set<PAGNode*> LeakyNodes;
    unordered_set<PAGNode*> static_field_nodes;
    std::unordered_map<int, PAGNode*> nodeIndexToNode;
    std::unordered_map<std::string, int> _methodIndices;

    std::unordered_set<std::string> staticFields; // class_name.field_name
    std::unordered_set<std::string> threadAccessibleFields;// class_name.field_name
    
    std::unordered_map<int,int> callsite_to_storeNodeIndex;
    unordered_map<int,vector<PAGNode*>> methods_to_formalNodes;
    unordered_map<int,vector<PAGNode*>> methods_to_allMethodNodes;
    std::unordered_set<PAGNode*> allEscpaingObjects;
    int number_of_escapingObjs = -8;

    unordered_map<int,PAGNode*> methods_to_returnNode;

    unordered_map<METHOD_INDEX,vector<PAGNode*>> methodIndex_to_formalNodes;
    unordered_map<METHOD_INDEX,vector<PAGNode*>> methodIndex_to_allMethodNodes;

    unordered_map<METHOD_INDEX,PAGNode*> methodIndex_to_returnNode;
    unordered_map<std::string,vector<PAGEdge*>> field_to_getFieldEdges;
    unordered_map<std::string,vector<PAGEdge*>> field_to_putFieldEdges;

    /*methods on PAG*/
     std::unordered_set<PAGNode*> getEscapingObjects(int method);
    unordered_set<PAGNode*> getLeakyNodes();
    PAGNode* getReturnNode(METHOD_INDEX method);


    vector<PAGNode*> getFormalParameterNodes(METHOD_INDEX method);
    vector<PAGNode*> getActualParameterNodes(METHOD_INDEX method,CALLSITE_BCI cs);

    void removeEdgeFrom(PAGNode* src,CALLSITE_BCI callsite);
    void removeAllEdgesFrom(PAGNode* node);
    void removeEdge(PAGNode* src,PAGNode* dest,CALLSITE_BCI callsite);
    void removeEdge(PAGNode* src,PAGNode* dest);
    void removeEdge(PAGEdge* edge);
   
    vector<PAGEdge*> getStoreEdges(); // for entire PAG
    vector<PAGEdge*> getStoreEdges(int method); // for the given method
    vector<PAGEdge*> getLoadEdges(); // for entire PAG
    vector<PAGEdge*> getLoadEdges(int method);// for the given method
    std::unordered_set<PAGNode*> points_to(PAGNode* src);
    vector<PAGEdge*> getIntraproceduralAssignEdges(int method);
    unordered_set<PAGEdge*> getAllocEdges(int method);
    std::unordered_set<PAGNode*> flowsTo(PAGNode* object);
    std::unordered_set<PAGNode*> FlowsToReg(PAGNode* object);

    void removeNodes(int method);

    void addEdge(PAGNode* src,PAGNode* dest,EdgeType type);
    void addEdge(PAGNode* src,PAGNode* dest,EdgeType type,std::string field);
    void addEdge(PAGNode* src, PAGNode* dest, EdgeType type, std::string field,int callsiteBCI);
    void addEdge(PAGNode* src, PAGNode* dest, EdgeType type,int callsiteBCI);

    unordered_set<std::string> get_fields(PAGNode* object);
    unordered_set<PAGNode*> get_field_target(PAGNode* object,std::string field);

    PointerAssignmentGraph();
    ~PointerAssignmentGraph();
    
    private:
     
    void deleteEdge(PAGEdge* edge);


};

PointerAssignmentGraph::PointerAssignmentGraph()
{
    bottom_node = new PAGNode(GLOBAL,-9,NULL,NULL,-9,-9);
    PAG_nodes.insert(bottom_node);
}


PAGNode* PointerAssignmentGraph::getReturnNode(int method)
{
    return (methodIndex_to_returnNode.find(method) != methodIndex_to_returnNode.end()) ? methodIndex_to_returnNode[method]: NULL;
}

vector<PAGNode*>  PointerAssignmentGraph::getFormalParameterNodes(METHOD_INDEX method)
{   
    static std::vector<PAGNode*> emptyVec;
    return (methodIndex_to_formalNodes.find(method) != methodIndex_to_formalNodes.end()) ? methodIndex_to_formalNodes[method]: emptyVec;
}

std::vector<PAGNode*> PointerAssignmentGraph::getActualParameterNodes(METHOD_INDEX method, CALLSITE_BCI callsite_bci) {
    std::vector<PAGNode*> actualParams;
    for (const auto& entry : CG.callsiteParams) {
        int caller = std::get<0>(entry.first);
        int bci = std::get<2>(entry.first);
        if (caller == method && bci == callsite_bci) {
            actualParams.insert(actualParams.end(), entry.second.begin(), entry.second.end());
        }
    }
    return actualParams;
}

void PointerAssignmentGraph::removeEdgeFrom(PAGNode* src, CALLSITE_BCI callsite) {
    auto it = src->outgoing.begin();
    while (it != src->outgoing.end()) {
        if ((*it)->callsiteBCI == callsite) {
            deleteEdge(*it);
            it = src->outgoing.erase(it);
        } else {
            ++it;
        }
    }
}
void PointerAssignmentGraph::removeAllEdgesFrom(PAGNode* node) {
    // Collect edges to delete first
    std::vector<PAGEdge*> edgesToDelete(node->outgoing.begin(), node->outgoing.end());
    
    for (PAGEdge* edge : edgesToDelete) {
        deleteEdge(edge);
    }
    node->outgoing.clear();
}



void PointerAssignmentGraph::removeEdge(PAGNode* src, PAGNode* dest, CALLSITE_BCI callsite) {
    auto it = src->outgoing.begin();
    while (it != src->outgoing.end()) {
        if ((*it)->dest == dest && (*it)->callsiteBCI == callsite) {
            deleteEdge(*it);
            it = src->outgoing.erase(it);
        } else {
            ++it;
        }
    }
}

void PointerAssignmentGraph::removeEdge(PAGNode* src, PAGNode* dest) {
    auto it = src->outgoing.begin();
    while (it != src->outgoing.end()) {
        if ((*it)->dest == dest) {
            it = src->outgoing.erase(it); 
            delete *it; 
        } else {
            ++it;
        }
    }
}


void PointerAssignmentGraph::removeEdge(PAGEdge* edge) {
    edge->src->outgoing.erase(edge);
    edge->dest->incoming.erase(edge);
    delete edge;
}


std::vector<PAGEdge*> PointerAssignmentGraph::getStoreEdges() {
    std::vector<PAGEdge*> result;
    for (auto node : PAG_nodes) {
        for (auto edge : node->outgoing) {
            if (edge->type == EdgeType::PUTFIELD) {
                result.push_back(edge);
            }
        }
    }
    return result;
}

std::vector<PAGEdge*> PointerAssignmentGraph::getStoreEdges(int method) {
    std::vector<PAGEdge*> result;
    for (auto node : methodIndex_to_allMethodNodes[method]) {
        for (auto edge : node->outgoing) {
            if (edge->type == EdgeType::PUTFIELD) {
                result.push_back(edge);
            }
        }
    }
    return result;
}

std::vector<PAGEdge*> PointerAssignmentGraph::getIntraproceduralAssignEdges(int method) {
    std::vector<PAGEdge*> result;
    for (auto node : methodIndex_to_allMethodNodes[method]) {
        for (auto edge : node->outgoing) {
            if (edge->type == EdgeType::ASSIGN && 
                edge->dest->methodIndex == method) {
                result.push_back(edge);
            }
        }
    }
    return result;
}


void PointerAssignmentGraph::removeNodes(int method) {
    auto& nodes = methodIndex_to_allMethodNodes[method];
    for (auto node : nodes) {
       
        removeAllEdgesFrom(node);
 
        PAG_nodes.erase(node);
        
       
        for (auto it = nodeIndexToNode.begin(); it != nodeIndexToNode.end(); ++it) {
            if (it->second == node) {
                nodeIndexToNode.erase(it);
                break;
            }
        }
        delete node;
    }
    
 
    methodIndex_to_allMethodNodes.erase(method);
    methodIndex_to_formalNodes.erase(method);
    methodIndex_to_returnNode.erase(method);
}


 
std::unordered_set<std::string> PointerAssignmentGraph::get_fields(PAGNode* object) {
    std::unordered_set<std::string> fields;
    for (auto edge : object->outgoing) {
        if (edge->type == EdgeType::PUTFIELD && !edge->field.empty()) {
            fields.insert(edge->field);
        }
    }
    return fields;
}

std::unordered_set<PAGNode*> PointerAssignmentGraph::get_field_target(PAGNode* object, std::string field) {
    std::unordered_set<PAGNode*> targets;
    for (auto edge : object->outgoing) {
        if (edge->type == EdgeType::PUTFIELD && edge->field == field) {
            targets.insert(edge->dest);
        }
    }
    return targets;
}

// Destructor
PointerAssignmentGraph::~PointerAssignmentGraph() {
    for (auto node : PAG_nodes) {
        for (auto edge : node->outgoing) {
            delete edge;
        }
        node->outgoing.clear();
        node->incoming.clear();
    }
    
    for (auto node : PAG_nodes) {
        delete node;
    }
    PAG_nodes.clear();
    nodeIndexToNode.clear();
}

void PointerAssignmentGraph::deleteEdge(PAGEdge* edge) {
    edge->src->outgoing.erase(edge);
    edge->dest->incoming.erase(edge);
    delete edge;
}


void PointerAssignmentGraph::addEdge(PAGNode* src, PAGNode* dest, EdgeType type) {
    addEdge(src, dest, type, "<N/A>", INVALID_BCI);
}

void PointerAssignmentGraph::addEdge(PAGNode* src, PAGNode* dest, EdgeType type, std::string field) {
    addEdge(src, dest, type, field, INVALID_BCI);
}

void PointerAssignmentGraph::addEdge(PAGNode* src, PAGNode* dest, EdgeType type, int callsiteBCI) {
    addEdge(src, dest, type, "<N/A>", callsiteBCI);
}

void PointerAssignmentGraph::addEdge(PAGNode* src, PAGNode* dest, EdgeType type, std::string field, int callsiteBCI) {
    auto edge = new PAGEdge(src, dest, type, field, callsiteBCI);
    src->outgoing.insert(edge);
    dest->incoming.insert(edge);

    EdgeType reverseType = static_cast<EdgeType>(type + 5);
    auto edge_bar = new PAGEdge(dest, src, reverseType, field, callsiteBCI);
    dest->outgoing.insert(edge_bar);
    src->incoming.insert(edge_bar);
}


std::unordered_set<PAGNode*> PointerAssignmentGraph::flowsTo(PAGNode* object)
{
    return FlowsToReg(object);
}


// using `flowsToReg -> new ( assign | match )*`
std::unordered_set<PAGNode*> PointerAssignmentGraph::FlowsToReg(PAGNode* object) {
    std::unordered_set<PAGNode*> result;
    std::unordered_set<PAGNode*> visited;
    std::queue<PAGNode*> worklist;
    
    worklist.push(object);
    visited.insert(object);
    
    while (!worklist.empty()) {
        PAGNode* current = worklist.front();
        worklist.pop();
        
        for (PAGEdge* edge : current->outgoing) {
            switch (edge->type) {
                case EdgeType::NEW:
                    
                    result.insert(edge->dest);
                    if (visited.find(edge->dest) == visited.end()) {
                        visited.insert(edge->dest);
                        worklist.push(edge->dest);
                    }
                    break;
                    
                case EdgeType::ASSIGN:
                    
                    if (visited.find(edge->dest) == visited.end()) {
                        visited.insert(edge->dest);
                        worklist.push(edge->dest);
                    }
                    break;
                    
                case EdgeType::MATCH:
                    
                    if (visited.find(edge->dest) == visited.end()) {
                        visited.insert(edge->dest);
                        worklist.push(edge->dest);
                    }
                    break;
                    
                default:
                   
                    break;
            }
        }
    }
    
    return result;
}

 std::unordered_set<PAGNode*> PointerAssignmentGraph::getEscapingObjects(int method)
{
     std::unordered_set<PAGNode*> escaping;
    if(allEscpaingObjects.size()>0 )
    {
        for(auto * obj:allEscpaingObjects)
        {
            if(obj->methodIndex==method) escaping.insert(obj);
        }
    }
    else if(number_of_escapingObjs >= 0)
    {
        for(auto* leaky : LeakyNodes)
        {
           std::unordered_set<PAGNode*> esc = points_to(leaky);
           number_of_escapingObjs += esc.size();
           for(auto * obj:esc)
            {
                if(obj->methodIndex==method) escaping.insert(obj);
            }
            allEscpaingObjects.insert(esc.begin(),esc.end());
        }
    }

    return escaping;
}

std::unordered_set<PAGNode*> PointerAssignmentGraph::points_to(PAGNode* src)
{
    return regularPT(src);
}
std::unordered_set<PAGEdge*> PointerAssignmentGraph::getAllocEdges(int method) {
    std::unordered_set<PAGEdge*> allocEdges;
    auto it = methodIndex_to_allMethodNodes.find(method);
    if (it != methodIndex_to_allMethodNodes.end()) {
        for (PAGNode* node : it->second) {
            for (PAGEdge* edge : node->outgoing) {
                if (edge->type == EdgeType::NEW) {
                    allocEdges.insert(edge);
                }
            }
        }
    }
    return allocEdges;
}
