#ifndef PAG_HPP
#define PAG_HPP

#include "PAG_Components.hpp"
#include "il/ResolvedMethodSymbol.hpp"
#include "CallGraph.hpp"
#include "optimizer/PAG/regularPT.hpp"
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
    void removeEdges(int method);
   
    vector<PAGEdge*> getStoreEdges(); // for entire PAG
    vector<PAGEdge*> getStoreEdges(int method); // for the given method
    vector<PAGEdge*> getLoadEdges(); // for entire PAG
    vector<PAGEdge*> getLoadEdges(int method);// for the given method
    vector<PAGEdge*> getMatchEdgesEndingAt(PAGNode*);  
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
#endif