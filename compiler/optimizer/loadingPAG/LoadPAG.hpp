#ifndef LOADPAG_HPP
#define LOADPAG_HPP
#include <unordered_set>
#include <unordered_map>
#include <fstream>
#include <sstream>
#include <iostream>

#ifndef PAG_POINTER_ASSIGNMENT_GRAPH_CPP
#define PAG_POINTER_ASSIGNMENT_GRAPH_CPP
#pragma once
#include "../PAG/PointerAssignmentGraph.hpp"
#endif

#ifndef PAG_COMPONENTS_CPP
#define PAG_COMPONENTS_CPP
#include "../PAG/PAG_Components.hpp"
#endif
extern std::unordered_map<std::string, int> readMethodIndices();
class LoadPAG {
    public:
        LoadPAG(const std::string& nodeFile, const std::string& edgeFile,const std::string& methodNodeMappingFile,const std::string& callgraphfile,std::string& threadfieldFile,std::string& staticfieldFile);
    
        PointerAssignmentGraph* getPAG();  
    
    private:
        std::string nodeFile;
        std::string edgeFile;
        std::string methodNodeMappingFile;
        std::string callgraphfile;
        std::string& threadfieldFile;
        std::string& staticfieldFile;
        bool loaded = false;
    
        PointerAssignmentGraph* pag = new PointerAssignmentGraph();
        std::unordered_map<int, PAGNode*> nodeIndexToNode;
    
        void loadNodes(const std::string& filename);
        void loadEdges(const std::string& filename);
        void loadMethodNodeMappings(const std::string& filename);
        void addMatchEdges(); 
        void loadCG(const std::string& filename);
        void loadSyncSites(const std::string& filename);
        void loadInlinedMethods(const std::string& filename);
        void getImportantFieldNames(const std::string& file,int static_or_thread);
    
        NodeType parseNodeType(int typeVal);
        EdgeType parseEdgeType(int typeVal);
    };
#endif