#include "LoadPAG.hpp"
// #include <zlib.h>
// #include "../../../../openj9/runtime/include/zlib.h"
// Bypass OpenJ9's internal zlib header to use standard OS zlib
extern "C" {
    typedef void* gzFile;
    gzFile gzopen(const char *path, const char *mode);
    int gzclose(gzFile file);
    int gzprintf(gzFile file, const char *format, ...);
    char *gzgets(gzFile file, char *buf, int len);
}
#include <algorithm>
static std::unordered_map<int, std::string> classIndexToStr;
static std::unordered_map<int, std::string> methodIndexToStr;
static void loadIndices() {
    if (!classIndexToStr.empty()) return;
    
    gzFile cfile = gzopen("ci.txt.gz", "r");
    if (!cfile) cfile = gzopen("ci.txt", "r");
    if (cfile) {
        char buffer[1024];
        int idx = 1;
        while (gzgets(cfile, buffer, sizeof(buffer)) != NULL) {
            std::string line(buffer);
            line.erase(std::remove(line.begin(), line.end(), '\n'), line.end());
            line.erase(std::remove(line.begin(), line.end(), '\r'), line.end());
            if (!line.empty()) classIndexToStr[idx++] = line;
        }
        gzclose(cfile);
    }

    gzFile mfile = gzopen("mi.txt.gz", "r");
    if (!mfile) mfile = gzopen("mi.txt", "r");
    if (mfile) {
        char buffer[4096];
        int idx = 1;
        while (gzgets(mfile, buffer, sizeof(buffer)) != NULL) {
            std::string line(buffer);
            line.erase(std::remove(line.begin(), line.end(), '\n'), line.end());
            line.erase(std::remove(line.begin(), line.end(), '\r'), line.end());
            if (!line.empty()) methodIndexToStr[idx++] = line;
        }
        gzclose(mfile);
    }
}
static bool gzGetLine(gzFile file, std::string &line)
{
    line.clear();
    char buffer[4096];
    bool hasData = false;

    while (true)
    {
        if (gzgets(file, buffer, sizeof(buffer)) == NULL)
        {
            return hasData; 
        }
        hasData = true;
        line.append(buffer);
        
        if (!line.empty() && line.back() == '\n')
        {
            line.pop_back(); 
            if (!line.empty() && line.back() == '\r') 
                line.pop_back(); 
            return true;
        }
    }
}
LoadPAG::LoadPAG(const std::string &nodeFile, const std::string &edgeFile, const std::string &methodNodeMappingFile, const std::string &callgraphfile, std::string &threadfieldFile, std::string &staticfieldFile)
    : nodeFile(nodeFile), edgeFile(edgeFile), methodNodeMappingFile(methodNodeMappingFile), callgraphfile(callgraphfile), threadfieldFile(threadfieldFile), staticfieldFile(staticfieldFile) {}

PointerAssignmentGraph *LoadPAG::getPAG()
{
    if (!loaded)
    {
        pag->_methodIndices = readMethodIndices();
        loadNodes(nodeFile);
        loadEdges(edgeFile);
        loadMethodNodeMappings(methodNodeMappingFile);
        // addMatchEdges();
        loadCG(callgraphfile);
        getImportantFieldNames(threadfieldFile, 0);
        getImportantFieldNames(staticfieldFile, 1);
        loaded = true;
    }

    return pag;
}

NodeType LoadPAG::parseNodeType(int typeVal)
{
    switch (typeVal)
    {
    case 0:
        return NodeType::VARIABLE;
    case 1:
        return NodeType::OBJECT;
    case 2:
        return NodeType::RETURN;
    case 3:
        return NodeType::NULL_OBJ;
    case 4:
        return NodeType::STATIC;
    case 5:
        return NodeType::GLOBAL;
    default:
        return NodeType::NONTYPE;
    }
}

EdgeType LoadPAG::parseEdgeType(int typeVal)
{
    switch (typeVal)
    {
    case 0:
        return EdgeType::ASSIGN;
    case 1:
        return EdgeType::NEW;
    case 2:
        return EdgeType::PUTFIELD;
    case 3:
        return EdgeType::GETFIELD;
    case 4:
        return EdgeType::MATCH;
    case 5:
        return EdgeType::ASSIGN_BAR;
    case 6:
        return EdgeType::NEW_BAR;
    case 7:
        return EdgeType::PUTFIELD_BAR;
    case 8:
        return EdgeType::GETFIELD_BAR;
    case 9:
        return EdgeType::MATCH_BAR;
    default:
        throw std::runtime_error("Unknown EdgeType: " + std::to_string(typeVal));
    }
}

void LoadPAG::loadNodes(const std::string &filename)
{
    loadIndices(); 
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file) file = gzopen((filename ).c_str(), "r");
    if (!file) return;

    std::string line;
    int index = 1;

    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        std::stringstream ss(line);
        int bci, methodIndex, typeInt, name, isLeaky;

        if (!(ss >> bci >> methodIndex >> typeInt >> name >> isLeaky)) continue;

        NodeType type = parseNodeType(typeInt);
        std::unordered_set<std::string> pointee_names;
        std::string token;

        while (ss >> token)
        {
            bool isDigit = true;
            for(char c : token) if(!isdigit(c)) { isDigit = false; break; }

            if (isDigit) pointee_names.insert(classIndexToStr[std::stoi(token)]);
            else pointee_names.insert(token);
        }

        if (!(bci == -9 && type == NodeType::GLOBAL && name == -9))
        {
            PAGNode *node = new PAGNode(type, name, nullptr, nullptr, bci, methodIndex);
            pag->PAG_nodes.insert(node);
            pag->nodeIndexToNode[index++] = node;
            node->pointee_class_names.insert(pointee_names.begin(), pointee_names.end());
            if (isLeaky == 1) pag->LeakyNodes.insert(node);
        }
        else
        {
            pag->nodeIndexToNode[index++] = pag->bottom_node;
        }
    }
    gzclose(file);
}

void LoadPAG::loadEdges(const std::string &filename)
{
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file) file = gzopen((filename ).c_str(), "r");
    if (!file) return;

    std::string line;

    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        std::stringstream ss(line);
        int srcIndex;
        if (!(ss >> srcIndex)) continue;

        PAGNode *src = pag->nodeIndexToNode[srcIndex];
        if (!src) continue;

        int destIndex, edgeTypeInt, callsiteBCI;
        std::string fieldName;

        // Automatically extract chunks of 4 variables at a time
        while (ss >> destIndex >> edgeTypeInt >> fieldName >> callsiteBCI)
        {
            if (fieldName == "") fieldName = "";

            PAGNode *dest = pag->nodeIndexToNode[destIndex];
            if (!dest) continue;

            EdgeType eType = parseEdgeType(edgeTypeInt);
            pag->addEdge(src, dest, eType, fieldName, callsiteBCI);
        }
    }
    gzclose(file);
}
void LoadPAG::loadMethodNodeMappings(const std::string &filename)
{
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file) file = gzopen((filename ).c_str(), "r");
    if (!file) return;

    std::string line;

    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        std::stringstream ss(line);
        int methodIndex;
        if (!(ss >> methodIndex)) continue;

        int nodeIndex, isParam;
        
        // Extract chunks of 2 variables at a time
        while (ss >> nodeIndex >> isParam)
        {
            PAGNode *node = pag->nodeIndexToNode[nodeIndex];
            if (!node) continue;

            pag->methodIndex_to_allMethodNodes[methodIndex].push_back(node);

            if (isParam == 1) pag->methodIndex_to_formalNodes[methodIndex].push_back(node);
            if (node->type == NodeType::RETURN) pag->methodIndex_to_returnNode[methodIndex] = node;
        }
    }
    gzclose(file);
}

void LoadPAG::addMatchEdges()
{
    std::unordered_map<std::string, std::vector<PAGEdge *>> puts, gets;

    for (auto &entry : pag->nodeIndexToNode)
    {
        PAGNode *n = entry.second;
        std::vector<PAGEdge *> edges(n->outgoing.begin(), n->outgoing.end());
        for (PAGEdge *e : edges)
        {
            if (e->type == EdgeType::PUTFIELD)
                puts[e->field].push_back(e);
            else if (e->type == EdgeType::GETFIELD)
                gets[e->field].push_back(e);
        }
    }

    for (auto &kv : puts)
    {
        const std::string &field = kv.first;
        auto getIt = gets.find(field);
        if (getIt == gets.end())
            continue;

        for (PAGEdge *pe : kv.second)
        {
            for (PAGEdge *ge : getIt->second)
            {
                pag->addEdge(pe->src, ge->dest, EdgeType::MATCH, field); // will also add MATCH_BAR edge
            }
        }
    }
}

void LoadPAG::loadCG(const std::string &filename)
{
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file) file = gzopen((filename ).c_str(), "r");
    if (!file) return;

    std::string line;

    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        std::stringstream ss(line);
        int callsiteBCI, receiverIndex;
        
        if (!(ss >> callsiteBCI >> receiverIndex)) continue;

        if (receiverIndex != -56765) // Using the RETURN_NODE_NAME logic
            pag->callsite_to_storeNodeIndex[callsiteBCI] = receiverIndex;

        int targetMethodIndex, numParams;

        // Extract the target and how many parameters it has
        while (ss >> targetMethodIndex >> numParams)
        {
            std::vector<PAGNode *> actualParams;
            
            // Loop exactly numParams times to get all parameters
            for (int i = 0; i < numParams; ++i)
            {
                int nodeIndex;
                if (ss >> nodeIndex) {
                    auto nodeIt = pag->nodeIndexToNode.find(nodeIndex);
                    if (nodeIt != pag->nodeIndexToNode.end()) {
                        actualParams.push_back(nodeIt->second);
                    }
                }
            }

            if (!actualParams.empty())
            {
                int callerMethodIndex = actualParams[0]->methodIndex;

                pag->CG.calleeToCallers[targetMethodIndex].insert(callerMethodIndex);
                pag->CG.callerCalleeSites[callerMethodIndex][targetMethodIndex].insert(callsiteBCI);

                std::ostringstream oss;
                oss << callerMethodIndex << ' ' << targetMethodIndex << ' ' << callsiteBCI;
                pag->CG.callsiteParams[oss.str()] = actualParams;
            }
        }
    }
    gzclose(file);
}
void LoadPAG::getImportantFieldNames(const std::string &threadfieldFile, int static_or_thread)
{
   
    std::ifstream file(threadfieldFile);

    if (!file.is_open())
    {
        std::cerr << "Error: Could not open file " << threadfieldFile << std::endl;
        return;
    }

    std::string line;
    while (std::getline(file, line))
    {
        if (line.empty()) continue;
        std::string fieldName = line;

        if (isdigit(line[0])) {
            auto dotPos = line.find('.');
            if (dotPos != std::string::npos) {
                int cIdx = std::stoi(line.substr(0, dotPos));
                fieldName = classIndexToStr[cIdx] + "." + line.substr(dotPos + 1);
            }
        }

        if (static_or_thread == 0)
            pag->threadAccessibleFields.insert(fieldName);
        else
            pag->staticFields.insert(fieldName);
    }

    file.close();
}