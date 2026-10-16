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
    
    // SmartAOT: the class indices in the dumped PAG files are the line numbers of smartaot_class_index.txt, which
    // only the cold-run JIT writes (ci.txt is also written by the cold-run agent and does not match them).
    gzFile cfile = gzopen("smartaot_class_index.txt", "r");
    if (!cfile)
        throw std::runtime_error("smartaot_class_index.txt not found (PAG files from an older cold run?)");
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
        loadSyncSites("syncSites.txt.gz");
        loadStaticNodes("staticNodes.txt.gz");
        loadDependencies("dependencies.txt.gz");
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

        auto srcIt = pag->nodeIndexToNode.find(srcIndex);
        if (srcIt == pag->nodeIndexToNode.end() || !srcIt->second) continue;
        PAGNode *src = srcIt->second;

        int destIndex, edgeTypeInt, callsiteBCI;
        std::string fieldName;

        // Automatically extract chunks of 4 variables at a time
        while (ss >> destIndex >> edgeTypeInt >> fieldName >> callsiteBCI)
        {
            if (fieldName == "") fieldName = "";

            auto destIt = pag->nodeIndexToNode.find(destIndex);
            if (destIt == pag->nodeIndexToNode.end() || !destIt->second) continue;
            PAGNode *dest = destIt->second;

            EdgeType eType = parseEdgeType(edgeTypeInt);
            // The dump contains both halves of every edge; addEdge() recreates the *_BAR half itself.
            if (eType >= EdgeType::ASSIGN_BAR)
                continue;
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
            auto nodeIt = pag->nodeIndexToNode.find(nodeIndex);
            if (nodeIt == pag->nodeIndexToNode.end() || !nodeIt->second) continue;
            PAGNode *node = nodeIt->second;

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

// Format (v2, first line "#v2"), one call site per line:
//   callerIndex bci isInstance returnNodeIndex numTargets t1 .. numReceivers r1 .. numArgs a1 ..
// The caller is written explicitly and the receiver is kept apart from the other parameters. (The old format keyed
// call sites by bytecode index alone, merging those of different methods, and stored the receiver and arguments in
// one pointer-ordered set, so the node read back as the receiver was arbitrary.)
void LoadPAG::loadCG(const std::string &filename)
{
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file) return;

    std::string line;
    bool formatChecked = false;

    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        if (!formatChecked)
        {
            formatChecked = true;
            if (line == "#v2")
                continue;
            gzclose(file);
            throw std::runtime_error("callgraph.txt.gz is not in the v2 format (written by an older cold run)");
        }

        std::stringstream ss(line);
        int callerMethodIndex, callsiteBCI, isInstance, returnNodeIndex;
        size_t numTargets, numReceivers, numArgs;
        if (!(ss >> callerMethodIndex >> callsiteBCI >> isInstance >> returnNodeIndex >> numTargets))
            throw std::runtime_error("malformed call site line in callgraph.txt.gz: " + line);

        std::vector<int> targets;
        for (size_t i = 0; i < numTargets; i++)
        {
            int t;
            if (!(ss >> t)) throw std::runtime_error("malformed call site line in callgraph.txt.gz: " + line);
            targets.push_back(t);
        }

        auto readNodes = [&](size_t &count, std::vector<PAGNode *> &nodes, bool &allResolved)
        {
            allResolved = true;
            if (!(ss >> count)) throw std::runtime_error("malformed call site line in callgraph.txt.gz: " + line);
            for (size_t i = 0; i < count; i++)
            {
                int nodeIndex;
                if (!(ss >> nodeIndex)) throw std::runtime_error("malformed call site line in callgraph.txt.gz: " + line);
                auto nodeIt = pag->nodeIndexToNode.find(nodeIndex);
                if (nodeIt != pag->nodeIndexToNode.end() && nodeIt->second)
                    nodes.push_back(nodeIt->second);
                else
                    allResolved = false;
            }
        };

        std::vector<PAGNode *> receivers, args;
        bool receiversResolved, argsResolved;
        readNodes(numReceivers, receivers, receiversResolved);
        readNodes(numArgs, args, argsResolved);

        if (targets.empty())
            targets.push_back(-1);

        std::vector<PAGNode *> actualParams(receivers);
        actualParams.insert(actualParams.end(), args.begin(), args.end());

        for (int targetMethodIndex : targets)
        {
            std::ostringstream oss;
            oss << callerMethodIndex << ' ' << targetMethodIndex << ' ' << callsiteBCI;
            std::string key = oss.str();

            if (targetMethodIndex >= 0)
            {
                pag->CG.calleeToCallers[targetMethodIndex].insert(callerMethodIndex);
                pag->CG.callerCalleeSites[callerMethodIndex][targetMethodIndex].insert(callsiteBCI);
            }
            pag->CG.callsiteParams[key] = actualParams;

            if (isInstance)
            {
                if (receivers.empty() || !receiversResolved)
                    pag->CG.unresolvedReceiverCallsites.insert(key);
                else
                    pag->CG.callsiteReceivers[key] = receivers;
            }
        }
    }
    gzclose(file);
}
// Format: <staticNodeIndex> <fieldType>   (fieldType is the key the analysis uses for the shared static-field node)
void LoadPAG::loadStaticNodes(const std::string &filename)
{
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file)
        return;

    std::string line;
    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        std::stringstream ss(line);
        int nodeIndex;
        std::string fieldType;
        if (!(ss >> nodeIndex >> fieldType)) continue;

        auto nodeIt = pag->nodeIndexToNode.find(nodeIndex);
        if (nodeIt == pag->nodeIndexToNode.end() || !nodeIt->second) continue;
        nodeIt->second->class_name = fieldType;
        pag->staticTypeToNode[fieldType] = nodeIt->second;
    }
    gzclose(file);
}

// Format: <methodIndex>_<bci> <lockedVariableNodeIndex>   (bci -1 = synchronized method entry)
void LoadPAG::loadSyncSites(const std::string &filename)
{
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file)
        return;

    std::string line;
    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        std::stringstream ss(line);
        std::string syncSiteKey;
        int nodeIndex;
        if (!(ss >> syncSiteKey >> nodeIndex)) continue;

        auto nodeIt = pag->nodeIndexToNode.find(nodeIndex);
        if (nodeIt == pag->nodeIndexToNode.end() || !nodeIt->second) continue;
        pag->CG.syncSites[syncSiteKey].push_back(nodeIt->second);
    }
    gzclose(file);
}

// Format: callerSig<TAB>K depSig<TAB>K depSig ...   (K = I for inlined, P for peeked)
// Signatures are resolved to method indices here; methods unknown to the PAG are skipped.
void LoadPAG::loadDependencies(const std::string &filename)
{
    gzFile file = gzopen(filename.c_str(), "r");
    if (!file)
        return;

    std::string line;
    while (gzGetLine(file, line))
    {
        if (line.empty()) continue;

        std::stringstream ss(line);
        std::string callerSig;
        if (!std::getline(ss, callerSig, '\t')) continue;
        auto callerIt = pag->_methodIndices.find(callerSig);
        int callerIndex = (callerIt != pag->_methodIndices.end()) ? callerIt->second : -1;

        // The file is appended to during the cold run; a later line for the same caller replaces an earlier one.
        pag->CG.inlinedMethodNames.erase(callerSig);
        pag->CG.dependencyNames.erase(callerSig);
        if (callerIndex >= 0)
        {
            pag->CG.inlinedMethods.erase(callerIndex);
            pag->CG.peekedMethods.erase(callerIndex);
        }

        std::string field;
        while (std::getline(ss, field, '\t'))
        {
            if (field.size() < 3) continue;
            char kind = field[0];
            std::string depSig = field.substr(2);
            pag->CG.dependencyNames[callerSig].insert(depSig);
            if (kind == 'I')
                pag->CG.inlinedMethodNames[callerSig].insert(depSig);

            if (callerIndex < 0) continue;
            auto depIt = pag->_methodIndices.find(depSig);
            if (depIt == pag->_methodIndices.end()) continue;
            if (kind == 'I')
                pag->CG.inlinedMethods[callerIndex].insert(depIt->second);
            else
                pag->CG.peekedMethods[callerIndex].insert(depIt->second);
        }
    }
    gzclose(file);
}

void LoadPAG::getImportantFieldNames(const std::string &threadfieldFile, int static_or_thread)
{
    // SmartAOT: the cold run writes these files with gzopen; reading them with std::ifstream returned the compressed
    // bytes, so the thread-accessible and static field sets were filled with garbage.
    gzFile file = gzopen(threadfieldFile.c_str(), "r");

    if (!file)
    {
        std::cerr << "Error: Could not open file " << threadfieldFile << std::endl;
        return;
    }

    std::string line;
    while (gzGetLine(file, line))
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

    gzclose(file);
}