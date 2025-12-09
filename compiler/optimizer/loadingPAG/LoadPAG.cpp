#include "LoadPAG.hpp"
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
    std::ifstream file(filename);
    std::string line;
    int index = 1;

    while (std::getline(file, line))
    {
        if (line.empty())
            continue;

        if (line.front() == '[')
            line = line.substr(1);
        if (line.back() == ']')
            line.pop_back();

        std::stringstream ss(line);
        std::string token;

        std::getline(ss, token, ',');
        int bci = std::stoi(token);

        std::getline(ss, token, ',');
        int methodIndex = std::stoi(token);

        std::getline(ss, token, ',');
        int typeInt = std::stoi(token);

        std::getline(ss, token, ',');
        int name = std::stoi(token);

        std::getline(ss, token, ',');
        int isLeaky = std::stoi(token);

        NodeType type = parseNodeType(typeInt);

        std::unordered_set<std::string> pointee_names;
        while (std::getline(ss, token, ','))
        {
            if (!token.empty())
                pointee_names.insert(token);
        }
        if (!(bci == -9 && type == 5 && name == -9))
        {
            PAGNode *node = new PAGNode(type, name, nullptr, nullptr, bci, methodIndex);
            pag->PAG_nodes.insert(node);
            pag->nodeIndexToNode[index++] = node;
            node->pointee_class_names.insert(pointee_names.begin(), pointee_names.end());
            if (isLeaky)
                pag->LeakyNodes.insert(node);
        }
        else
        {
            pag->nodeIndexToNode[index++] = pag->bottom_node;
        }
    }
}

void LoadPAG::loadEdges(const std::string &filename)
{
    std::ifstream file(filename);
    std::string line;

    while (std::getline(file, line))
    {
        if (line.empty())
            continue;

        auto colonPos = line.find(':');
        if (colonPos == std::string::npos)
            continue;

        int srcIndex = std::stoi(line.substr(0, colonPos));
        std::string edgesPart = line.substr(colonPos + 1);

        std::stringstream listSS(edgesPart);
        std::string tuple;

        while (std::getline(listSS, tuple, ';'))
        {
            if (tuple.empty())
                continue;

            tuple.erase(remove_if(tuple.begin(), tuple.end(), ::isspace), tuple.end());

            if (tuple.front() == '[')
                tuple.erase(tuple.begin());
            if (!tuple.empty() && tuple.back() == ']')
                tuple.pop_back();

            if (tuple.empty())
                continue;

            std::stringstream tupleSS(tuple);
            std::string token;

            if (!std::getline(tupleSS, token, ','))
                continue;
            int destIndex = std::stoi(token);

            if (!std::getline(tupleSS, token, ','))
                continue;
            int edgeTypeInt = std::stoi(token);

            if (!std::getline(tupleSS, token, ','))
                continue;
            std::string fieldName = token;
            if (fieldName == "<N/A>")
                fieldName = "";

            if (!std::getline(tupleSS, token, ','))
                continue;
            int callsiteBCI = 0;
            try
            {
                callsiteBCI = std::stoi(token);
            }
            catch (...)
            {
                callsiteBCI = -1;
            }

            PAGNode *src = pag->nodeIndexToNode[srcIndex];
            PAGNode *dest = pag->nodeIndexToNode[destIndex];

            if (!src || !dest)
            {
                std::cerr << "Invalid edge in line: " << line << "\n";
                continue;
            }

            EdgeType eType = parseEdgeType(edgeTypeInt);
            pag->addEdge(src, dest, eType, fieldName, callsiteBCI);
        }
    }
}

void LoadPAG::loadMethodNodeMappings(const std::string &filename)
{
    std::ifstream file(filename);
    std::string line;

    while (std::getline(file, line))
    {
        if (line.empty())
            continue;

        auto colonPos = line.find(':');
        int methodIndex = std::stoi(line.substr(0, colonPos));
        std::string nodeData = line.substr(colonPos + 2, line.size() - colonPos - 3); // remove ":[" and "]"

        std::stringstream ss(nodeData);
        std::string pair;

        while (std::getline(ss, pair, ';'))
        {
            if (pair.empty())
                continue;

            // Remove [ and ] if present
            if (pair.front() == '[')
                pair = pair.substr(1);
            if (pair.back() == ']')
                pair.pop_back();

            std::stringstream pairSS(pair);
            std::string token;

            std::getline(pairSS, token, ',');
            int nodeIndex = std::stoi(token);

            std::getline(pairSS, token, ',');
            int isParam = std::stoi(token);

            PAGNode *node = pag->nodeIndexToNode[nodeIndex];
            if (!node)
            {
                std::cerr << "Node index not found in PAG: " << nodeIndex << "\n";
                continue;
            }

            // Add to allMethodNodes
            pag->methodIndex_to_allMethodNodes[methodIndex].push_back(node);

            // If it's a formal parameter
            if (isParam == 1)
            {
                pag->methodIndex_to_formalNodes[methodIndex].push_back(node);
            }

            // If it's a return node
            if (node->type == NodeType::RETURN)
            {
                pag->methodIndex_to_returnNode[methodIndex] = node;
            }
        }
    }
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
    std::ifstream file(filename);
    std::string line;

    while (std::getline(file, line))
    {
        if (line.empty())
            continue;

        size_t colonPos = line.find(':');
        if (colonPos == std::string::npos)
            continue;

        std::string callsiteInfo = line.substr(0, colonPos);
        std::string targetsStr = line.substr(colonPos + 1);

        if (callsiteInfo.front() != '(' || callsiteInfo.back() != ')')
            continue;
        callsiteInfo = callsiteInfo.substr(1, callsiteInfo.length() - 2); // Remove parentheses

        size_t commaPos = callsiteInfo.find(',');
        if (commaPos == std::string::npos)
            continue;

        int callsiteBCI = std::stoi(callsiteInfo.substr(0, commaPos));
        int receiverIndex = std::stoi(callsiteInfo.substr(commaPos + 1));
        // std::cout << "BCI is " << callsiteBCI << "reciever index is "<<receiverIndex <<std::endl;
        if (receiverIndex != -90898)
            pag->callsite_to_storeNodeIndex[callsiteBCI] = receiverIndex;

        std::stringstream targetsStream(targetsStr);
        std::string targetEntry;
        while (std::getline(targetsStream, targetEntry, ';'))
        {
            if (targetEntry.empty())
                continue;

            size_t openBracket = targetEntry.find('[');
            size_t closeBracket = targetEntry.find(']');
            if (openBracket == std::string::npos || closeBracket == std::string::npos)
                continue;

            targetEntry = targetEntry.substr(openBracket + 1, closeBracket - openBracket - 1);

            std::stringstream entryStream(targetEntry);
            std::string token;

            if (!std::getline(entryStream, token, ','))
                continue;
            int targetMethodIndex = std::stoi(token);

            std::vector<PAGNode *> actualParams;
            while (std::getline(entryStream, token, ','))
            {
                if (token.empty())
                    continue;
                int nodeIndex = std::stoi(token);
                auto nodeIt = pag->nodeIndexToNode.find(nodeIndex);
                if (nodeIt != pag->nodeIndexToNode.end())
                {
                    actualParams.push_back(nodeIt->second);
                }
            }

            if (!actualParams.empty())
            {
                int callerMethodIndex = actualParams[0]->methodIndex;

                pag->CG.calleeToCallers[targetMethodIndex].insert(callerMethodIndex);
                pag->CG.callerCalleeSites[callerMethodIndex][targetMethodIndex].insert(callsiteBCI);

                std::ostringstream oss;
                oss << callerMethodIndex << ' ' << targetMethodIndex << ' ' << callsiteBCI;
                std::string key = oss.str();
                pag->CG.callsiteParams[key] = actualParams;
            }
        }
    }
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
        // std::cout << line << std::endl;
        if (static_or_thread == 0)
            pag->threadAccessibleFields.insert(line);
        else
            pag->staticFields.insert(line);
    }

    file.close();
}
