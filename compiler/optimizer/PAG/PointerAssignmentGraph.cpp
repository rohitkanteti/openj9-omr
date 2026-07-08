#include "PointerAssignmentGraph.hpp"

PointerAssignmentGraph::PointerAssignmentGraph()
{
    bottom_node = new PAGNode(GLOBAL, -9, NULL, NULL, -9, -9);
    PAG_nodes.insert(bottom_node);
}

PAGNode *PointerAssignmentGraph::getReturnNode(int method)
{
    PAGNode* returnNode = (methodIndex_to_returnNode.find(method) != methodIndex_to_returnNode.end()) ? methodIndex_to_returnNode[method] : NULL;
    if(returnNode == NULL)
    {
        methodIndex_to_returnNode[method] = new PAGNode(RETURN, -56765, NULL, NULL, -1, method);
        PAG_nodes.insert(methodIndex_to_returnNode[method]);
        methodIndex_to_allMethodNodes[method].push_back(methodIndex_to_returnNode[method]);
        returnNode = methodIndex_to_returnNode[method];
    }
    return returnNode;
}

vector<PAGNode *> PointerAssignmentGraph::getFormalParameterNodes(METHOD_INDEX method)
{
    static std::vector<PAGNode *> emptyVec;
    return (methodIndex_to_formalNodes.find(method) != methodIndex_to_formalNodes.end()) ? methodIndex_to_formalNodes[method] : emptyVec;
}

std::vector<PAGNode *> PointerAssignmentGraph::getActualParameterNodes(METHOD_INDEX method, CALLSITE_BCI callsite_bci)
{
    std::vector<PAGNode *> actualParams;
    for (const auto &entry : CG.callsiteParams)
    {

        std::istringstream iss(entry.first);
        int caller, calleeMethodIndex, bci;

        iss >> caller >> calleeMethodIndex >> bci;

        if (caller == method && bci == callsite_bci)
        {
            actualParams.insert(actualParams.end(), entry.second.begin(), entry.second.end());
        }
    }
    return actualParams;
}

// void PointerAssignmentGraph::removeEdgeFrom(PAGNode* src, CALLSITE_BCI callsite) {
//     auto it = src->outgoing.begin();
//     while (it != src->outgoing.end()) {
//         if ((*it)->callsiteBCI == callsite) {
//             deleteEdge(*it);
//             it = src->outgoing.erase(it);
//         } else {
//             ++it;
//         }
//     }
// }

void PointerAssignmentGraph::removeEdgeFrom(PAGNode *src, CALLSITE_BCI callsite)
{
    auto it = src->outgoing.begin();
    while (it != src->outgoing.end())
    {
        if ((*it)->callsiteBCI == callsite)
        {
            PAGEdge *edge = *it;
            it = src->outgoing.erase(it);
            deleteEdge(edge);
        }
        else
        {
            ++it;
        }
    }
}

void PointerAssignmentGraph::removeAllEdgesFrom(PAGNode *node)
{
    // Collect edges to delete first
    std::vector<PAGEdge *> edgesToDelete;
    for (PAGEdge *edge : node->outgoing)
    {
        edgesToDelete.push_back(edge);
    }
    for (PAGEdge *edge : edgesToDelete)
    {
        deleteEdge(edge);
    }
    // node->outgoing.clear();
}

void PointerAssignmentGraph::removeEdge(PAGNode *src, PAGNode *dest, CALLSITE_BCI callsite)
{
    auto it = src->outgoing.begin();
    while (it != src->outgoing.end())
    {
        if ((*it)->dest == dest && (*it)->callsiteBCI == callsite)
        {
            deleteEdge(*it);
            it = src->outgoing.erase(it);
        }
        else
        {
            ++it;
        }
    }
}

void PointerAssignmentGraph::removeEdge(PAGNode *src, PAGNode *dest)
{
    auto it = src->outgoing.begin();
    while (it != src->outgoing.end())
    {
        if ((*it)->dest == dest)
        {
            it = src->outgoing.erase(it);
            // delete *it;
        }
        else
        {
            ++it;
        }
    }
}

void PointerAssignmentGraph::removeEdge(PAGEdge *edge)
{
    edge->src->outgoing.erase(edge);
    edge->dest->incoming.erase(edge);
    // delete edge;
}

std::vector<PAGEdge *> PointerAssignmentGraph::getStoreEdges()
{
    std::vector<PAGEdge *> result;
    for (auto node : PAG_nodes)
    {
        for (auto edge : node->outgoing)
        {
            if (edge->type == EdgeType::PUTFIELD)
            {
                result.push_back(edge);
            }
        }
    }
    return result;
}

std::vector<PAGEdge *> PointerAssignmentGraph::getStoreEdges(int method)
{
    std::vector<PAGEdge *> result;
    if(methodIndex_to_allMethodNodes.find(method)==methodIndex_to_allMethodNodes.end()) 
    {
        // std::cout << "The method with method_index=" << method << "was not found in " << std::endl;
         return result;
    }
    for (auto node : methodIndex_to_allMethodNodes[method])
    {
        for (auto edge : node->outgoing)
        {
            if (edge->type == EdgeType::PUTFIELD)
            {
                result.push_back(edge);
            }
        }
    }
    return result;
}

std::vector<PAGEdge *> PointerAssignmentGraph::getIntraproceduralAssignEdges(int method)
{
    std::vector<PAGEdge *> result;
    if(methodIndex_to_allMethodNodes.find(method)==methodIndex_to_allMethodNodes.end()) 
    {
        // std::cout << "The method with method_index=" << method << "was not found in " << std::endl;
         return result;
    }
    for (auto node : methodIndex_to_allMethodNodes[method])
    {
        for (auto edge : node->outgoing)
        {
            if (edge->type == EdgeType::ASSIGN &&
                edge->dest->methodIndex == method)
            {
                result.push_back(edge);
            }
        }
    }
    return result;
}

void PointerAssignmentGraph::removeEdges(int method)
{
    if(methodIndex_to_allMethodNodes.find(method)==methodIndex_to_allMethodNodes.end()) 
    {
        // std::cout << "The method with method_index=" << method << "was not found in " << std::endl;
         return;
    }
    for (auto node : methodIndex_to_allMethodNodes[method])
    {   
        std::unordered_set<PAGEdge*> delete_these;
        for (auto edge : node->outgoing)
        {
            // std::cout << "In removeEdges " <<edge <<  std::endl;
            // if(edge->dest->methodIndex == method)
            // {
            bool is_formal = false;
            vector<PAGNode *> f_params = getFormalParameterNodes(method);
            for (auto *f_p : f_params)
            {
                if (f_p == node || node->type == RETURN) // don't remove the formal param nodes and return node;
                {
                    is_formal = true;
                }
            }

            if (!is_formal)
            {
                if (edge->type == EdgeType::PUTFIELD)
                {
                    if (staticFields.find(edge->field) != staticFields.end() || threadAccessibleFields.find(edge->field) != threadAccessibleFields.end())
                    {
                        LeakyNodes.erase(edge->dest);
                    }
                }

                // }

                // removeEdge(edge);
                delete_these.insert(edge);
            }
        }
        for(PAGEdge* to_del : delete_these)
        {
            removeEdge(to_del);
        }
    }
}
void PointerAssignmentGraph::removeNodes(int method)
{   
    if(methodIndex_to_allMethodNodes.find(method)==methodIndex_to_allMethodNodes.end()) 
    {
        // std::cout << "The method with method_index=" << method << "was not found in " << std::endl;
         return;
    }

    vector<PAGNode *> nodes = methodIndex_to_allMethodNodes[method];
    vector<PAGNode *> &allNodes = methodIndex_to_allMethodNodes[method];
    // std::cout << "The number of nodes of methodIndex " << method << " may be removed are  " << nodes.size() << std::endl;
    PAGNode *ret_node = methodIndex_to_returnNode[method];
    vector<PAGNode *> f_params = getFormalParameterNodes(method);
    std::unordered_set<PAGNode*> formal_params(f_params.begin(),f_params.end());
    int index = 0;
    for (auto *node : nodes)
    {
       
        if (node->type != RETURN)
            removeAllEdgesFrom(node);

        if (formal_params.find(node)==formal_params.end() && node->type != RETURN) // don't remove the formal param nodes and return node;
        {
            PAG_nodes.erase(node);
            for (auto it = nodeIndexToNode.begin(); it != nodeIndexToNode.end(); ++it)
            {
                if (it->second == node)
                {
                    nodeIndexToNode.erase(it);
                    break;
                }
            }
            // std::cout << "Erase Index : " << index << std::endl;
        }

        // delete node;
        index++;
    }

    methodIndex_to_allMethodNodes.erase(method);
    methodIndex_to_allMethodNodes[method].insert(methodIndex_to_allMethodNodes[method].end(), methodIndex_to_formalNodes[method].begin(),methodIndex_to_formalNodes[method].end());
    if(methodIndex_to_returnNode[method]) methodIndex_to_allMethodNodes[method].push_back(methodIndex_to_returnNode[method]);

    // methodIndex_to_formalNodes.erase(method);
    // methodIndex_to_returnNode.erase(method);
}

std::unordered_set<std::string> PointerAssignmentGraph::get_fields(PAGNode *object)
{
    std::unordered_set<std::string> fields;
    for (auto edge : object->incoming)
    {
        if (edge->type == EdgeType::PUTFIELD && !edge->field.empty())
        {
            fields.insert(edge->field);
        }
    }
    return fields;
}

std::unordered_set<PAGNode *> PointerAssignmentGraph::get_field_target(PAGNode *object, std::string field)
{
    std::unordered_set<PAGNode *> targets;
    for (auto edge : object->incoming)
    {
        if (edge->type == EdgeType::PUTFIELD && edge->field == field)
        {
            targets.insert(edge->src);
        }
    }
    return targets;
}

// Destructor
PointerAssignmentGraph::~PointerAssignmentGraph()
{
    for (auto node : PAG_nodes)
    {
        // for (auto edge : node->outgoing) {
        //     delete edge;
        // }
        node->outgoing.clear();
        node->incoming.clear();
    }

    // for (auto node : PAG_nodes) {
    //     delete node;
    // }
    PAG_nodes.clear();
    nodeIndexToNode.clear();
}

void PointerAssignmentGraph::deleteEdge(PAGEdge *edge)
{
    edge->src->outgoing.erase(edge);
    edge->dest->incoming.erase(edge);
    // delete edge;
}

void PointerAssignmentGraph::addEdge(PAGNode *src, PAGNode *dest, EdgeType type)
{
    addEdge(src, dest, type, "<N/A>", INVALID_BCI);
}

void PointerAssignmentGraph::addEdge(PAGNode *src, PAGNode *dest, EdgeType type, std::string field)
{
    addEdge(src, dest, type, field, INVALID_BCI);
}

void PointerAssignmentGraph::addEdge(PAGNode *src, PAGNode *dest, EdgeType type, int callsiteBCI)
{
    addEdge(src, dest, type, "<N/A>", callsiteBCI);
}

void PointerAssignmentGraph::addEdge(PAGNode *src, PAGNode *dest, EdgeType type, std::string field, int callsiteBCI)
{
    auto edge = new PAGEdge(src, dest, type, field, callsiteBCI);
    src->outgoing.insert(edge);
    dest->incoming.insert(edge);

    if (type == EdgeType::PUTFIELD)
    {
        if (staticFields.find(field) != staticFields.end() || threadAccessibleFields.find(field) != threadAccessibleFields.end())
        {
            LeakyNodes.insert(dest);
        }
    }

    EdgeType reverseType = static_cast<EdgeType>(type + 5);
    auto edge_bar = new PAGEdge(dest, src, reverseType, field, callsiteBCI);
    dest->outgoing.insert(edge_bar);
    src->incoming.insert(edge_bar);
}

std::unordered_set<PAGNode *> PointerAssignmentGraph::flowsTo(PAGNode *object)
{
    return FlowsToReg(object);
}

// using `flowsToReg -> new ( assign | match )*`
std::unordered_set<PAGNode *> PointerAssignmentGraph::FlowsToReg(PAGNode *object)
{
    std::unordered_set<PAGNode *> result;
    std::unordered_set<PAGNode *> visited;
    std::queue<PAGNode *> worklist;

    worklist.push(object);
    visited.insert(object);

    while (!worklist.empty())
    {
        PAGNode *current = worklist.front();
        worklist.pop();

        for (PAGEdge *edge : current->outgoing)
        {
            switch (edge->type)
            {
            case EdgeType::NEW:

                result.insert(edge->dest);
                if (visited.find(edge->dest) == visited.end())
                {
                    visited.insert(edge->dest);
                    worklist.push(edge->dest);
                }
                break;

            case EdgeType::ASSIGN:

                if (visited.find(edge->dest) == visited.end())
                {
                    visited.insert(edge->dest);
                    worklist.push(edge->dest);
                }
                break;

            case EdgeType::MATCH:

                if (visited.find(edge->dest) == visited.end())
                {
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

std::unordered_set<PAGNode *> PointerAssignmentGraph::getEscapingObjects(int method)
{
    std::unordered_set<PAGNode *> escaping;
    if (allEscpaingObjects.size() > 0)
    {
        for (auto *obj : allEscpaingObjects)
        {
            if (obj->methodIndex == method)
                escaping.insert(obj);
        }
    }
    else //if (number_of_escapingObjs  0)
    {
        for (auto *leaky : LeakyNodes)
        {
            std::unordered_set<PAGNode *> esc = points_to(leaky);
            for(auto* edge : leaky->incoming) // all fields of the object pointed to by a leaky node are also escaping.
            {
                if(edge->type == PUTFIELD)
                {   
                    std::unordered_set<PAGNode *> points = points_to(edge->src);
                    esc.insert(points.begin(),points.end());
                }
            }
            for (auto *obj : esc) // Collect the escaping object of this method
            {
                if (obj->methodIndex == method)
                    escaping.insert(obj);
            }
            number_of_escapingObjs += esc.size();
            allEscpaingObjects.insert(esc.begin(), esc.end());
        }
    }

    return escaping;
}

std::unordered_set<PAGNode *> PointerAssignmentGraph::points_to(PAGNode *src)
{
    Regular_PointsTo rp;
    return rp.regularPT(src);
}
std::unordered_set<PAGEdge *> PointerAssignmentGraph::getAllocEdges(int method)
{
    std::unordered_set<PAGEdge *> allocEdges;
    auto it = methodIndex_to_allMethodNodes.find(method);
    if (it != methodIndex_to_allMethodNodes.end())
    {
        for (PAGNode *node : it->second)
        {
            for (PAGEdge *edge : node->outgoing)
            {
                if (edge->type == EdgeType::NEW)
                {
                    allocEdges.insert(edge);
                }
            }
        }
    }
    return allocEdges;
}

unordered_set<PAGNode *> PointerAssignmentGraph::getLeakyNodes()
{
    return LeakyNodes;
}

std::vector<PAGEdge *> PointerAssignmentGraph::getLoadEdges()
{
    std::vector<PAGEdge *> result;
    for (auto node : PAG_nodes)
    {
        for (auto edge : node->outgoing)
        {
            if (edge->type == EdgeType::GETFIELD)
            {
                result.push_back(edge);
            }
        }
    }
    return result;
}

std::vector<PAGEdge *> PointerAssignmentGraph::getLoadEdges(int method)
{
    std::vector<PAGEdge *> result;
    if(methodIndex_to_allMethodNodes.find(method)==methodIndex_to_allMethodNodes.end()) 
    {
        // std::cout << "The method with method_index=" << method << "was not found in " << std::endl;
         return result;
    }
    for (auto node : methodIndex_to_allMethodNodes[method])
    {
        for (auto edge : node->outgoing)
        {
            if (edge->type == EdgeType::GETFIELD)
            {
                result.push_back(edge);
            }
        }
    }
    return result;
}

std::vector<PAGEdge *> PointerAssignmentGraph::getMatchEdgesEndingAt(PAGNode *node)
{
    std::vector<PAGEdge *> result;

    for (PAGEdge *edge : node->incoming)
    {
        if (edge->type == MATCH && edge->dest == node)
        {
            result.push_back(edge);
        }
    }

    return result;
}
