#include "regularPT.hpp"

void Regular_PointsTo::propagate(PAGNode* x,std::unordered_set<PAGNode*>& marked,std::queue<PAGNode*>& worklist)
{
    if(marked.find(x)==marked.end())
    {
        marked.insert(x);
        worklist.push(x);
    }
}
std::unordered_set<PAGNode*> Regular_PointsTo::regularPT(PAGNode* src)
{
    std::unordered_set<PAGNode*> pointsTo;
    std::unordered_set<PAGNode*> marked;
    std::queue<PAGNode*> workList;

    propagate(src,marked,workList);
    while(workList.size()>0)
    {
        PAGNode* w = workList.front();
        workList.pop();

        for(auto* edge : w->incoming)
        {
            if(edge->type == EdgeType::NEW)
            {
                pointsTo.insert(edge->src);
            }
            else if(edge->type == EdgeType::ASSIGN || edge->type == EdgeType::MATCH)
            {
                propagate(edge->src,marked,workList);
            }
           
        }
    }

    return pointsTo;
}