#include<bits/stdc++.h>
#include "PointerAssignmentGraph.cpp"
/*
 Implementation of REFINED points analysis as in the paper 
 Manu Sridharan, Denis Gopan, Lexin Shan, and Rastislav Bodík. 2005. 
 Demand-driven points-to analysis for Java. SIGPLAN Not. 40, 10 (October 2005), 59–76.
  https://doi.org/10.1145/1103845.1094817
*/

void propagate(PAGNode* x,unordered_set<PAGNode*>& marked,queue<PAGNode*>& worklist);
bool refinedRegularPT(PAGNode* x);
bool positivelyAnswered(unordered_set<PAGNode*>) ;

unordered_set<PAGEdge*> getfieldsToRefine; // Set of GETFIELD[f] edges
unordered_set<PAGEdge*> getfieldsSeen; //Set of GETFIELD[f] edges
PointerAssignmentGraph* pag; // read from the dumped file.

unordered_set<PAGNode*> doTraversal(PAGNode* x)
{
    unordered_set<PAGNode*> pointsTo; // Set of Node
    unordered_set<PAGNode*> marked ; // Set of Node
    queue<PAGNode*> worklist; //List of Node

    propagate(x,marked,worklist);

    while(worklist.size() > 0)
    {
        PAGNode* w = worklist.front();
        worklist.pop();
        unordered_set<PAGEdge*> new_edges;
        unordered_set<PAGEdge*> assign_edges;
        unordered_set<PAGEdge*> getfield_edges;
        unordered_set<PAGEdge*> putfield_edges;

        for(PAGEdge* e : w->incoming)
        {
            if(e->type == NEW)
            {
                new_edges.insert(e);
            }
            else if(e->type == ASSIGN)
            {
                assign_edges.insert(e);
            }
            else if(e->type == GETFIELD)
            {
                getfield_edges.insert(e);
            }
            else if(e->type == PUTFIELD)
            {
                putfield_edges.insert(e);
            }
        }

        for(PAGEdge* e: new_edges)
        {
            pointsTo.insert(e->src);
        }
        for(PAGEdge* e: assign_edges)
        {
            propagate(e->src,marked,worklist);
        }

        for(PAGEdge* e: getfield_edges)
        {
            string field_name = e->field;
            if(getfieldsToRefine.find(e) == getfieldsToRefine.end())
            {
                getfieldsSeen.insert(e);
                for(PAGEdge* e2 : pag->field_to_putFieldEdges[field_name])
                {
                    propagate(e2->src,marked,worklist);
                }
            }
            else
            {    
                // e = p --getfield[field_name]--> w
                getfieldsToRefine.erase(e); 
                unordered_set<PAGNode*> ptOfP = doTraversal(e->src);
                for(PAGEdge* e2 : pag->field_to_putFieldEdges[field_name])
                {   
                    // e2 = y --putfield[field_name]--> q
                    unordered_set<PAGNode*> ptOfQ = doTraversal(e->dest);
                    std::vector<PAGNode*> intersectionResult;
                    
                    if() // set_intersection(ptOfP,ptOfQ) > 0
                    {
                        propagate(e2->src,marked,worklist);
                    }
                }

                getfieldsToRefine.insert(e);
                
            }
        }
    }

    return pointsTo;
}

bool refinedRegularPT(PAGNode* x)
{
    getfieldsToRefine.clear();
    while(true)
    {
        getfieldsSeen.clear();
        unordered_set<PAGNode*> pointsTo = doTraversal(x);

        if ( positivelyAnswered(pointsTo) )
           return true;
        else
        {
            if(containedIn(getfieldsSeen,getfieldsToRefine))
                return false;
            else
            {
                for(auto e : getfieldsSeen)
                {
                    getfieldsToRefine.insert(e);
                }
            }
        }
    }
}

void propagate(PAGNode* x,unordered_set<PAGNode*>& marked,queue<PAGNode*>& worklist)
{
    if(marked.find(x)==marked.end())
    {
        marked.insert(x);
        worklist.push(x);
    }
}

bool positivelyAnswered(unordered_set<PAGNode*> x)
{   
    // TODO: implement this
    return true;
}