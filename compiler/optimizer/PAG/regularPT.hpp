#ifndef REG_PT_HPP
#define REG_PT_HPP
#include<unordered_set>
#include<queue>
#include "PAG_Components.hpp"

class Regular_PointsTo
{   public:
        void propagate(PAGNode* x,std::unordered_set<PAGNode*>& marked,std::queue<PAGNode*>& worklist);
        std::unordered_set<PAGNode*> regularPT(PAGNode* src);
};


#endif