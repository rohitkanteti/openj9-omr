#ifndef ENUMS_H
#define ENUMS_H

enum NodeType {   
    NONTYPE = -1,
    VARIABLE = 0,
    OBJECT = 1,
    RETURN = 2,
    NULL_OBJ = 3,
    STATIC = 4,
    GLOBAL = 5
};   
enum EdgeType {   
    ASSIGN = 0,
    NEW = 1,
    PUTFIELD = 2,
    GETFIELD = 3,
    MATCH = 4,
    ASSIGN_BAR = 5,
    NEW_BAR = 6,
    PUTFIELD_BAR = 7,
    GETFIELD_BAR = 8,
    MATCH_BAR = 9
};   

#endif
