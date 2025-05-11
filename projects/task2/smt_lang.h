#ifndef SMT_LANG_H
#define SMT_LANG_H 1
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

typedef struct SmtProp SmtProp;
typedef struct SmtProplist SmtProplist;
typedef enum SmtPropBop SmtPropBop;
typedef enum SmtPropUop SmtPropUop;
typedef enum SmtPropType SmtPropType;



enum SmtPropBop{
    SMTPROP_AND ,
    SMTPROP_OR, SMTPROP_IMPLY, SMTPROP_IFF
};

enum SmtPropUop{
    SMTPROP_NOT = SMTPROP_IFF+1  
};


enum SmtPropType {
    SMTB_PROP = SMTPROP_NOT + 1, 
    SMTU_PROP, 
    SMT_PROPVAR
};


struct SmtProp {
    SmtPropType type;
    union {
        struct {
            SmtPropBop op;
            SmtProp *prop1, *prop2;
        } Binary_prop;
        struct {
            SmtPropUop op;
            SmtProp *prop1;
        } Unary_prop;
        int Propvar; //表示将原子命题抽象成的命题变元对应的编号
    } prop;
};

struct SmtProplist {
    SmtProp* prop;
    SmtProplist* next;
};

#endif