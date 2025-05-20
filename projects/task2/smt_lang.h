enum SmtPropBop{
    SMTPROP_AND ,
    SMTPROP_OR, SMTPROP_IMPLY, SMTPROP_IFF
};
typedef enum SmtPropBop SmtPropBop;

enum SmtPropUop{
    SMTPROP_NOT = 4
};
typedef enum SmtPropUop SmtPropUop;

enum SmtPropType {
    SMTB_PROP = 5, 
    SMTU_PROP, 
    SMT_PROPVAR
};
typedef enum SmtPropType SmtPropType;

struct SmtProp {
    SmtPropType type;
    union {
        struct {
            SmtPropBop op;
            struct SmtProp * prop1; 
            struct SmtProp * prop2;
        } Binary_prop;
        struct {
            SmtPropUop op;
            struct SmtProp *prop1;
        } Unary_prop;
        int Propvar; //表示将原子命题抽象成的命题变元对应的编号
    } prop;
};

typedef struct SmtProp SmtProp;

struct SmtProplist {
    SmtProp* prop;
    struct SmtProplist* next;
};

typedef struct SmtProplist SmtProplist;
