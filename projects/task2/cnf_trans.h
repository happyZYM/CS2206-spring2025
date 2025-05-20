#include "smt_lang.h"

struct cnf_list{
    int size; //变量数量
    int* clause; //clause[i]存储命题变元的编号
    struct cnf_list* next;
};
typedef struct cnf_list cnf_list;

typedef struct{
    cnf_list* cnf_res;
    int prop_cnt; //命题变元数量
    int clause_cnt; //转成cnf后clause的数量
} PreData;
