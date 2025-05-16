#include "cnf_trans.h"

/* BEGIN Given Functions */

// 分配一个大小为size的全零的int数组
int* malloc_int_array(int size);

// 释放int数组
void free_int_array(int* array);

// 分配一个初始全零 cnf_list 结构体
cnf_list* malloc_cnf_list();

// 释放 cnf_list 结构体
void free_cnf_list(cnf_list* list);

/* END Given Functions */


//生成p3<->(p1 op p2)对应的cnf中的clause
//p3<->not p2 (op为 not时， 此时p1缺省为0)
void clause_gen(int p1, int p2, int p3, int op, PreData* data){
    int size = 3;
    int *clause1 = malloc_int_array(size);
    int *clause2 = malloc_int_array(size);
    int *clause3 = malloc_int_array(size);
    int *clause4 = malloc_int_array(size);
    // 完成 SET_PROP: p3<->(p1 op p2) / p3<->not p2
    int cnt = 0;
    switch (op)
    {
    case SMTPROP_OR:
    {
        // p3\/非p1
        clause1[0] = -p1;
        clause1[1] = p3;
        // p3\/非p2
        clause2[0] = -p2;
        clause2[1] = p3;
        if (p1 != p2)
        {
            // 非p3\/p1\/p2
            clause3[0] = p1;
            clause3[1] = p2;
            clause3[2] = -p3;
        }
        else
        {
            clause3[0] = p1;
            clause3[1] = -p3;
        }
        cnt += 3;
        break;
    }
    case SMTPROP_AND:
    {
        // 非p3\/p1
        clause1[0] = p1;
        clause1[1] = -p3;
        // 非p3\/p2
        clause2[0] = p2;
        clause2[1] = -p3;
        if (p1 != p2)
        {
            // p3\/非p1\/非p2
            clause3[0] = -p1;
            clause3[1] = -p2;
            clause3[2] = p3;
        }
        else
        {
            clause3[0] = -p1;
            clause3[1] = p3;
        }
        cnt += 3;
        break;
    }
    case SMTPROP_IMPLY:
    {
        if (p1 != p2)
        {
            // p3\/p1
            clause1[0] = p1;
            clause1[1] = p3;
            // p3\/非p2
            clause2[0] = -p2;
            clause2[1] = p3;
            // 非p3\/非p1\/p2
            clause3[0] = -p1;
            clause3[1] = p2;
            clause3[2] = -p3;
            cnt += 3;
        }
        else
        {
            clause1[0] = p3;
            cnt += 1;
        }
        break;
    }
    case SMTPROP_IFF:
    {
        if (p1 != p2)
        {
            // p3\/p1\/p2
            clause1[0] = p1;
            clause1[1] = p2;
            clause1[2] = p3;
            // p3\/非p1\/非p2
            clause2[0] = -p1;
            clause2[1] = -p2;
            clause2[2] = p3;
            // 非p3\/p1\/非p2
            clause3[0] = p1;
            clause3[1] = -p2;
            clause3[2] = -p3;
            // 非p3\/非p1\/p2
            clause4[0] = -p1;
            clause4[1] = p2;
            clause4[2] = -p3;
            cnt += 4;
        }
        else
        {
            clause1[0] = p3;
            cnt += 1;
        }
        break;
    }
    case SMTPROP_NOT:
    {
        // p3\/p2
        clause1[0] = p2;
        clause1[1] = p3;
        // 非p3\/非p2
        clause2[0] = -p2;
        clause2[1] = -p3;
        cnt += 2;
        break;
    }
    default:
    {
        //unreachable 
    }
    }
    cnf_list *list1 = malloc_cnf_list();
    cnf_list *list2 = malloc_cnf_list();
    cnf_list *list3 = malloc_cnf_list();
    cnf_list *list4 = malloc_cnf_list();
    list1->size = size;
    list2->size = size;
    list3->size = size;
    list4->size = size;
    list1->clause = clause1;
    list2->clause = clause2;
    list3->clause = clause3;
    list4->clause = clause4;
    if (cnt == 1)
    {
        list1->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 1;
        free_int_array(clause2);
        free_int_array(clause3);
        free_int_array(clause4);
        free_cnf_list(list2);
        free_cnf_list(list3);
        free_cnf_list(list4);
    }
    else if (cnt == 2)
    {
        list1->next = list2;
        list2->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 2;
        free_int_array(clause3);
        free_int_array(clause4);
        free_cnf_list(list3);
        free_cnf_list(list4);
    }
    else if (cnt == 3)
    {
        list1->next = list2;
        list2->next = list3;
        list3->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 3;
        free_int_array(clause4);
        free_cnf_list(list4);
    }
    else
    {
        list1->next = list2;
        list2->next = list3;
        list3->next = list4;
        list4->next = data->cnf_res;
        data->cnf_res = list1;
        data->clause_cnt += 4;
    }
}

int prop2cnf(SmtProp* p, PreData* data){
    int res = 0;
    switch(p->type){
        case SMTB_PROP: {
            int p1 = prop2cnf(p->prop.Binary_prop.prop1, data);
            int p2 = prop2cnf(p->prop.Binary_prop.prop2, data);
            res = ++(data->prop_cnt);
            clause_gen(p1, p2, res, p->prop.Binary_prop.op, data);
            break;
        }
        case SMTU_PROP: {
            int p1 = prop2cnf(p->prop.Unary_prop.prop1, data);
            res = ++(data->prop_cnt);
            clause_gen(0, p1, res, p->prop.Binary_prop.op, data);
            break;
        }
        case SMT_PROPVAR:
            res = p->prop.Propvar;
            break;
        default:
            //unreachable
    }
    return res;
}
