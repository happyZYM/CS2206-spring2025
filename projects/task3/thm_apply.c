#include "ast.h"

term* sub_thm(term* thm, var_sub_list* list){
    if(list == (void*) 0) return copy_term(thm);
    if(thm->type == Quant){
        term* den = list->cur->sub_term;
        return sub_thm(subst_term(den, list->cur->var, thm->content.Quant.body), list->next);
    }
    else return (void*) 0;
}

// apply (apply (impl) h1) (h2)
//不是imply形式时返回(void*) 0
ImplyProp *separate_imply(term *t)
{
    if (t->type != Apply || t->content.Apply.left->type != Apply ||
        t->content.Apply.left->content.Apply.left->type != Const ||
        t->content.Apply.left->content.Apply.left->content.Const.type != Impl)
        return (void*) 0;
    else
        return createImplyProp(t->content.Apply.left->content.Apply.right, t->content.Apply.right);
}

//根据定理形式，匹配结论，得出要检验的前提
term_list* check_list_gen(term* thm, term* target) {
    if (thm == (void*) 0 || target == (void*) 0) {
        return (void*) 0;
    }
    term_list* check_list = (void*) 0;
    term_list** tail_ptr = &check_list; 
    while (thm != (void*) 0 && !alpha_equiv(thm, target)) {
        ImplyProp* p = separate_imply(thm);    
        if (p == (void*) 0) {
            free_term_list(check_list);
            return (void*) 0;
        }
        // 添加新节点到链表
        term_list* new_node = malloc_term_list();        
        new_node->element = p->assum;  // 转移所有权
        new_node->next = (void*) 0;
        
        *tail_ptr = new_node;
        tail_ptr = &(new_node->next);     
        thm = p->concl;     
        free_imply_prop(p); // 释放ImplyProp结构体（不释放其成员）
    }
    return check_list;
}


solve_res* thm_apply(term* thm, var_sub_list* list, term* goal){
    term* thm_ins = sub_thm(thm, list);
    solve_res* res = malloc_solve_res();
    if(thm_ins == (void*) 0) {
        res->type = bool_res;
        res->d.ans = false;
    }
    else if(alpha_equiv(thm_ins, goal)){
        res->type = bool_res;
        res->d.ans = true;
    }
    else{
        res->type = termlist;
        res->d.list = check_list_gen(thm_ins, goal);
    }
    return res;
}