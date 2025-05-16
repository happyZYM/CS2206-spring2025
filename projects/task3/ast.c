#include "ast.h"

term *copy_term(term *t)
{
    if (t == (void *)0) return (void *)0;
    term *new_term = malloc_term();
    new_term->type = t->type;
    // 根据类型进行深拷贝
    switch (t->type){
        case Var: {
            if (t->content.Var) new_term->content.Var = strdup(t->content.Var);
            else new_term->content.Var = (void *)0;
            break;
        }
        case Const: {
            new_term->content.Const.type = t->content.Const.type;
            new_term->content.Const.content = t->content.Const.content;
            break;
        }
        case Apply: {
            new_term->content.Apply.left = copy_term(t->content.Apply.left);
            new_term->content.Apply.right = copy_term(t->content.Apply.right);
            break;
        }
        case Quant: {
            new_term->content.Quant.type = t->content.Quant.type;
            if (t->content.Quant.var)
                new_term->content.Quant.var = strdup(t->content.Quant.var);
            else new_term->content.Quant.var = (void*) 0;
            new_term->content.Quant.body = copy_term(t->content.Quant.body);
            break;
        }
    }
    return new_term;
}

// 假设 term_list 的深拷贝实现
term_list *copy_term_list(term_list *list)
{
    if (list == (void*) 0)
    {
        return (void*) 0;
    }
    // 创建新节点
    term_list *new_list = malloc_term_list();
    // 复制当前节点的 element
    new_list->element = copy_term(list->element);
    // 递归复制后续节点
    new_list->next = copy_term_list(list->next);
    return new_list;
}

void free_term(term *t)
{
    if (t == (void*) 0)
        return;
    switch (t->type)
    {
    case Var:
        free_str(t->content.Var);
        break;
    case Const:
        break;
    case Apply:
        free_term(t->content.Apply.left);
        free_term(t->content.Apply.right);
        break;
    case Quant:
        free_str(t->content.Quant.var);
        free_term(t->content.Quant.body);
        break;
    default:
        break;
    }
    free_term_struct(t);
}

void free_term_list(term_list *list)
{
    while (list != (void*) 0)
    {
        struct term_list *next = list->next;
        free_term(list->element);
        free_term_list_struct(list);
        list = next;
    }
}