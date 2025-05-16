#include "ast.h"

bool alpha_equiv(term *t1, term *t2)
{
    if (t1 == (void*) 0 || t2 == (void*) 0)
        return false;
    if (t1->type != t2->type)
        return false;
    switch (t1->type){
        case Var: {
            return strcmp(t1->content.Var, t2->content.Var) == 0;
        }
        case Const: {
            if (t1->content.Const.type != t2->content.Const.type)
                return false;
            if (t1->content.Const.type == Num){
                return t1->content.Const.content == t2->content.Const.content;
            }
            return true;
        }
        case Apply: {
            return alpha_equiv(t1->content.Apply.left, t2->content.Apply.left) &&
                alpha_equiv(t1->content.Apply.right, t2->content.Apply.right);
        }
        case Quant: {
            if (t1->content.Quant.type != t2->content.Quant.type)
                return false;
            if (strcmp(t1->content.Quant.var, t2->content.Quant.var) == 0){
                return alpha_equiv(t1->content.Quant.body, t2->content.Quant.body);
            }
            else{
                term *t21 = subst_var(t1->content.Quant.var, t2->content.Quant.var, copy_term(t2->content.Quant.body));
                bool result = alpha_equiv(t1->content.Quant.body, t21);
                free_term(t21);
                return result;
            }
        }
    }
}