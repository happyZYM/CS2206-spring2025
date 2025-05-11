#ifndef AST_H
#define AST_H

#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct term term;
typedef enum const_type const_type;
typedef enum quant_type quant_type;

enum const_type
{
    Num = 0,
    // oper
    Add,
    Mul,
    // pred
    Eq,
    Le,
    // connect
    And,
    Or,
    Impl
};

enum quant_type
{
    Forall,
    Exists
};


enum term_type
{
    Var ,
    Const,
    Apply,
    Quant,
};

typedef enum term_type term_type;

typedef struct term_list term_list;

struct term
{
    term_type type;
    union {
        char *Var;
        struct
        {
            const_type type;
            int content;
        } Const;
        struct
        {
            struct term *left;
            struct term *right;
        } Apply;
        struct
        {
            quant_type type;
            char *var;
            struct term *body;
        } Quant;
    } content;
};


struct term_list
{
    term *element;
    struct term_list *next;
};

typedef struct var_sub
{
    char *var;
    term *sub_term;
} var_sub;

typedef struct var_sub_list
{
    var_sub *cur;
    struct var_sub_list *next;
} var_sub_list;

typedef enum {bool_res, termlist} res_type;
typedef struct{
    res_type type;
    union{
        bool ans;
        term_list* list;
    };
} solve_res;

term *substr_var(char *den, char *src, term *t);
term* substr_term(term* den, char* src, term* t);
bool alpha_equiv(term *t1, term *t2);
term_list *copy_term_list(term_list *list);
term *copy_term(term *t);
void free_term(term *t);
void free_term_list(term_list *list);
#endif