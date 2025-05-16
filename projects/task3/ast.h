typedef enum {false, true} bool;

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
typedef enum const_type const_type;

enum quant_type
{
    Forall,
    Exists
};
typedef enum quant_type quant_type;

enum term_type
{
    Var,
    Const,
    Apply,
    Quant
};
typedef enum term_type term_type;

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
typedef struct term term;

struct term_list
{
    term *element;
    struct term_list *next;
};
typedef struct term_list term_list;

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
    } d;
} solve_res;

typedef struct{
    term *assum;
    term *concl;
} ImplyProp;

/* BEGIN Given Functions */

// malloc 函数，内存均初始为全0
term_list *malloc_term_list();
solve_res *malloc_solve_res();

// 构造函数
ImplyProp *createImplyProp(term *t1, term *t2);

// 深拷贝函数
term *copy_term(term *t);
term_list *copy_term_list(term_list *list);

// free 函数
void free_str(char *s);
void free_imply_prop(ImplyProp *p);
void free_term(term *t);
void free_term_list(term_list *list);

// string 相关函数
char *strdup(const char *s);
int strcmp(const char *s1, const char *s2);

/* END Given Functions */

term *subst_var(char *den, char *src, term *t);
term* subst_term(term* den, char* src, term* t);
bool alpha_equiv(term *t1, term *t2);
