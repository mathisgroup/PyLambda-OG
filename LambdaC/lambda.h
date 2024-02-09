/*
    lambda.h
    
    c 1994 Walter Fontana
 */

#ifndef	__LAMBDA_H
#define	__LAMBDA_H

typedef struct element
  {
    char *symbol;
    int key;
    int next;
  }
element;

typedef struct pair
  {
    char a;
    int b;
  }
pair;

typedef struct heap_node
  {
    int code;
    int op1;
    boolean marker;
    int scope;
    union
      {
	int op2;
	float alt;
      }
    u;
  }
heap_node;

typedef struct flags
  {
    int cycle_limit;
    int space_limit;
    int cycle_limit_hits;
    int space_limit_hits;
    int sum_no_nf_terms;
    int no_nf_term;
    int output_overflow_hits;
    int symbol_table_overflow_hits;
    int output_overflow;
    int symbol_table_overflow;
    int not_free_overflow_hits;
    int not_free_overflow;
    int path_overflow_in_reduce;
    int wrong_renaming;
    int wrong_second_operand_for_arithmetics;
    int wrong_second_operand_for_comparison;
    int wrong_operand_for_pred_succ;
    int wrong_operand_for_zero;
    int wrong_operand_for_null;
    int wrong_operand_for_list_arithmetic;
    int wrong_operand_for_iota;
    int wrong_operand_for_not;
    int wrong_first_operand_for_and_or;
    int wrong_second_operand_for_and_or;
    int wrong_argument_for_map;
    int wrong_operand_for_append;
    int wrong_expr_for_hd_tl;
    int wrong_expr_for_selection;
    int wrong_operator;
  }
flags;

typedef struct parmsLambda	/* parameters */
  {
    int heap_size;		/* size of heap that houses computation */
    int cycle_limit;		/* maximum number of cycles */

    int symbol_table_size;	/* size of symbol table */
    int stack_size;		/* stack size */
    int name_length;		/* max length of identifiers */
    char standard_variable;	/* name of standard variable; e.g 'x' */

    FILE *error_fp;		/* error report */
  }
parmsLambda;

typedef struct interpreter
  {
    parmsLambda *parms;

    heap_node *heap;
    pair *stack;
    element *table;
    flags error;

    char peek;
    char *letters;
    char *numbers;
    char *input_expression;
    char *output_expression;
    char *output_expression_ptr;
    char *current_expression;
    char *new_name;
    char **free_vars;
    int *identifiers;
    int *path;
    int group[98];
    int fresh;
    int root;
    int _free;
    int char_count;
    int n_identifiers;
    int n_free_vars;
    int error_number;
    int errors_occurred;
    int reductions;
    int cycles;
    int standard;
    int scope_offset;
    int garbage_collected;
    int busy;

    /* ---- reduction state */

    int top;
    int sys_var;
    int code;
    int n1;
    int n2;
    int n3;
    int n4;
    int n5;
    int k1;
    int k2;
    int k3;
    int k4;
    int position;
    int rest;
    heap_node *node;
    boolean iterate;
    boolean done;
    boolean changed;
    boolean empty;
    boolean resume;

    /* ---- end of reduction state */
  }
interpreter;

/*----------------------------------------------------------------------------*/

extern interpreter *initialize_lambda (parmsLambda  * Params);
extern void free_interpreter (interpreter * Interp);
extern char *reduce_lambda (char *in, interpreter * Interp);
extern char *standardize (char *expression, interpreter * Interp);
extern char *bind_all_free_vars (char *expression, interpreter * Interp);
extern int  Free_Variables (char *expression, interpreter * Interp);
extern void status (FILE * fp);

#endif /* __LAMBDA_H */
