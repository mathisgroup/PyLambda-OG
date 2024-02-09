/*
    lambda.c 
       
    c 1994 Walter Fontana
 */

/************************************************************************

    Graph based reduction of extended lambda-expressions to normal form. 

*************************************************************************

The reduction machine is based on a Pascal source due to 

                            Gyorgy E. REVESZ

                     IBM T.J.Watson Research Center
                          Yorktown Heights, NY
                   
Translated and rewritten by

                             Walter FONTANA

                              T-13 MS-B213
                     Los Alamos National Laboratory
                          Los Alamos, NM 87545

*************************************************************************/

#include <stdio.h>
#include <math.h>
#include <string.h>
#include <setjmp.h>
#include <sys/types.h>
#include <malloc.h>
#include "utilities.h"
#include "lambda.h"

#define	  HEAD     '^'		/* symbol for head operation */
#define	  TAIL     '~'		/* symbol for tail operation */
#define	  SIZE     2000		/* size of local arrays */
#define	  SMALL    100		/* size of small local arrays */

/*==================================================================*/

PUBLIC interpreter *initialize_lambda (parmsLambda * Params);
PUBLIC void free_interpreter (interpreter * Interp);
PUBLIC char *reduce_lambda (char *in, interpreter * Interp);
PUBLIC char *standardize (char *expression, interpreter * Interp);
PUBLIC char *bind_all_free_vars (char *expression, interpreter * Interp);
PUBLIC int  Free_Variables (char *expression, interpreter * Interp);
PUBLIC void status (FILE * fp);

PRIVATE int locate (char *name);
PRIVATE int hash (char *any);
PRIVATE char get_token (int *n, float *x);
PRIVATE int r_child (int point);
PRIVATE int l_child (int point);
PRIVATE void clear (void);
PRIVATE int garbage (void);
PRIVATE int get_node (void);
PRIVATE void print_expression (int rt);
PRIVATE boolean print_char (int x, int *count);
PRIVATE void print_id (int dummy, int point, int *count);
PRIVATE void make_name (int scpe);
PRIVATE int pop (int *track, int *top, boolean * more, int *count);
PRIVATE void parse (int *rt);
PRIVATE void push (char item, int *top, boolean * ok);
PRIVATE void add_identifier (int n);
PRIVATE boolean not_free (int id, int point);
PRIVATE int back_up (int *top, boolean * move, int *trace);
PRIVATE void recurve (int id, int point);
PRIVATE int reduce (int rt, heap_node * nd);
PRIVATE void store (int index);
PRIVATE void go_back (void);
PRIVATE void alpha (void);
PRIVATE void beta1 (void);
PRIVATE void beta2 (void);
PRIVATE void beta3 (void);
PRIVATE void beta3p (void);
PRIVATE void beta4 (void);
PRIVATE void beta4p (void);
PRIVATE void gamma0 (void);
PRIVATE void gamma1 (void);
PRIVATE void gamma2 (void);
PRIVATE void arithmetics (int which);
PRIVATE void rational (int some, int which);
PRIVATE void relation (int which);
PRIVATE void racomp (int some, int which, boolean * answer, boolean * done);
PRIVATE void unary (int which);
PRIVATE void binary (int which);
PRIVATE int alpha_standardize (int rt);
PRIVATE int silent_pop (int *track, int *top, boolean * more);
PRIVATE void scope (int id, int point, int scope_id);
PRIVATE int free_vars_list (void);
PRIVATE void clear_free_vars_list (int n);
PRIVATE void print_free_vars_list (FILE * fp);
PRIVATE int str_getc (char *string);
PRIVATE void strip (char *string, char *string2);
PRIVATE void err (char *message);

/*==================================================================*/

PRIVATE interpreter *L;

PRIVATE jmp_buf LONGJUMP;
PRIVATE jmp_buf RECOVER;

/*==================================================================*/

PUBLIC interpreter *
initialize_lambda (parmsLambda * Params)
{
  register int i;
  interpreter *Interp;

  Interp = (interpreter *) space (sizeof (interpreter));

  Interp->parms = Params;

  Interp->table = (element *) space (sizeof (element) * (Interp->parms->symbol_table_size + 1));
  for (i = 0; i <= Interp->parms->symbol_table_size; i++)
    {
      Interp->table[i].symbol = (char *) space (sizeof (char) * (Interp->parms->name_length + 2));
      Interp->table[i].key = 0;
      Interp->table[i].next = 0;
    }

  Interp->stack = (pair *) space (sizeof (pair) * (Interp->parms->stack_size + 1));
  Interp->path = (int *) space (sizeof (int) * (Interp->parms->stack_size + 1));
  Interp->identifiers = (int *) space (sizeof (int) * (Interp->parms->symbol_table_size + 1));
  Interp->free_vars = (char **) space (sizeof (char *) * (Interp->parms->symbol_table_size + 1));

  Interp->letters = (char *) space (sizeof (char) * 2 * 28);
  strcpy (Interp->letters, "abcdefghijklmnopqrstuvwxyz$");
  strcat (Interp->letters, "ABCDEFGHIJKLMNOPQRSTUVWXYZ");

  Interp->numbers = (char *) space (sizeof (char) * 11);
  strcpy (Interp->numbers, "0123456789");

  Interp->new_name = (char *) space (sizeof (char) * (Interp->parms->name_length + 1));
  Interp->output_expression = (char *) space (sizeof (char) * (Interp->parms->heap_size + 2));
  Interp->output_expression_ptr = Interp->output_expression;

  for (i = 1; i <= 97; Interp->group[i++] = 0);
  Interp->fresh = 0;

  Interp->heap = (heap_node *) space (sizeof (heap_node) * (Interp->parms->heap_size + 1));

  for (i = 1; i <= Interp->parms->heap_size; i++)
    {
      Interp->heap[i].code = 0;	/* free nodes will be indirection nodes */
      Interp->heap[i].op1 = 0;
      Interp->heap[i].u.op2 = i - 1;
      Interp->heap[i].marker = FALSE;
      Interp->heap[i].scope = 0;
    }

  Interp->_free = Interp->parms->heap_size;
  Interp->garbage_collected = 0;

  Interp->error.output_overflow_hits = 0;
  Interp->error.symbol_table_overflow_hits = 0;
  Interp->error.not_free_overflow_hits = 0;
  Interp->error.cycle_limit_hits = 0;
  Interp->error.space_limit_hits = 0;
  Interp->error.path_overflow_in_reduce = 0;
  Interp->error.sum_no_nf_terms = 0;
  Interp->error.wrong_renaming = 0;
  Interp->error.wrong_second_operand_for_arithmetics = 0;
  Interp->error.wrong_second_operand_for_comparison = 0;
  Interp->error.wrong_operand_for_pred_succ = 0;
  Interp->error.wrong_operand_for_zero = 0;
  Interp->error.wrong_operand_for_null = 0;
  Interp->error.wrong_operand_for_list_arithmetic = 0;
  Interp->error.wrong_operand_for_iota = 0;
  Interp->error.wrong_operand_for_not = 0;
  Interp->error.wrong_first_operand_for_and_or = 0;
  Interp->error.wrong_second_operand_for_and_or = 0;
  Interp->error.wrong_argument_for_map = 0;
  Interp->error.wrong_operand_for_append = 0;
  Interp->error.wrong_expr_for_hd_tl = 0;
  Interp->error.wrong_expr_for_selection = 0;
  Interp->error.wrong_operator = 0;
  Interp->errors_occurred = 0;

  L = Interp;

  Interp->table[locate (" pred      ")].key = 1;
  Interp->table[locate (" zero      ")].key = 2;
  Interp->table[locate (" succ      ")].key = 3;
  Interp->table[locate (" null      ")].key = 4;
  Interp->table[locate (" add       ")].key = 5;
  Interp->table[locate (" sub       ")].key = 6;
  Interp->table[locate (" mult      ")].key = 7;
  Interp->table[locate (" div       ")].key = 8;
  Interp->table[locate (" iota      ")].key = 15;
  Interp->table[locate (" show      ")].key = 16;
  Interp->table[locate (" more      ")].key = 17;
  Interp->table[locate (" not       ")].key = 20;
  Interp->table[locate (" true      ")].key = 21;
  Interp->table[locate (" false     ")].key = 22;
  Interp->table[locate (" and       ")].key = 23;
  Interp->table[locate (" or        ")].key = 24;
  Interp->table[locate (" map       ")].key = 25;
  Interp->table[locate (" append    ")].key = 26;

  L = NULL;

  return Interp;
}

/*==================================================================*/

PUBLIC void
free_interpreter (interpreter * Interp)
{
  register int i;

  for (i = 0; i <= Interp->parms->symbol_table_size; i++)
    free (Interp->table[i].symbol);
  free (Interp->table);
  free (Interp->stack);
  free (Interp->path);
  free (Interp->identifiers);
  free (Interp->free_vars);
  free (Interp->numbers);
  free (Interp->letters);
  free (Interp->new_name);
  free (Interp->heap);
  free (Interp->output_expression);
  free (Interp);
}

/*==================================================================*/

/* 
 * returns normal form, or NULL if reduction was not successful;
 * reduction result is not standardized 
 */

PUBLIC char *
reduce_lambda (char *in, interpreter * Interp)
{
  char *result;
  int rc = 0;
  int number;
  int prefix;
  int expr;
  int body;
  float ratio;

  L = Interp;
  L->busy = 1;

  clear ();

  L->input_expression = in;
  L->current_expression = in;
  L->output_expression[0] = '\0';
  
  if (setjmp (RECOVER))
    {
      L->output_expression[0] = '\0';
      L->busy = 0;
      return NULL;
    }
  
  L->peek = str_getc (L->input_expression);
  body = get_node ();
  L->root = body;

  while (L->peek != '\0')
    {
      if (get_token (&number, &ratio) == 'a')
	{
	  if (strcmp (L->table[number].symbol, " eval      ") == 0)
	    {
	      parse (&body);
	      rc = reduce (L->root, L->heap);
	      if (rc)
		{
		  print_expression (L->root);
		}
	      else
		{
		  L->error.no_nf_term = 1;
		  L->error.sum_no_nf_terms++;
		}
	    }
	  else if (strcmp (L->table[number].symbol, " let       ") == 0)
	    {
	      if (get_token (&number, &ratio) != 'a')
		err ("Identifier missing from let\n");
	      else
		{
		  prefix = get_node ();
		  L->heap[body].op1 = prefix;
		  expr = get_node ();
		  L->heap[body].u.op2 = expr;
		  L->heap[body].code = 2;
		  L->heap[prefix].code = 1;
		  L->heap[prefix].op1 = number;
		  body = get_node ();
		  L->heap[prefix].u.op2 = body;
		  if (get_token (&number, &ratio) != '_')
		    err ("The _ sign is missing from let\n");
		  else
		    {
		      parse (&expr);
		      recurve (L->heap[prefix].op1, expr);
		    }
		}
	    }
	}
      else
	err ("Wrong Command\n");
    }

  L->busy = 0;
  
  if (L->output_expression[0] == '\0')
    return NULL;
    
  result = (char *) space (sizeof (char) * (strlen (L->output_expression) + 1));
  strcpy (result, L->output_expression);
  return result;
}

/*==================================================================*/

/* symbol table */

PRIVATE int
locate (char *name)
{
  int h;
  int p;

  h = hash (name);
  p = L->group[h];

  while (p != 0 && strcmp (L->table[p].symbol, name) != 0)
    p = L->table[p].next;

  if (p == 0)
    {				/* allocate new name */

      if (L->fresh < L->parms->symbol_table_size)
	L->fresh++;
      else
	{
	  L->error.symbol_table_overflow = TRUE;
	  L->error.symbol_table_overflow_hits++;
	  err ("Symbol Table Overflow.\n");
	}
      p = L->fresh;
      strcpy (L->table[p].symbol, name);
      L->table[p].key = 0;
      L->table[p].next = L->group[h];

      L->group[h] = p;
    }
  return p;
}

/*------------------------------------------------------------------*/

PRIVATE int
hash (char *any)
{
  return (any[1] + any[2]) % 97 + 1;
}

/*==================================================================*/

PRIVATE char
get_token (int *n, float *x)
{
  char c;
  int i;
  int j;
  int location;
  char str[SMALL];
  float place;

  *n = 0;
  str[0] = ' ';

  /* skip consecutive blanks, new line chars, and markers */

  while (((L->peek == ' ') || (L->peek == '\n'))
	 && !(L->peek == '\0'))
    L->peek = str_getc (L->input_expression);

  if (strchr (L->letters, L->peek) != NULL)
    {				/* identifier token */
      i = 1;
      while ((strchr (L->letters, L->peek) != NULL)
	     || (strchr (L->numbers, L->peek) != NULL))
	{
	  str[i++] = L->peek;
	  L->peek = str_getc (L->input_expression);
	}
      for (j = i; j <= L->parms->name_length; str[j++] = ' ');
      str[L->parms->name_length + 1] = '\0';
      location = locate (str);
      c = 'a';
      *n = location;
    }				/* end of identifier token */
  else if (strchr (L->numbers, L->peek) != NULL)
    {				/* numeric token */
      c = 'i';			/* integer */
      while (strchr (L->numbers, L->peek) != NULL)
	{
	  *n = 10 * (*n) + (L->peek - '0');
	  L->peek = str_getc (L->input_expression);
	}
      if (L->peek == '.')
	{			/* real */
	  c = 'r';
	  L->peek = str_getc (L->input_expression);
	  *x = *n;
	  place = 1.;
	  while (strchr (L->numbers, L->peek) != NULL)
	    {
	      place /= 10.;
	      *x = (*x) + (L->peek - '0') * place;
	      L->peek = str_getc (L->input_expression);
	    }
	}
    }				/* end of numeric token */
  else
    {				/* other token */
      c = L->peek;
      L->peek = str_getc (L->input_expression);
    }

  if (c == '<')
    {
      if (L->peek == '=')
	{
	  L->peek = str_getc (L->input_expression);
	  *n = 3;
	}
      else if (L->peek == '>')
	{
	  L->peek = str_getc (L->input_expression);
	  *n = 5;
	}
      else
	*n = 1;
    }
  else if (c == '>')
    {
      if (L->peek == '=')
	{
	  L->peek = str_getc (L->input_expression);
	  *n = 4;
	}
      else
	*n = 2;
    }
  return c;
}

/*==================================================================*/

PRIVATE int
r_child (int point)
{
  register int child;

  child = L->heap[point].u.op2;
  while (L->heap[child].code == 0)
    child = L->heap[child].u.op2;
  L->heap[point].u.op2 = child;

  return child;
}

/*==================================================================*/

PRIVATE int
l_child (int point)
{
  register int child;

  child = L->heap[point].op1;
  while (L->heap[child].code == 0)
    child = L->heap[child].u.op2;
  L->heap[point].op1 = child;

  return child;
}

/*==================================================================*/

/* initialization of the heap */

PRIVATE void
clear (void)
{
  int begin;

  L->heap[0].code = 12;		/* NIL code */
  L->heap[0].marker = TRUE;	/* NIL remains marked */
  L->char_count = 0;		/* reset str_getc() char_count */
  L->reductions = 0;		/* reset reduction counter */
  L->cycles = 0;		/* reset cycle counter */
  L->standard = FALSE;
  L->n_identifiers = 0;
  L->error_number = 0;
  L->error.cycle_limit = 0;	/* reset step limit flag */
  L->error.space_limit = 0;	/* reset space limit flag */
  L->error.output_overflow = 0;	/* print expression overflow flag */
  L->error.symbol_table_overflow = 0;	/* symbol table overflow flag */
  L->error.not_free_overflow = 0;	/* not_free() overflow flag */
  L->error.no_nf_term = 0;

  L->output_expression = L->output_expression_ptr;

  /* 
   * if the previous call to lambda did not trigger the garbage collector
   * then we clean up only the used part,
   * else we can't do that efficiently (used blocks may be scattered around).
   */

  if (!L->garbage_collected)
    begin = L->_free;
  else
    begin = 1;

  {
    register int i;		/* very important here: speed! */

    for (i = begin; i <= L->parms->heap_size; i++)
      {
	L->heap[i].code = 0;	/* free nodes will be indirection nodes */
	L->heap[i].op1 = 0;
	L->heap[i].u.op2 = i - 1;
	L->heap[i].marker = FALSE;
	L->heap[i].scope = 0;
      }
  }

  L->_free = L->parms->heap_size;
  L->garbage_collected = 0;
}

/*==================================================================*/

PRIVATE int
garbage (void)
{
  static int track[SIZE + 1];
  int code;
  int point;
  int top;
  int i;
  int stop;
  boolean more;

  L->garbage_collected = 1;	/* set clean-up flag for clear() on next round */

  more = TRUE;
  top = 0;
  stop = 0;
  point = L->root;

  while (more)
    {				/* marking phase */
      code = L->heap[point].code;
      if (code > 3)
	L->heap[point].marker = TRUE;
      if (L->heap[point].marker == TRUE)
	{			/* may be NIL */
	  if (top > 0)
	    point = track[top--];
	  else
	    more = FALSE;
	}
      else
	{
	  L->heap[point].marker = TRUE;
	  if ((code == 2) || (code == 3))
	    {
	      if (top < SIZE)
		track[++top] = r_child (point);
	      else
		{
		  err ("garbage track overflow.\n");
		  more = FALSE;
		  stop = 1;
		}
	      point = l_child (point);
	    }
	  else
	    point = r_child (point);	/* code must be less than 2 */
	}
    }				/* end of marking phase */

  for (i = 1; i <= L->parms->heap_size; i++)
    {
      if (L->heap[i].marker)
	L->heap[i].marker = FALSE;
      else
	{
	  L->heap[i].code = 0;
	  L->heap[i].op1 = 0;
	  L->heap[i].u.op2 = L->_free;
	  L->_free = i;
	}
    }
  return stop;
}

/*==================================================================*/

PRIVATE int
get_node (void)
{
  int gn;

  if (L->_free == 0)		/* corrected 08/08/92  WF   */
    if (garbage () == 1)
      {
	err ("garbage collection error.\n");
	return FALSE;
      }
  if (L->_free == 0)
    {
      L->iterate = FALSE;
      if (!L->error.space_limit)
	L->error.space_limit_hits += 1;
      L->error.space_limit = TRUE;
      err ("ran out of space.\n");
      return FALSE;
    }
  else
    {
      gn = L->_free;		/* node has code = 0 and op1 = 0 */
      L->_free = L->heap[L->_free].u.op2;
      return gn;
    }
}

/*==================================================================*/

PRIVATE void
print_expression (int rt)
{
  static int track[SIZE + 1];
  int point;
  int top;
  int count;
  int next;
  int i;
  char num[20];
  boolean more;

  count = 0;
  point = rt;
  top = 0;
  more = TRUE;

  if (L->standard)
    L->scope_offset = 0;

  while (more)
    {
      switch (L->heap[point].code)
	{

	case 0:		/* ---- indirection ---- */

	  point = L->heap[point].u.op2;
	  break;

	case 1:		/* ---- abstraction ---- */

	  /* if (count > (78 - L->parms->name_length)) count = 80; */
	  print_char ('\\', &count);
	  next = L->heap[point].op1;
	  print_id (next, point, &count);
	  print_char ('.', &count);
	  point = L->heap[point].u.op2;
	  break;

	case 2:		/* ---- application ---- */

	  if (top < SIZE)
	    track[++top] = L->heap[point].u.op2;
	  else
	    {
	      more = FALSE;
	      err ("print_expression track overflow.\n");
	    }
	  print_char ('(', &count);
	  point = L->heap[point].op1;
	  break;

	case 3:
	case 13:		/* ---- list structure ---- */

	  if (L->heap[point].code == 3)
	    print_char ('[', &count);
	  else
	    {
	      print_char (',', &count);
	      L->heap[point].code = 3;
	    }

	  if (top < SIZE)
	    {
	      top++;
	      next = r_child (point);	/* needed here */
	      track[top] = next;
	      if ((L->heap[next].code == 3) || (L->heap[next].code == 4))
		L->heap[next].code = L->heap[next].code + 10;
	    }
	  else
	    {
	      more = FALSE;
	      err ("print_expression track overflow.\n");
	    }
	  point = L->heap[point].op1;
	  break;

	case 4:
	case 14:		/* ---- empty list or end of list ---- */

	  if (L->heap[point].code == 4)
	    print_char ('[', &count);
	  else
	    L->heap[point].code = 4;

	  print_char (']', &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 5:		/* ---- Y combinator ---- */

	  print_char ('?', &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 6:		/* ---- head of list ---- */

	  print_char (HEAD, &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 7:		/* ---- tail of list ---- */

	  print_char (TAIL, &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 8:		/* ---- cons operator ---- */

	  print_char ('&', &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 9:		/* ---- integer ---- */

	  sprintf (num, "%d", L->heap[point].u.op2);
	  for (i = 0; num[i] != '\0'; i++)
	    print_char (num[i], &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 10:		/* ---- real ---- */

	  sprintf (num, "%5.5f", L->heap[point].u.alt);
	  for (i = 0; num[i] != '\0'; i++)
	    print_char (num[i], &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 11:		/* ---- variable or key word ---- */

	  next = L->heap[point].op1;
	  print_id (next, point, &count);
	  point = pop (track, &top, &more, &count);
	  break;

	case 15:		/* ---- arithmetic operator ---- */

	  switch (L->heap[point].u.op2)
	    {

	    case 1:
	      print_char ('+', &count);
	      break;
	    case 2:
	      print_char ('-', &count);
	      break;
	    case 3:
	      print_char ('*', &count);
	      break;
	    case 4:
	      print_char ('/', &count);
	      break;

	    }
	  point = pop (track, &top, &more, &count);
	  break;

	case 16:		/* ---- relational operator ---- */

	  switch (L->heap[point].u.op2)
	    {

	    case 0:
	      print_char ('=', &count);
	      break;
	    case 1:
	      print_char ('<', &count);
	      break;
	    case 2:
	      print_char ('>', &count);
	      break;
	    case 3:
	      print_char ('<', &count);
	      print_char ('=', &count);
	      break;
	    case 4:
	      print_char ('>', &count);
	      print_char ('=', &count);
	      break;

	    case 5:
	      print_char ('<', &count);
	      print_char ('>', &count);
	      break;
	    }
	  point = pop (track, &top, &more, &count);
	  break;

	default:		/* ---- renaming prefix ---- */

	  if (L->heap[point].code < 0)
	    {
	      print_char ('{', &count);
	      print_id (L->heap[point].code, point, &count);
	      print_char ('/', &count);
	      print_id (L->heap[point].op1, point, &count);
	      print_char ('}', &count);
	      point = r_child (point);
	    }
	  else
	    {
	      err ("\n");
	      err ("Wrong Expression!\n");
	      more = FALSE;
	    }
	  break;

	}			/* switch */
    }				/* while */

  L->output_expression[count] = '\0';
}

/*------------------------------------------------------------------*/

PRIVATE boolean
print_char (int x, int *count)
{
  if (*count > L->parms->heap_size)
    {
      L->error.output_overflow = TRUE;
      err ("print overflow.\n");
      return FALSE;
    }
  L->output_expression[*count] = x;
  (*count)++;
  return TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
print_id (int dummy, int point, int *count)
{
  char name[SMALL], num[20];
  int index;
  
  if (dummy > 0)
    {

      if (L->standard && L->heap[point].scope != 0)
	{
	  make_name (L->heap[point].scope);
	  for (index = 0; index < strlen (L->new_name); index++)
	    print_char (L->new_name[index], count);
	}
      else
	{
	  strcpy (name, L->table[dummy].symbol);
	  for (index = 1; index <= L->parms->name_length; index++)
	    {
	      if (name[index] != ' ')
		print_char (name[index], count);
	    }
	}
    }
  else
    {
      print_char ('$', count);
      sprintf (num, "%d", -dummy);
      for (index = 0; num[index] != '\0'; index++)
	print_char (num[index], count);
    }
}

/*------------------------------------------------------------------*/

PRIVATE void
make_name (int scpe)
{
  int i;
  int redo;
  char numb[10];

  do
    {
      int_to_char (scpe + L->scope_offset, numb);
      L->new_name[0] = L->parms->standard_variable;
      L->new_name[1] = '\0';
      strcat (L->new_name, numb);
      /* check if new composite name is free */
      redo = 0;
      for (i = 1; i <= L->n_free_vars; i++)
	{
	  if (strcmp (L->new_name, L->free_vars[i]) == 0)
	    {
	      redo = 1;
	      L->scope_offset++;
	      break;
	    }
	}
    }
  while (redo);
}

/*------------------------------------------------------------------*/

PRIVATE int
pop (int *track, int *top, boolean * more, int *count)
{
  int i;

  if (*top > 0)
    {
      i = track[(*top)--];
      if ((L->heap[i].code != 13) && (L->heap[i].code != 14))
	print_char (')', count);
      return i;
    }
  else
    {
      *more = FALSE;
      return 0;
    }
}

/*==================================================================*/

PRIVATE void
parse (int *rt)
{
  char ch;
  int whole;
  int k;
  int i;			/* top of the parser stack */
  float decimal;
  boolean ok;

  i = 1;
  ok = TRUE;
  L->stack[i].a = 'E';
  L->stack[i].b = *rt;
  ch = get_token (&whole, &decimal);

  while ((ch != ' ') && (ch != ';') && ok)
    {

      switch (L->stack[i].a)
	{

	case ')':

	  if (ch == ')')
	    i--;
	  else
	    {
	      ok = FALSE;
	      err ("Error )\n");
	    }
	  break;

	case ']':		/* end of list */

	  if (ch == ']')
	    {
	      L->heap[L->stack[i].b].code = 4;
	      i--;
	    }
	  else if (ch == ',')
	    {
	      k = L->stack[i].b;
	      L->heap[k].op1 = get_node ();
	      L->heap[k].u.op2 = get_node ();
	      L->heap[k].code = 3;
	      L->stack[i].b = L->heap[k].u.op2;
	      push ('E', &i, &ok);
	      L->stack[i].b = L->heap[k].op1;
	    }
	  else
	    {
	      ok = FALSE;
	      err ("Invalid symbol for ]\n");
	    }
	  break;

	case 'N':
	case 'E':

	  if ((L->stack[i].a == 'N') && (ch == ']'))
	    {

	      /* empty list */
	      L->heap[k].code = 4;
	      i -= 2;
	    }
	  else
	    {
	      k = L->stack[i--].b;	/* speculative pop-ing */

	      switch (ch)
		{

		case '[':

		  L->heap[k].u.op2 = get_node ();
		  L->heap[k].op1 = get_node ();
		  L->heap[k].code = 3;
		  push (']', &i, &ok);
		  L->stack[i].b = L->heap[k].u.op2;
		  push ('N', &i, &ok);
		  L->stack[i].b = L->heap[k].op1;
		  break;

		case '\\':	/* \ prefix */

		  ch = get_token (&whole, &decimal);
		  if (ch != 'a')
		    err ("Error \\ \n");
		  else
		    {
		      i++;	/* undo pop */
		      L->heap[k].code = 1;
		      L->heap[k].op1 = whole;
		      L->heap[k].u.op2 = get_node ();
		      L->stack[i].b = L->heap[k].u.op2;
		      add_identifier (whole);
		      ch = get_token (&whole, &decimal);
		      if (ch != '.')
			err ("dot is missing\n");
		    }
		  break;

		case '(':

		  i++;		/* undo pop */
		  L->heap[k].op1 = get_node ();
		  L->heap[k].u.op2 = get_node ();
		  L->heap[k].code = 2;
		  L->stack[i].b = L->heap[k].u.op2;
		  push (')', &i, &ok);
		  push ('E', &i, &ok);
		  L->stack[i].b = L->heap[k].op1;
		  break;

		case 'a':	/* identifier */

		  L->heap[k].code = 11;
		  L->heap[k].op1 = whole;
		  L->heap[k].u.op2 = L->table[whole].key;
		  if (L->table[whole].key == 0)
		    add_identifier (whole);
		  break;

		case 'i':	/* integer */

		  L->heap[k].code = 9;
		  L->heap[k].u.op2 = whole;
		  break;

		case 'r':	/* real constant */

		  L->heap[k].code = 10;
		  L->heap[k].u.alt = decimal;
		  break;

		case '?':

		  L->heap[k].code = 5;
		  break;

		case '^':

		  L->heap[k].code = 6;
		  break;

		case '~':

		  L->heap[k].code = 7;
		  break;

		case '&':

		  L->heap[k].code = 8;
		  break;

		case '+':

		  L->heap[k].code = 15;
		  L->heap[k].u.op2 = 1;
		  break;

		case '-':

		  L->heap[k].code = 15;
		  L->heap[k].u.op2 = 2;
		  break;

		case '*':

		  L->heap[k].code = 15;
		  L->heap[k].u.op2 = 3;
		  break;

		case '/':

		  L->heap[k].code = 15;
		  L->heap[k].u.op2 = 4;
		  break;

		case '<':
		case '=':
		case '>':

		  L->heap[k].code = 16;
		  L->heap[k].u.op2 = whole;
		  break;

		default:

		  ok = FALSE;
		  err ("Undefined Symbol\n");
		  break;
		}		/* switch on ch */
	    }
	  break;

	default:

	  break;

	}			/* switch on L->stack[i].a */

      ch = get_token (&whole, &decimal);

    }				/* while */

  if ((!ok) || (ch != ';'))
    err ("Illegal Expression\n");
}

/*------------------------------------------------------------------*/

PRIVATE void
push (char item, int *top, boolean * ok)
{
  if (*top < L->parms->stack_size)
    L->stack[++(*top)].a = item;
  else
    {
      *ok = FALSE;
      err ("parser stack overflow.\n");
    }
}

/*------------------------------------------------------------------*/

PRIVATE void
add_identifier (int n)
{
  register int i;

  for (i = 1; i <= L->n_identifiers; i++)
    if (L->identifiers[i] == n)
      return;
  L->identifiers[++L->n_identifiers] = n;
}

/*==================================================================*/

/*  
 * renaming nodes should not occur in the graph when not_free() gets
 * executed.
 */

PRIVATE boolean
not_free (int id, int point)
{
  static int trace[SIZE + 1];
  boolean move;
  boolean nf;
  int top;
  int self;

  nf = TRUE;
  move = TRUE;
  top = 0;
  self = point;

  while (move)
    {
      if (L->heap[point].marker)
	point = back_up (&top, &move, trace);
      else
	{
	  L->heap[point].marker = TRUE;

	  switch (L->heap[point].code)
	    {

	    case 0:		/* ---- indirection ---- */

	      point = r_child (point);
	      break;

	    case 1:		/* ---- abstraction ---- */

	      if (id == L->heap[point].op1)
		point = back_up (&top, &move, trace);
	      else
		point = r_child (point);
	      break;

	    case 2:
	    case 3:		/* ---- application or list ---- */

	      if (top < SIZE)
		trace[++top] = r_child (point);
	      else
		{
		  move = FALSE;
		  err ("not_free(): trace overflow.\n");
		  longjmp (LONGJUMP, 1);
		}
	      point = l_child (point);
	      break;

	    case 11:		/* ---- variable ---- */

	      if (id == L->heap[point].op1)
		{
		  nf = FALSE;
		  move = FALSE;
		}
	      else
		point = back_up (&top, &move, trace);
	      break;

	    default:

	      /*
	       * if (L->heap[point].code < 0) point = r_child(point);
	       * else 
	       */

	      point = back_up (&top, &move, trace);
	      break;

	    }			/* switch */
	}			/* else */
    }				/* while */

  top = 0;			/* restore the marker */
  point = self;
  move = TRUE;

  while (move)
    {
      if (!L->heap[point].marker)
	point = back_up (&top, &move, trace);
      else
	{
	  L->heap[point].marker = FALSE;

	  switch (L->heap[point].code)
	    {

	    case 0:		/* ---- indirection ---- */

	      point = r_child (point);
	      break;

	    case 1:		/* ---- abstraction ---- */

	      if (id == L->heap[point].op1)
		point = back_up (&top, &move, trace);
	      else
		point = r_child (point);
	      break;

	    case 2:
	    case 3:		/* ---- application or list ---- */

	      trace[++top] = r_child (point);
	      point = l_child (point);
	      break;

	    case 11:		/* ---- variable ---- */

	      if (id == L->heap[point].op1)
		move = FALSE;
	      else
		point = back_up (&top, &move, trace);
	      break;

	    default:

	      /*
	       * if (L->heap[point].code < 0) point = r_child(point);
	       * else 
	       */

	      point = back_up (&top, &move, trace);
	      break;

	    }			/* switch */
	}			/* else */
    }				/* while */

  return nf;
}

/*------------------------------------------------------------------*/

PRIVATE int
back_up (int *top, boolean * move, int *trace)
{
  int bu;

  if (*top > 0)
    {
      bu = trace[*top];
      (*top)--;
      return bu;
    }
  else
    *move = FALSE;
}

/*==================================================================*/

/*  
 * renaming nodes should not occur in the graph when not_free() gets
 * executed.
 */

PRIVATE void
recurve (int id, int point)
{
  static int trace[SIZE + 1];
  boolean move;
  int top;
  int self;

  move = TRUE;
  top = 0;
  self = point;

  while (move)
    {
      if (L->heap[point].marker)
	point = back_up (&top, &move, trace);
      else
	{
	  L->heap[point].marker = TRUE;

	  switch (L->heap[point].code)
	    {

	    case 0:		/* ---- indirection ---- */

	      point = r_child (point);
	      break;

	    case 1:		/* ---- abstraction ---- */

	      if (id == L->heap[point].op1)
		point = back_up (&top, &move, trace);
	      else
		point = r_child (point);
	      break;

	    case 2:
	    case 3:		/* ---- application or list ---- */

	      if (top < SIZE)
		trace[++top] = r_child (point);
	      else
		{
		  move = FALSE;
		  err ("recurve(): trace overflow.\n");
		}
	      point = l_child (point);
	      break;

	    case 11:		/* ---- variable ---- */

	      if (id == L->heap[point].op1)
		{
		  L->heap[point].code = 0;
		  L->heap[point].u.op2 = self;
		}
	      else
		point = back_up (&top, &move, trace);
	      break;

	    default:

	      point = back_up (&top, &move, trace);
	      break;

	    }			/* switch */
	}			/* else */
    }				/* while */

  top = 0;			/* restore the marker */
  point = self;
  move = TRUE;

  while (move)
    {
      if (!L->heap[point].marker)
	point = back_up (&top, &move, trace);
      else
	{
	  L->heap[point].marker = FALSE;

	  switch (L->heap[point].code)
	    {

	    case 0:		/* ---- indirection ---- */

	      point = r_child (point);
	      break;

	    case 1:		/* ---- abstraction ---- */

	      if (id == L->heap[point].op1)
		point = back_up (&top, &move, trace);
	      else
		point = r_child (point);
	      break;

	    case 2:
	    case 3:		/* ---- application or list ---- */

	      trace[++top] = r_child (point);
	      point = l_child (point);
	      break;

	    default:

	      point = back_up (&top, &move, trace);
	      break;

	    }			/* switch */
	}			/* else */
    }				/* while */
}

/*==================================================================*/

PRIVATE int
reduce (int rt, heap_node * nd)
{

  if (!L->resume)
    {
      L->done = FALSE;
      L->node = nd;
      L->sys_var = 0;
      L->top = 0;
      L->iterate = TRUE;
      L->changed = TRUE;
      L->n1 = rt;
    }

  if (L->error.symbol_table_overflow)
    return FALSE;

  /* abort reduction in case of overflow in not_free() */

  if (setjmp (LONGJUMP))
    {
      L->iterate = FALSE;
      L->error.not_free_overflow_hits++;
      L->error.not_free_overflow = TRUE;
    }

  while (L->iterate)
    {

      if (L->cycles >= L->parms->cycle_limit)
	{
	  L->error.cycle_limit_hits += 1;
	  L->error.cycle_limit = TRUE;
	  return FALSE;
	}

      L->cycles++;
      L->reductions++;

      switch (L->node[L->n1].code)
	{

	case 0:		/* ---- indirection ---- */

	  L->reductions--;

	  L->n1 = r_child (L->n1);
	  break;

	case 1:		/* ---- abstraction ---- */

	  L->reductions--;

	  L->n2 = r_child (L->n1);
	  if (L->node[L->n2].code == 3)
	    {
	      gamma2 ();
	    }
	  else if (L->node[L->n2].code == 4)
	    gamma0 ();
	  else
	    L->n1 = L->n2;
	  break;

	case 2:		/* ---- application ---- */

	  L->n2 = l_child (L->n1);
	  L->n4 = r_child (L->n1);

	  switch (L->node[L->n2].code)
	    {

	    case 1:		/* ---- beta-redex ---- */

	      L->n3 = r_child (L->n2);

	      switch (L->node[L->n3].code)
		{

		case 1:

		  if (not_free (L->node[L->n2].op1, L->n3))
		    beta2 ();
		  else if (not_free (L->node[L->n3].op1, L->n4))
		    {
		      beta3p ();
		    }
		  else
		    {
		      beta3 ();
		    }
		  break;

		case 2:

		  if (not_free (L->node[L->n2].op1, l_child (L->n3)))
		    {
		      if (not_free (L->node[L->n2].op1, r_child (L->n3)))
			beta2 ();
		      else
			{
			  beta4p ();
			}
		    }
		  else
		    {
		      beta4 ();
		    }
		  break;

		case 11:

		  if (L->node[L->n2].op1 != L->node[L->n3].op1)
		    beta2 ();
		  else
		    beta1 ();
		  break;

		default:

		  if (not_free (L->node[L->n2].op1, L->n3))
		    beta2 ();
		  else
		    {
		      L->reductions--;
		      store (L->n1);
		      L->n1 = L->n2;
		    }
		  break;
		}
	      break;

	    case 2:		/* ---- double application ---- */

	      L->n3 = l_child (L->n2);

	      switch (L->node[L->n3].code)
		{

		case 8:	/* ---- cons operator & ---- */

		  L->node[L->n1].code = 3;
		  L->node[L->n1].op1 = r_child (L->n2);
		  L->changed = TRUE;
		  go_back ();
		  break;

		case 11:	/* ---- binary operator ---- */

		  if (L->node[L->n3].u.op2 > 20)
		    {
		      binary (L->node[L->n3].u.op2);
		    }
		  else
		    {
		      L->reductions--;
		      store (L->n1);
		      L->n1 = L->n2;
		    }
		  break;

		case 15:	/* ---- {+, -, *, or /} ---- */

		  arithmetics (L->node[L->n3].u.op2);
		  break;

		case 16:	/* ---- {=, <, >, <=, >=, <>} ---- */

		  relation (L->node[L->n3].u.op2);
		  break;

		default:

		  L->reductions--;
		  store (L->n1);
		  L->n1 = L->n2;
		  break;
		}
	      break;

	    case 3:

	      gamma1 ();
	      break;

	    case 4:

	      gamma0 ();
	      break;

	    case 5:		/* ---- Y combinator ---- */

	      L->k1 = get_node ();
	      L->node[L->k1].code = 2;
	      L->node[L->k1].op1 = L->n2;
	      L->node[L->k1].u.op2 = L->n4;
	      L->node[L->n1].op1 = L->n4;
	      L->node[L->n1].u.op2 = L->k1;
	      break;

	    case 6:
	    case 7:		/* ---- head or tail ---- */

	      if (L->node[L->n4].code == 4)
		gamma0 ();
	      else if (L->node[L->n4].code == 3)
		{
		  L->node[L->n1].code = 0;
		  if (L->node[L->n2].code == 6)
		    L->node[L->n1].u.op2 = l_child (L->n4);
		  else
		    L->node[L->n1].u.op2 = r_child (L->n4);
		  L->changed = TRUE;
		  go_back ();
		}
	      else if (L->node[L->n4].code < 3)
		{
		  L->reductions--;
		  store (L->n1);
		  L->n1 = L->n4;
		}
	      else
		{
		  L->iterate = FALSE;
		  L->error.wrong_expr_for_hd_tl += 1;
		  err ("Wrong Expression for Head/Tail\n");
		}
	      break;

	    case 9:		/* ---- select operation ---- */

	      if (L->node[L->n4].code == 3)
		{
		  if (L->node[L->n2].u.op2 == 1)
		    {
		      L->node[L->n1].code = 0;
		      L->node[L->n1].op1 = 0;
		      L->node[L->n1].u.op2 = l_child (L->n4);
		      L->changed = TRUE;
		      go_back ();
		    }
		  else if (L->node[L->n2].u.op2 > 1)
		    {
		      L->position = L->node[L->n2].u.op2 - 1;
		      L->rest = r_child (L->n4);
		      while ((L->position > 1) && (L->node[L->rest].code == 3))
			{
			  L->position--;
			  L->rest = r_child (L->rest);
			}
		      L->k1 = get_node ();
		      L->node[L->k1].code = 9;
		      L->node[L->k1].u.op2 = L->position;
		      L->node[L->k1].op1 = 0;
		      L->node[L->n1].op1 = L->k1;
		      L->node[L->n1].u.op2 = L->rest;
		    }
		}
	      else if (L->node[L->n4].code < 3)
		{
		  L->reductions--;
		  store (L->n1);
		  L->n1 = L->n4;
		}
	      else
		{
		  L->iterate = FALSE;
		  L->error.wrong_expr_for_selection += 1;
		  err ("Wrong Expression for Selection\n");
		}
	      break;

	    case 11:

	      if ((L->node[L->n2].op1 > 0) && (L->node[L->n2].u.op2 > 0))
		{
		  if (L->node[L->n2].u.op2 < 21)
		    {
		      unary (L->node[L->n2].u.op2);
		    }
		  else
		    {
		      L->reductions--;
		      go_back ();	/* binary operator */
		      if (L->empty)
			L->n1 = L->n4;
		    }
		}
	      else
		{
		  L->reductions--;
		  L->n1 = L->n4;
		}
	      break;

	    case 8:
	    case 15:
	    case 16:

	      L->reductions--;
	      go_back ();
	      if (L->empty)
		L->n1 = L->n4;
	      break;

	    default:

	      L->iterate = FALSE;
	      L->error.wrong_operator += 1;
	      err ("Wrong Operator\n");
	      break;
	    }
	  break;		/* end of application */

	case 3:		/* ---- list structure ---- */

	  L->reductions--;
	  store (L->n1);
	  L->n1 = l_child (L->n1);
	  break;

	default:

	  if (L->node[L->n1].code < 0)
	    {
	      alpha ();		/* renaming */
	    }
	  else
	    {
	      L->reductions--;
	      go_back ();
	      if (L->empty)
		{
		  L->iterate = FALSE;
		  L->done = TRUE;
		}
	      else if (L->changed)
		L->changed = FALSE;
	      else
		L->n1 = r_child (L->n1);
	    }
	  break;
	}

      /* you can exit reduce here after setting L->resume = 1
       * to enable continuation anytime by calling reduce again */

    }				/* while */

  L->resume = 0;

  if (L->done)
    return TRUE;
  else
    return FALSE;
}

/*------------------------------------------------------------------*/

PRIVATE void
store (int index)
{
  if (L->top < L->parms->stack_size)
    L->path[++L->top] = index;
  else
    {
      L->iterate = FALSE;
      L->error.path_overflow_in_reduce += 1;
      err ("Path Overflow in Reduce.\n");
    }
}

/*------------------------------------------------------------------*/

PRIVATE void
go_back (void)
{
  if (L->top > 0)
    {
      L->n1 = L->path[L->top--];
      L->empty = FALSE;
    }
  else
    L->empty = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
alpha (void)
{
  L->n2 = r_child (L->n1);
  if (not_free (L->node[L->n1].op1, L->n2))
    {				/* alpha2 */
      L->node[L->n1].code = 0;
      go_back ();
      if (L->empty)
	{
	  L->iterate = FALSE;
	  L->error.wrong_renaming += 1;
	  err ("Wrong Renaming\n");
	}
    }
  else
    {

      switch (L->node[L->n2].code)
	{
	case 1:		/* alpha3 */

	  L->k1 = get_node ();
	  L->node[L->k1].code = L->node[L->n1].code;
	  L->node[L->k1].op1 = L->node[L->n1].op1;
	  L->node[L->k1].u.op2 = r_child (L->n2);
	  L->node[L->n1].code = 1;
	  L->node[L->n1].op1 = L->node[L->n2].op1;
	  L->node[L->n1].u.op2 = L->k1;
	  L->n1 = L->k1;
	  break;

	case 2:
	case 3:		/* alpha4 and alpha5 */

	  L->k1 = get_node ();
	  L->node[L->k1].code = L->node[L->n1].code;
	  L->node[L->k1].op1 = L->node[L->n1].op1;
	  L->node[L->k1].u.op2 = l_child (L->n2);
	  L->node[L->n1].code = L->node[L->n2].code;
	  L->node[L->n1].op1 = L->k1;
	  L->k2 = get_node ();
	  L->node[L->k2].code = L->node[L->k1].code;
	  L->node[L->k2].op1 = L->node[L->k1].op1;
	  L->node[L->k2].u.op2 = r_child (L->n2);
	  L->node[L->n1].u.op2 = L->k2;
	  store (L->k2);
	  L->n1 = L->k1;
	  break;

	case 11:		/* alpha1 */

	  L->node[L->n1].op1 = L->node[L->n1].code;
	  L->node[L->n1].code = 11;
	  L->node[L->n1].u.op2 = 0;
	  go_back ();
	  if (L->empty)
	    {
	      L->iterate = FALSE;
	      L->error.wrong_renaming += 1;
	      err ("Wrong Renaming\n");
	    }
	  break;

	}			/* switch */
    }
}

/*------------------------------------------------------------------*/

PRIVATE void
beta1 (void)
{
  L->node[L->n1].code = 0;
  L->changed = TRUE;
  go_back ();
}

/*------------------------------------------------------------------*/

PRIVATE void
beta2 (void)
{
  L->node[L->n1].code = 0;
  L->node[L->n1].u.op2 = L->n3;
  L->changed = TRUE;
  go_back ();
}

/*------------------------------------------------------------------*/

PRIVATE void
beta3 (void)
{
  L->k1 = get_node ();
  L->node[L->k1].code = 2;
  L->node[L->k1].op1 = L->n2;	/* temporary */
  L->node[L->k1].u.op2 = L->n4;
  L->sys_var--;
  L->node[L->n1].code = 1;
  L->node[L->n1].op1 = L->sys_var;
  L->node[L->n1].u.op2 = L->k1;
  L->k2 = get_node ();
  L->node[L->k2].code = 1;
  L->node[L->k2].op1 = L->node[L->n2].op1;
  L->node[L->k2].u.op2 = L->n3;	/* temporary */
  L->node[L->k1].op1 = L->k2;
  L->k3 = get_node ();
  L->node[L->k3].code = L->sys_var;
  L->node[L->k3].op1 = L->node[L->n3].op1;
  L->node[L->k3].u.op2 = r_child (L->n3);
  L->node[L->k2].u.op2 = L->k3;
  store (L->k1);
  L->n1 = L->k3;
  L->changed = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
beta3p (void)
{
  L->k1 = get_node ();
  L->node[L->k1].code = 2;
  L->node[L->k1].op1 = L->n2;	/* temporary */
  L->node[L->k1].u.op2 = L->n4;
  L->node[L->n1].code = 1;
  L->node[L->n1].op1 = L->node[L->n3].op1;
  L->node[L->n1].u.op2 = L->k1;
  L->k2 = get_node ();
  L->node[L->k2].code = 1;
  L->node[L->k2].op1 = L->node[L->n2].op1;
  L->node[L->k2].u.op2 = r_child (L->n3);
  L->node[L->k1].op1 = L->k2;
  L->n1 = L->k1;
  L->changed = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
beta4 (void)
{
  L->k1 = get_node ();
  L->node[L->k1].code = 2;
  L->node[L->k1].op1 = L->n2;	/* temporary */
  L->node[L->k1].u.op2 = L->n4;
  L->node[L->n1].op1 = L->k1;
  L->k2 = get_node ();
  L->node[L->k2].code = 2;
  L->node[L->k2].op1 = L->n2;	/* temporary */
  L->node[L->k2].u.op2 = L->n4;
  L->node[L->n1].u.op2 = L->k2;
  L->k3 = get_node ();
  L->node[L->k3].code = 1;
  L->node[L->k3].op1 = L->node[L->n2].op1;
  L->node[L->k3].u.op2 = l_child (L->n3);
  L->node[L->k1].op1 = L->k3;
  L->k4 = get_node ();
  L->node[L->k4].code = 1;
  L->node[L->k4].op1 = L->node[L->n2].op1;
  L->node[L->k4].u.op2 = r_child (L->n3);
  L->node[L->k2].op1 = L->k4;
  go_back ();

  if (L->empty)
    {
      store (L->n1);
      L->n1 = L->k1;
    }
  L->changed = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
beta4p (void)
{
  L->k1 = get_node ();
  L->node[L->k1].code = 2;
  L->node[L->k1].op1 = L->n2;	/* temporary */
  L->node[L->k1].u.op2 = L->n4;
  L->node[L->n1].op1 = l_child (L->n3);
  L->node[L->n1].u.op2 = L->k1;
  L->k2 = get_node ();
  L->node[L->k2].code = 1;
  L->node[L->k2].op1 = L->node[L->n2].op1;
  L->node[L->k2].u.op2 = r_child (L->n3);
  L->node[L->k1].op1 = L->k2;
  go_back ();
  L->changed = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
gamma0 (void)
{
  L->node[L->n1].code = 4;
  L->changed = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
gamma1 (void)
{
  L->node[L->n1].code = 3;
  L->k1 = get_node ();
  L->node[L->k1].code = 2;
  L->node[L->k1].op1 = l_child (L->n2);
  L->node[L->k1].u.op2 = L->n2;	/* temporary */
  L->node[L->n1].op1 = L->k1;
  L->k2 = get_node ();
  L->node[L->k2].code = 2;
  L->node[L->k2].op1 = r_child (L->n2);
  L->node[L->k2].u.op2 = L->n4;
  L->node[L->n1].u.op2 = L->k2;
  L->node[L->k1].u.op2 = L->n4;
  go_back ();
  L->changed = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
gamma2 (void)
{
  L->node[L->n1].code = 3;
  L->k1 = get_node ();
  L->node[L->k1].code = 1;
  L->node[L->k1].op1 = L->node[L->n1].op1;
  L->node[L->k1].u.op2 = l_child (L->n2);
  L->node[L->n1].op1 = L->k1;
  L->k2 = get_node ();
  L->node[L->k2].code = 1;
  L->node[L->k2].op1 = L->node[L->k1].op1;
  L->node[L->k2].u.op2 = r_child (L->n2);
  L->node[L->n1].u.op2 = L->k2;
  go_back ();
  L->changed = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
arithmetics (int which)
{
  L->n5 = r_child (L->n2);

  if (L->node[L->n5].code == 9)
    {
      if (L->node[L->n4].code == 9)
	{
	  L->node[L->n1].code = 9;

	  switch (which)
	    {

	    case 1:
	      L->node[L->n1].u.op2 = (L->node[L->n5].u.op2 + L->node[L->n4].u.op2);
	      break;
	    case 2:
	      L->node[L->n1].u.op2 = (L->node[L->n5].u.op2 - L->node[L->n4].u.op2);
	      break;
	    case 3:
	      L->node[L->n1].u.op2 = (L->node[L->n5].u.op2 * L->node[L->n4].u.op2);
	      break;
	    case 4:
	      L->node[L->n1].u.op2 = (L->node[L->n5].u.op2 / L->node[L->n4].u.op2);
	      break;
	    }
	  L->changed = TRUE;	/* L->n1 becomes leaf node */
	}
      else if (L->node[L->n4].code == 10)
	rational (1, which);
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_second_operand_for_arithmetics += 1;
	  err ("Wrong Second Operand for Arithmetics\n");
	}
    }
  else if (L->node[L->n5].code == 10)
    {
      if (L->node[L->n4].code == 9)
	rational (2, which);
      else if (L->node[L->n4].code == 10)
	rational (3, which);
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_second_operand_for_arithmetics += 1;
	  err ("Wrong Second Operand for Arithmetics\n");
	}
    }
  else if (L->node[L->n5].code == 2)
    {
      store (L->n1);
      L->n1 = L->n5;
    }
  else
    {
      L->iterate = FALSE;
      L->error.wrong_second_operand_for_arithmetics += 1;
      err ("Wrong Second Operand for Arithmetics\n");
    }
}

/*------------------------------------------------------------------*/

PRIVATE void
rational (int some, int which)
{
  float x;
  float y;

  L->node[L->n1].code = 10;

  switch (some)
    {

    case 1:

      x = L->node[L->n5].u.op2;
      y = L->node[L->n4].u.alt;
      break;

    case 2:

      x = L->node[L->n5].u.alt;
      y = L->node[L->n4].u.op2;
      break;

    case 3:

      x = L->node[L->n5].u.alt;
      y = L->node[L->n4].u.alt;
      break;
    }
  switch (which)
    {

    case 1:
      L->node[L->n1].u.alt = (x + y);
      break;
    case 2:
      L->node[L->n1].u.alt = (x - y);
      break;
    case 3:
      L->node[L->n1].u.alt = (x * y);
      break;
    case 4:
      L->node[L->n1].u.alt = (x / y);
      break;
    }
  L->changed = TRUE;		/* L->n1 becomes a leaf node */
}

/*------------------------------------------------------------------*/

PRIVATE void
relation (int which)
{
  boolean answer;
  boolean done;

  done = FALSE;
  L->n5 = r_child (L->n2);

  if (L->node[L->n5].code == 9)
    {
      if (L->node[L->n4].code == 9)
	{

	  switch (which)
	    {

	    case 0:
	      answer = (L->node[L->n5].u.op2 == L->node[L->n4].u.op2);
	      break;
	    case 1:
	      answer = (L->node[L->n5].u.op2 < L->node[L->n4].u.op2);
	      break;
	    case 2:
	      answer = (L->node[L->n5].u.op2 > L->node[L->n4].u.op2);
	      break;
	    case 3:
	      answer = (L->node[L->n5].u.op2 <= L->node[L->n4].u.op2);
	      break;
	    case 4:
	      answer = (L->node[L->n5].u.op2 >= L->node[L->n4].u.op2);
	      break;
	    case 5:
	      answer = (L->node[L->n5].u.op2 != L->node[L->n4].u.op2);
	      break;
	    }
	  done = TRUE;
	}
      else if (L->node[L->n4].code == 10)
	racomp (1, which, &answer, &done);
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_second_operand_for_comparison += 1;
	  err ("Wrong Second Operand for Comparison\n");
	}
    }
  else if (L->node[L->n5].code == 10)
    {
      if (L->node[L->n4].code == 9)
	racomp (2, which, &answer, &done);
      else if (L->node[L->n4].code == 10)
	racomp (3, which, &answer, &done);
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_second_operand_for_comparison += 1;
	  err ("Wrong Second Operand for Comparison\n");
	}
    }
  else if (L->node[L->n5].code == 2)
    {
      store (L->n1);
      L->n1 = L->n5;
    }
  else
    {
      L->iterate = FALSE;
      L->error.wrong_second_operand_for_comparison += 1;
      err ("Wrong Second Operand for Comparison\n");
    }
  if (done)
    {
      L->node[L->n1].code = 11;
      if (answer)
	{
	  L->node[L->n1].op1 = locate (" TRUE      ");
	  L->node[L->n1].u.op2 = 21;
	}
      else
	{
	  L->node[L->n1].op1 = locate (" FALSE     ");
	  L->node[L->n1].u.op2 = 22;
	}
      L->changed = TRUE;
    }
}

/*------------------------------------------------------------------*/

PRIVATE void
racomp (int some, int which, boolean * answer, boolean * done)
{
  float x;
  float y;

  switch (some)
    {

    case 1:

      x = L->node[L->n5].u.op2;
      y = L->node[L->n4].u.alt;
      break;

    case 2:

      x = L->node[L->n5].u.alt;
      y = L->node[L->n4].u.op2;
      break;

    case 3:

      x = L->node[L->n5].u.alt;
      y = L->node[L->n4].u.alt;
      break;
    }
  switch (which)
    {

    case 0:
      *answer = (x == y);
      break;
    case 1:
      *answer = (x < y);
      break;
    case 2:
      *answer = (x > y);
      break;
    case 3:
      *answer = (x <= y);
      break;
    case 4:
      *answer = (x >= y);
      break;
    case 5:
      *answer = (x != y);
      break;
    }
  *done = TRUE;
}

/*------------------------------------------------------------------*/

PRIVATE void
unary (int which)
{
  int i;

  switch (which)
    {

    case 1:
    case 3:			/* ---- predecessor and successor */

      if (L->node[L->n4].code == 9)
	{
	  L->node[L->n1].code = 9;
	  L->node[L->n1].u.op2 = L->node[L->n4].u.op2 + which - 2;
	  L->changed = TRUE;	/* L->n1 becomes a leaf node */
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_operand_for_pred_succ += 1;
	  err ("Wrong Operand for pred or succ\n");
	}
      break;

    case 2:			/* ---- Zero Test */

      if (L->node[L->n4].code == 9)
	{
	  L->node[L->n1].code = 11;
	  if (L->node[L->n4].u.op2 == 0)
	    {
	      L->node[L->n1].op1 = locate (" TRUE      ");
	      L->node[L->n1].u.op2 = 21;
	    }
	  else
	    {
	      L->node[L->n1].op1 = locate (" FALSE     ");
	      L->node[L->n1].u.op2 = 22;
	    }
	  L->changed = TRUE;	/* L->n1 becomes a leaf node */
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_operand_for_zero += 1;
	  err ("Wrong Operand for zero\n");
	}
      break;

    case 4:			/* ---- Null Test */

      if (L->node[L->n4].code == 4)
	{
	  L->node[L->n1].code = 11;
	  L->node[L->n1].op1 = locate (" TRUE      ");
	  L->node[L->n1].u.op2 = 21;
	  L->changed = TRUE;	/* leaf node */
	}
      else if (L->node[L->n4].code == 3)
	{
	  L->node[L->n1].code = 11;
	  L->node[L->n1].op1 = locate (" FALSE     ");
	  L->node[L->n1].u.op2 = 22;
	  L->changed = TRUE;	/* leaf node */
	}
      else if ((L->node[L->n4].code == 1) || (L->node[L->n4].code == 2))
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_operand_for_null += 1;
	  err ("Wrong Operand for null\n");
	}
      break;

    case 5:
    case 6:
    case 7:
    case 8:			/* ---- List Arithmetic */

      if (L->node[L->n4].code == 3)
	{
	  L->k1 = get_node ();
	  L->node[L->k1].code = 2;
	  L->node[L->k1].op1 = L->n2;	/* temporary */
	  L->node[L->k1].u.op2 = l_child (L->n4);
	  L->node[L->n1].op1 = L->k1;
	  L->k2 = get_node ();
	  L->node[L->k2].code = 2;
	  L->node[L->k2].op1 = L->n2;
	  L->node[L->k2].u.op2 = r_child (L->n4);
	  L->node[L->n1].u.op2 = L->k2;
	  L->k3 = get_node ();
	  L->node[L->k3].code = 15;
	  L->node[L->k3].u.op2 = which - 4;
	  L->node[L->k1].op1 = L->k3;
	  if ((which == 6) || (which == 8))
	    {
	      L->k4 = get_node ();
	      L->node[L->k4].code = 11;
	      L->node[L->k4].op1 = which - 1;
	      L->node[L->k4].u.op2 = which - 1;
	      L->node[L->k2].op1 = L->k4;
	    }
	}
      else if (L->node[L->n4].code == 4)
	{
	  L->node[L->n1].code = 9;

	  switch (which)
	    {

	    case 5:
	    case 6:
	      L->node[L->n1].u.op2 = 0;
	      break;
	    case 7:
	    case 8:
	      L->node[L->n1].u.op2 = 1;
	      break;
	    }
	  L->changed = TRUE;
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_operand_for_list_arithmetic += 1;
	  err ("Wrong Operand for List Arithmetic\n");
	}
      break;

    case 15:			/* ---- iota */

      if (L->node[L->n4].code == 9)
	{
	  if (L->node[L->n4].u.op2 > 0)
	    {
	      for (i = 1; i <= L->node[L->n4].u.op2; i++)
		{
		  L->k1 = get_node ();
		  L->node[L->k1].code = 9;
		  L->node[L->k1].u.op2 = i;
		  L->node[L->n1].code = 3;
		  L->node[L->n1].op1 = L->k1;
		  L->k2 = get_node ();
		  L->node[L->k2].code = 4;
		  L->node[L->n1].u.op2 = L->k2;
		  L->n1 = L->k2;
		}
	      L->changed = TRUE;
	    }
	  else if (L->node[L->n4].u.op2 == 0)
	    {
	      L->node[L->n1].code = 4;
	      L->changed = TRUE;
	    }
	  else
	    {
	      L->iterate = FALSE;
	      L->error.wrong_operand_for_iota += 1;
	      err ("Wrong Operand for iota\n");
	    }
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_operand_for_iota += 1;
	  err ("Wrong Operand for iota\n");
	}
      break;

    case 16:			/* ---- show */

      if (L->node[L->n4].code == 3)
	{
	  if (L->node[l_child (L->n4)].code > 4)
	    {
	      printf ("\n");
	      printf ("Showing the list [");
	      print_expression (l_child (L->n4));
	      L->k1 = get_node ();
	      L->node[L->k1].code = 11;
	      L->node[L->k1].op1 = locate (" more      ");
	      L->node[L->k1].u.op2 = 17;
	      L->node[L->n1].op1 = L->k1;
	      L->node[L->n1].u.op2 = r_child (L->n4);
	    }
	  else
	    {
	      store (L->n1);
	      L->n1 = l_child (L->n4);
	    }
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  err ("Wrong operand for Show\n");
	}
      break;

    case 17:			/* ---- more */

      if (L->node[L->n4].code == 3)
	{
	  if (L->node[l_child (L->n4)].code > 4)
	    {
	      printf (",");
	      print_expression (l_child (L->n4));
	      L->node[L->n1].u.op2 = r_child (L->n4);
	    }
	  else
	    {
	      store (L->n1);
	      L->n1 = l_child (L->n4);
	    }
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else if (L->node[L->n4].code == 4)
	{
	  printf ("]");
	  L->node[L->n1].code = 4;
	}
      else
	{
	  L->iterate = FALSE;
	  err ("Wrong operand for More\n");
	}
      break;

    case 20:			/* ---- not */

      if ((L->node[L->n4].code == 11) && (L->node[L->n4].op1 > 0))
	{
	  if (L->node[L->n4].u.op2 == 21)
	    {
	      L->node[L->n1].code = 11;
	      L->node[L->n1].op1 = locate (" FALSE     ");
	      L->node[L->n1].u.op2 = 22;
	      L->changed = TRUE;
	    }
	  else if (L->node[L->n4].u.op2 == 22)
	    {
	      L->node[L->n1].code = 11;
	      L->node[L->n1].op1 = locate (" TRUE      ");
	      L->node[L->n1].u.op2 = 21;
	      L->changed = TRUE;
	    }
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_operand_for_not += 1;
	  err ("Wrong Operand for not\n");
	}
      break;

    default:

      err ("Function is not a built-in unary one\n");
    }
}

/*------------------------------------------------------------------*/

PRIVATE void
binary (int which)
{
  int code;

  switch (which)
    {

    case 21:			/* ---- True */

      L->node[L->n1].code = 0;
      L->node[L->n1].op1 = 0;
      L->node[L->n1].u.op2 = r_child (L->n2);
      L->changed = TRUE;
      break;

    case 22:			/* ---- False */

      L->node[L->n1].code = 0;
      L->node[L->n1].op1 = 0;
      L->node[L->n1].u.op2 = L->n4;
      L->changed = TRUE;
      break;

    case 23:
    case 24:			/* ---- and/or */

      L->n5 = r_child (L->n2);
      if ((L->node[L->n4].code == 11) && (L->node[L->n4].op1 > 0) &&
	  ((L->node[L->n4].u.op2 == 21) || (L->node[L->n4].u.op2 == 22)))
	{
	  if ((L->node[L->n5].code == 11) && (L->node[L->n5].op1 > 0) &&
	      ((L->node[L->n5].u.op2 == 21) || (L->node[L->n5].u.op2 == 22)))
	    {

	      L->node[L->n1].code = 11;		/* leaf node */
	      L->changed = TRUE;

	      if (((L->node[L->n4].u.op2 == 21) && (L->node[L->n5].u.op2 == 21)
		   && (which == 23))
		  || (((L->node[L->n4].u.op2 == 21) || (L->node[L->n5].u.op2 == 21))
		      && (which == 24)))
		{

		  L->node[L->n1].op1 = locate (" TRUE      ");
		  L->node[L->n1].u.op2 = 21;
		}
	      else
		{
		  L->node[L->n1].op1 = locate (" FALSE     ");
		  L->node[L->n1].u.op2 = 22;
		}
	    }
	  else if (L->node[L->n5].code == 2)
	    {
	      store (L->n1);
	      L->n1 = L->n5;
	    }
	  else
	    {
	      L->iterate = FALSE;
	      L->error.wrong_first_operand_for_and_or += 1;
	      err ("Wrong First Operand for and/or\n");
	    }
	}
      else if (L->node[L->n4].code == 2)
	{
	  store (L->n1);
	  L->n1 = L->n4;
	}
      else
	{
	  L->iterate = FALSE;
	  L->error.wrong_second_operand_for_and_or += 1;
	  err ("Wrong Second Operand for and/or\n");
	}
      break;

    case 25:			/* ---- map */

      switch (L->node[L->n4].code)
	{

	case 1:
	case 2:

	  store (L->n1);
	  L->n1 = L->n4;
	  break;

	case 3:

	  L->k1 = get_node ();
	  L->node[L->k1].code = 2;
	  L->node[L->k1].op1 = L->n2;	/* temporary */
	  L->node[L->k1].u.op2 = l_child (L->n4);
	  L->node[L->n1].code = 3;
	  L->node[L->n1].op1 = L->k1;
	  L->k2 = get_node ();
	  L->node[L->k2].code = 2;
	  L->node[L->k2].op1 = L->n2;
	  L->node[L->k2].u.op2 = r_child (L->n4);
	  L->node[L->k1].op1 = r_child (L->n2);
	  L->node[L->n1].u.op2 = L->k2;
	  go_back ();
	  L->changed = TRUE;
	  break;

	case 4:

	  L->node[L->n1].code = 4;
	  go_back ();
	  L->changed = TRUE;
	  break;

	default:

	  L->iterate = FALSE;
	  L->error.wrong_argument_for_map += 1;
	  err ("Wrong Argument for Map\n");
	  break;
	}
      break;

    case 26:			/* ---- append */

      code = L->node[r_child (L->n2)].code;

      switch (code)
	{

	case 1:
	case 2:

	  store (L->n1);
	  L->n1 = r_child (L->n2);
	  break;

	case 3:

	  L->node[L->n1].code = 3;
	  L->k1 = get_node ();
	  L->node[L->k1].code = 2;
	  L->node[L->k1].u.op2 = L->n4;
	  L->node[L->n1].u.op2 = L->k1;
	  L->k2 = get_node ();
	  L->node[L->k2].code = 2;
	  L->node[L->k2].op1 = l_child (L->n2);
	  L->node[L->k2].u.op2 = r_child (r_child (L->n2));
	  L->node[L->k1].op1 = L->k2;
	  L->node[L->n1].op1 = l_child (r_child (L->n2));
	  go_back ();
	  L->changed = TRUE;
	  break;

	case 4:

	  L->node[L->n1].code = 0;
	  go_back ();
	  L->changed = TRUE;
	  break;

	default:

	  L->iterate = FALSE;
	  L->error.wrong_operand_for_append += 1;
	  err ("Wrong Operand for Append\n");
	  break;
	}
      break;

    default:

      err ("Function is not built-in binary\n");
      break;
    }
}

/*==================================================================*/
/*==================================================================*/
/*                                                                  */
/*                        END OF INTERPRETER                        */
/*                                                                  */
/*==================================================================*/
/*==================================================================*/

/* 
 * 
 * standard renaming of bound variables: 
 * 
 * running alpha_standardize(), and then print_expression() with the
 * standard flag TRUE, returns an expression where all bound
 * variables are renamed so that the name of a bound variable
 * will be uniquely determined by the order in which the binding
 * \'s occur. Free variables remain untouched. All bound variables
 * obtain names that are different from the free variables occurring in the
 * expression.
 * 
 * This is used to establish alpha-congruence between two expressions.
 * 
 */

/*==================================================================*/

PRIVATE int
alpha_standardize (int rt)
{
  static int track[SIZE + 1];
  int point;
  int top;
  int next;
  int scope_id;
  boolean more;

  point = rt;
  top = 0;
  more = TRUE;
  scope_id = 0;

  if (setjmp (LONGJUMP))
    return 0;

  while (more)
    {
      switch (L->heap[point].code)
	{

	case 0:		/* ---- indirection ---- */

	  point = L->heap[point].u.op2;
	  break;

	case 1:		/* ---- abstraction ---- */

	  L->heap[point].scope = ++scope_id;
	  next = L->heap[point].op1;
	  point = L->heap[point].u.op2;
	  scope (next, point, scope_id);
	  break;

	case 2:		/* ---- application ---- */

	  if (top < SIZE)
	    track[++top] = L->heap[point].u.op2;
	  else
	    {
	      more = FALSE;
	      err ("alpha_standardize track overflow.\n");
	    }
	  point = L->heap[point].op1;
	  break;

	case 3:
	case 13:		/* ---- list structure ---- */

	  if (L->heap[point].code == 3);
	  else
	    L->heap[point].code = 3;

	  if (top < L->parms->stack_size)
	    {
	      top++;
	      next = r_child (point);	/* needed here */
	      track[top] = next;
	      if ((L->heap[next].code == 3) || (L->heap[next].code == 4))
		L->heap[next].code = L->heap[next].code + 10;
	    }
	  else
	    {
	      more = FALSE;
	      err ("alpha_standardize track overflow.\n");
	    }
	  point = L->heap[point].op1;
	  break;

	case 4:
	case 14:		/* ---- empty list or end of list ---- */

	  if (L->heap[point].code == 4);
	  else
	    L->heap[point].code = 4;

	  point = silent_pop (track, &top, &more);
	  break;

	case 5:
	case 6:
	case 7:
	case 8:
	case 9:
	case 10:
	case 11:
	case 15:
	case 16:

	  point = silent_pop (track, &top, &more);
	  break;

	default:		/* ---- renaming prefix ---- */

	  if (L->heap[point].code < 0)
	    {
	      point = r_child (point);
	    }
	  else
	    {
	      err ("\n");
	      err ("Wrong Expression!\n");
	      more = FALSE;
	    }
	  break;

	}			/*switch */
    }				/*while */

  if (L->error_number)
    return 0;
  else 
    return 1;
}

/*------------------------------------------------------------------*/

PRIVATE int
silent_pop (int *track, int *top, boolean * more)
{
  int i;

  if (*top > 0)
    {
      i = track[(*top)--];
      return i;
    }
  else
    {
      *more = FALSE;
      return 0;
    }
}

/*------------------------------------------------------------------*/

/*  
 * renaming nodes should not occur in the graph when scope() gets
 * executed.
 */

PRIVATE void
scope (int id, int point, int scope_id)
{
  static int trace[SIZE + 1];
  boolean move;
  int top, self;

  move = TRUE;
  top = 0;
  self = point;

  while (move)
    {
      if (L->heap[point].marker)
	point = back_up (&top, &move, trace);
      else
	{
	  L->heap[point].marker = TRUE;

	  switch (L->heap[point].code)
	    {

	    case 0:		/* ---- indirection ---- */

	      point = r_child (point);
	      break;

	    case 1:		/* ---- abstraction ---- */

	      if (id == L->heap[point].op1)
		point = back_up (&top, &move, trace);
	      else
		point = r_child (point);
	      break;

	    case 2:
	    case 3:		/* ---- application or list ---- */

	      if (top < SIZE)
		trace[++top] = r_child (point);
	      else
		{
		  move = FALSE;
		  err ("scope(): trace overflow.\n");
		  longjmp (LONGJUMP, 1);
		}
	      point = l_child (point);
	      break;

	    case 11:		/* ---- variable ---- */

	      if (id == L->heap[point].op1)
		{
		  L->heap[point].scope = scope_id;
		}
	      else
		point = back_up (&top, &move, trace);
	      break;

	    default:

	      point = back_up (&top, &move, trace);
	      break;

	    }			/* switch */
	}			/* else */
    }				/* while */

  top = 0;			/* restore the marker */
  point = self;
  move = TRUE;

  while (move)
    {
      if (!L->heap[point].marker)
	point = back_up (&top, &move, trace);
      else
	{
	  L->heap[point].marker = FALSE;

	  switch (L->heap[point].code)
	    {

	    case 0:		/* ---- indirection ---- */

	      point = r_child (point);
	      break;

	    case 1:		/* ---- abstraction ---- */

	      if (id == L->heap[point].op1)
		point = back_up (&top, &move, trace);
	      else
		point = r_child (point);
	      break;

	    case 2:
	    case 3:		/* ---- application or list ---- */

	      trace[++top] = r_child (point);
	      point = l_child (point);
	      break;

	    default:

	      point = back_up (&top, &move, trace);
	      break;

	    }			/* switch */
	}			/* else */
    }				/* while */
}

/*------------------------------------------------------------------*/

PRIVATE int
free_vars_list ()
{
  int n_free;
  int i;
  int j;
  boolean dejavu;
  char symbol[SMALL];

  if (setjmp (LONGJUMP))
    {
      L->n_free_vars = n_free;
      return 0;
    }

  n_free = 0;

  for (i = 1; i <= L->n_identifiers; i++)
    {
      if (not_free (L->identifiers[i], L->root) == 0)
	{
	  strip (L->table[L->identifiers[i]].symbol, symbol);
	  L->free_vars[++n_free] = (char *) space (sizeof (char) * (strlen (symbol) + 1));
	  strcpy (L->free_vars[n_free], symbol);
	}
    }

  L->n_free_vars = n_free;

  /* print_free_vars_list(stdout); */

  return 1;
}

/*------------------------------------------------------------------*/

PRIVATE void
clear_free_vars_list (int n)
{
  int i;

  for (i = 1; i <= n; i++)
    free (L->free_vars[i]);
}

/*------------------------------------------------------------------*/

PRIVATE void
print_free_vars_list (FILE * fp)
{
  int i;

  fprintf (fp, "\n");
  fprintf (fp, "free variables:\n");
  fprintf (fp, "\n");

  for (i = 1; i <= L->n_free_vars; i++)
    fprintf (fp, "%d: %s\n", i, L->free_vars[i]);
  fprintf (fp, "\n");
}

/*------------------------------------------------------------------*/

PUBLIC char *
standardize (char *expression, interpreter * Interp)
{
  char *result;
  char buffer[BUFSIZE];
  int i;
  int body;

  if (!expression || strlen (expression) >= (BUFSIZE-10))
      return NULL;

  L = Interp;
  L->output_expression[0] = '\0';

  if (setjmp (RECOVER))
    return NULL;
  
  strcpy (buffer, expression);
  strcat (buffer, ";");

  L->input_expression = buffer;

  clear ();

  L->peek = str_getc (L->input_expression);
  body = get_node ();
  L->root = body;

  if (L->peek == '\0')
    return NULL;

  parse (&body);

  /* list of free variables */

  if (free_vars_list () && alpha_standardize (L->root))
    {
      L->standard = TRUE;
      print_expression (L->root);
    }

  clear_free_vars_list (L->n_free_vars);

  result = (char *) space (sizeof (char) * (strlen (L->output_expression) + 1));
  strcpy (result, L->output_expression);

  return result;
}

/*==================================================================*/
/*
 * end of standard renaming of bound variables 
 */
/*==================================================================*/
/*==================================================================*/
/*
 * Services
 */
/*==================================================================*/

PUBLIC char *
bind_all_free_vars (char *expression, interpreter * Interp)
{
  char *bound;
  char *expr;
  char *result;
  int body;
  int i;
  int len;

  L = Interp;

  L->output_expression[0] = '\0';

  if (!expression)
    return NULL;

  expr = (char *) space (sizeof (char) * ((len = strlen (expression)) + 2));
  strcpy (expr, expression);
  strcat (expr, ";");

  if (setjmp (RECOVER))
    {
      free (expr);
      return NULL;
    }
    
  L->input_expression = expr;

  clear ();

  L->peek = str_getc (L->input_expression);
  body = get_node ();
  L->root = body;

  if (L->peek == '\0')
    return NULL;

  parse (&body);

  free (expr);

  /* list of free variables */

  if (!free_vars_list () || !L->n_free_vars)
    {				
      clear_free_vars_list (L->n_free_vars);
      bound = (char *) space (sizeof (char));
      *bound = '\0';
      return bound;
    }

  bound = (char *) space (sizeof (char) * (len + L->n_free_vars * 12));

  strcpy (bound, "\\");
  strcat (bound, L->free_vars[L->n_free_vars]);
  strcat (bound, ".");
  for (i = L->n_free_vars - 1; i >= 1; i--)
    {				/* bind them */
      strcat (bound, "\\");
      strcat (bound, L->free_vars[i]);
      strcat (bound, ".");
    }
  strcat (bound, expression);

  clear_free_vars_list (L->n_free_vars);	/* drop free vars list */

  return bound;
}

/*==================================================================*/

PUBLIC int
Free_Variables (char *expression, interpreter * Interp)
{
  char *bound;
  char *expr;
  int result;
  int body;
  int i;
  int len;

  L = Interp;

  L->output_expression[0] = '\0';

  if (!expression)
    return 0;

  expr = (char *) space (sizeof (char) * ((len = strlen (expression)) + 2));
  strcpy (expr, expression);
  strcat (expr, ";");

  if (setjmp (RECOVER))
    {
      free (expr);
      return 0;
    }
    
  L->input_expression = expr;

  clear ();

  L->peek = str_getc (L->input_expression);
  body = get_node ();
  L->root = body;

  if (L->peek == '\0')
    return 0;

  parse (&body);

  free (expr);

  /* list of free variables */

  if (!free_vars_list () || !L->n_free_vars) {
    result = 0;
  } else {
    result = 1;
  }

  L->output_expression[0] = '\0';

  clear_free_vars_list (L->n_free_vars);	/* drop free vars list */

  return result;
}

/*==================================================================*/

/* get next character from input string */

PRIVATE int
str_getc (char *string)
{
  int c;

  switch (c = string[L->char_count++])
    {

    case '\0':
    case '\n':
      L->char_count = 0;
      return ((int) '\0');
      break;
    default:
      return c;
      break;
    }
}

/*==================================================================*/

PRIVATE void
strip (char *string, char *string2)
{
  int i, j, k;

  for (i = 0; i < strlen (string) && string[i] == ' '; i++);
  for (j = strlen (string) - 1; j >= 0 && string[j] == ' '; j--);

  for (k = i; k <= j; k++)
    string2[k - i] = string[k];
  string2[j - i + 1] = '\0';
}

/*==================================================================*/

PRIVATE void
err (char *message)
{
  L->error_number++;
  L->errors_occurred++;

  if (L->parms->error_fp)
    {
      fprintf (L->parms->error_fp, "error %d at expression\n", L->error_number);
      fprintf (L->parms->error_fp, "%s\n", L->input_expression);
      fprintf (L->parms->error_fp, "%s", message);
      fflush (L->parms->error_fp);
    }
  
  longjmp (RECOVER, 1);
}

/*==================================================================*/

PUBLIC void
status (FILE * fp)
{
  if (fp != NULL)
    {

      fprintf (fp, "\n\n");

      fprintf (fp, "reductions in current computation    =  %d\n",
	       L->reductions);
      fprintf (fp, "cycles in current computation        =  %d\n",
	       L->cycles);
      fprintf (fp, "computations beyond cycle limit      =  %d\n",
	       L->error.cycle_limit_hits);
      fprintf (fp, "computations beyond space limit      =  %d (*)\n",
	       L->error.space_limit_hits);
      if (L->error.sum_no_nf_terms)
	fprintf (fp, "terms passed not in normal form      =  %d\n",
		 L->error.sum_no_nf_terms);
      if (L->fresh)
	fprintf (fp, "symbol table level                   =  %d\n",
		 L->fresh);
      if (L->error.output_overflow_hits)
	fprintf (fp, "output overflows                     =  %d (*)\n",
		 L->error.output_overflow_hits);
      if (L->error.symbol_table_overflow_hits)
	fprintf (fp, "symbol table overflows               =  %d (*)\n",
		 L->error.symbol_table_overflow_hits);
      if (L->error.not_free_overflow_hits)
	fprintf (fp, "overflow in checking for free vars   =  %d (*)\n",
		 L->error.not_free_overflow_hits);
      if (L->error.path_overflow_in_reduce)
	fprintf (fp, "path_overflow_in_reduce              =  %d (*)\n",
		 L->error.path_overflow_in_reduce);
      if (L->error.wrong_renaming)
	fprintf (fp, "wrong_renaming                       =  %d (*)\n",
		 L->error.wrong_renaming);
      if (L->error.wrong_second_operand_for_arithmetics)
	fprintf (fp, "wrong_second_operand_for_arithmetics =  %d (*)\n",
		 L->error.wrong_second_operand_for_arithmetics);
      if (L->error.wrong_second_operand_for_comparison)
	fprintf (fp, "wrong_second_operand_for_comparison  =  %d (*)\n",
		 L->error.wrong_second_operand_for_comparison);
      if (L->error.wrong_operand_for_pred_succ)
	fprintf (fp, "wrong_operand_for_pred_succ          =  %d (*)\n",
		 L->error.wrong_operand_for_pred_succ);
      if (L->error.wrong_operand_for_zero)
	fprintf (fp, "wrong_operand_for_zero               =  %d (*)\n",
		 L->error.wrong_operand_for_zero);
      if (L->error.wrong_operand_for_null)
	fprintf (fp, "wrong_operand_for_null               =  %d (*)\n",
		 L->error.wrong_operand_for_null);
      if (L->error.wrong_operand_for_list_arithmetic)
	fprintf (fp, "wrong_operand_for_list_arithmetic    =  %d (*)\n",
		 L->error.wrong_operand_for_list_arithmetic);
      if (L->error.wrong_operand_for_iota)
	fprintf (fp, "wrong_operand_for_iota               =  %d (*)\n",
		 L->error.wrong_operand_for_iota);
      if (L->error.wrong_operand_for_not)
	fprintf (fp, "wrong_operand_for_not                =  %d (*)\n",
		 L->error.wrong_operand_for_not);
      if (L->error.wrong_first_operand_for_and_or)
	fprintf (fp, "wrong_first_operand_for_and_or       =  %d (*)\n",
		 L->error.wrong_first_operand_for_and_or);
      if (L->error.wrong_second_operand_for_and_or)
	fprintf (fp, "wrong_second_operand_for_and_or      =  %d (*)\n",
		 L->error.wrong_second_operand_for_and_or);
      if (L->error.wrong_argument_for_map)
	fprintf (fp, "wrong_argument_for_map               =  %d (*)\n",
		 L->error.wrong_argument_for_map);
      if (L->error.wrong_operand_for_append)
	fprintf (fp, "wrong_operand_for_append             =  %d (*)\n",
		 L->error.wrong_operand_for_append);
      if (L->error.wrong_expr_for_hd_tl)
	fprintf (fp, "wrong_expr_for_hd_tl                 =  %d (*)\n",
		 L->error.wrong_expr_for_hd_tl);
      if (L->error.wrong_expr_for_selection)
	fprintf (fp, "wrong_expr_for_selection             =  %d (*)\n",
		 L->error.wrong_expr_for_selection);
      if (L->error.wrong_operator)
	fprintf (fp, "wrong_operator                       =  %d (*)\n",
		 L->error.wrong_operator);

      fprintf (fp, "\n");
      fprintf (fp, "(*) these conditions issue a message to the error file\n");
      fprintf (fp, "\n");

      if (L->errors_occurred)
	fprintf (fp, "%d error messages\n", L->errors_occurred);
      else
	fprintf (fp, "no error messages\n");

      fprintf (fp, "\n");
    }
}

/*===========================================================================
  ===========================================================================

                     APPENDIX    list of codes

  ===========================================================================
  ===========================================================================

  
	CODE	pure lambda		MEANING
	
	
	0			free node, indirection node (technical)
	1	   yes		abstractor (\)
	2	   yes		application (  (OP1)OP2  )
	3			list begin ([), list separator (,)
	4			end of list (])
	5			Y combinator (?)
	6			head (^)
	7			tail (~)
	8			add-to-list operator (&)
	9			integer number
	10			real number
	11	   yes		identifier (variable or built-in name)
	12			NIL code (technical)
	13			list structure
	14			empty list or end of list
	15			arithmetics (+, -, *, /)
	16			relational (>, =, <)    
      
  ===========================================================================*/

/*-----------------------------------------------------------------*/

/*
 * Legal expression are:
 * 
 * [let "legal declaration"; ...] eval "legal lambda expression";
 * 
 * where "..." is a legal declaration or a legal lambda expression.
 * 
 * For example:
 * 
 * eval (((\f.\x.\y.(x)(f)y)p)q)r;
 * 
 * or
 * 
 * let fact _ (?)\f.\n.(((zero)n)1)((*)n)(f)(pred)n;
 * eval (fact)4;
 * 
 * or
 * 
 * let I _ \x.x;
 * let K _ \x.\y.x;
 * let S _ \x.\y.\z.((x)z)(y)z;
 * eval (((K)I)(K)A)B;
 */

char *
get_expression (FILE * fp)
{
  char *expr = NULL, *next_expr = NULL;

  expr = get_line (fp);
  if (*expr == '@')
    exit (0);
  if (str_index (expr, "eval") == -1)
    {
      while (str_index (next_expr, "eval") == -1)
	{
	  if (next_expr)
	    free (next_expr);
	  next_expr = get_line (fp);
	  if (*next_expr == '@')
	    exit (0);
	  expr = realloc (expr, strlen (expr) + strlen (next_expr) + 1);
	  strcat (expr, next_expr);
	}
      free (next_expr);
    }

  return expr;
}

/*-----------------------------------------------------------------*/

int
main (int argc, char **argv)
{
  char *expression, *correct, *result, *stdrd;
  int mode, i = 0;
  FILE *fp, *fp2, *fopen ();

  interpreter *Lambda;
  parmsLambda *Parameters;
  
  Parameters = (parmsLambda *) space (sizeof (parmsLambda));

  Parameters->heap_size = 4000;	/* size of heap */
  Parameters->cycle_limit = 100000; /* maximum number of cycles */
  Parameters->symbol_table_size = 500;	/* size of symbol table */
  Parameters->stack_size = 2000;  /* stack size */
  Parameters->name_length = 10;	/* max length of identifiers */
  Parameters->standard_variable = 'x';	/* name of standard variable */
  Parameters->error_fp = stdout;  /* error report */

  Lambda = initialize_lambda (Parameters);

  printf ("perform test suite (0) or enter interactive mode (1)\n");
  scanf ("%d", &mode);

  if (mode)
    {
      while (1)
	{
	  printf ("enter expression\n\n");
	  expression = get_expression (stdin);
	  printf ("\nexpression\n%s\n", expression);

	  result = reduce_lambda (expression, Lambda);

	  if (!result)
	    printf ("NO normal form achieved within limits.\n");
	  else
	    printf ("\nresult:\n%s\n\n", result);
	  printf ("reductions: %d (cycles: %d)\n\n", Lambda->reductions, Lambda->cycles);

	  stdrd = standardize (result, Lambda);

	  printf ("standardized\n%s\n\n", stdrd);

	  free (result);
	  free (stdrd);
	  free (expression);
	}
    }
  else
    {
      fp = fopen ("lambda.test", "r");
      if (fp == NULL)
	{
	  printf ("no file lambda.test\n");
	  exit (0);
	}
      fp2 = fopen ("lambda.res", "r");
      if (fp2 == NULL)
	{
	  printf ("no file lambda.res\n");
	  exit (0);
	}
      while (1)
	{
	  i++;
	  expression = get_expression (fp);
	  correct    = get_line (fp2);
	  printf ("-------------------------------------------------\n");
	  printf ("%d\nREDUCE:\n%s\n", i, expression);
	  result = reduce_lambda (expression, Lambda);
	  if (!result)
	    printf ("NO normal form achieved within limits.\n");
	  else
	    printf ("RESULT (reductions: %d):\n%s\n", Lambda->reductions, result);
	  if (strcmp (result, correct) == 0)
	    printf( "correct.\n");
	  else
	    {
	      printf ("wrong! (does not compare with lambda.res)\n");
	      exit (0);
	    }
	  free (expression);
	  free (result);
	}
    }
}
