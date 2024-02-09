/* 
    utilities.h 

    c 1994 Walter Fontana and Ivo Hofacker
 */

#ifndef	__UTILITIES_H
#define	__UTILITIES_H

#include "include.h"

extern void *space (unsigned int size);
extern void nrerror (char *message);
extern double urn (void);
extern int int_urn (int from, int to);
extern void file_copy (FILE * from, FILE * to);
extern char *time_stamp (void);
extern char *random_string (int l, char *symbols);
extern int hamming (char *s1, char *s2);
extern char *get_line (FILE * fp);
extern void next_line (FILE * fp);
extern int str_index (char *s, char *t);
extern void reverse (char *s);
extern void sort (int n, int *ra);
extern double cpu_time ();
extern char *time_stamp ();
extern char *int_to_char (int n, char *s);
extern char *float_to_char (float n, char *s);
extern char *double_to_char (double n, char *s);
extern int **int_matrix (int nrl, int nrh, int ncl, int nch);
extern void free_int_matrix (int **m, int nrl, int nrh, int ncl, int nch);
extern float **float_matrix (int rl, int rh, int cl, int ch);
extern void free_float_matrix (float **m, int nrl, int nrh, int ncl, int nch);
extern double **double_matrix (int nrl, int nrh, int ncl, int nch);
extern void free_double_matrix (double **m, int nrl, int nrh, int ncl, int nch);

extern unsigned short seed[3];

#endif /* __UTILITIES_H */
