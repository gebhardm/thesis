/* This programme checks Base-Property of Matroids */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MPKT 17              /* maximale Punktzahl + 1 */
#define MRANG 5              /* maximaler Rang */
#define TRUE  1
#define FALSE 0

typedef unsigned int perm[MPKT];
typedef long int longint;
typedef unsigned int uint;
typedef char boolean;

const char hex[]   = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

uint npkt;                  /* Anzahl der Punkte */
uint rang;                  /* Rang des Chirotops */
uint nelt, anzelt;          /* Anzahl der Elemente des Matroids */
uint *mat;                  /* das zu pruefende Matroid */
int  i,j,k,iso;             /* diverse Zaehlvariablen */
char in;                    /* Einlesecharakter */

char name[50];              /* Dateiname, Fragestring */
char inname[50];            /* Dateiname der Elementliste */
char outname[50];           /* Dateiname der Ausgabedatei */
FILE *indatei;              /* File of Text (Eingabe) */
FILE *outdatei;             /* File of Text (Ausgabe) */
FILE *wohin;                
FILE *outdatei;

longint choose(int n, int k)
/* Binomialkoeffizienten */
{
  int i;
  longint o=1,u=1;
  if ((k<0) || (k>n)) return 0;
  if (k==0) return 1;
  for(i=n;i>n-k;i--) o = o * i;
  for(i=2;i<=k;i++)  u = u * i;
  return ((longint) o / u);
}

int swap(int *x, int *y)
/* tauscht Werte x und y, aufrufen mit swap(&x,&y) */
{
  int z;
   z = *x;
  *x = *y;
  *y = z;
  return 0;
}

int sortperm(int k, perm p)
/* sortiert eine Permutation lexikographisch */
{
  int i, permanz=0, changed;
  if (k>1)
  {
    do
    {
      changed = FALSE;
      k--;
      for(i=1;i<=k;i++)
      {
        if (p[i]>p[i+1])
        {
          permanz++;
          changed = TRUE;
          swap(&p[i],&p[i+1]);
        }
      }
    } while (changed);
  }
  return permanz;
}

void bracket(int pos, int n, int k, perm x)
/* Erzeugt zur Nummer 'pos' das zugeordnete k-Tupel 'x'.
   Nach kanonischer Sortierung. Die Umkehrfunktion ist INDEX.
   Nach einer Pascal-Prozedur von Peter Schuchert             */
{
   int i,j,l,bin;
   pos--; l = 0;
   for(i=1;i<=k;i++)
   {
      bin = 0;
      j = n-l;
      do { l++; j--;  pos = pos-bin; bin = choose(j, k-i); }
      while (pos>=bin);
      x[i] = l;
   }
}  /* bracket */

int position(int n, int k, perm p)
/* gibt lexikographischen Index einer Permutation aus */
{
  int i,j,ind;
  perm q;
  for(i=1;i<=k;i++) q[i]=p[i];
  i = sortperm(k,q);
  ind = 1;
  for(j=n-q[1]+1;j<n;j++) ind = ind + choose(j,k-1);
  for(i=2;i<=k;i++)
  {
    for(j=n-q[i]+1;j<n-q[i-1];j++) ind = ind + choose(j,k-i);
  }
  return ind;
}

void writebracket(perm brk)
{
    int i;
    fprintf(wohin,"[");
    for(i=1;i<=rang;i++) fprintf(wohin,"%c",hex[brk[i]]);
    fprintf(wohin,"]");
}

int a_ohne_b(int rng, perm A, perm B, perm C)
/* Berechnet die Menge C als A ohne B */
{
  int anzc, i, j;
  boolean enthalten;
  anzc=0;
  /*
    writebracket(A); fprintf(wohin,"\\");
    writebracket(B);
  */
  for(i=1;i<=rng;i++)
  {
    enthalten = FALSE;
    for(j=1;j<=rng && !enthalten;j++) if (A[i]==B[j]) enthalten=TRUE;
    if (enthalten==FALSE) { anzc++; C[anzc]=A[i]; }
  }
  /*
    fprintf(wohin," = { ");
    for(i=1;i<=anzc;i++) fprintf(wohin,"%i ",C[i]);
    fprintf(wohin,"}, # = %i\n",anzc);
  */
  return anzc;
}

boolean new_base(perm B, uint q, uint p)
/* schaut, ob (B mit q) ohne p eine Base ist */
{
  int i,pos; perm br;
  for(i=1;i<=rang;i++) { br[i]=B[i]; if (br[i]==p) br[i]=q; }
  /* fprintf(wohin,"possible base is "); writebracket(br); fprintf(wohin,"\n"); */
  pos = position(npkt,rang,br);
  /* fprintf(wohin,"position is %i, value is %i\n",pos,mat[pos]); */
  if (mat[pos]==0) return FALSE;
  return TRUE;
}

void test_base_axiom(void)
/* testet die Erfuellung des Basisaxioms fuer Matroide nach der Definition */
{
   int i,j,k,l,anzp,anzq;
   boolean nobase,nomatroid;
   perm B1,B2,P,Q;
   nobase = FALSE; nomatroid=FALSE;
   for(i=1;i<=anzelt && !nomatroid;i++)
   {
     if (mat[i]!=0)
     {
       bracket(i,npkt,rang,B1);     /* B1 ist Base zur Position i */
       for(j=1;j<=anzelt && !nomatroid;j++)
         if (i!=j && mat[j]!=0)
         {
            bracket(j,npkt,rang,B2);         /* B2 ist Base zur Position j */
            anzp = a_ohne_b(rang,B1,B2,P);   /* P = B1\B2 */
            anzq = a_ohne_b(rang,B2,B1,Q);   /* Q = B2\B1 */
            if (anzp!=0)
            {
               for(k=1;k<=anzp;k++)
               {
                 nobase = TRUE;
                 for(l=1;l<=anzq && nobase;l++)
                 {
                   if (new_base(B1,Q[l],P[k])==TRUE) nobase=FALSE;
                 }
               }
               if (nobase==TRUE)
               {
                 fprintf(wohin,"NO MATROID !!\n");
                 printf("NO MATROID !! (see file matroid.tst)\n");
                 fprintf(wohin,"Brackets ");
                 writebracket(B1); fprintf(wohin," and ");
                 writebracket(B2); fprintf(wohin," violate the axiom\n");
                 nomatroid=TRUE;
               }
            } /* if (anzp!=0) */
         }  /* if (i!=j ... */
     } /* if (mat[i]!=0) */
   } /* for(i=1... */
   if (nomatroid==FALSE)
   {
     fprintf(wohin,"%s is the list of a matroid.\n",inname);
     printf("%s is the list of a matroid.\n",inname);
   }
   /* fprintf(wohin,"i = %i, j = %i\n",i,j); */
} /* test_base_axiom */

/* Das Hauptprogramm */
void main(void)
{
  printf("\nThis programme checks base-axiom for possible matroids\n");

  printf("\nName of input file (without extension .mat): ");
  scanf("%s",name);
  strcpy(inname,name); strcpy(outname,name);
  strcat(inname,".mat"); strcat(outname,".tst");
  indatei  = fopen(inname,"r");
  outdatei = fopen(outname,"w");
  wohin    = outdatei;

  if (indatei==NULL)
  {
    printf(" Error while fileoperation on %s\n",inname);
    exit(1);
  }
  else
  if (outdatei==NULL)
  {
    printf(" Error while fileoperation on %s\n",outname);
    exit(1);
  }
  else
  {
    printf("Reading file %s\n",inname);
    fprintf(wohin,"Computing file %s ...\n",inname);
    fscanf(indatei,"%i",&npkt);
    if (npkt>MPKT-1) { printf("Too many points to compute"); exit(1); }
    fscanf(indatei,"%i",&rang);
    if (rang>MRANG) { printf("Rank too large to compute"); exit(1); }
    anzelt=choose(npkt,rang);
    mat = calloc(anzelt+1,sizeof(uint));
    nelt = 0;
    do
    {
      do
      {
        in = fgetc(indatei);
      } while (in!='1' && in!='0' && in!='*' && in!=EOF);
      nelt++;
      mat[nelt] = (in=='0')?0:(in=='1')?1:2;
    }
    while (nelt<=anzelt && in!=EOF && in!='*');
    nelt--;
    fclose(indatei);
  }

  for(i=1;i<=nelt;i++) fprintf(wohin,"%i",mat[i]);
  fprintf(wohin,"\n");
  fprintf(wohin,"There are %i elements ",anzelt);
  fprintf(wohin,"of %i points ",npkt);
  fprintf(wohin,"in rank %i\n",rang);
  fprintf(wohin,"Number of totally read elements is %i\n",nelt);

  test_base_axiom();

  free(mat);
}
