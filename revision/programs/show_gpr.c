/* Show_Grassmann_Pluecker_Relations */
/* gibt die k-summandigen GPR aus */

#include <stdio.h>
#include <string.h>

#define mpkt 17              /* maximale Punktzahl + 1 */
#define mrng 5               /* maximaler Rang */
#define true  1
#define false 0

typedef int perm[mpkt];
typedef long int longint;

const char hex[]   = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

int  npkt;                   /* Anzahl der Punkte */
int  rang;                   /* Rang des Chirotops */
int  ks;                     /* k-summandige GPR */
int  i,j,k,iso;              /* diverse Zaehlvariablen */
perm a,b,c;                  /* Indexmengen fuer GPR */
int  na,nb,nc;               /* Anzahl der Elemente in den GPR */

const char name[]="gpr.dat";

FILE *datei;

int swap(int *a, int *b)
/* tauscht Werte a und b, aufrufen mit swap(&a,&b) */
{
  int c;
   c = *a;
  *a = *b;
  *b = c;
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
      changed = false;
      k--;
      for(i=1;i<=k;i++)
      {
        if (p[i]>p[i+1])
        {
          permanz++;
          changed = true;
          swap(&p[i],&p[i+1]);
        }
      }
    } while (changed);
  }
  return permanz;
}

void write_gpr(void)
{
    int i,j;
    perm ma,mb,mc,ausw;           /* Grundmengen fuer GPR */
    for(i=1;i<=npkt;i++) ausw[i] = i;
    for(i=1;i<=na;i++) { ma[i] = ausw[a[i]]; ausw[a[i]] = npkt+1; }
    i=sortperm(npkt,ausw);
    for(i=1;i<=nb;i++) { mb[i] = ausw[b[i]]; ausw[b[i]] = npkt+1; }
    i=sortperm(npkt,ausw);
    for(i=1;i<=nc;i++) { mc[i] = ausw[c[i]]; }
    fprintf(datei,"{");
    for(j=1;j<=na;j++) fprintf(datei,"%c",hex[ma[j]]);
    fprintf(datei,"|");
    for(j=1;j<=nb;j++) fprintf(datei,"%c",hex[mb[j]]);
    fprintf(datei,"|");
    for(j=1;j<=nc;j++) fprintf(datei,"%c",hex[mc[j]]);
    fprintf(datei,"} = ");
    for(j=1;j<=ks;j++)
    {
        fprintf(datei," %c [",((j+1)%2==0)?'+':'-');
        for(i=1;i<=na;i++) fprintf(datei,"%c",hex[ma[i]]);
        for(i=1;i<=nc;i++) if (i!=j) fprintf(datei,"%c",hex[mc[i]]);
        fprintf(datei,"] [");
        for(i=1;i<=na;i++) fprintf(datei,"%c",hex[ma[i]]);
        for(i=1;i<=nb;i++) fprintf(datei,"%c",hex[mb[i]]);
        fprintf(datei,"%c]",hex[mc[j]]);
    }
    fprintf(datei,"\n");
}

void perm_c(int p1, int p2)
/* Auswahlen fuer C in {A|B|C} */
{
int i,bis;
bis = npkt - na - nb;
for(i=p2+1;i<=bis;i++)
    {
      c[p1] = i;
      if (p1==nc) write_gpr();
      else perm_c(p1+1,i);
    }
}

void perm_b(int p1, int p2)
/* Auswahlen fuer B in {A|B|C} */
{
int i, bis;
bis = npkt - na;
for(i=p2+1;i<=bis;i++)
    {
      b[p1] = i;
      if (p1==nb) perm_c(1,0);
      else perm_b(p1+1,i);
    }
}

void perm_a(int p1, int p2)
/* Auswahlen fuer A in {A|B|C} */
{
int i;
for(i=p2+1;i<=npkt;i++)
    {
      a[p1] = i;
      if (p1==na) perm_b(1,0);
      else perm_a(p1+1,i);
    }
}

void grassmann(void)
{
    if (na!=0) perm_a(1,0); else perm_b(1,0);
}

/* Das Hauptprogramm */
void main(void)
{
  printf("Please give number of points to compute : "); scanf("%i",&npkt);
  printf("Please give rank to compute             : "); scanf("%i",&rang);
  printf("Please give number of summands for GPR  : "); scanf("%i",&ks);
  na = rang - ks + 1;
  nb = ks - 2;
  nc = ks;
  datei = fopen(name,"w");
  if (datei==NULL) { printf("Error while operating on %s",name); exit(1); }
  grassmann();
  fclose(datei);
}
