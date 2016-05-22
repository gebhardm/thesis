/* Symmetries_of_matroidlist   */
/* Berechnet die Symmetriegruppe einer Matroidliste */
/* by Markus Gebhard, THD, FB04AG3b */

#include <stdio.h>
#include <string.h>

#define mpkt 17              /* maximale Punktzahl + 1 */
#define mrng 5               /* maximaler Rang */
#define mmat 8000            /* maximale Anzahl von Elementen + 1 */
#define msy  2000            /* maximale Anzahl an Symmetrien + 1 */
#define true  1
#define false 0

typedef unsigned int perm[mpkt];
typedef long int longint;
typedef unsigned int uint;
typedef char boolean;

const char hex[]   = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

uint nmat,npkt,anzmat;       /* Anzahl der Vorzeichen und Punkte */
uint rang;                   /* Rang des Chirotops */
int  i,j,k,iso;              /* diverse Zaehlvariablen */
uint nsym;                   /* Zaehlvariable fuer alle Symmetrien */
uint ez;                     /* Elementzaehler */
boolean ex;                  /* Symmetrie ? */
perm br;                     /* Kombinationsarray */
perm vl;                     /* Permutationsarray */
perm aut[msy];               /* die Elemente der Automorphismengruppe */
char mat[mmat];              /* erzeugte Matroidliste */
char vmat[mmat];             /* eingelesene Matroidiste */
char in;                     /* Einzulesender Wert fuer Vorzeichenliste */
char instr[80];              /* Eingabezeile fuer Fragen */

char name[50], frage[50];    /* Dateiname, Fragestring */
char inname[50];             /* Dateiname Vorzeichenliste */
char outname[50];            /* Dateiname Symmetriedatei */
FILE *indatei;               /* File of Text (Eingabe) */
FILE *outdatei;              /* File of Text (Ausgabe) */
FILE *wohin;

char ao(int x)
{ return hex[x]; }

char neg(char x)
/* negiert das Vorzeichen */
{ return((x=='+')?'-':(x=='-')?'+':(x=='0')?'0':'?'); }

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

int permord(perm p)
/* berechnet die Ordnung einer Permutation */
{
  int i, symord=0, ident;
  perm c;
  for (i=1;i<=npkt;i++) c[i]=i;
  do
  {
    symord++;
    ident = 1;
    for (i=1;i<=npkt;i++)
      {
        c[i]=p[c[i]]; if (c[i]==i) { ident++; }
      }
   } while ( ident<npkt );
  return symord;
}

int position(int n, int k, perm p)
/* gibt lexikographischen Index einer Permutation aus */
{
  int i,j,flg,ind;
  i = sortperm(k,p);
  if ((int) i/2 == (float) i/2) flg = false; else flg = true;
  ind = 1;
  for(j=n-p[1]+1;j<n;j++) ind = ind + choose(j,k-1);
  for(i=2;i<=k;i++)
  {
    for(j=n-p[i]+1;j<n-p[i-1];j++) ind = ind + choose(j,k-i);
  }
  if (flg) return(-ind); else return ind;
}

void matroid(int idx, int k)
/* Berechnet Elementliste */
{
int i, z, pos;
char v;
perm u;
if (ex) return;
for(i=k+1;i<=npkt;i++)
    {
      br[idx] = i;
      if (idx==rang) {
                        for(z=1;z<=rang;z++) u[z] = vl[br[z]];
                        ez++;
                        pos = position(npkt,rang,u);
                        if (pos<0) v = vmat[-pos]; else v = vmat[pos];
                        if (v!=vmat[ez]) { ex = true; return; }
                        mat[ez] = v;
                     }
      else matroid(idx+1,i);
    }
}

void writeperm(perm p)
/* gibt Zykeldarstellung der Permutation aus */
{
  int i, j, k, f, enth, anzzyk; perm c;
  anzzyk = 0;
  f = 0;
  c[0] = 1;
  for (i=1;i<=npkt;i++)
  {
    c[i] = p[c[i-1]];
    if (c[i]==c[f])
    {
        anzzyk++;
        if (i-f>1) {
                      fprintf(wohin,"(");
                      for (j=f;j<i;j++) { fprintf(wohin,"%c",ao(c[j])); }
                      fprintf(wohin,")");
                   } /* if (i-f>1) */
        f = i; k = 1;
        do { enth = false;
             k++;
             for (j=1;j<=i;j++) { if (c[j]==k) enth = true; }
           } while (enth);
        c[f] = k;
    } /* if (c[i]==c[f]) */
  } /* for (i=1... */
  if (anzzyk==npkt) fprintf(wohin,"identity");
}

void storeperm(void)
/* speichert das Symmetrieelement als Permutationsvorschrift */
{
    int i;
    for(i=1;i<=npkt;i++) aut[nsym][i]=vl[i];
    aut[nsym][0]=permord(aut[nsym]);
    fprintf(wohin,"No.%i : ",nsym); writeperm(vl); fprintf(wohin,"\n");
}

void doperm(void)
/* berechnet Vorzeichenliste einer Permutation */
{
  ez = 0;
  ex = false;
  matroid(1,0);
  if (!ex) { nsym++; storeperm(); }
}

void visit(int k)
/* die Permutationsroutine nach R. Sedgewick, Algorithms (Addison-Wesley) */
{
  int t;
  iso++;
  vl[k] = iso;
  if (iso==npkt) doperm();
  for (t=1;t<=npkt;t++) { if (vl[t]==0) visit(t); }
  iso--;
  vl[k] = 0;
}

void normalteiler(void)
/* extrahiert aus der Symmetriegruppe eine normale Untergruppe */
{
    int i=1,j, k, norm;
    perm m1, m2;
    fprintf(wohin,"Normal subgroup :\n");
    do {
         j=1; norm=true;
         do {
              k=1;
              do {
                   m1[k]=aut[i][aut[j][k]];
                   m2[k]=aut[j][aut[i][k]];
                   if (m1[k]!=m2[k]) norm=false;
                   k++;
                 } while (k<=npkt && norm);
              j++;
            } while (j<=nsym && norm);
         if (norm)
         {
            fprintf(wohin,"No.%i : ",i);
            writeperm(aut[i]);
            fprintf(wohin,"\n");
         }
         i++;
       } while (i<=nsym);
}

int autnr(perm p)
/* gibt die Nummer des Elements p der Automorphismengruppe aus */
{
    int i=0, j, eq;
    do
    {
        i++; j=0; eq=true;
        do
        {
            j++;
            if (p[j]!=aut[i][j]) eq=false;
        } while (eq && j<npkt);
    } while (!eq && i<nsym);
    return i;
}

void untergruppen(void)
/* berechnet alle disjunkten zyklischen Untergruppen der Symmetriegruppe */
{
   perm p, q, ugr[msy]; int maxord=1,a,b,c,ordn,or,anzugr=0;
   for(a=1;a<=nsym;a++) { for(b=0;b<=npkt;b++) ugr[a][b]=aut[a][b]; }
   fprintf(wohin,"\nDifferent cyclic subgroups of the automorphismgroup are:\n");
   ugr[1][0]=0;
   while (maxord>=1)
   {
     maxord=0;
     for(b=2;b<=nsym;b++)
     {
       ordn=ugr[b][0];
       if (ordn>maxord) maxord=ordn;
     };
     for(a=2;a<=nsym;a++)
     {
       ordn=ugr[a][0];
       if (ordn>0 && ordn==maxord)
       {
         anzugr++; fprintf(wohin,"No.%i : ",anzugr);
         for(b=1;b<=npkt;b++) { p[b]=b; q[b]=ugr[a][b]; }
         fprintf(wohin,"{ id, ");
         for(b=1;b<ordn;b++)
         {
           for(c=1;c<=npkt;c++) p[c]=q[p[c]];
           or=autnr(p);
           fprintf(wohin,"[%i]",or);
           fprintf(wohin,(b<ordn-1)?", ":" ");
           ugr[or][0]=0;
         }
         fprintf(wohin,"}\n");
       }
     }
   }
   anzugr++; fprintf(wohin,"No.%i : { id }\n",anzugr);
}

void writeaut(void)
/* schreibt die Automorphismengruppe als Eingabedatei name.aut */
{
   char autname[50];
   int i, j;
   FILE *autdatei;
   strcpy(autname,name);
   strcat(autname,".aut");
   autdatei = fopen(autname,"w");
   if (autdatei==NULL)
   {
     printf("Error while fileoperation on %s\n",autname);
     exit(1);
   }
   else
   {
     fprintf(autdatei,"%i\n",npkt);
     fprintf(autdatei,"%i\n",nsym);
     for(i=1;i<=nsym;i++)
     {
       for(j=1;j<=npkt;j++) fprintf(autdatei,"%i ",aut[i][j]);
       fprintf(autdatei,"\n");
     }
     fprintf(autdatei,"*");
     fclose(autdatei);
   }
}

/* Das Hauptprogramm */
void main(void)
{
  nsym = 0;
  iso = -1;
  for (i=1;i<mpkt;i++) vl[i] = 0;
  for (i=1;i<mmat;i++) { vmat[i] = '?'; mat[i] = '?'; }

  printf("\nName of input file (without extension .mat): ");
  scanf("%s",name);
  strcpy(inname,name);
  strcpy(outname,name);
  strcat(inname,".mat");
  strcat(outname,".sym");
  indatei = fopen(inname,"r");

  printf("Where should I put the Output to (file/screen) ?");
  scanf("%s",frage);
  if (frage[0]=='f' || frage[0]=='F')
  {
     outdatei = fopen(outname,"w");
     wohin = outdatei;
  }
  else { wohin = stdout; outdatei = stdout; }

  if ((indatei==NULL) || (outdatei==NULL))
  {
    printf(" Error while fileoperation on %s, %s\n",inname, outname);
    exit(1);
  }
  else
    {
      printf("Reading file %s\n",inname);
      fprintf(wohin,"Computing file %s ...\n",inname);
      fscanf(indatei,"%i",&npkt);
      if (npkt>16) { printf("Too many points to compute"); exit(1); }
      fscanf(indatei,"%i",&rang);
      anzmat=choose(npkt,rang);
      nmat = 0;
      do
      {
        do
        {
          in = fgetc(indatei);
        } while (in!='1' && in!='0' && in!='*' && in!=EOF);
        nmat++;
        vmat[nmat] = in;
      }
      while (in!=EOF && in!='*');
      nmat--;
      fclose(indatei);
    }
  for(i=1;i<=nmat;i++) fprintf(wohin,"%c",vmat[i]);
  fprintf(wohin,"\n");
  fprintf(wohin,"There are %i elements ",anzmat);
  fprintf(wohin,"of %i points ",npkt);
  fprintf(wohin,"in rank %i\n\n",rang);
  printf("Number of totally read elements is %i\n",nmat);

  visit(0);
  fprintf(wohin,"\n# of symmetries     : %i",nsym);
  fprintf(wohin,"\n\n");
  writeaut();
  normalteiler();
  untergruppen();
  if (wohin==outdatei) fclose(outdatei);
}
