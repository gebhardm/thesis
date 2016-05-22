/* AUtomorphismgroup_ON_MATroid */
/* testet eine Matroidliste auf Erfuellung einer Automorphismengruppe */
/* by Markus Gebhard, THD, FB04AG3b */

#include <stdio.h>
#include <string.h>

#define mpkt 17              /* maximale Punktzahl + 1 */
#define mrng 5               /* maximaler Rang */
#define mvrz 8000            /* maximale Anzahl von Vorzeichen + 1 */
#define msy 500              /* maximale Anzahl an Symmetrien + 1 */
#define true  1
#define false 0

typedef int perm[mpkt];
typedef long int longint;

const char hex[]   = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

int  nvrz,npkt,anzvrz;       /* Anzahl der Vorzeichen und Punkte */
int  inpkt;                  /* Anzahl der Punkte der vorgeg. Automorphismen */
int  anzaut;                 /* Anzahl der vorgegebenen Automorphismen */
int  rang;                   /* Rang des Chirotops */
int  i,j,k,iso;              /* diverse Zaehlvariablen */
int  nsym;                   /* Zaehlvariable fuer alle Symmetrien */
int  vzz;                    /* Vorzeichenzaehler */
int  ex;                     /* Symmetrie ? */
perm br;                     /* Kombinationsarray */
perm vl;                     /* Permutationsarray */
perm id;                     /* Identitaetsarray */
perm aut[msy];               /* die Elemente der Automorphismengruppe */
perm inaut[msy];             /* eingelesene Automorphismen */
char mat[mvrz], vrz[mvrz];   /* Matroidliste */
char in;                     /* Einzulesender Wert fuer Vorzeichenliste */
char instr[80];              /* Eingabezeile fuer Fragen */

char name[50];               /* Dateiname */
char inname[50];             /* Dateiname Vorzeichenliste */
char outname[50];            /* Dateiname Symmetriedatei */
char autname[50];            /* Name der Automorphismendatei */
FILE *indatei;               /* File of Text (Eingabe) */
FILE *outdatei;              /* File of Text (Ausgabe) */
FILE *autdatei;              /* File of Text (Automorphismen der Eingabe) */
FILE *wohin;

char ao(int x)
{ return hex[x]; }

int ai(char x)
{
  if (x>47 && x<58) return ((int) x-48);
  else if (x>64 && x<91) return ((int) x-55);
       else if (x>96 && x<123) return ((int) x-61);
            else return -1;
}

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
  int i,j,ind;
  i = sortperm(k,p);
  ind = 1;
  for(j=n-p[1]+1;j<n;j++) ind = ind + choose(j,k-1);
  for(i=2;i<=k;i++)
  {
    for(j=n-p[i]+1;j<n-p[i-1];j++) ind = ind + choose(j,k-i);
  }
  return(ind);
}

void matroid(int idx, int k)
/* Berechnet Brackets einer Matroidliste */
{
int i, z;
char v;
perm u;
if (ex) return;
for(i=k+1;i<=npkt;i++)
    {
      br[idx] = i;
      if (idx==rang) {
                     for(z=1;z<=rang;z++) u[z] = vl[br[z]];
                     vzz++;
                     v = mat[position(npkt,rang,u)];
                     if (v!=mat[vzz]) { ex = true; return; }
                     vrz[vzz] = v;
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
  vzz = 0;
  ex = false;
  matroid(1,0);
  if (!ex) { nsym++; storeperm(); }
}

void proveaut(void)
/* prueft alle vorgegebenen Automorphismen auf Symmetrie der Vorzeichenliste */
{
  int i,j;
  for(i=1;i<=anzaut;i++)
  {
    for(j=1;j<=npkt;j++) vl[j] = inaut[i][j];
    doperm();
  }
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

/* Das Hauptprogramm */
void main(void)
{
  nsym = 0;
  iso = -1;
  for (i=1;i<mpkt;i++) { vl[i] = 0; id[i]=i; }
  for (i=1;i<mvrz;i++) mat[i] = '?';

  printf("\nThis program tests defined automorphisms of a matroidlist\n");
  printf("\nName of file with signlist (without extension .mat): ");
  scanf("%s",name);
  strcpy(inname,name);
  strcat(inname,".mat");
  strcpy(outname,name);
  strcat(outname,".sym");
  printf("\nName of file with automorphisms (without extension .aut): ");
  scanf("%s",name);
  strcpy(autname,name);
  strcat(autname,".aut");

  indatei  = fopen(inname,"r");
  autdatei = fopen(autname,"r");
  printf("Where should I put the Output to (file/screen) ?");
  scanf("%s",name);
  if (name[0]=='f' || name[0]=='F')
  {
     printf("Outfile is %s\n",outname);
     outdatei = fopen(outname,"w");
     wohin = outdatei;
  }
  else { wohin = stdout; outdatei = stdout; }

  if (indatei==NULL)
  { printf("Error while fileoperation on %s\n",inname); exit(1); }
  else
  if (outdatei==NULL)
  { printf("Error while fileoperation on %s\n",outname); exit(1); }
  else
  if (autdatei==NULL)
  { printf("Error while fileoperation on %s\n",autname); exit(1); }
  else
    {
      printf("Reading file %s\n",inname);
      fprintf(wohin,"Computing file %s ...\n",inname);
      fscanf(indatei,"%i",&npkt);
      if (npkt>16) { printf("Too many points to compute"); exit(1); }
      fscanf(indatei,"%i",&rang);
      anzvrz=choose(npkt,rang);
      nvrz = 0;
      do
      {
        do
        {
          in = fgetc(indatei);
        } while (in!='1' && in!='0' && in!='*' && in!=EOF);
        nvrz++;
        mat[nvrz] = in;
      }
      while (nvrz<=anzvrz && in!=EOF && in!='*');
      fclose(indatei);
      fscanf(autdatei,"%i",&inpkt);
      if (inpkt!=npkt) { printf("Number of points not equal"); exit(1); }
      fscanf(autdatei,"%i",&anzaut);
      for(i=1;i<=anzaut;i++)
      {
        for(j=1;j<=npkt;j++)
        {
          fscanf(autdatei,"%i",&inaut[i][j]);
          /* printf("%i ",inaut[i][j]); */
        }
        in = fgetc(autdatei);
        /* printf("\n"); */
      }
      fclose(autdatei);
    }
  for(i=1;i<=anzvrz;i++) fprintf(wohin,"%c",mat[i]);
  fprintf(wohin,"\n");
  fprintf(wohin,"There are %i signs ",anzvrz);
  fprintf(wohin,"of %i points ",npkt);
  fprintf(wohin,"in rank %i\n\n",rang);

  proveaut();
  fprintf(wohin,"\n# of symmetries     : %i",nsym);
  fprintf(wohin,"\n\n");
  normalteiler();
  untergruppen();
  if (wohin==outdatei) fclose(outdatei);
}
