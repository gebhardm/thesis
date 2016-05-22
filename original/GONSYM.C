/* Symmetries_of_List_of_n_gons */
/* Berechnet die Symmetriegruppe einer Liste polygonal begrenzter Zellen */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MPKT 21              /* maximale Punktzahl+1 */
#define MGON 51              /* maximale Anzahl von Facetten+1 */
#define MEDG 241             /* maximale Anzahl an Kanten+1 */
#define MLGON 11             /* maximale Punktanzahl pro Polygonzug+1 */
#define MSY 301              /* maximale Anzahl an Symmetrien+1 */
#define TRUE  1
#define FALSE 0

const char hex[62]   = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

typedef unsigned int perm[MPKT];
typedef long int longint;
typedef unsigned int uint;
typedef char boolean;

int  ngon,npkt,nedg;               /* Anzahl der Flaechen, Punkte, Kanten */
int  ngons;                        /* Zahl symmetrischer Tetraeder */
int  nlgon;                        /* Zahl der Punkte pro Polygonzug */
int  i,j,k,l,iso;                  /* diverse Zaehlvariablen */
int  nsym;                         /* Zaehlvariable fuer alle Symmetrien */
perm br, vl;                       /* Kombinations-, Permutationsarray */
perm aut[MSY];                     /* die Elemente der Automorphismengruppe */
int  gon[MGON][MLGON];             /* Facettenliste */
int  sgon[MGON][MLGON];            /* Facettenliste lexikographisch sortiert */
uint conn[MPKT][MPKT];             /* Liste der Verbindungen einer Ecke */
char inwert;                       /* Einzulesender Wert */

char name[50];               /* Dateiname */
char frage[10];              /* Fragestring */
char inname[50];             /* Dateiname Polygonliste */
char outname[50];            /* Dateiname Symmetriedatei */
FILE *indatei;               /* File of Text (Eingabe) */
FILE *outdatei;              /* File of Text (Ausgabe) */
FILE *wohin;

int ai(char c)
/* (Pseudo-)Hex nach Int-Wandler */
{
  int i;
  for(i=0;c!=hex[i];i++);
  return i;
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
                      for (j=f;j<i;j++) { fprintf(wohin,"%c",hex[c[j]]); }
                      fprintf(wohin,")");
                   } /* if (i-f>1) */
        f = i; k = 1;
        do { enth = FALSE;
             k++;
             for (j=1;j<=i;j++) { if (c[j]==k) enth = TRUE; }
           } while (enth);
        c[f] = k;
    } /* if (c[i]==c[f]) */
  } /* for (i=1... */
  if (anzzyk==npkt) fprintf(wohin,"identity");
}

int ingon(int q[MLGON])
/* prueft, ob ein Facettenbild eine Facette ist */
{
    int j, i=1, ing=FALSE, eq;
    while (!ing && i<=ngon)
    {
      j=1; eq=TRUE;
      while (eq && j<=nlgon)
      {
        if (q[j]!=sgon[i][j]) eq=FALSE;
        j++; 
      }
      if (eq) ing=TRUE;
      i++;
    }
    return (ing?1:0);
}

int abbild(void)
/* Berechnet und vergleicht die Bilder der Facetten */
{
  int a[MLGON], b[MLGON], i, z=1, ok=TRUE;
  do
  {
    for(i=1;i<=nlgon;i++) { a[i] = vl[gon[z][i]]; b[i] = a[i]; }
    i=sortperm(nlgon,b);
    if (!ingon(b)) ok=FALSE;
    i=1;
    while ((ok) && (i<nlgon))
    {
      if (conn[a[i]][a[i+1]]==0) ok=FALSE;
      i++;
    }
    if (ok) { if (conn[a[nlgon]][a[1]]==0) ok=FALSE; }
    z++;
  } while (z<=ngon && ok);
  return ok;
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

void storeperm(void)
/* speichert das Symmetrieelement als Permutationsvorschrift */
{
    int i;
    for(i=1;i<=npkt;i++) { aut[nsym][i] = vl[i]; }
    aut[nsym][0]=permord(aut[nsym]);
    fprintf(wohin,"No.%i : ",nsym); writeperm(vl); fprintf(wohin,"\n");
}

void doperm(void)
/* berechnet Vorzeichenliste einer Permutation */
{
  if (abbild()) { nsym++; storeperm(); }
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
    fprintf(wohin,"\nNormal subgroup :\n");
    do {
         j=1; norm=TRUE;
         do {
              k=1;
              do {
                   m1[k]=aut[i][aut[j][k]];
                   m2[k]=aut[j][aut[i][k]];
                   if (m1[k]!=m2[k]) norm=FALSE;
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
        i++; j=0; eq=TRUE;
        do
        {
            j++;
            if (p[j]!=aut[i][j]) eq=FALSE;
        } while (eq && j<npkt);
    } while (!eq && i<nsym);
    return i;
}

void untergruppen(void)
/* berechnet alle disjunkten zyklischen Untergruppen der Symmetriegruppe */
{
   perm p, q, ugr[MSY]; int maxord=1,a,b,c,ordn,or,anzugr=0;
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

void main(int aanz, char *arg[])
/* Das Hauptprogramm */
{
  int d[MLGON];
  nsym = 0;
  iso = -1;
  for (i=1;i<MPKT;i++)
  {
    vl[i] = 0;
    for(j=1;j<MPKT;j++) conn[i][j]=0;
  } 

  printf("This program computes automorphisms of 2-CW-complexes\n");
  printf("with linear facette-boundaries\n");
  if (arg[1]==NULL)
  {
    printf("\nName of input file (without extension .gon): ");
    scanf("%s",name);
  }
  else strcpy(name,arg[1]);
  strcpy(inname,name);
  strcpy(outname,name);
  strcat(inname,".gon");
  strcat(outname,".sym");
  indatei = fopen(inname,"r");

  if (arg[2]!=NULL) strcpy(frage,arg[2]);

  if (frage[0]!='s' && frage[0]!='S' && frage[0]!='f' && frage[0]!='F')
  {
    printf("Where should I put the Output to (file/screen) ?");
    scanf("%s",frage);
  }

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
      fprintf(wohin,"Computing file %s\n",inname);
      fscanf(indatei,"%i",&nlgon);
      if(nlgon>=MLGON)
      {
        printf("\nError : Too many points per facette");
        fclose(indatei); fclose(outdatei);
        exit(1);
      }
      fgets(frage,10,indatei);
      ngon=0; nedg=0; npkt=0;
      do
      {
         ngon++;
         for(i=0;i<nlgon;i++)
         {
           inwert=fgetc(indatei);
           d[i]=ai(inwert);
           gon[ngon][i+1]=d[i]; sgon[ngon][i+1]=d[i];
           if (d[i]>npkt) npkt=d[i];
         }
         for(i=0;i<nlgon-1;i++)
           { conn[d[i]][d[i+1]]=1; conn[d[i+1]][d[i]]=1; }
         conn[d[nlgon-1]][d[0]]=1; conn[d[0]][d[nlgon-1]]=1;
         j=sortperm(nlgon,sgon[ngon]);
         fscanf(indatei,"%c",&inwert);
      } while (inwert!=EOF && inwert!='*');
      fclose(indatei);
    }
  for(i=1;i<=npkt;i++)
    for(j=i;j<=npkt;j++) if (conn[i][j]==1) nedg++;
  fprintf(wohin,"\nvertices %i",npkt);
  fprintf(wohin,"\nedges    %i",nedg);
  fprintf(wohin,"\nfaces    %i",ngon);
  fprintf(wohin,"\ngenus    %i",(2-npkt+nedg-ngon)/2);
  fprintf(wohin,"\n");
  fprintf(wohin,"\nFacettes are\n");
  for(i=1;i<=ngon;i++)
  {
    for(j=1;j<=nlgon;j++) fprintf(wohin,"%c",hex[gon[i][j]]);
    fprintf(wohin," ");
  }
  fprintf(wohin,"\nEdges are\n");
  for(i=1;i<=npkt;i++)
    for(j=i;j<=npkt;j++)
      if (conn[i][j]==1) fprintf(wohin,"%c%c ",hex[i],hex[j]);
  fprintf(wohin,"\n\n");
  visit(0);
  fprintf(wohin,"\nThere are %i automorphisms\n",nsym);
  normalteiler();
  untergruppen();
  writeaut();
  if (wohin==outdatei) fclose(outdatei);
}
