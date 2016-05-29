/* Gives sure bases for an admissable matroid for */
/* a 2-CW-complex with linear face boundary */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* #define DEBUG */

#define MPKT 21              /* maximale Punktzahl+1 */
#define MGON 51              /* maximale Anzahl von Facetten+1 */
#define MEDG 241             /* maximale Anzahl an Kanten+1 */
#define MLGON 11             /* maximale Punktanzahl pro Polygonzug+1 */
#define MSY 301              /* maximale Anzahl an Symmetrien+1 */
#define TRUE  1
#define FALSE 0

const char hex[]   = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

typedef unsigned int perm[MPKT];
typedef long int longint;
typedef unsigned int uint;
typedef char boolean;

int  ngon,npkt,nedg;               /* Anzahl der Flaechen, Punkte, Kanten */
int  nlgon;                        /* Zahl der Punkte pro Polygonzug */
char *matroid;                     /* vorzulegende Matroidgrundstruktur */
int  rang;                         /* Rang des Matroids */
int  lenmat;                       /* Laenge der Liste des Matroids */
int  i,j,k,l,iso,zeile;            /* diverse Zaehlvariablen */
perm bra;                          /* Bracket */
perm pz;                           /* Elementauswahlarray */
int  gon[MGON][MLGON];             /* Facettenliste */
int  sgon[MGON][MLGON];            /* Facettenliste lexikographisch sortiert */
uint conn[MPKT][MPKT];             /* Liste der Verbindungen einer Ecke */
char inwert;                       /* Einzulesender Wert */

char name[50];               /* Dateiname */
char frage[10];              /* Fragestring */
char inname[50];             /* Dateiname Polygonliste */
char outname[50];            /* Dateiname Ausgabedatei */
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

int position(int n, int k, perm p)
/* gibt lexikographischen Index einer Permutation aus */
{
  int i,j,flg,ind=1;
  i = sortperm(k,p);
  flg = (i%2==0)?FALSE:TRUE;
  for(j=n-p[1]+1;j<n;j++) ind = ind + choose(j,k-1);
  for(i=2;i<=k;i++)
  {
    for(j=n-p[i]+1;j<n-p[i-1];j++) ind = ind + choose(j,k-i);
  }
  if (flg) return(-ind); else return ind;
}

void writebracket(perm bra)
/* gibt eine Bracket in Klartext aus */
{
    int i;
    fprintf(wohin,"[");
    for(i=1;i<=rang;i++) fprintf(wohin,"%c",hex[bra[i]]);
    fprintf(wohin,"]");
}

int schnitt(int len, int *a, int *b, int *c)
/* c ist die Schnittmenge der Mengen a und b der Laenge len */
{
    int i,j,k;
    k=0;
    for(i=1;i<=len;i++)
      for(j=1;j<=len;j++)
        if (a[i]==b[j]) { k++; c[k]=a[i]; }
    return k;
}

void do_eins(int *a, int *b, int p1, int p2)
/* erzeugt Brackets aus benachbarten Zellen */
{
    int i,j,k;
    for(i=p2+1;i<=nlgon;i++)
    {
        pz[p1]=i;
        if (p1==rang-1)
        {
            for(j=1;j<=nlgon;j++)
            {
               for(k=1;k<=rang-1;k++) bra[k]=a[pz[k]];
               for(k=1;k<=rang-1 && b[j]!=bra[k];k++);
               if (k==rang)
               {
                 bra[rang]=b[j];
                 k = position(npkt,rang,bra);
                 if (k<0) k=-k;
#ifdef DEBUG
                 writebracket(bra); fprintf(wohin,"\n");
#endif
                 matroid[k]='1';
               }
            }
        }
        else do_eins(a,b,p1+1,i);
    }
}

void setze_einsen(void)
/* setzt Einsen aufgrund von benachbarten Zellen */
{
    int i,j,k,l;
    int *z1, *z2, *cut;
    z1  = calloc(nlgon+1,sizeof(int));
    z2  = calloc(nlgon+1,sizeof(int));
    cut = calloc(nlgon+1,sizeof(int));
    for(i=1;i<=ngon;i++)
      for(j=i+1;j<=ngon;j++)
      {
         for(k=1;k<=nlgon;k++) { z1[k]=sgon[i][k]; z2[k]=sgon[j][k]; }
         l=schnitt(nlgon,z1,z2,cut);
#ifdef DEBUG
           fprintf(wohin,"\ni=%i, j=%i, l=%i {",i,j,l);
           for(k=1;k<=l-1;k++) fprintf(wohin,"%c,",hex[cut[k]]);
           fprintf(wohin,"%c}\n",hex[cut[l]]);
#endif
         if (l>=rang-2)
         {
            do_eins(z1,z2,1,0);
#ifdef DEBUG
            fprintf(wohin,"----------------\n");
#endif
            do_eins(z2,z1,1,0);
         }
      }
}

void perm_zellen(int nr,int p1, int p2)
/* waehlt Brackets aus Zellenpunkten aus */
{
    int i,j;
    for(i=p2+1;i<=nlgon;i++)
    {
        pz[p1]=i;
        if (p1==rang)
        {
            for(j=1;j<=rang;j++) bra[j]=sgon[nr][pz[j]];
            j = position(npkt,rang,bra);
            if (j<0) j=-j;
            matroid[j]='0';
        }
        else perm_zellen(nr,p1+1,i);
    }
}

void setze_nullen(void)
/* setzt Nullen aufgrund der vorhandenen Zellen */
{
  int i;
  for(i=1;i<=ngon;i++) perm_zellen(i,1,0);
}

void main(int aanz, char *arg[])
/* Das Hauptprogramm */
{
  int d[MLGON];
  iso = -1;
  for (i=1;i<MPKT;i++)
  {
    for(j=1;j<MPKT;j++) conn[i][j]=0;
  } 

  printf("This program computes sure bases for an admissable matroid for\n");
  printf("a 2-CW-complex with linear facette-boundaries\n");
  if (arg[1]==NULL)
  {
    printf("\nName of input file (without extension .gon): ");
    scanf("%s",name);
  }
  else strcpy(name,arg[1]);
  strcpy(inname,name);
  strcpy(outname,name);
  strcat(inname,".gon");
  strcat(outname,".bas");
  indatei = fopen(inname,"r");

  if (arg[2]!=NULL) strcpy(frage,arg[2]);

  if (frage[0]!='s' && frage[0]!='S' && frage[0]!='f' && frage[0]!='F')
  {
    printf("Where should I put the Output to (file/screen) ?");
    scanf("%s",frage);
  }

  if (frage[0]=='f' || frage[0]=='F')
  {
     printf("\nOutput file is %s\n",outname);
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
#ifdef DEBUG
      fprintf(wohin,"Computing file %s\n",inname);
#endif
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
#ifdef DEBUG
  fprintf(wohin,"\nvertices %i",npkt);
  fprintf(wohin,"\nedges    %i",nedg);
  fprintf(wohin,"\nfaces    %i",ngon);
  fprintf(wohin,"\ngenus    %i",(2-npkt+nedg-ngon)/2);
  fprintf(wohin,"\n");
  fprintf(wohin,"\nFacettes are\n");
  zeile=0;
  for(i=1;i<=ngon;i++)
  {
    for(j=1;j<=nlgon;j++) fprintf(wohin,"%c",hex[gon[i][j]]);
    fprintf(wohin," "); zeile=zeile+nlgon+1;
    if (zeile>72) { zeile=0; fprintf(wohin,"\n"); }
  }
  zeile=0;
  fprintf(wohin,"\nEdges are\n");
  for(i=1;i<=npkt;i++)
    for(j=i;j<=npkt;j++)
    {
      if (conn[i][j]==1)
      {
         fprintf(wohin,"%c%c ",hex[i],hex[j]);
         zeile=zeile+3;
      }
      if (zeile>72) { zeile=0; fprintf(wohin,"\n"); }
    }
  fprintf(wohin,"\n\n");
#endif

  rang = 4;

  lenmat = choose(npkt,rang);

  matroid = calloc(lenmat+1,sizeof(char));
  for(i=1;i<=lenmat;i++) matroid[i]='?';

  setze_einsen();
  setze_nullen();

#ifdef DEBUG
  fprintf(wohin,"An admissable matroid to %s has surely ",inname);
  fprintf(wohin,"the following structure:\n\n");
#endif
  fprintf(wohin,"%i\n%i\n",npkt,rang);
  for(i=1;i<=lenmat;i++)
  {
    fprintf(wohin,"%c",matroid[i]);
    if (i%72==0) fprintf(wohin,"\n");
  }
  fprintf(wohin,"*");
  if (wohin==outdatei) fclose(outdatei);
}
