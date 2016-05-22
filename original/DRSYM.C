/* Symmetries_of_List_of Triangles */
/* Berechnet die Symmetriegruppe einer Dreiecksliste */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define mpkt 16              /* maximale Punktzahl */
#define mdrl 200             /* maximale Anzahl von Dreiecken */
#define msy 500              /* maximale Anzahl an Symmetrien */
#define true  1
#define false 0

typedef int perm[mpkt];
typedef long int longint;

const char hex[16]   = "0123456789ABCDEF";
const char alpha[27] = "0ABCDEFGHIJKLMNOPQRSTUVWXYZ";

int  ndrl,npkt;              /* Anzahl der Dreiecke und Punkte einer Liste */
int  ndrls;                  /* Zahl symmetrischer Dreiecke */
int  i,j,k,iso;              /* diverse Zaehlvariablen */
int  nsym;                   /* Zaehlvariable fuer alle Symmetrien */
longint allsym;              /* Zaehlvariable fuer alle Permutationen */
int  br[mpkt];               /* Kombinationsarray */
int  vl[mpkt];               /* Permutationsarray */
int  id[mpkt];               /* Identit„tsarray */
perm aut[msy];               /* die Elemente der Automorphismengruppe */
int  drl[mdrl][3];           /* Dreiecksliste Dr#, Indizes */
int  drc[mpkt][mpkt][mpkt];  /* kubischer Dreieckslistenarray */
char inwert;                 /* Einzulesender Wert fuer Punktematrix */
char hexalpha[10];           /* Liste Hex oder Alpha */
int  hexa;                   /* hex ja oder nein */

char name[50];               /* Dateiname */
char frage[8];               /* Fragestring */
char inname[50];             /* Dateiname Dreiecksliste */
char outname[50];            /* Dateiname Symmetriedatei */
FILE *indatei;               /* File of Text (Eingabe) */
FILE *outdatei;              /* File of Text (Ausgabe) */
FILE *wohin;

int imax(int x, int y)
/* Die Maximumsfunktion */
{ return (x>y) ? (int) x: (int) y; }

int ai(char c)
/* Hex und Alpha nach Int-Wandler */
{
  int i;
  if (hexa) { for(i=0;c!=hex[i];i++); }
  else { for(i=0;c!=alpha[i];i++); }
  return i;
}

char ao(int i)
/* Int nach Hex-Wandler */
{
    if (hexa) return hex[i & 15];
    else return alpha[i];
}

void abbild()
/* Berechnet und vergleicht die Bilder der Dreiecksliste */
{
  ndrls=1;
  do { ndrls++; }
  while (drc[vl[drl[ndrls][1]]][vl[drl[ndrls][2]]][vl[drl[ndrls][3]]]==1);
  ndrls--;
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
    for(i=1;i<=npkt;i++) { aut[nsym][i] = vl[i]; }
    aut[nsym][0]=permord(aut[nsym]);
    fprintf(wohin,"No.%i : ",nsym); writeperm(vl); fprintf(wohin,"\n");
}

void doperm(void)
/* berechnet Vorzeichenliste einer Permutation */
{
  allsym++;
  ndrls = 0;
  abbild();
  /* if (allsym==1) ndrl = ndrls; */
  if (ndrls==ndrl) { nsym++; storeperm(); }
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

void main(void)
/* Das Hauptprogramm */
{
  int d[2];    /* int-Array von 0..2 */
  allsym = 0;
  nsym = 0;
  iso = -1;
  for (i=1;i<mpkt;i++)
    { vl[i] = 0; id[i] = i; }
  for (i=1;i<mpkt;i++)
  {
     for (j=1;j<mpkt;j++)
     {
        for (k=1;k<mpkt;k++)
          {
             drc[i][j][k]=0;
          }
     }
  }

  printf("\nName of input file (without extension .drl): ");
  scanf("%s",name);
  strcpy(inname,name);
  strcpy(outname,name);
  strcat(inname,".drl");
  strcat(outname,".sym");
  indatei = fopen(inname,"r");

  printf("Where should I put the Output to (file/screen) ?");
  scanf("%s",frage);
  if (frage[0]=='f' || frage[0]=='F')
  {
     outdatei = fopen(outname,"w");
     wohin = outdatei;
  }
  else { wohin = stdout; }

  if ((indatei==NULL) && (outdatei==NULL))
  {
    printf("Error while fileoperation on %s, %s\n",inname, outname);
    exit(1);
  }
  else
    {
      fprintf(wohin,"Reading file %s\n",inname);
      fgets(hexalpha,10,indatei);
      if (hexalpha[0]=='h') hexa=1; else hexa=0;
      ndrl=0; npkt=0;
      do
      {
         ndrl++;
         for(i=0;i<3;i++)
         {
           inwert=fgetc(indatei);
           d[i]=ai(inwert);
           drl[ndrl][i+1]=d[i]; if (d[i]>npkt) npkt=d[i];
         }
         fscanf(indatei,"%c",&inwert);
         drc[d[0]][d[1]][d[2]]=1;   /* all permutations are triangles */
         drc[d[1]][d[2]][d[0]]=1;
         drc[d[2]][d[0]][d[1]]=1;
         drc[d[2]][d[1]][d[0]]=1;
         drc[d[0]][d[2]][d[1]]=1;
         drc[d[1]][d[0]][d[2]]=1;
      } while (inwert!=EOF && inwert!='*');
      fclose(indatei);
    }
  fprintf(wohin,"\nvertices     %i (max. %i)",npkt,mpkt-1);
  fprintf(wohin,"\ntriangles    %i (max. %i)",ndrl,mdrl-1);
  fprintf(wohin,"\n");
  for(i=1;i<=ndrl;i++)
  {
    for(j=1;j<=3;j++)
    { fprintf(wohin,"%c",ao(drl[i][j])); }
    fprintf(wohin," ");
  }
  fprintf(wohin,"\n");
  visit(0);
  fprintf(wohin,"\nThere are %i automorphisms\n",nsym);
  normalteiler();
  untergruppen();
  writeaut();
  if (wohin==outdatei) fclose(outdatei);
}
