/* program Symmetries_on_Grassmann_Pluecker-Relations */
/* Programm zum erzeugen von Matroiden unter Symmetrievorgaben */
/* by Markus Gebhard, THD, FB04AG3b */
/* Projekt im Rahmen einer Diplomarbeit Juli 1994 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MPKT 13              /* maximale Punktzahl + 1 */
#define MRNG 5               /* maximaler Rang */
#define MSY 100              /* maximale Anzahl an Symmetrien + 1 */
#define MBRA 500             /* maximale Anzahl an Bracketorbits (12 ueber 4)*/
#define TRUE  1
#define FALSE 0

typedef unsigned int perm[MPKT];
typedef unsigned long int longint;
typedef unsigned int uint;
typedef char boolean;
typedef unsigned int gleichung[7];

const char hex[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

uint baumtiefe;              /* Tiefe der Rekursion */
uint npkt;                   /* Anzahl der Punkte */
uint inpkt;                  /* Anzahl der Punkte der vorgeg. Automorphismen */
uint anzaut;                 /* Anzahl der vorgegebenen Automorphismen */
uint anzbr;                  /* Anzahl der erzeugten Brackets pro Orbit */
uint anzbro;                 /* Anzahl der Bracketorbits */
uint anzgpr;                 /* Anzahl der erzeugten GPR pro Orbit */
uint anzgpo;                 /* Anzahl der GPR-Orbits */
uint anzgl;                  /* Anzahl der zu erfuellenden Gleichungen */
uint rang;                   /* Rang des Chirotops / Matroids */
int  i,j,k,iso;              /* diverse Zaehlvariablen */
uint bra[MBRA][MSY];         /* Vergleichsliste fuer die Brackets */
perm br;                     /* Kombinationsarray */
perm a,b;                    /* Indexmengen fuer GPR */
perm *erza;                  /* erzeugte bzw. gekoppelte GPR */
perm *erzb;
perm *erzbr;                 /* Brackets im Orbit */
perm *orbit;                 /* Repraesentanten der Orbits der GPR */
gleichung *gpr;              /* Zeiger auf die GPRn als Gleichungen */
uint na,nb;                  /* Anzahl der Elemente in den GPR */
perm *aut;                   /* eingelesene Automorphismen */
char in;                     /* Einzulesender Wert fuer Vorzeichenliste */
char instr[80];              /* Eingabezeile fuer Fragen */

char name[50];               /* Dateiname */
#ifdef DEBUG
char outname[50];            /* Dateiname Ausgabedatei fuer Debuginfos */
FILE *outdatei;              /* File of Text (Ausgabe) */
#endif
char autname[50];            /* Name der Automorphismendatei */
FILE *autdatei;              /* File of Text (Automorphismen der Eingabe) */
char matname[50];            /* Name der Matroiddatei */
FILE *matdatei;              /* File of Text (moegliche Matroide) */
FILE *wohin;

/* ######################################################################### */

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

/* ######################################################################### */

int swap(int *a, int *b)
/* tauscht Werte a und b, aufrufen mit swap(&a,&b) */
{
  int c;
   c = *a;
  *a = *b;
  *b = c;
  return 0;
}

/* ######################################################################### */

int sortperm(int k, perm p)
/* sortiert eine Permutation lexikographisch und gibt Fehlstellenanzahl zurueck */
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

/* ######################################################################### */

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

/* ######################################################################### */

void bracket(int nr, int n, int k, perm x)
/* Erzeugt zur Nummer 'nr' das zugeordnete k-Tupel 'x'.
   Nach kanonischer Sortierung. Die Umkehrfunktion ist POSITION.
   Mit freundlicher Unterstuetzung von Peter Schuchert (c) 1993 */
{
   int i,j,l,bin;
   nr--;
   l = 0;
   for(i=1;i<=k;i++)
   {
      bin = 0;
      j = n-l;
      do
      {
        l++;
        j--;
        nr = nr-bin;
        bin = choose(j, k-i);
      } while (nr>=bin);
      x[i] = l;
   }
}  /* bracket */

#ifdef DEBUG
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
#endif

/* ######################################################################### */

void bracketorbits(int idx, int k)
/* Berechnet permutierte Bracket */
{
int i, j, z, vrz, w1, w2; perm pe;
for(i=k+1;i<=npkt;i++)
    {
      br[idx] = i;
      if (idx==rang)
      {
        for(j=1;j<=anzaut;j++)
        {
          for(z=1;z<=rang;z++) pe[z] = aut[j][br[z]];
          vrz = sortperm(rang,pe);
          if (j==1) { anzbr=0; w1=position(npkt,rang,pe); }
          w2=position(npkt,rang,pe);
          if (w2>=w1)
          {
             anzbr++;
             erzbr[anzbr][0]=vrz;
             for(z=1;z<=rang;z++) erzbr[anzbr][z]=pe[z];
          }
        }
        if (anzbr==anzaut)
        {
            anzbro++;
            for(j=1;j<=anzaut;j++)
            {
                bra[anzbro][j]=position(npkt,rang,erzbr[j]);
                bra[anzbro][0]=2; /* heisst hier, dass Bracket ungesetzt */
            }
	  }
      }
      else bracketorbits(idx+1,i);
    }
}

/* ######################################################################### */

void null_br(void)
/* laesst Auswahl von Brackets zu Null zu */
{
   int i,j; perm bkt;
   printf("\nRepresentants of the bracket orbits are :\n");
   for(i=1;i<=anzbro;i++)
   {
      bracket(bra[i][1],npkt,rang,bkt);
      printf("No. %3i : [",i);
      for(j=1;j<=rang;j++) printf("%c",hex[bkt[j]]);
      printf("]   ");
      if (i%4==0) printf("\n");
   }
   printf("\nWhich orbit should be set to 0 ? (0 = exit)\n");
   do
   {
      printf("Orbit No. >"); scanf("%i",&i);
      if (i>0 && i<=anzbro) bra[i][0]=0;
      else if (i!=0) printf("1 <= No. <= %i !\n",anzbro);
   } while (i!=0);
#ifdef DEBUG
   fprintf(wohin,"Bracket orbits set to 0 are :\n");
   for(i=1;i<=anzbro;i++) if (bra[i][0]==0) fprintf(wohin,"(#%i) ",i);
   fprintf(wohin,"\n");
#endif
}

/* ######################################################################### */

void eins_br(void)
/* laesst Auswahl von Brackets zu Eins zu */
{
   int i,j; perm bkt;
   printf("\nRepresentants of the bracket orbits are :\n");
   for(i=1;i<=anzbro;i++)
   {
      bracket(bra[i][1],npkt,rang,bkt);
      printf("No. %3i : [",i);
      for(j=1;j<=rang;j++) printf("%c",hex[bkt[j]]);
      printf("]   ");
      if (i%4==0) printf("\n");
   }
   printf("\nWhich orbit should be set to 1 ? (0 = exit)\n");
   do
   {
      printf("Orbit No. >"); scanf("%i",&i);
      if (i>0 && i<=anzbro) bra[i][0]=1;
      else if (i!=0) printf("1 <= No. <= %i !\n",anzbro);
   } while (i!=0);
#ifdef DEBUG
   fprintf(wohin,"Bracket orbits set to 1 are :\n");
   for(i=1;i<=anzbro;i++) if (bra[i][0]==1) fprintf(wohin,"(#%i) ",i);
   fprintf(wohin,"\n");
#endif
}

/* ######################################################################### */

int change(perm br)
/* ersetzt eine vorgegebene Bracket durch den Repraesentanten des Orbits */
{
    int i=0,j,nr;
    nr = position(npkt,rang,br);
    do
    {
        j=0; i++;
        do
        {
           j++;
        } while (bra[i][j]!=nr && j<anzaut);
    } while (bra[i][j]!=nr && i<anzbro);
    bracket(bra[i][1],npkt,rang,br);
    return(bra[i][0]);                 /* Orbit zu Null gesetzt ? */
}

/* ######################################################################### */

uint br_orb_nr(perm br)
/* gibt die Nummer des Orbits der Bracket br zurueck */
{
    int i=0,nr;
    nr = position(npkt,rang,br);
    do { i++; } while (bra[i][1]!=nr && i<anzbro);
    return i;
}

/* ######################################################################### */

void gprorbits(void)
/* berechnet zu einer GPR deren Orbit */
{
    int i,j;
    perm ma,mb,ausw;           /* Grundmengen fuer GPR */
    perm sa,sb;                /* GPR-Grundmengen unter einer Symmetrie */
    int  v,v1,v2;              /* Vorzeichen der Umordnung */
    uint p1,p2,q1,q2;          /* lexikographische Position der GPR */
    uint out;
    for(i=1;i<=npkt;i++) ausw[i] = i;
    for(i=1;i<=na;i++) { ma[i] = ausw[a[i]]; ausw[a[i]] = npkt+1; }
    i=sortperm(npkt,ausw);
    for(i=1;i<=nb;i++) mb[i] = ausw[b[i]];
    for(i=1;i<=anzaut;i++)
    {
        v = 1;
        for(j=1;j<=na;j++) sa[j]=aut[i][ma[j]];
        v1=sortperm(na,sa); if (v1%2==0) v1 = 1; else v1 = -1;
        for(j=1;j<=nb;j++) sb[j]=aut[i][mb[j]];
        v2=sortperm(nb,sb); if (v2%2==0) v2 = 1; else v2 = -1;
        v = v1 * v2;
        p1 = position(npkt,na,sa);
        p2 = position(npkt,nb,sb);
        if (i==1) { anzgpr=0; q1=p1; q2=p2; }
        if (p1>q1) out = TRUE;
        else if (p1==q1 && p2>=q2) out = TRUE;
             else out = FALSE;
        if (out)
        {
           anzgpr++;
           erza[i][0]=v;
           for(j=1;j<=na;j++) erza[i][j] = sa[j];
           for(j=1;j<=nb;j++) erzb[i][j] = sb[j];
        }
    }
    if (anzgpr==anzaut)
    {
        anzgpo++;
        for(i=1;i<=na;i++) orbit[anzgpo][i]=erza[1][i];
        for(i=1;i<=nb;i++) orbit[anzgpo][i+na]=erzb[1][i];
    }
}

/* ######################################################################### */

void make_equations(gleichung *gp)
/* erzeugt das Gleichungssystem un */
/* gibt Repraesentanten der Orbits der GPR aus */
{
    int i,j,k,v[7],nl[7];
    perm brk[7];
#ifdef DEBUG
    fprintf(wohin,"\nRepresenting elements of GPR orbits are:\n");
#endif
    for(j=1;j<=anzgpo;j++)
    {
#ifdef DEBUG
       fprintf(wohin,"{");
       for(i=1;i<=na;i++) fprintf(wohin,"%c",hex[orbit[j][i]]);
       fprintf(wohin,"|");
       for(i=1;i<=nb;i++) fprintf(wohin,"%c",hex[orbit[j][i+na]]);
       fprintf(wohin,"}  ");
       if (j%6==0) fprintf(wohin,"\n");
#endif
       for(k=1;k<=6;k++)
         { for(i=1;i<=na;i++) brk[k][i] = orbit[j][i]; }
       brk[1][na+1] = orbit[j][na+1]; brk[1][na+2] = orbit[j][na+2];
       brk[2][na+1] = orbit[j][na+3]; brk[2][na+2] = orbit[j][na+4];
       brk[3][na+1] = orbit[j][na+1]; brk[3][na+2] = orbit[j][na+3];
       brk[4][na+1] = orbit[j][na+2]; brk[4][na+2] = orbit[j][na+4];
       brk[5][na+1] = orbit[j][na+1]; brk[5][na+2] = orbit[j][na+4];
       brk[6][na+1] = orbit[j][na+2]; brk[6][na+2] = orbit[j][na+3];
       for(k=1;k<=6;k++)
       {
          v[k]      = (sortperm(rang,brk[k])%2==0)?1:-1;
          nl[k]     = change(brk[k]);
          gp[j][k]  = br_orb_nr(brk[k]);
       }
    } /* for(j=... */
#ifdef DEBUG
    fprintf(wohin,"\n");
#endif
}

/* ######################################################################### */

int gt(uint x[7],uint y[7])
/* prueft, ob x lexikographisch groesser als y ist */
{
    if (x[1]>y[1]) return 1;
    else if (x[1]==y[1]) if (x[2]>y[2]) return 1;
    else if (x[2]==y[2]) if (x[3]>y[3]) return 1;
    else if (x[3]==y[3]) if (x[4]>y[4]) return 1;
    else if (x[4]==y[4]) if (x[5]>y[5]) return 1;
    else if (x[5]==y[5]) if (x[6]>y[6]) return 1;
    else return 0;
   return 0;
}

/* ######################################################################### */

boolean validgpr(gleichung e)
/* prueft, ob eine Gleichung ueber GF(2) erfuellt ist */
{
   int i;
   for(i=1;i<=6;i++)
   {
      if (e[i]==2)
        if (i%2!=0) break;
        else if (e[i-1]!=0) break;
   }
   i--;
   if (i==6)
   {
     if((int)(e[1]*e[2]+e[3]*e[4]+e[5]*e[6]+e[1]*e[2]*e[3]*e[4]*e[5]*e[6])%2==0)
       return TRUE;
     else return FALSE;
   }
   else return TRUE;
}

/* ######################################################################### */

int sortgpr(int anzg, gleichung *gp, uint *bset, uint *bgh)
/* sortiert die Gleichungen der GPRn kanonisch und gibt sie aus */
{
    int i,j,k,equ,anzgln;
    boolean valid, redo;
    gleichung v, gl;
    /* die Gleichungen selbst werden sortiert */
    for(i=1;i<=anzg;i++)
    {
      for(j=1;j<=6;j++) if (bset[gp[i][j]]==0) gp[i][j]=0;
      for(j=1;j<=3;j++)
      { if (gp[i][2*j-1]>gp[i][2*j]) swap(&gp[i][2*j-1],&gp[i][2*j]); }
      if (gp[i][1]>gp[i][3])
      { swap(&gp[i][1],&gp[i][3]); swap(&gp[i][2],&gp[i][4]); }
      if (gp[i][1]>gp[i][5])
      { swap(&gp[i][1],&gp[i][5]); swap(&gp[i][2],&gp[i][6]); }
      if (gp[i][3]>gp[i][5])
      { swap(&gp[i][3],&gp[i][5]); swap(&gp[i][4],&gp[i][6]); }
      if (gp[i][1]==gp[i][3] && gp[i][2]>gp[i][4])
      { swap(&gp[i][1],&gp[i][3]); swap(&gp[i][2],&gp[i][4]); }
      if (gp[i][1]==gp[i][5] && gp[i][2]>gp[i][6])
      { swap(&gp[i][1],&gp[i][5]); swap(&gp[i][2],&gp[i][6]); }
      if (gp[i][3]==gp[i][5] && gp[i][4]>gp[i][6])
      { swap(&gp[i][3],&gp[i][5]); swap(&gp[i][4],&gp[i][6]); }
      if (gp[i][1]==0)
      {
        if (gp[i][3]!=0)
        {
          swap(&gp[i][1],&gp[i][3]); swap(&gp[i][2],&gp[i][4]);
        }
        else if (gp[i][5]!=0)
        {
          swap(&gp[i][1],&gp[i][5]); swap(&gp[i][2],&gp[i][6]);
        }
      }
      if (gp[i][3]==0)
      {
        if (gp[i][5]!=0)
        {
          swap(&gp[i][3],&gp[i][5]); swap(&gp[i][4],&gp[i][6]);
        }
      }
    } /* for(i=... */
    /* das Gleichungssystem wird sortiert */
    /* Insertion Sort nach R. Sedgewick */
    /* (abgewandelt fuer lexikographische Sortierung) */
    for(i=2;i<=anzg;i++)
    {
        for(k=1;k<=6;k++) v[k]=gp[i][k];
        j=i;
        while (gt(gp[j-1],v))
        {
          for(k=1;k<=6;k++) gp[j][k]=gp[j-1][k];
          j--;
        }
        for(k=1;k<=6;k++) gp[j][k]=v[k];
    }
    /* alle redundanten Gleichungen werden entfernt */
    anzgln=0; valid=TRUE;
    for(i=1;i<=anzg && valid;i++)
    {
      equ=(i != 1);
      for(j=1;j<=6;j++) { gl[j] = gp[i][j]; v[j] = bset[gp[i][j]]; }

      /* handelt es sich um eine gueltige Gleichung ? */
      valid = validgpr(v);
#ifdef DEBUG
      if (!valid) fprintf(wohin,"Peng !\n");
#endif

      /* jetzt die redundanten Gleichungen rausschmeissen */
      if (gl[1]==0 && gl[3]==0 && gl[5]==0) equ=TRUE;
      else
      if (gl[5]==0)
      {
        if (v[1]==1 && v[2]==1 && v[3]==1 && v[4]==1) equ=TRUE;
        else
        if (gl[1]==gl[3] && gl[2]==gl[4]) equ=TRUE;
        else
        if (i>1) for(j=1;j<=4 && equ;j++) if (gl[j]!=gp[i-1][j]) equ=FALSE;
      }
      else
      if (v[1]==1 && v[2]==1 && v[3]==1 && v[4]==1 && v[5]==1 && v[6]==1)
        equ=TRUE;
      else
      if (i>1) for(j=1;j<=6 && equ;j++) if (gl[j]!=gp[i-1][j]) equ=FALSE;
      if (equ==FALSE)
      {
        anzgln++; for(j=1;j<=6;j++) gp[anzgln][j]=gl[j];
      }
    } /* for(i=... */

    /* ist vielleicht schon eine Null oder Eins induziert ? */
    if (valid)
    {
       /* zuerst die Nullen */
       redo = FALSE;
       for (i=1;i<=anzgln;i++)
       {
         if (gp[i][3]==0 && gp[i][5]==0)
         {
           if (bset[gp[i][1]]==1 && bset[gp[i][2]]==2) /* 1 A = 0 */
           {
             for(j=1;j<=anzbro;j++)
               if (bgh[j]==gp[i][2]) bset[j]=0;
             redo=TRUE;
#ifdef DEBUG
             fprintf(wohin,"(%i) = 0\n",gp[i][2]);
#endif
           }
           else
           if (bset[gp[i][1]]==2 && bset[gp[i][2]]==1) /* A 1 = 0 */
           {
             for(j=1;j<=anzbro;j++)
               if (bgh[j]==gp[i][1]) bset[j]=0;
             redo=TRUE;
#ifdef DEBUG
             fprintf(wohin,"(%i) = 0\n",gp[i][1]);
#endif
           }
           else
           if (gp[i][1]==gp[i][2] && bset[gp[i][1]]==2) /* A A = 0 */
           {
             for(j=1;j<=anzbro;j++)
               if (bgh[j]==gp[i][1]) bset[j]=0;
             redo=TRUE;
#ifdef DEBUG
             fprintf(wohin,"(%i) = 0\n",gp[i][1]);
#endif
           }
         } /* if (gp[i][3]... */
       } /* for(i=... */

       /* und nun die Einsen */
       for (i=1;i<=anzgln;i++)
       {
         if (gp[i][5]==0)
         {
           if (bset[gp[i][1]]==1 && bset[gp[i][2]]==1)
           {
             if (bset[gp[i][3]]==1 && bset[gp[i][4]]==2) /* 1 1 + 1 A = 0 */
             {
               for(j=1;j<=anzbro;j++)
                 if (bgh[j]==gp[i][4]) bset[j]=1;
               redo=TRUE;
#ifdef DEBUG
               fprintf(wohin,"(%i) = 1\n",gp[i][4]);
#endif
             }
             else
             if (bset[gp[i][3]]==2 && bset[gp[1][4]]==1) /* 1 1 + A 1 = 0 */
             {
               for(j=1;j<=anzbro;j++)
                 if (bgh[j]==gp[i][3]) bset[j]=1;
               redo=TRUE;
#ifdef DEBUG
               fprintf(wohin,"(%i) = 1\n",gp[i][3]);
#endif
             }
             else
             if (gp[i][3]==gp[i][4] && bset[gp[i][3]]==2) /* 1 1 + A A = 0 */
             {
               for(j=1;j<=anzbro;j++)
                 if (bgh[j]==gp[i][3]) bset[j]=1;
               redo=TRUE;
#ifdef DEBUG
               fprintf(wohin,"(%i) = 1\n",gp[i][3]);
#endif
             }
           } /* if (bset[gp[i][1]... */
           else
           if (bset[gp[i][3]]==1 && bset[gp[i][4]]==1)
           {
             if (bset[gp[i][1]]==1 && bset[gp[i][2]]==2) /* 1 A + 1 1 = 0 */
             {
               for(j=1;j<=anzbro;j++)
                 if (bgh[j]==gp[i][2]) bset[j]=1;
               redo=TRUE;
#ifdef DEBUG
               fprintf(wohin,"(%i) = 1\n",gp[i][2]);
#endif
             }
             else
             if (bset[gp[i][1]]==2 && bset[gp[1][2]]==1) /* A 1 + 1 1 = 0 */
             {
               for(j=1;j<=anzbro;j++)
                 if (bgh[j]==gp[i][1]) bset[j]=1;
               redo=TRUE;
#ifdef DEBUG
               fprintf(wohin,"(%i) = 1\n",gp[i][1]);
#endif
             }
             else
             if (gp[i][1]==gp[i][2] && bset[gp[i][1]]==2) /* A A + 1 1 = 0 */
             {
               for(j=1;j<=anzbro;j++)
                 if (bgh[j]==gp[i][1]) bset[j]=1;
               redo=TRUE;
#ifdef DEBUG
               fprintf(wohin,"(%i) = 1\n",gp[i][1]);
#endif
             }
           } /* if (bset[gp... */
         } /* if (gp[i][5]... */
       } /* for(i=... */

       if (redo==TRUE) anzgln = sortgpr(anzgln,gp,bset,bgh);
    } /* if (valid)... */
    return ((valid)?anzgln:-1);
}

/* ######################################################################### */

void sortlist(uint list[6], uint cn[6])
/* sortiert die Liste list nach Sedgewicks Insertion-Sort */
{
    int i,j,v,w;
    for(i=2;i<=6;i++)
    {
        v=list[i]; w=cn[i]; j=i;
        while (list[j-1]>v) { list[j]=list[j-1]; cn[j]=cn[j-1]; j--; }
        list[j]=v; cn[j]=w;
    }
}

/* ######################################################################### */

void writegpr(int anzg, gleichung *gp, uint *bset)
/* das Gleichungssystem wird ausgegeben */
{
    int i,j,nl,ecnt,ncnt,plus;
    uint v[7], bk[7];
    fprintf(wohin,"\nEquations to be valid in GF(2):\n");
    for(i=1;i<=anzg;i++)
    {
      fprintf(wohin,"No.%i : ",i);
      for(j=1;j<=6;j++)
      {
        bk[j] = gp[i][j];
        v[j] = bset[gp[i][j]];
      }
      nl=FALSE; ecnt=0; ncnt=0; plus=0;
      for(j=1;j<=3;j++)
      {
          if (v[2*j-1]!=0 && v[2*j]!=0)
          {
            plus++;
            if (plus>1) fprintf(wohin," + ");
            if (bk[2*j-1]==bk[2*j] && v[2*j-1]==2)
              fprintf(wohin,"(%i)",bk[2*j-1]);
            else
            if (v[2*j-1]==1 && v[j*2]==1) fprintf(wohin," 1 ");
            else
            if (v[2*j-1]==2 && v[j*2]==1) fprintf(wohin,"(%i)",bk[2*j-1]);
            else
            if (v[2*j-1]==1 && v[j*2]==2) fprintf(wohin,"(%i)",bk[2*j]);
            else
            if (v[2*j-1]==2 && v[j*2]==2)
              fprintf(wohin,"(%i)(%i)",bk[2*j-1],bk[2*j]);
          }
          else { nl=TRUE; ncnt++; }
      } /* for(j=... */
      if (nl==FALSE)
      {
        fprintf(wohin," + ");
        sortlist(bk,v);
        if (v[1]!=1) fprintf(wohin,"(%i)",bk[1]); else ecnt++;
        for(j=2;j<=6;j++)
        {
          if (v[j]!=1 && bk[j]!=bk[j-1]) fprintf(wohin,"(%i)",bk[j]);
          else ecnt++;
        }
        if (ecnt==6) fprintf(wohin,"1");
      } /* if (nl==... */
      if (ncnt!=3) fprintf(wohin," = 0\n"); else fprintf(wohin,"0 = 0\n");
    } /* for(i=... */
}

/* ######################################################################### */

void perm_b(int p1, int p2)
/* Auswahlen fuer B in {A|B} */
{
int i, bis;
bis = npkt - na;
for(i=p2+1;i<=bis;i++)
    {
      b[p1] = i;
      if (p1==nb) gprorbits();
      else perm_b(p1+1,i);
    }
}

/* ######################################################################### */

void perm_a(int p1, int p2)
/* Auswahlen fuer A in {A|B} */
{
int i;
for(i=p2+1;i<=npkt;i++)
    {
      a[p1] = i;
      if (p1==na) perm_b(1,0);
      else perm_a(p1+1,i);
    }
}

/* ######################################################################### */

void writebracket(perm brk)
{
    int i;
    fprintf(wohin,"[");
    for(i=1;i<=rang;i++) fprintf(wohin,"%c",hex[brk[i]]);
    fprintf(wohin,"]");
}

/* ######################################################################### */

int a_ohne_b(int rng, perm A, perm B, perm C)
/* Berechnet die Menge C als A ohne B */
{
  int anzc, i, j;
  boolean enthalten;
  anzc=0;
  for(i=1;i<=rng;i++)
  {
    enthalten = FALSE;
    for(j=1;j<=rng && !enthalten;j++) if (A[i]==B[j]) enthalten=TRUE;
    if (enthalten==FALSE) { anzc++; C[anzc]=A[i]; }
  }
  return anzc;
}

/* ######################################################################### */

boolean new_base(uint *matroid, perm B, uint q, uint p)
/* schaut, ob (B mit q) ohne p eine Base ist */
{
  int i,pos; perm br;
  for(i=1;i<=rang;i++) { br[i]=B[i]; if (br[i]==p) br[i]=q; }
  pos = position(npkt,rang,br); if (pos<0) pos=-pos;
  if (matroid[pos]==0) return FALSE;
  return TRUE;
}

/* ######################################################################### */

boolean test_base_axiom(uint *matroid)
/* testet die Erfuellung des Basisaxioms fuer Matroide nach der Definition */
{
   int i,j,k,l,anzelt,anzp,anzq;
   boolean nobase,nomatroid;
   perm B1,B2,P,Q;
   nobase = FALSE; nomatroid=FALSE;
   anzelt = choose(npkt,rang);
   for(i=1;i<=anzelt && !nomatroid;i++)
   {
     if (matroid[i]!=0)
     {
       bracket(i,npkt,rang,B1);     /* B1 ist Base zur Position i */
       for(j=1;j<=anzelt && !nomatroid;j++)
         if (i!=j && matroid[j]!=0)
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
                   if (new_base(matroid,B1,Q[l],P[k])==TRUE) nobase=FALSE;
                 }
               }
               if (nobase==TRUE)
               {
#ifdef DEBUG
                 fprintf(wohin,"NO MATROID !!\n");
                 fprintf(wohin,"Brackets ");
                 writebracket(B1); fprintf(wohin," and ");
                 writebracket(B2); fprintf(wohin," violate the axiom\n");
#endif
                 nomatroid=TRUE;
               }
            } /* if (anzp!=0) */
         }  /* if (i!=j ... */
     } /* if (mat[i]!=0) */
   } /* for(i=1... */
   if (nomatroid==FALSE) return TRUE; else return FALSE;
} /* test_base_axiom */


/* ######################################################################### */

void writebrset(uint *bset)
/* schreibt die Belegung der Bracketorbits heraus */
{
    int i;
#ifdef DEBUG
    fprintf(wohin,"<%3d>",baumtiefe);
#endif
    printf("<%3d>",baumtiefe);
    for(i=1;i<=anzbro;i++)
    {
#ifdef DEBUG
       fprintf(wohin,"%c",(bset[i]==0)?'0':(bset[i]==1)?'1':'?');
#endif
       printf("%c",(bset[i]==0)?'0':(bset[i]==1)?'1':'?');
    }
#ifdef DEBUG
    fprintf(wohin, "\n");
#endif
    printf("\n");
}

/* ######################################################################### */

void writematroid(uint *bset)
/* schreibt die berechneten moeglichen Matroide in eine Datei */
{
    int i,j;
    uint *matroid;
    int anzb;
    for(i=1;i<=anzbro && bset[i]!=2;i++) ;
    if (i==anzbro+1)
    {
       anzb = choose(npkt,rang);
       matroid = calloc(anzb+1,sizeof(uint));
       for(i=1;i<=anzbro;i++)
         for(j=1;j<=anzaut;j++) matroid[bra[i][j]]=bset[i];

       if (test_base_axiom(matroid)==TRUE)
       {
#ifdef DEBUG
          fprintf(wohin,"\nAdmissable matroid :\n");
#endif
          for(i=1;i<=anzb;i++)
          {
#ifdef DEBUG
            fprintf(wohin,"%c",(matroid[i]==2)?'?':(matroid[i]==1)?'1':'0');
#endif
            fprintf(matdatei,"%c",(matroid[i]==2)?'?':(matroid[i]==1)?'1':'0');
          }
#ifdef DEBUG
          fprintf(wohin,"\n\n");
#endif
          fprintf(matdatei,"\n");
       }
#ifdef DEBUG
       else
       fprintf(wohin,"NO MATROID\n");
#endif
       free(matroid);
    }
}

/* ######################################################################### */

void solvegpr(int nrgl, gleichung *gp, uint *bset, uint *bg)
/* fuellt Gleichungen mit 0 und 1 zu evtln Matroiden auf */
{
  int i,j,k;
  int anzfrei;           /* Anzahl freier Bracketorbits */
  int newnrgl;           /* neue Laenge des Gleichungssystems */
  gleichung *gs;         /* das Gleichungssystem */
  uint *bgh;             /* neue Abhaengigkeiten der Bracketorbits */
  uint *brset;           /* neu gesetzte Bracketorbits */
  char *frei;            /* Freiheitsgrade */

  baumtiefe++;
  bgh    = calloc(anzbro+1,sizeof(uint));
  frei   = calloc(anzbro+1,sizeof(boolean));
  brset  = calloc(anzbro+1,sizeof(uint));
  gs     = calloc(nrgl+1,sizeof(gleichung));

  memcpy(brset,bset,((long)anzbro+1)*sizeof(uint)); /* brset = bset */
  memcpy(bgh,bg,((long)anzbro+1)*sizeof(uint));     /* bgh = bg */

#ifdef DEBUG
  fprintf(wohin,"\nNow entering new pass of solvegpr\n");
#endif

  /* Schritt 1 : Untersuche auf direkte Gleichheiten */
  for(i=1;i<=nrgl;i++)
  {
     if (gp[i][5]==0)
       if (gp[i][1]==gp[i][2] && bset[gp[i][1]]==2) 
       {
          /* AA + BB = 0 => A = B, A frei */
          if (gp[i][1]!=gp[i][3] && gp[i][3]==gp[i][4] && bset[gp[i][3]]==2)
          {
            bgh[gp[i][3]]=gp[i][1]; frei[gp[i][1]]=1;
#ifdef DEBUG
            fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][3],gp[i][1]);
#endif
          }
          else
          /* AA + 1B = 0 => A = B, A frei */
          if (gp[i][1]!=gp[i][4] && bset[gp[i][3]]==1 && bset[gp[i][4]]==2)
          {
            bgh[gp[i][4]]=gp[i][1]; frei[gp[i][1]]=1;
#ifdef DEBUG
            fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][4],gp[i][1]);
#endif
          }
          else
          /* AA + B1 = 0 => A = B, A frei */
          if (gp[i][1]!=gp[i][3] && bset[gp[i][4]]==1 && bset[gp[i][3]]==2)
          {
            bgh[gp[i][3]]=gp[i][1]; frei[gp[i][1]]=1;
#ifdef DEBUG
            fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][3],gp[i][1]);
#endif
          }
       }
       else
       if (bset[gp[i][1]]==1 && bset[gp[i][2]]==2)
       {
          /* 1A + BB = 0 => A = B, A frei */
          if (gp[i][3]==gp[i][4] && bset[gp[i][3]]==2 && gp[i][2]!=gp[i][3])
          {
             if (gp[i][3]>gp[i][2])
             {
               bgh[gp[i][3]]=gp[i][2]; frei[gp[i][2]]=1;
#ifdef DEBUG
               fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][3],gp[i][2]);
#endif
             }
             else
             {
               bgh[gp[i][2]]=gp[i][3]; frei[gp[i][3]]=1;
#ifdef DEBUG
               fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][2],gp[i][3]);
#endif
             }
          }
          else
          /* 1A + 1B = 0 => A = B, A frei */
          if (bset[gp[i][3]]==1 && bset[gp[i][4]]==2)
          {
            if (gp[i][4]>gp[i][2])
            {
               bgh[gp[i][4]]=gp[i][2]; frei[gp[i][2]]=1;
#ifdef DEBUG
               fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][4],gp[i][2]);
#endif
            }
            else
            {
               bgh[gp[i][2]]=gp[i][4]; frei[gp[i][4]]=1;
#ifdef DEBUG
               fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][2],gp[i][4]);
#endif
            }
          }
          else
          /* 1A + B1 = 0 => A = B, A frei */
          if (bset[gp[i][3]]==2 && bset[gp[i][4]]==1)
          {
            if (gp[i][3]>gp[i][2])
            {
               bgh[gp[i][3]]=gp[i][2]; frei[gp[i][2]]=1;
#ifdef DEBUG
               fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][3],gp[i][2]);
#endif
            }
            else
            {
               bgh[gp[i][2]]=gp[i][3]; frei[gp[i][3]]=1;
#ifdef DEBUG
               fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][2],gp[i][3]);
#endif
            }
          }
       }
       else
       if (bset[gp[i][1]]==2 && bset[gp[i][2]]==1)
       {
         /* A1 + BB = 0 => A = B, A frei */
         if (gp[i][3]==gp[i][4] && bset[gp[i][3]]==2)
         {
            bgh[gp[i][3]]=gp[i][1]; frei[gp[i][1]]=1;
#ifdef DEBUG
            fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][3],gp[i][1]);
#endif
         }
         else
         /* A1 + B1 = 0 => A = B, A frei */
         if(bset[gp[i][3]]==2 && bset[gp[i][4]]==1)
         {
            bgh[gp[i][3]]=gp[i][1]; frei[gp[i][1]]=1;
#ifdef DEBUG
            fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][3],gp[i][1]);
#endif
         }
         else
         /* A1 + 1B = 0 => A = B, A frei */
         if (bset[gp[i][3]]==1 && bset[gp[i][4]]==2)
         {
           bgh[gp[i][4]]=gp[i][1]; frei[gp[i][1]]=1;
#ifdef DEBUG
           fprintf(wohin, "%3d: (%d)=(%d)\n",i,gp[i][4],gp[i][2]);
#endif
         }
       }
  }

  /* Gleichheiten minimieren */
  for(i=anzbro;i>0;i--)
    while(bgh[i] != bgh[bgh[i]]) bgh[i] = bgh[bgh[i]];

  /* Gleichheiten uebertragen */
  for(i=1;i<=nrgl;i++)
    for(j=1;j<=6;j++) gs[i][j]=bgh[gp[i][j]]; 

  /* Sortierung der Gleichung unter Beruecksichtigung der Gleichheiten */
#ifdef DEBUG
  fprintf(wohin,"Bracketset before sorting :\n");
  writebrset(brset);
#endif

  newnrgl = sortgpr(nrgl, gs, brset, bgh);

#ifdef DEBUG
  fprintf(wohin,"Bracketset after sorting  :\n");
#endif
  writebrset(brset);
  if (newnrgl!=-1) 
  {
      if (newnrgl==0)
      {
#ifdef DEBUG
        fprintf(wohin,"\nAll equations solved -- everything fine ...\n");
#endif
        writematroid(brset);
      }

      /* Schritt 2 : Weitere freie Bracketorbits ermitteln */
      for(i=1;i<=newnrgl;i++)
      {
        if (gs[i][5]==0)
          /* AB + AC = 0 => A frei */
          if (gs[i][1]==gs[i][3] && brset[gs[i][1]]==2)
          {
             if (brset[gs[i][2]]==2 && brset[gs[i][4]]==2) frei[gs[i][1]]=1;
          }
          else
          /* AB + CB = 0 => B frei */
          if (gs[i][2]==gs[i][4] && brset[gs[i][2]]==2)
          {
             if (brset[gs[i][1]]==2 && brset[gs[i][3]]==2) frei[gs[i][2]]=1;
          }
          else
          /* AB + BC = 0 => B frei */
          if (gs[i][2]==gs[i][3] && brset[gs[i][2]]==2)
          {
             if (brset[gs[i][1]]==2 && brset[gs[i][4]]==2) frei[gs[i][2]]=1;
          }
      }

      /* nur kleinste aus gleichen Bracketorbits sind frei */
      anzfrei=0;
      for(i=1;i<=anzbro;i++)
        if (frei[i])
          if (bgh[i]==i && brset[i]==2) { frei[i]=TRUE; anzfrei++; }
          else frei[i]=FALSE;

      /* wenn es keine freien Bracketorbits aus den Gleichungen gibt, */
      /* so muessen alle Auffuellmoeglichkeiten betrachtet werden     */
      if (anzfrei==0)
        for(i=1;i<=anzbro;i++)
          if (bgh[i]==i && brset[i]==2) { frei[i]=TRUE; anzfrei++; }
          else frei[i]=FALSE;

#ifdef DEBUG
      if (anzfrei>0)
      {
        fprintf(wohin,"\nResulting free bracketorbits : ");
        for(i=1;i<=anzbro;i++) if (frei[i]) fprintf(wohin,"(#%i) ",i);
        fprintf(wohin,"\n");
      }
#endif

      /* Schritt 3: Setzen der freien Bracketorbits auf 1 und 0 */
      if (anzfrei!=0)
      {
          for(i=1;i<=anzbro && !frei[i];i++) ;
          for(j=0;j<2;j++)
          {
#ifdef DEBUG
            fprintf(wohin,"\nPreparing for next recursion pass...\n");
#endif
            for(k=1;k<=anzbro;k++)
            {
              if (bgh[k]==i)
              {
#ifdef DEBUG
                 fprintf(wohin,"(#%i) ",k);
#endif
                 brset[k]=j;
              }
            }
#ifdef DEBUG
            fprintf(wohin,"set to %i\n",j);
#endif
            solvegpr(newnrgl,gs,brset,bgh);
         } /* for(j=0... */
      } /* if (anzfrei... */
  } /* if (newnrgl!=-1) ... */
#ifdef DEBUG
  else fprintf(wohin,"\nGPR crashed ...\n");
#endif

  free(bgh);
  free(frei);
  free(brset);
  free(gs);

  baumtiefe--;
}

/* ######################################################################### */

void get_bases(void)
/* liest eine Basisdatei ein und setzt die Brackets dementsprechend */
{
    int  i;
    uint *basen;         /* die Grundstruktur */
    char basname[50];    /* Name der Datei fuer eine Grundstruktur */
    FILE *basdatei;      /* File of Text (Grundstruktur) */
    int  listlen, nlist;
    int  einint;
    char einchar;

    printf("Please give name of BAS-File (without extension .bas): ");
    scanf("%s",instr);
    strcpy(basname,instr);
    strcat(basname,".bas");
    basdatei = fopen(basname,"r");
    if (basdatei==NULL)
    {
      printf(" Error while fileoperation on %s\n",basname);
      exit(1);
    }
    else
    {
       printf("Reading file %s\n",basname);
#ifdef DEBUG
       fprintf(wohin,"Getting file %s ...\n",basname);
#endif
       fscanf(basdatei,"%i",&einint);
       if (einint!=npkt) { printf("Different number of points\n"); exit(1); }
       fscanf(basdatei,"%i",&einint);
       if (einint!=rang) { printf("Different rank\n"); exit(1); }
       listlen=choose(npkt,rang);
       basen = calloc(listlen+1,sizeof(uint));
       nlist=0;
       do
       {
            einchar = fgetc(basdatei);
            if (einchar=='1') { nlist++; basen[nlist]=1; }
            else
            if (einchar=='0') { nlist++; basen[nlist]=0; }
            else
            if (einchar=='?') { nlist++; basen[nlist]=2; }
       } while (nlist<=listlen && einchar!=EOF && einchar!='*');
       fclose(basdatei);
       if (nlist!=listlen)
       {
         printf("Error while reading %s (not enough elements)\n",basname);
         exit(1);
       }
#ifdef DEBUG
       for(i=1;i<=listlen;i++)
         fprintf(wohin,"%c",(basen[i]==0)?'0':(basen[i]==1)?'1':'?');
       fprintf(wohin,"\n");
#endif
    } /* else ... */
    /* Trage das Gelesene in die Bracketorbits ein */
    for(i=1;i<=anzbro;i++)
    {
        bra[i][0]=basen[bra[i][1]];
    } /* for (i=1;i<=anzbro... */
    free(basen);
}

/* ######################################################################### */

void grassmann(void)
/* fuehrt die einzelnen Schritte der Vorzeichenbestimmung durch */
{
    int i;
    uint *brset, *broglh;   /* gesetzte Bracketorbits und -gleichheiten */
    anzgpo=0;
    anzbro=0;
    bracketorbits(1,0);     /* berechnet die Bracketorbits */

    printf("Do you wish to set brackets to 0 or 1 manually or\n");
    printf("do you wish to give a fundamental file of bases (m/f) ? ");
    scanf("%s",instr);
    if (instr[0]=='f' || instr[0]=='F')
    {
       get_bases();        /* liest eine Basisdatei und setzt die Brackets */
    }
    else
    {
       null_br();          /* gibt Moeglichkeit, Bracket(s) zu 0 zu setzen */
       eins_br();          /* dito. fuer 1 */
    }

    perm_a(1,0);            /* berechnet die GPR-Orbits */
    make_equations(gpr);    /* erzeugt Gleichungen durch GPR-Orbits */

    brset  = calloc(anzbro+1,sizeof(uint));
    broglh = calloc(anzbro+1,sizeof(uint));
    for(i=1;i<=anzbro;i++) { brset[i]=bra[i][0]; broglh[i] = i; }
    baumtiefe=0;

    anzgl = sortgpr(anzgpo,gpr,brset,broglh);
    if (anzgl==-1)
    {
      printf("GPR crashed from input ...\n");
      printf("PLEASE CHECK YOUR DECLARATIONS\n");
      free(brset);
      free(broglh);
      exit(1);
    }
    writebrset(brset);
#ifdef DEBUG
    writegpr(anzgl,gpr,brset);
#endif
    solvegpr(anzgl,gpr,brset,broglh);

    free(brset);
    free(broglh);
}

/* ######################################################################### */

/* Das Hauptprogramm */
void main(void)
{
  iso = -1;
  printf("\nName of input file (without extension .aut): ");
  scanf("%s",name);
#ifdef DEBUG
  strcpy(outname,name);
  strcat(outname,".gp3");
#endif
  strcpy(autname,name);
  strcat(autname,".aut");
  strcpy(matname,name);
  strcat(matname,".mat");
  printf("Please give number of points to compute : "); scanf("%i",&npkt);
  if (npkt>MPKT) { printf("Maximal number of points is %i",MPKT); exit(1); }
  printf("Please give rank to compute             : "); scanf("%i",&rang);
  if (rang>MRNG) { printf("Maximal rank is %i",MRNG); exit(1); }
  na = rang - 2;
  nb = 4;

  /* Speicher fuer die Relationen allokieren */
  anzgpr = choose(npkt,na) * choose(npkt-na,nb) + 1;
  gpr    = calloc(anzgpr,sizeof(gleichung));
  orbit  = calloc(anzgpr,sizeof(perm));

  autdatei = fopen(autname,"r");
  matdatei = fopen(matname,"w");
#ifdef DEBUG
  outdatei = fopen(outname,"w");
  wohin = outdatei;

  if (outdatei==NULL)
  { printf("Error while fileoperation on %s\n",outname); exit(1); }
  else
#endif
  if (autdatei==NULL)
  { printf("Error while fileoperation on %s\n",autname); exit(1); }
  else
  if (matdatei==NULL)
  { printf("Error while fileoperation on %s\n",matname); exit(1); }
  else
    {
      fscanf(autdatei,"%i",&inpkt);
      if (inpkt!=npkt) { printf("Number of points not equal"); exit(1); }
      fscanf(autdatei,"%i",&anzaut);

      /* Speicher fuer verwendete Strukturen allokieren */
      erza  = calloc(anzaut+1,sizeof(perm));
      erzb  = calloc(anzaut+1,sizeof(perm));
      erzbr = calloc(anzaut+1,sizeof(perm));
      aut   = calloc(anzaut+1,sizeof(perm));

      for(i=1;i<=anzaut;i++)
      {
        for(j=1;j<=npkt;j++) fscanf(autdatei,"%i",&aut[i][j]);
#ifdef DEBUG
        fprintf(wohin,"[%i] : ",i); writeperm(aut[i]); fprintf(wohin,"\n");
#endif
        in = fgetc(autdatei);
      }
      fclose(autdatei);
    }
#ifdef DEBUG
  fprintf(wohin,"Computing %i points ",npkt);
  fprintf(wohin,"in rank %i\n",rang);
#endif
  fprintf(matdatei,"Admissable matroids with %i points in rank %i ",npkt,rang);
  fprintf(matdatei,"to file %s\n",autname);
  grassmann();
#ifdef DEBUG
  if (wohin==outdatei) fclose(outdatei);
#endif
  fclose(matdatei);
}
