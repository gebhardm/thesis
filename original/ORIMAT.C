/* Programm : Orientieren von Matroiden bezueglich Symmetrien */
/* von Markus Gebhard, THD, FB04AG3b */
/* entstanden im Rahmen einer Diplomarbeit im Juli bis August 1994 */

/* #define DEBUG   gibt Debug-Informationen in datei.chi aus */

#ifdef DEBUG
  #define SHOWBRO
  #define SHOWGPO
  #define FOLLOWS
#endif

/* #define SHOWBRO gibt die Bracketorbits   in datei.chi aus */
/* #define SHOWEQN gibt das grosse Gl.sys.  in datei.chi aus */
/* #define SHOWGPO gibt die GPR-Orbits      in datei.chi aus */
/* #define FOLLOWS gibt Vrz.folgerungen     in datei.chi aus */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MPKT 13              /* maximale Punktzahl + 1 */
#define MRNG 5               /* maximaler Rang */
#define MSY 500              /* maximale Anzahl an Symmetrien + 1 */
#define MBRA 500             /* maximale Anzahl an Bracketorbits (12 ueber 4) */
#define TRUE  1
#define FALSE 0

typedef int perm[MPKT];
typedef long int longint;
typedef unsigned int uint;
typedef char boolean;
typedef int gleichung[7];

const char hex[]   = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

char name[50], frage[50];     /* Dateiname, Fragestring */
char matname[50];             /* Dateiname der Matroiddatei */
char autname[50];             /* Dateiname der Automorphismendatei */
char chiname[50];             /* Dateiname der Chirotopdatei */
FILE *matdatei;               /* File of Text (Matroid) */
FILE *autdatei;               /* File of Text (Automorphismen) */
FILE *chidatei;               /* File of Text (Chirotop) */
FILE *wohin;                  /* Filezeiger fuer (Standard-)Ausgabe */

int  npkt, rang;              /* Punktanzahl und Rang des oM */
int  matlen;                  /* Laenge der Matroidliste */
int *matroid;                 /* Zeiger auf das eingelesene Matroid */
int  einlen;                  /* Laenge der eingelesenen Liste */
char einchar;                 /* eingelesener Charwert */
int  einint;                  /* eingelesener Integerwert */
int  anzaut;                  /* Anzahl der vorgelegten Automorphismen */
perm *aut;                    /* Zeiger auf die Automorphismen */
int  *symmtyp;                /* bildet \sigma \chi auf \chi oder -\chi ab */
int  i,j,k,l;                 /* Zaehlvariablen fuer Schleifen etc. */
int  bra[MBRA][MSY];          /* Vergleichsliste fuer die Brackets */
perm br;                      /* Kombinationsfeld */
int anzbro;                   /* Anzahl der Bracketorbits */
int anzgpo;                   /* Anzahl der GPR-Orbits */
perm a,b;                     /* Indexmengen fuer GPR */
perm *erza, *erzb;            /* erzeugte bzw. gekoppelte GPR-Orbits */
int na,nb;                    /* Anzahl der Elemente in den GPR */
gleichung *gpr;               /* Zeiger auf die GPRn als Gleichungen */
perm      *gpo;               /* {A|B} der Orbitrepraesentanten der GPR */
int baumtiefe;                /* Rekursionstiefe bei der Vorzeichenbestimmung */
boolean newtype;              /* neuer Symmetrietyp */
boolean first;                /* Normierung fuer orientierte Matroide */

#ifdef DEBUG
longint validsym=0;           /* Anzahl der erlaubten Symmetrietypen */
int  presym;                  /* Anzahl der vorbestimmten Symmetrien */
#endif

/* ######################################################################### */

char neg(char x)
/* negiert das Vorzeichen */
{ return((x=='+')?'-':(x=='-')?'+':(x=='0')?'0':'?'); }

/* ######################################################################### */

int sgn(int x)
/* die Signumfunktion */
{ return((x==0)?0:(x<0)?-1:1); }

/* ######################################################################### */

char vrz(int x)
/* schreibt das Vorzeichen fuer x als char */
{
    return ((abs(x)==2)?'?':(sgn(x)==0)?'0':(sgn(x)==1)?'+':(sgn(x)==-1)?'-':'?');
}

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

int swap(int *x, int *y)
/* tauscht Werte x und y, aufrufen mit swap(&x,&y) bei Nichtzeigern */
{
  int z;
   z = *x;
  *x = *y;
  *y = z;
  return TRUE;
}

/* ######################################################################### */

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

/* ######################################################################### */

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

/* ######################################################################### */

int position(int n, int k, perm p)
/* gibt lexikographischen Index einer Permutation aus */
{
  int i,j,flg,ind;
  i = sortperm(k,p);
  if (i%2==0) flg = FALSE; else flg = TRUE;
  ind = 1;
  for(j=n-p[1]+1;j<n;j++) ind = ind + choose(j,k-1);
  for(i=2;i<=k;i++)
  {
    for(j=n-p[i]+1;j<n-p[i-1];j++) ind = ind + choose(j,k-i);
  }
  if (flg) return(-ind); else return ind;
}

/* ######################################################################### */

void writeperm(FILE *whereto, perm p)
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
                      fprintf(whereto,"(");
                      for (j=f;j<i;j++) { fprintf(whereto,"%c",hex[c[j]]); }
                      fprintf(whereto,")");
                   } /* if (i-f>1) */
        f = i; k = 1;
        do { enth = FALSE;
             k++;
             for (j=1;j<=i;j++) { if (c[j]==k) enth = TRUE; }
           } while (enth);
        c[f] = k;
    } /* if (c[i]==c[f]) */
  } /* for (i=1... */
  if (anzzyk==npkt) fprintf(whereto,"identity");
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

void bracketorbits(int idx, int k)
/* Berechnet Bracketorbits */
{
  int i, j, z, vrz, w1, w2, anzbr, pos, typ;
  perm pe, *erzbr;
  /* die erzeugten Brackets */
  erzbr = calloc(anzaut+1,sizeof(perm));
  /* Erzeugung  */
  for(i=k+1;i<=npkt;i++)
  {
     br[idx] = i;
     if (idx==rang)
     {
       for(j=1;j<=anzaut;j++)
       {
         for(z=1;z<=rang;z++) pe[z] = aut[j][br[z]];
         vrz = sortperm(rang,pe);
         /* ist es die erste erzeugte Bracket, dann Repraesentant, */
         if (j==1) { anzbr=0; w1=position(npkt,rang,pe); }
         /* sonst im Orbit enthalten */
         w2=position(npkt,rang,pe);
         if (w2>=w1)
         {
            anzbr++;
            if ((w2==w1) && (matroid[w1]==1))
            {
              typ = (vrz%2==0)?1:-1;
              if (symmtyp[j]==0) symmtyp[j]=typ;
              else
              if (symmtyp[j]!=typ)
              {
                printf("CONFLICTING SYMMETRYTYPES\n");
                printf("Permutation ");
                writeperm(stdout,aut[j]);
                printf(" can't be rotation and reflection at the same time.\n");
                printf("Matroid not orientable with this symmetrygroup !!!");
                exit(1);
              }
            }
            /* Vorzeichen der Bracket nach Sortierung */
            erzbr[anzbr][0]=(vrz%2==0)?1:-1;
            /* die erzeugte Bracket (schon richtig sortiert) */
            for(z=1;z<=rang;z++) erzbr[anzbr][z]=pe[z];
         }
       }
       if (anzbr==anzaut)
       {
          anzbro++;
          for(j=1;j<=anzaut;j++)
          {
             /* speichere die Nummern der erzeugten Brackets */
             pos=position(npkt,rang,erzbr[j]);
             bra[anzbro][j]=erzbr[j][0]*pos;
             bra[anzbro][0]=(matroid[pos]!=0)?2:0;
             /* 2 heisst hier, dass Bracket ungesetzt */
#ifdef SHOWBRO
             fprintf(wohin,"%c[",(erzbr[j][0]==-1)?'-':'+');
             for(z=1;z<=rang;z++) fprintf(wohin,"%c",hex[erzbr[j][z]]);
             fprintf(wohin,"] ");
#endif
          }
#ifdef SHOWBRO
          fprintf(wohin,"\n");
#endif
       } /* endif (anzbr==anzaut) */
     } /* endif (idx==rang) */
     else bracketorbits(idx+1,i);
  } /* for (i=k+1... */
  free(erzbr);
}

/* ######################################################################### */

void make_gpr(void)
/* berechnet eine GPR, sowie deren Orbit */
{
    int i,j, anzgpp;
    perm ma,mb,ausw;           /* Grundmengen fuer GPR */
    perm sa,sb;                /* GPR-Grundmengen unter einer Symmetrie */
    int  v,v1,v2;              /* Vorzeichen der Umordnung */
    int  p1,p2,q1,q2;          /* lexikographische Position der GPR */
    int  out;

    /* Erzeuge die Mengen A und B fuer {A|B} */
    for(i=1;i<=npkt;i++) ausw[i] = i;
    for(i=1;i<=na;i++) { ma[i] = ausw[a[i]]; ausw[a[i]] = npkt+1; }
    i=sortperm(npkt,ausw);
    for(i=1;i<=nb;i++) mb[i] = ausw[b[i]];
    /* berechne ein Grassmann-Pluecker-Polynom und dessen Orbit */
    for(i=1;i<=anzaut;i++)
    {
        /* wende auf A die Permutation aut[i] an */
        for(j=1;j<=na;j++) sa[j]=aut[i][ma[j]];
        v1=sortperm(na,sa); if (v1%2==0) v1 = 1; else v1 = -1;
        /* wende auf B die Permutation aut[i] an */
        for(j=1;j<=nb;j++) sb[j]=aut[i][mb[j]];
        v2=sortperm(nb,sb); if (v2%2==0) v2 = 1; else v2 = -1;
        /* Vorzeichen des erzeugten GPP nach Umsortierung */
        v = v1 * v2;
        /* lag dieses GPP schon vor ? */
        p1 = position(npkt,na,sa);
        p2 = position(npkt,nb,sb);
        /* wenn es das erste war, dann nicht */
        if (i==1) { anzgpp=0; q1=p1; q2=p2; }
        if (p1>q1) out = TRUE;
        else if (p1==q1 && p2>=q2) out = TRUE; else out = FALSE;
/*
#ifdef SHOWGPO
        fprintf(wohin,"%c{",vrz(v));
        for(j=1;j<=na;j++) fprintf(wohin,"%c",hex[sa[j]]);
        fprintf(wohin,"|");
        for(j=1;j<=nb;j++) fprintf(wohin,"%c",hex[sb[j]]);
        fprintf(wohin,"} ");
#endif
*/
        /* wenn es ein neues war, dann uebernehme es */
        if (out)
        {
           anzgpp++;
           erza[i][0]=v;
           for(j=1;j<=na;j++) erza[i][j] = sa[j];
           for(j=1;j<=nb;j++) erzb[i][j] = sb[j];
        } /* endif (out) */
    } /* endfor (i=1;i<=anzaut... */
/*
#ifdef SHOWGPO
    fprintf(wohin,"\n");
#endif
*/
    if (anzgpp==anzaut)
    {
        anzgpo++;
        for(i=1;i<=na;i++) gpo[anzgpo][i]=erza[1][i];
        for(i=1;i<=nb;i++) gpo[anzgpo][i+na]=erzb[1][i];
    }
    /* am Ende stehen in gpo[1..anzgpo] die Repraesentanten der GPP als {A|B} */
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
      if (p1==nb) make_gpr();
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

int change(int *styp, perm br)
/* ersetzt eine vorgegebene Bracket durch den Repraesentanten des Orbits */
{
    int i=0,j,nr,brnr,vz;
    /* ermittle Index der Bracket br */
    nr = position(npkt,rang,br);
    /* br wurde umsortiert, hat also Vorzeichen */
    if (nr<0) { nr=-nr; vz=-1; } else vz=1;
    /* suche br in bra */
    do {
         j=0; i++;
         do {
              j++;
              brnr = abs(bra[i][j]);
            } while (brnr!=nr && j<anzaut);
       } while (brnr!=nr && i<anzbro);
    /* beruecksichtige Vorzeichen aus bra */
    if (bra[i][j]<0) vz = -vz;
    /* erzeuge Repraesentant */
    bracket(bra[i][1],npkt,rang,br);
    /* gib Vorzeichen dieses Repraesentanten zurueck */
    vz = vz * styp[j];
    return(vz);
}

/* ######################################################################### */

int br_orb_nr(perm br)
/* gibt die Nummer des Orbits der Bracket br zurueck */
{
    int i=0, nr;
    nr = position(npkt,rang,br); if (nr<0) nr=-nr;
    do { i++; } while (bra[i][1]!=nr && i<anzbro);
    return i;
}

/* ######################################################################### */

void make_equations(int *typ, gleichung *gp)
/* erzeugt das Gleichungssystem und */
/* gibt Repraesentanten der Orbits der GPR aus */
{
    int i,j,k,v,pos;
    perm brk[7];
#ifdef SHOWEQN
    fprintf(wohin,"\nRepresenting elements of GPR orbits are:\n");
#endif
    for(j=1;j<=anzgpo;j++)
    {
#ifdef SHOWEQN
       fprintf(wohin,"{");
       for(i=1;i<=na;i++) fprintf(wohin,"%c",hex[gpo[j][i]]);
       fprintf(wohin,"|");
       for(i=1;i<=nb;i++) fprintf(wohin,"%c",hex[gpo[j][i+na]]);
       fprintf(wohin,"} = ");
#endif
       /* {A|B} = {a_1,a_2,...a_(d-2),b_1,b_2,b_3,b_4} */
       /* A -> [a_1,a_2,...a_(d-2),?,?] */
       for(k=1;k<=6;k++)
         { for(i=1;i<=na;i++) brk[k][i] = gpo[j][i]; }
       /* 1.Bracket : [a_1,a_2,...a_(d-2),b_1,b_2] */
       brk[1][na+1] = gpo[j][na+1]; brk[1][na+2] = gpo[j][na+2];
       /* 2.Bracket : [a_1,a_2,...a_(d-2),b_3,b_4] */
       brk[2][na+1] = gpo[j][na+3]; brk[2][na+2] = gpo[j][na+4];
       /* 3.Bracket : [a_1,a_2,...a_(d-2),b_1,b_3] */
       brk[3][na+1] = gpo[j][na+1]; brk[3][na+2] = gpo[j][na+3];
       /* 4.Bracket : [a_1,a_2,...a_(d-2),b_2,b_4] */
       brk[4][na+1] = gpo[j][na+2]; brk[4][na+2] = gpo[j][na+4];
       /* 5.Bracket : [a_1,a_2,...a_(d-2),b_1,b_4] */
       brk[5][na+1] = gpo[j][na+1]; brk[5][na+2] = gpo[j][na+4];
       /* 6.Bracket : [a_1,a_2,...a_(d-2),b_2,b_3] */
       brk[6][na+1] = gpo[j][na+2]; brk[6][na+2] = gpo[j][na+3];
#ifdef SHOWEQN
       for(k=1;k<=3;k++)
       {
          if (k==2) fprintf(wohin," - ");
          if (k==3) fprintf(wohin," + ");
          writebracket(brk[2*k-1]); writebracket(brk[2*k]);
       }
       fprintf(wohin," = ");
#endif
       for(k=1;k<=6;k++)
       {
          /* ersetze Bracket durch Orbitrepraesentanten */
          v        = change(typ,brk[k]);
          /* ermitteln der Nummer des Bracketorbits */
          pos      = br_orb_nr(brk[k]);
          /* speichern dieser Orbitnummer in der Gleichung */
          gp[j][k] = v*pos;
       }
#ifdef SHOWEQN
       for(k=1;k<=3;k++)
       {
          if (k==2) fprintf(wohin," - ");
          if (k==3) fprintf(wohin," + ");
          fprintf(wohin,"(%c",(gp[j][2*k-1]<0)?'-':'+');
          writebracket(brk[2*k-1]);
          fprintf(wohin,")(%c",(gp[j][2*k]<0)?'-':'+');
          writebracket(brk[2*k]);
          fprintf(wohin,")");
       }
       fprintf(wohin,"\n");
#endif
       /* ziehe das Minuszeichen der Gleichungen vor dem zweiten Summanden */
       /* in die dritte Bracket, so dass nur Addition auftritt */
       gp[j][3]=-gp[j][3];
    } /* for(j=... */
#ifdef SHOWEQN
    fprintf(wohin,"\n");
#endif
}

/* ######################################################################### */

void sortlist(int list[6], int cn[6])
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

void writegpr(int anzg, gleichung *gp)
/* das Gleichungssystem wird ausgegeben */
{
    int i,j;
    gleichung bk;
    fprintf(wohin,"\nEquations to solve:\n");
    for(i=1;i<=anzg;i++)
    {
      for(j=1;j<=6;j++)
        /* bk ist Index des Repraesentanten des Orbits gp[i][j] */
        if (gp[i][j]<0) bk[j]=bra[-gp[i][j]][1];
        else bk[j]=bra[gp[i][j]][1];
      fprintf(wohin,"No.%3i : ",i);
      for(j=1;j<=3;j++)
      {
         if (j>1) fprintf(wohin," + ");
         if (matroid[bk[j*2-1]]!=0 && matroid[bk[2*j]]!=0)
           fprintf(wohin,"(%i)(%i)",gp[i][2*j-1],gp[i][2*j]);
         else fprintf(wohin,"0");
      } /* for(j=... */
      fprintf(wohin,"\n");
    } /* for(i=... */
}

/* ######################################################################### */

void writebrset(int *bset)
/* schreibt die Belegung der Bracketorbits heraus */
{
  int i;
  printf("<%2d>",baumtiefe);
#ifdef DEBUG
  fprintf(wohin,"<%2d>",baumtiefe);
#endif
  for(i=1;i<=anzbro;i++)
  {
#ifdef DEBUG
    fprintf(wohin,"%c",(bset[i]==0)?'0':(bset[i]==1)?'+':(bset[i]==-1)?'-':'?');
#endif
    printf("%c",(bset[i]==0)?'0':(bset[i]==1)?'+':(bset[i]==-1)?'-':'?');
  }
#ifdef DEBUG
  fprintf(wohin, "\n");
#endif
  printf("\n");
}

/* ######################################################################### */

boolean gt(gleichung x, gleichung y)
/* prueft, ob x lexikographisch groesser als y ist */
{
    if (abs(x[1])>abs(y[1])) return TRUE;
    else if (abs(x[1])==abs(y[1])) if (abs(x[2])>abs(y[2])) return 1;
    else if (abs(x[2])==abs(y[2])) if (abs(x[3])>abs(y[3])) return 1;
    else if (abs(x[3])==abs(y[3])) if (abs(x[4])>abs(y[4])) return 1;
    else if (abs(x[4])==abs(y[4])) if (abs(x[5])>abs(y[5])) return 1;
    else if (abs(x[5])==abs(y[5])) if (abs(x[6])>abs(y[6])) return 1;
    else return FALSE;
   return FALSE;
}

/* ######################################################################### */

boolean validgpr(gleichung e)
/* prueft, ob eine Gleichung erfuellt ist */
{
    int i, s1, s2, s3;
    for(i=1;i<=6 && abs(e[i])!=2;i++) ;
    if (i>6)
    {
        s1 = e[1]*e[2]; s2 = e[3]*e[4]; s3 = e[5]*e[6];
        if (s1==0) { if (s2==-s3) return TRUE; else return FALSE; }
        else if (s2==0) { if (s1==-s3) return TRUE; else return FALSE; }
        else if (s3==0) { if (s1==-s2) return TRUE; else return FALSE; }
        else if (s1== 1 && s2== 1 && s3==-1) return TRUE;
        else if (s1== 1 && s2==-1 && s3== 1) return TRUE;
        else if (s1== 1 && s2==-1 && s3==-1) return TRUE;
        else if (s1==-1 && s2== 1 && s3== 1) return TRUE;
        else if (s1==-1 && s2== 1 && s3==-1) return TRUE;
        else if (s1==-1 && s2==-1 && s3== 1) return TRUE;
        else return FALSE;
    }
    return TRUE;
}

/* ######################################################################### */

void writeeqn(gleichung eq, int *bset)
/* schreibt eine Gleichung heraus */
{
   int i; char ch;
   for(i=1;i<=3;i++)
   {
      if (i>1) fprintf(wohin," + ");
      if (bset[abs(eq[2*i-1])]==2)
        fprintf(wohin,"(%i)",eq[2*i-1]);
      else
      {
        ch=vrz(bset[abs(eq[2*i-1])]);
        fprintf(wohin,"%c",(eq[2*i-1]<0)?neg(ch):ch);
      }
      if (bset[abs(eq[2*i])]==2)
        fprintf(wohin,"(%i)",eq[2*i]);
      else
      {
        ch=vrz(bset[abs(eq[2*i])]);
        fprintf(wohin,"%c",(eq[2*i]<0)?neg(ch):ch);
      }
   }
   fprintf(wohin,"\n");
}

/* ######################################################################### */

int sortgpr(int anzg, gleichung *gp, int *bset, int *bgh)
/* sortiert die Gleichungen der GPRn kanonisch */
{
    int i,j,k,anzgln,s1,s2,s3,anz,vergleich;
    boolean valid, equ, redo;
    gleichung v;
    gleichung gl, agl, vgl, sig;

    /* die Gleichungen selbst werden sortiert */
    for(i=1;i<=anzg;i++)
    {
      /* ersetze Null gesetzte Brackets durch 0 */
      for(j=1;j<=6;j++)
      {
        if (bra[abs(gp[i][j])][0]==0) gp[i][j]=0;
      }
      /* ersetze Brackets durch Gleichheiten */
      for(j=1;j<=6;j++)
      {
        if (gp[i][j]!=0) gp[i][j]=sgn(gp[i][j])*bgh[abs(gp[i][j])];
      }
      /* sortiere die Gleichungen lexikographisch */
      /* AB+CD+EF => |A|<|B|,|C|<|D|,|E|<|F| */
      for(j=1;j<=3;j++)
      {
        if (abs(gp[i][2*j-1])>abs(gp[i][2*j]))
          swap(&gp[i][2*j-1],&gp[i][2*j]);
      }
      /* Ordnung innerhalb der Gleichung */
      /* A < C */
      if (abs(gp[i][1])>abs(gp[i][3]))
      { swap(&gp[i][1],&gp[i][3]); swap(&gp[i][2],&gp[i][4]); }
      /* A < E */
      if (abs(gp[i][1])>abs(gp[i][5]))
      { swap(&gp[i][1],&gp[i][5]); swap(&gp[i][2],&gp[i][6]); }
      /* C < E */
      if (abs(gp[i][3])>abs(gp[i][5]))
      { swap(&gp[i][3],&gp[i][5]); swap(&gp[i][4],&gp[i][6]); }
      /* AB + AC + DE => B < C */
      if (abs(gp[i][1])==abs(gp[i][3]) && abs(gp[i][2])>abs(gp[i][4]))
      { swap(&gp[i][1],&gp[i][3]); swap(&gp[i][2],&gp[i][4]); }
      /* AB + CD + AE => B < E */
      if (abs(gp[i][1])==abs(gp[i][5]) && abs(gp[i][2])>abs(gp[i][6]))
      { swap(&gp[i][1],&gp[i][5]); swap(&gp[i][2],&gp[i][6]); }
      /* AB + CD + CE => D < E */
      if (abs(gp[i][3])==abs(gp[i][5]) && abs(gp[i][4])>abs(gp[i][6]))
      { swap(&gp[i][3],&gp[i][5]); swap(&gp[i][4],&gp[i][6]); }
      /* Nullen hinten in die Gleichung */
      if (abs(gp[i][1])==0)
      {
        if (abs(gp[i][3])!=0)
        {
          swap(&gp[i][1],&gp[i][3]);
          swap(&gp[i][2],&gp[i][4]);
          if (abs(gp[i][5])!=0)
          swap(&gp[i][3],&gp[i][5]);
          swap(&gp[i][4],&gp[i][6]);
        }
        else if (abs(gp[i][5])!=0)
        { swap(&gp[i][1],&gp[i][5]); swap(&gp[i][2],&gp[i][6]); }
      }
      if (abs(gp[i][3])==0)
      {
        if (abs(gp[i][5])!=0)
        { swap(&gp[i][3],&gp[i][5]); swap(&gp[i][4],&gp[i][6]); }
      }
      /* Minuszeichen im ersten Faktor pro Summand */
      for(j=1;j<=3;j++)
      {
        if (sgn(gp[i][2*j-1]*gp[i][2*j])==-1)
        { gp[i][2*j-1]=-abs(gp[i][2*j-1]); gp[i][2*j]=abs(gp[i][2*j]); }
        else
        { gp[i][2*j-1]= abs(gp[i][2*j-1]); gp[i][2*j]=abs(gp[i][2*j]); }
      }
      /* ist der dritte Summand 0, die ersten beiden negativ, so ist */
      /* aequivalent alles positiv */
      if (gp[i][5]*gp[i][6]==0)
      {
        if (sgn(gp[i][1])==-1 && sgn(gp[i][3])==-1)
        { gp[i][1]=-gp[i][1]; gp[i][3]=-gp[i][3]; }
        else
        /* Minuszeichen so weit vorne wie es geht */
        if (sgn(gp[i][1])==1 && sgn(gp[i][3])==-1)
        { gp[i][1]=-gp[i][1]; gp[i][3]=-gp[i][3]; }
      }
      else
      {
        /* sind alle Summanden negativ, aequivalent alle positiv */
        if (sgn(gp[i][1])==-1 && sgn(gp[i][3])==-1 && sgn(gp[i][5])==-1)
        { gp[i][1]=-gp[i][1]; gp[i][3]=-gp[i][3]; gp[i][5]=-gp[i][5]; }
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

    /* nun werden die Gleichungen ueberprueft und redundante entfernt */
    anzgln=0; valid=TRUE;
    for(i=1;i<=anzg && valid;i++)
    {
      equ=(i != 1);
      for(j=1;j<=6;j++)
      {
        gl[j]  = gp[i][j];                /* Orbitsnr. des Faktors */
        agl[j] = abs(gl[j]);
        v[j]   = sgn(gl[j])*bset[agl[j]]; /* Vorzeichen in den Faktoren */
      }
      /* handelt es sich um eine gueltige Gleichung ? */

      valid = validgpr(v);

      if (v[5]==0)
      {
        if (agl[1]==agl[3] && agl[2]==agl[4])
          if (sgn(v[1]*v[2])==sgn(v[3]*v[4]) && sgn(v[1]*v[2])!=0) 
            valid = FALSE;
        /* AB + AB kann die GPR nicht erfuellen fuer A!=0 und B!=0 */
      }

#ifdef DEBUG
      for(j=1;j<=3;j++)
      {
         if (j>1) fprintf(wohin," + ");
         if (v[j*2-1]!=0 && v[2*j]!=0)
           fprintf(wohin,"(%i)(%i)",gl[2*j-1],gl[2*j]);
         else fprintf(wohin,"0");
      } /* for(j=... */
      fprintf(wohin," => ");
      for(j=1;j<=3;j++)
      {
         if (j>1) fprintf(wohin," + ");
         if (v[j*2-1]!=0 && v[2*j]!=0)
           fprintf(wohin,"(%c)(%c)",vrz(v[2*j-1]),vrz(v[2*j]));
         else fprintf(wohin,"0");
      } /* for(j=... */
      fprintf(wohin," %s\n",(valid)?"OK":"NOT VALID");
#endif



#ifdef DEBUG
      if (!valid)
      {
         fprintf(wohin,"Peng ! in equation %i\n",i);
         for(j=1;j<=3;j++)
         {
            if (j>1) fprintf(wohin," + ");
            if (matroid[bra[agl[j*2-1]][1]]!=0 && matroid[bra[agl[2*j]][1]]!=0)
              fprintf(wohin,"(%i)(%i)",gl[2*j-1],gl[2*j]);
            else fprintf(wohin,"0");
         } /* for(j=... */
         fprintf(wohin,"\n");
      }
#endif

      if (!valid) break; /* wenn ungueltig, keine weiter Berechnung sinnvoll */

      /* ist die Gleichung vollstaendig Null, so ist sie redundant */
      if (agl[1]*agl[2]==0 && agl[3]*agl[4]==0 && agl[5]*agl[6]==0)
        equ=TRUE;
      else

      /* ist die Gleichung erfuellt und voll besetzt, so ist sie redundant */
      if (agl[5]==0)
      {
        if (v[1]!=2 && v[2]!=2 && v[3]!=2 && v[4]!=2) equ=TRUE;
        else
        /* -AA + AA erfuellt trivialerweise */
        if (agl[1]==agl[2] && agl[3]==agl[4] &&
            agl[1]==agl[3] && v[1]*v[2]==-v[3]*v[4]) equ=TRUE;
        else
        /* war es eine doppelte Gleichung ? */
        if (i>1)
        { for(j=1;j<=4 && equ;j++)
            if (gp[i][j]!=gp[i-1][j]) equ=FALSE; }
      }
      else
      if (v[1]!=2 && v[2]!=2 &&
          v[3]!=2 && v[4]!=2 &&
          v[5]!=2 && v[6]!=2) equ=TRUE;
      else
      if (i>1)
      { for(j=1;j<=6 && equ;j++)
          if (gp[i][j]!=gp[i-1][j]) equ=FALSE; }

      /* erhalte nichtredundante, noch nicht erfuellte Gleichung */
      if (!equ)
      {
        anzgln++; for(j=1;j<=6;j++) gp[anzgln][j]=gp[i][j];
      }
    } /* for(i=1;i<=anzg... */

    /* ist vielleicht schon ein + oder - induziert ? */
    if (valid)
    {
      redo=FALSE;
      for(i=1;i<=anzgln;i++)
      {
        for(j=1;j<=6;j++)
        {
          gl[j]  = gp[i][j];         /* = vgl[j] * agl[j] */
          vgl[j] = sgn(gl[j]);
          agl[j] = abs(gl[j]);
          sig[j] = bset[agl[j]];     /* wie gesetzt */
        }
        /* Vorzeichen der Summanden der GPR */
        s1 = vgl[1] * sig[1] * vgl[2] * sig[2];
        s2 = vgl[3] * sig[3] * vgl[4] * sig[4];
        s3 = vgl[5] * sig[5] * vgl[6] * sig[6];

        /* setzen eines zu erschliessenden Vorzeichens */
        /* moeglich, wenn genau eine Bracket unbestimmt */
        /* dieser Teil ist eine C-Uebersetzung einer */
        /* Pascal-Routine von Peter Schuchert */
        anz=0;
        if (abs(s1)>1) anz++;
        if (abs(s2)>1) anz++;
        if (abs(s3)>1) anz++;
        if (anz<2)
        {
           /* im ersten Summanden etwas unbestimmt */
           if (abs(s1)==2)
           {
             if (s2==0 || s3==0 || s2==s3)
             {
               if (s2==0) vergleich = s3;
               else if (s3==0 || s2==s3) vergleich = s2;
               /* erster Faktor im ersten Summand ungesetzt */
               if (sig[1]==2)
               {
                 #ifdef FOLLOWS
                   writeeqn(gl,bset);
                 #endif
                 bset[agl[1]] = -vergleich * vgl[2] * sig[2] * vgl[1];
                 #ifdef FOLLOWS
                   fprintf(wohin," => (%i)=%i\n",agl[1],bset[agl[1]]);
                 #endif
                 redo=TRUE;
               }
               else
               /* zweiter Faktor im ersten Summand ungesetzt */
               if (sig[2]==2)
               {
                 #ifdef FOLLOWS
                   writeeqn(gl,bset);
                 #endif
                 bset[agl[2]] = -vergleich * vgl[1] * sig[1] * vgl[2];
                 #ifdef FOLLOWS
                   fprintf(wohin," => (%i)=%i\n",agl[2],bset[agl[2]]);
                 #endif
                 redo=TRUE;
               }
             } /* endif (s2==0 || s3==0 || s2==s3) */
           } /* if (abs(s1)... */
           else
           if (abs(s2)==2)
           {
             if (s1==0 || s3==0 || s1==s3)
             {
               if (s1==0) vergleich = s3;
               else if (s3==0 || s1==s3) vergleich = s1;
               if (sig[3]==2)
               {
                 #ifdef FOLLOWS
                   writeeqn(gl,bset);
                 #endif
                 bset[agl[3]] = -vergleich * vgl[4] * sig[4] * vgl[3];
                 redo=TRUE;
                 #ifdef FOLLOWS
                   fprintf(wohin," => (%i)=%i\n",agl[3],bset[agl[3]]);
                 #endif
               }
               else
               if (sig[4]==2)
               {
                 #ifdef FOLLOWS
                   writeeqn(gl,bset);
                 #endif
                 bset[agl[4]] = -vergleich * vgl[3] * sig[3] * vgl[4];
                 redo=TRUE;
                 #ifdef FOLLOWS
                   fprintf(wohin," => (%i)=%i\n",agl[4],bset[agl[4]]);
                 #endif
               }
             } /* endif (s1==0 || s3==0 || s1==s3) */
           } /* if (abs(s2)... */
           else
           if (abs(s3)==2)
           {
             if (s1==0 || s2==0 || s1==s2)
             {
               if (s1==0) vergleich = s2;
               else if (s2==0 || s1==s2) vergleich = s1;
               if (sig[5]==2)
               {
                 #ifdef FOLLOWS
                   writeeqn(gl,bset);
                 #endif
                 bset[agl[5]] = -vergleich * vgl[6] * sig[6] * vgl[5];
                 redo=TRUE;
                 #ifdef FOLLOWS
                   fprintf(wohin," => (%i)=%i\n",agl[5],bset[agl[5]]);
                 #endif
               }
               else
               if (sig[6]==2)
               {
                 #ifdef FOLLOWS
                   writeeqn(gl,bset);
                 #endif
                 bset[agl[6]] = -vergleich * vgl[5] * sig[5] * vgl[6];
                 redo=TRUE;
                 #ifdef FOLLOWS
                   fprintf(wohin," => (%i)=%i\n",agl[6],bset[agl[6]]);
                 #endif
               }
             } /* endif (s1==0 || s2==0 || s1==s2) */
           } /* if (abs(s3)... */
        } /* if (anz<2) */
      } /* for(i=1;i<=anzgln... */
      /* falls etwas gesetzt wurde, so starte erneute Sortierung */
      if (redo==TRUE) anzgln = sortgpr(anzgln,gp,bset,bgh);
    } /* if (valid) */

    return ((valid)?anzgln:-1);
}

/* ######################################################################### */

void write_om(int *styp, int *bset)
/* schreibt die berechneten moeglichen Chirotope in eine Datei */
{
    int i,j;
    int *chiro;
    int *brgh; /* Gleichheiten als Ident. zum Ueberpruefen der Vrz.liste */
    brgh = calloc(anzbro+1,sizeof(int));
    for(i=1;i<=anzbro;i++) brgh[i]=i;
    writebrset(bset);
    for(i=1;i<=anzbro && bset[i]!=2;i++) ;
#ifdef DEBUG
    fprintf(wohin,"Checking GPRs before output of oriented matroid\n");
    fprintf(wohin,"There are %i equations to check ...",anzgpo);
    writegpr(anzgpo,gpr);
#endif
    j = sortgpr(anzgpo,gpr,bset,brgh);
    if (i==anzbro+1 && j!=-1)
    {
       if (newtype) { fprintf(wohin,"\n"); newtype=FALSE; }
       chiro = calloc(matlen+1,sizeof(int));
       for(i=1;i<=anzbro;i++)
         for(j=1;j<=anzaut;j++)
           chiro[abs(bra[i][j])]=sgn(bra[i][j])*styp[j]*bset[i];
#ifdef DEBUG
       fprintf(wohin,"\nAdmissable oriented matroid :\n");
#endif
       for(i=1;i<=matlen;i++)
       {
         fprintf(wohin,"%c",vrz(chiro[i]));
#ifdef DEBUG
         if (i%72==0) fprintf(wohin,"\n");
#endif
       }
       fprintf(wohin,"\n");
       free(chiro);
    }
    free(brgh);
}

/* ######################################################################### */

void solvegpr(int *styp,int nrgl, gleichung *gp, int *bset, int *bg)
/* fuellt die Matroidliste mit Vorzeichen auf */
{
  int i,j,k,ngl,v1,v2;
  int anzfrei;           /* Anzahl freier Bracketorbits */
  int newnrgl;           /* neue Laenge des Gleichungssystems */
  gleichung *gs;         /* das Gleichungssystem */
  gleichung *gvs;        /* Gleichungssystem fuer check bei beiden Mglktn. */
  gleichung gl,sgl,sig;  /* eine bearbeitete Gleichung und ihre Vorzeichen */
  int *bgh;              /* neue Abhaengigkeiten der Bracketorbits */
  int *brset;            /* neu gesetzte Bracketorbits */
  char *frei;            /* Freiheitsgrade */

  baumtiefe++;
  /* ersten freien Bracketorbit zu + normieren */
  if (baumtiefe==1) first=TRUE; else first=FALSE;
  bgh    = calloc(anzbro+1,sizeof(int));
  frei   = calloc(anzbro+1,sizeof(boolean));
  brset  = calloc(anzbro+1,sizeof(int));
  gs     = calloc(nrgl+1,sizeof(gleichung));
  gvs    = calloc(nrgl+1,sizeof(gleichung));

  memcpy(brset,bset,((long)anzbro+1)*sizeof(int));  /* brset = bset */
  memcpy(bgh,bg,((long)anzbro+1)*sizeof(int));      /* bgh = bg */

  #ifdef DEBUG
    fprintf(wohin,"\nNow entering new pass of solvegpr\n");
  #endif

  /* Schritt 1 : Untersuche auf direkte Gleichheiten */
  for(i=1;i<=nrgl;i++)
  {
     /* Umspeichern , damit alles etwas kuerzer wird */
     for(j=1;j<=6;j++)
     {
        gl[j] =gp[i][j];
        sgl[j]=sgn(gl[j]);
        sig[j]=bset[abs(gl[j])];
     }

     /* lokales Gleichungssystem umspeichern */
     memcpy(gvs,gp,((long)nrgl+1)*sizeof(gleichung));

     /* untersuche zuerst die Gleichungen mit nur zwei Summanden */
     if (gl[5]==0)
     {
       /* echte Vorzeichen der Summanden */
       v1=sgn(sgl[1]*sgl[2]*sig[1]*sig[2]); 
       v2=sgn(sgl[3]*sgl[4]*sig[3]*sig[4]);

       /* Faelle (+-)AA + ... */
       if (abs(gl[1])==abs(gl[2]) && sig[1]==2)
       {
         /* -AA + BB => B=A oder B=-A */
         if (abs(gl[3])==abs(gl[4]) && sig[3]==2)
         {
           /* a) B=A */
           if (abs(gl[3])!=abs(gl[1]))
           {
             bgh[abs(gl[3])]=abs(gl[1]); frei[abs(gl[1])]=TRUE;
             #ifdef DEBUG
               writeeqn(gl,bset);
               fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[3]),abs(gl[1]));
             #endif
           }
           /* sortiere und ueberpruefe, ob gueltiges Gl.sys. */
           ngl = sortgpr(nrgl, gvs, brset, bgh);
           /* wenn das Gleichungssystem "umkippt" ist es */
           /* b) B=-A */
           if (ngl==-1)
           {
             if (abs(gl[3])!=abs(gl[1]))
             {
               bgh[abs(gl[3])]=-abs(gl[1]); frei[abs(gl[1])]=TRUE;
               #ifdef DEBUG
                 writeeqn(gl,bset);
                 fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[3]),-abs(gl[1]));
               #endif
             }
           } /* end if (ngl==-1) */
         } /* endif (abs(gl[3]... */
         else
         /* (+-)AA + (+-)B */
         if (sig[3]!=2 && sig[4]==2)
         {
           brset[abs(gl[4])]=-v1*sig[3];
           frei[abs(gl[1])]=TRUE;
           #ifdef DEBUG
             writeeqn(gl,bset);
             fprintf(wohin,"%3d: (%d)=%i\n",i,abs(gl[4]),-v1*sig[3]);
           #endif
         } /* endif gl[3]=+-, gl[4]=? */
         else
         /* (+-)AA + B(+-) */
         if (sig[3]==2 && sig[4]!=2)
         {
           brset[abs(gl[3])]=-v1*sig[4];
           frei[abs(gl[1])]=TRUE;
           #ifdef DEBUG
             writeeqn(gl,bset);
             fprintf(wohin,"%3d: (%d)=%i\n",i,abs(gl[3]),-v1*sig[4]);
           #endif
         } /* endif gl[3]=?, gl[4]=+- */
       } /* endif (+-)AA + ... */
       else
       /* Faelle (+-)(+-)A + ... */
       if (sig[1]!=2 && sig[2]==2)
       {
         /* (+-)A + BB */
         if (abs(gl[3])==abs(gl[4]) && sig[3]==2)
         {
           brset[abs(gl[2])]=-v1*v2;
           frei[abs(gl[3])]=TRUE;
           #ifdef DEBUG
             writeeqn(gl,bset);
             fprintf(wohin,"%3d: (%d)=%i\n",i,abs(gl[2]),-v1*v2);
           #endif
         } /* endif (+-)A + BB */
         else
         /* (+-)A + (+-)B */
         if (sig[3]!=2 && sig[4]==2)
         {
           if (abs(gl[2])>abs(gl[4]))
           {
             bgh[abs(gl[2])]=-v1*v2*abs(gl[4]);
             frei[abs(gl[4])]=TRUE;
             #ifdef DEBUG
               writeeqn(gl,bset);
               fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[2]),-v1*v2*abs(gl[4]));
             #endif
           }
           else
           {
             if (abs(gl[2])!=abs(gl[4]))
             {
               bgh[abs(gl[4])]=-v1*v2*abs(gl[2]);
               frei[abs(gl[2])]=TRUE;
               #ifdef DEBUG
                 writeeqn(gl,bset);
                 fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[4]),-v1*v2*abs(gl[2]));
               #endif
             }
           }
         } /* endif (+-)A + (+-)B */
         else
         /* (+-)A + B(+-) */
         if (sig[3]==2 && sig[4]!=2)
         {
           if (abs(gl[2])>abs(gl[3]))
           {
             bgh[abs(gl[2])]=-v1*v2*abs(gl[3]);
             frei[abs(gl[3])]=TRUE;
             #ifdef DEBUG
               writeeqn(gl,bset);
               fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[2]),-v1*v2*abs(gl[3]));
             #endif
           }
           else
           {
             if (abs(gl[2])!=abs(gl[3]))
             {
               bgh[abs(gl[3])]=-v1*v2*abs(gl[2]);
               frei[abs(gl[2])]=TRUE;
               #ifdef DEBUG
                 writeeqn(gl,bset);
                 fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[3]),-v1*v2*abs(gl[2]));
               #endif
             }
           }
         } /* endif (+-)A + (+-)B */
       } /* endif (+-)(+-)A + ... */
       else
       /* Faelle (+-)A(+-) + ... */
       if (sig[1]==2 && sig[2]!=2)
       {
         /* A(+-) + BB */
         if (abs(gl[3])==abs(gl[4]) && sig[3]==2)
         {
           brset[abs(gl[1])]=-v1*v2;
           frei[abs(gl[3])]=TRUE;
           #ifdef DEBUG
             writeeqn(gl,bset);
             fprintf(wohin,"%3d: (%d)=%i\n",i,abs(gl[1]),-v1*v2);
           #endif
         } /* endif (+-)A + BB */
         else
         /* A(+-) + (+-)B */
         if (sig[3]!=2 && sig[4]==2)
         {
           if (abs(gl[4])!=abs(gl[1]))
           {
             bgh[abs(gl[4])]=-v1*v2*abs(gl[1]);
             frei[abs(gl[1])]=TRUE;
             #ifdef DEBUG
               writeeqn(gl,bset);
               fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[4]),-v1*v2*abs(gl[1]));
             #endif
           }
         } /* endif A(+-) + (+-)B */
         else
         /* A(+-) + B(+-) */
         if (sig[3]==2 && sig[4]!=2)
         {
           if (abs(gl[3])!=abs(gl[1]))
           {
             bgh[abs(gl[3])]=-v1*v2*abs(gl[1]);
             frei[abs(gl[1])]=TRUE;
             #ifdef DEBUG
               writeeqn(gl,bset);
               fprintf(wohin,"%3d: (%d)=(%d)\n",i,abs(gl[3]),-v1*v2*abs(gl[1]));
             #endif
           }
         } /* endif (+-)A + (+-)B */
       } /* endif (+-)A(+-) + ... */
     } /* if (gl[5]==0) */
  } /* end for(i=1;i<=nrgl... */

  #ifdef DEBUG
    for(i=1;i<=anzbro;i++) fprintf(wohin,"(%i)",bgh[i]);
    fprintf(wohin,"\n");
  #endif

  /* Gleichheiten minimieren */
  for(i=anzbro;i>0;i--)
    while(abs(bgh[i]) != abs(bgh[abs(bgh[i])]))
      bgh[i] = sgn(bgh[i])*bgh[abs(bgh[i])];

  #ifdef DEBUG
    fprintf(wohin,"Equalities minimized:\n");
    for(i=1;i<=anzbro;i++) fprintf(wohin,"(%i)",bgh[i]);
    fprintf(wohin,"\n");
  #endif

  /* Gleichheiten uebertragen */
  for(i=1;i<=nrgl;i++)
    for(j=1;j<=6;j++) gs[i][j]=sgn(gp[i][j])*bgh[abs(gp[i][j])];

  /* Sortierung der Gleichung unter Beruecksichtigung der Gleichheiten */
  #ifdef DEBUG
    fprintf(wohin,"Bracketset before sorting :\n");
  #endif
  writebrset(brset);

  newnrgl = sortgpr(nrgl, gs, brset, bgh);

  /* falls Vorzeichen erschlossen wurden, diese in Gleichheiten uebertragen */
  for(i=1;i<=anzbro;i++)
  {
    if (brset[abs(bgh[i])]==2 && brset[i]!=2)
      brset[abs(bgh[i])]=sgn(bgh[i])*brset[i];
    if (brset[abs(bgh[i])]!=2 && brset[i]==2)
      brset[i]=sgn(bgh[i])*brset[abs(bgh[i])];
  }

  #ifdef DEBUG
    fprintf(wohin,"Bracketset after sorting  :\n");
    writebrset(brset);
    fprintf(wohin,"There are %i equations left ...\n",newnrgl);
  #endif
  if (newnrgl!=-1) 
  {
      if (newnrgl==0)
      {
        #ifdef DEBUG
          fprintf(wohin,"\nAll equations solved -- everything fine ...\n");
        #endif
        write_om(styp,brset);
      }

      /* Schritt 2 : Weitere freie Bracketorbits ermitteln */
      for(i=1;i<=newnrgl;i++)
      {
        /* Umspeichern , damit alles etwas kuerzer wird */
        for(j=1;j<=6;j++)
        {
           gl[j] =gs[i][j];
           sgl[j]=sgn(gl[j]);
           sig[j]=brset[abs(gl[j])];
        }
        if (gs[i][5]==0)
        {
          /* AB + AC = 0 => A frei */
          if (abs(gl[1])==abs(gl[3]) && sig[1]==2)
          { if (sig[2]==2 && sig[4]==2) frei[abs(gl[1])]=TRUE; }
          else
          /* AB + CB = 0 => B frei */
          if (abs(gl[2])==abs(gl[4]) && sig[2]==2)
          { if (sig[1]==2 && sig[3]==2) frei[abs(gl[2])]=TRUE; }
          else
          /* AB + BC = 0 => B frei */
          if (abs(gl[2])==abs(gl[3]) && sig[2]==2)
          { if (sig[1]==2 && sig[4]==2) frei[abs(gl[2])]=TRUE; }
        }
      } /* end for(i=1;i<=newnrgl... */

      /* nur kleinste aus gleichen Bracketorbits sind frei */
      anzfrei=0;
      for(i=1;i<=anzbro;i++)
        if (frei[i])
          if (abs(bgh[i])==i && brset[i]==2) { frei[i]=TRUE; anzfrei++; }
          else frei[i]=FALSE;

      /* wenn es keine freien Bracketorbits aus den Gleichungen gibt, */
      /* so muessen alle Auffuellmoeglichkeiten betrachtet werden     */
      if (anzfrei==0)
        for(i=1;i<=anzbro;i++)
          if (abs(bgh[i])==i && brset[i]==2) { frei[i]=TRUE; anzfrei++; }
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
        if (first)
        {
          #ifdef DEBUG
            fprintf(wohin,"First free bracketorbit ");
          #endif
          for(k=1;k<=anzbro;k++)
          {
            if (abs(bgh[k])==i)
            {
               #ifdef DEBUG
                 fprintf(wohin,"(#%i) ",sgn(bgh[k])*k);
               #endif
               brset[k]=sgn(bgh[k]);
            } /* if (abs(... */
          } /* for(k=1... */
          #ifdef DEBUG
            fprintf(wohin,"set to %c\n",vrz(brset[i]));
          #endif
          solvegpr(styp,newnrgl,gs,brset,bgh);
        } /* Normierung des ersten freien Bracketorbit auf + */
        else
        for(j=0;j<2;j++)
        {
          #ifdef DEBUG
            fprintf(wohin,"\nPreparing for next recursion pass...\n");
          #endif
          for(k=1;k<=anzbro;k++)
          {
            if (abs(bgh[k])==i)
            {
               #ifdef DEBUG
                 fprintf(wohin,"(#%i) ",sgn(bgh[k])*k);
               #endif
               if (j==0) brset[k]=sgn(bgh[k]);
               else brset[k]=-sgn(bgh[k]);
            } /* if (abs(... */
          } /* for(k=1... */
          #ifdef DEBUG
            fprintf(wohin,"set to %c\n",vrz(brset[i]));
          #endif
          solvegpr(styp,newnrgl,gs,brset,bgh);
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
  free(gvs);

  baumtiefe--;
}

/* ######################################################################### */

void setze_symmtyp(int *typ)
/* setzt, wie ein Automorphismus \chi abbilden soll, */
/* erzeugt ein Gleichungssystem und leitet dessen Loesung ein */
{
    int i;
#ifdef DEBUG
    int j;
#endif
    int *styp;                   /* wie die Automorphismen abbilden */
    int *brset, *broglh;         /* gesetzte und gleiche Bracketorbits */

    styp = calloc(anzaut+1,sizeof(int));
    /* schon bestimmte Symmetrietypen werden uebernommen */
    memcpy(styp,typ,((long) anzaut+1)*sizeof(int)); /* styp = symmtyp */
    /* leite die Setzung der freien Symm.typen ein, abwechselnd + und - */
    for(i=1;i<=anzaut && styp[i]!=0;i++) ;
    /* noch freie da, dann setze weiter */
    if (i<=anzaut)
    {
       styp[i]=1;
       setze_symmtyp(styp);
       styp[i]=-1;
       setze_symmtyp(styp);
    }
    else
    /* alle Symmetrietypen sind definiert, also Bracketorbits gegeben */
    {
#ifdef DEBUG
       fprintf(wohin,"\nNew constellation for symmetric mapping:\n");
       for(j=1;j<=anzaut;j++)
         fprintf(wohin,"%c",(styp[j]==0)?'0':(styp[j]==-1)?'-':'+');
       fprintf(wohin,"\n");
#endif
       newtype=TRUE;
       printf("Now working on symmetry constellation :\n");
       for(j=1;j<=anzaut;j++) printf("%c",vrz(styp[j]));
       printf("\n");

       /* definiere Bracketsetzungen */
       brset  = calloc(anzbro+1,sizeof(int));
       broglh = calloc(anzbro+1,sizeof(int));
       for(i=1;i<=anzbro;i++) { brset[i]=bra[i][0]; broglh[i]=i; }
       /* erzeuge das zugehoerige Gleichungssystem */
       make_equations(styp,gpr);

       /* sortiere und minimalisiere nun das Gleichungssystem */
       i = sortgpr(anzgpo,gpr,brset,broglh);

#ifdef DEBUG
       if (i!=-1) { writegpr(i,gpr); validsym++; }
       else fprintf(wohin,"GPR-System not valid.\n");
#endif
       if (i!=-1) solvegpr(styp,i,gpr,brset,broglh);
       free(brset);
       free(broglh);
    }
    free(styp);
}

/* ######################################################################### */

void gpr_orbits(void)
/* berechne die Orbits der Grassmann-Pluecker-Polynome */
{
    perm_a(1,0);
#ifdef SHOWGPO
    fprintf(wohin,"\n");
#endif
}

/* ######################################################################### */

void main(void)
/* Das Hauptprogramm */
{
  int anzgpr; /* Anzahl der maximal auftretenden GPP */
  int *stp;   /* Anwender zu setzenden Symmetrietyp */

  printf("\nThis programme tries to orientate matroids under symmetries\n");
  printf("\nName of matroid file (without extension .mat): ");
  scanf("%s",name);
  strcpy(matname,name); strcpy(chiname,name);
  strcat(matname,".mat"); strcat(chiname,".chi");
  printf("Name of automorphism file (without extension .aut): ");
  scanf("%s",name);
  strcpy(autname,name); strcat(autname,".aut");

  matdatei = fopen(matname,"r");
  autdatei = fopen(autname,"r");

  printf("Where should I put the Output to (file/screen) ?");
  scanf("%s",frage);
  if (frage[0]=='f' || frage[0]=='F')
  {
     chidatei = fopen(chiname,"w");
     wohin = chidatei;
  }
  else { wohin = stdout; chidatei = stdout; }

  if (matdatei==NULL)
  {
    printf(" Error while fileoperation on %s\n",matname);
    exit(1);
  }
  else
  if (autdatei==NULL)
  {
    printf(" Error while fileoperation on %s\n",autname);
    exit(1);
  }
  else
  if (chidatei==NULL)
  {
    printf(" Error while fileoperation on %s\n",chiname);
    exit(1);
  }
  else
    {
      /* Einlesen der Matroiddatei */
      printf("Reading file %s\n",matname);
      fscanf(matdatei,"%i",&npkt);
      if (npkt>MPKT-1) { printf("Too many points to compute"); exit(1); }
      fscanf(matdatei,"%i",&rang);
      if (rang>MRNG) { printf("Rank too large to compute"); exit(1); }
      matlen  = choose(npkt,rang);

      /* allokieren des Speichers fuer das vorgelegte Matroid */
      matroid = calloc(matlen+1,sizeof(int));

      einlen  = 0;
      do
      {
        einchar = fgetc(matdatei);
        if (einchar=='1') { einlen++; matroid[einlen]=1; }
        else
        if (einchar=='0') { einlen++; matroid[einlen]=0; }
      }
      while (einlen<=matlen && einchar!=EOF && einchar!='*');
      if (einlen!=matlen) { printf("Length of list not valid"); exit(1); }
      fclose(matdatei);

      /* Einlesen der Automorphismendatei */
      printf("Reading file %s\n",autname);
      fscanf(autdatei,"%i",&einint);
      if (einint!=npkt) { printf("Number of points not identical"); exit(1); }
      fscanf(autdatei,"%i",&anzaut);
      if (anzaut>MSY)
        { printf("Number of automorphisms too large to compute"); exit(1); }

      /* allokieren des Speichers fuer die Automorphismen */
      aut     = calloc(anzaut+1,sizeof(perm));
      symmtyp = calloc(anzaut+1,sizeof(int));

      for(i=1;i<=anzaut;i++)
      {
        for(j=1;j<=npkt;j++) fscanf(autdatei,"%i",&aut[i][j]);
#ifdef DEBUG
        fprintf(wohin,"[%3i] : ",i);
        writeperm(wohin,aut[i]);
        fprintf(wohin,"\n");
#endif
        einchar = fgetc(autdatei);
        if (einchar=='*' || einchar==EOF)
          { printf("Error while reading %s\n",autname); exit(1); }
      }
      fclose(autdatei);
    }

#ifdef DEBUG
  for(i=1;i<=matlen;i++)
  {
    fprintf(wohin,"%c",hex[matroid[i]]);
    if (i%72==0) fprintf(wohin,"\n");
  }
  fprintf(wohin,"\n");
  fprintf(wohin,"There are %i elements ",matlen);
  fprintf(wohin,"of %i points ",npkt);
  fprintf(wohin,"in rank %i\n",rang);
  fprintf(wohin,"Number of automorphisms : %i\n",anzaut);
#endif

  printf("Writing file %s\n",chiname);
  
  /* Berechnung der Bracketorbits */
  anzbro=0;
  bracketorbits(1,0);

#ifdef DEBUG
  presym=0;
  for(i=2;i<=anzaut;i++) if (symmtyp[i]!=0) presym++;
  fprintf(wohin,"There are %i predefined symmetry types\n",presym);
#endif

  /* allokieren des Speicher fuer die GPR */
  erza  = calloc(anzaut+1,sizeof(perm));
  erzb  = calloc(anzaut+1,sizeof(perm));
  na = rang - 2;
  nb = 4;
  anzgpr   = choose(npkt,na) * choose(npkt-na,nb);
  gpo      = calloc(anzgpr+1,sizeof(perm));

  /* Berechnung der GPR-Orbits und des Gleichungssystems */
  anzgpo=0;
  gpr_orbits();
#ifdef DEBUG
  fprintf(wohin,"There are %i equations from the GPR to consider\n",anzgpo);
#endif
  /* jetzt gibt es anzgpo zu beruecksichtigende Gleichungen */

  gpr      = calloc(anzgpo+1,sizeof(gleichung));

  /* Setzen des Symmetrietyps der Automorphismen */
  /* dabei Aufstellung des Ausgangsgleichungssystems und */
  /* Loesung des Ausgangsgleichungssystems */

  printf("Symmetrytypes set by now are :\n");
  for(i=1;i<=anzaut;i++) printf("%c",vrz(symmtyp[i]));
  printf("\nDo you wish to set further types ? (y/n)");
  scanf("%s",frage);
  if (frage[0]=='Y' || frage[0]=='y')
  {
    stp = calloc(anzaut+1,sizeof(int));
    do
    {
      memcpy(stp,symmtyp,((long) anzaut+1) * sizeof(int));
      printf("Please type full symmetrytype (+,-,0=?) as above ...\n");
      scanf("%s",frage);
      for(i=0;frage[i]!='\0' && i<anzaut;i++)
        stp[i+1]=(frage[i]=='+')?1:(frage[i]=='-')?-1:0;
      printf("You set the symmetrytypes as follows\n");
      if (stp[1]==-1)
      {
        stp[1]=1;
        printf("Identity maps always to +\n");
      }
      for(i=1;i<=anzaut;i++)
        if (symmtyp[i]!=0)
          if (symmtyp[i]!=stp[i])
          {
            stp[i]=symmtyp[i];
            printf("Predefined types cannot be altered : ");
            printf("#%i reset to %c\n",i,vrz(stp[i]));
          }
      for(i=1;i<=anzaut;i++) printf("%c",vrz(stp[i]));
      printf("\nIs this OK ? (y/n)");
      scanf("%s",frage);
    } while (frage[0]=='N' || frage[0]=='n');
    memcpy(symmtyp,stp,((long) anzaut+1) * sizeof(int));
    free(stp);
  }

  setze_symmtyp(symmtyp);

#ifdef DEBUG
  fprintf(wohin,"Number of valid symmetry constellations : %i",validsym);
#endif

  if (wohin==chidatei) fclose(chidatei);

  free(matroid);
  free(aut);
  free(erza);
  free(erzb);
  free(gpr);
  free(gpo);
}
