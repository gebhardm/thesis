/* Compute_Chirotop */
/* Berechnet zu einer (n x d)-Matrix ein Chirotop */

#include <stdio.h>
#include <string.h>

typedef double vector[30];
typedef double matrix[30][20];

matrix p;
int n; int d;
int z; int s;
int br[20];
int cnt;
float inwert;

char name[50];               /* Dateiname */
char inname[50];             /* Dateiname Vorzeichenliste */
char outname[50];            /* Dateiname Symmetriedatei */
FILE *indatei;               /* File of Text (Eingabe) */
FILE *outdatei;              /* File of Text (Ausgabe) */
FILE *wohin;

int sgn(float z)
{
  return((z<0)?-1:(z==0)?0:1);
}

char vorz(float z)
{
  return((z<0)?'-':(z==0)?'0':'+');
}

int high(int i)
{
  return((i/2 == (float) i/2)?1:-1);
}

double det(matrix m, int n)
{
  int i, j, k;
  double wert;
  matrix um;
  vector w;
  if (n==1) return(m[1][1]);
  else {
    for(i=1;i<=n;i++)
      {
        for(j=1;j<n;j++)
        {
          for(k=1;k<n;k++)
          {
            if (k<i) um[j][k] = m[j+1][k];
            else um[j][k] = m[j+1][k+1];
          }
       }
        w[i] = det(um,n-1);
      } /* for i */
      wert = 0.0;
      for(i=1;i<=n;i++)
      {
        wert = wert + high(i-1) * m[1][i] * w[i];
      }
      return(wert);
  } /* if n=1 */
}

void omat(int idx, int k)
{
int i, z, s;
matrix u;
  for(i=k+1;i<=n;i++)
    {
      br[idx] = i;
      if (idx==d) {
                     for(z=1;z<=d;z++)
                     {
                        for(s=1;s<=d;s++) u[z][s] = p[br[z]][s];
                     }
                     fprintf(wohin,"%c",vorz(det(u,d)));
                     cnt++;
                     if (cnt==72) { fprintf(wohin,"\n"); cnt = 0; }
                  }
      else omat(idx+1,i);
    }
}

void main(void)
{
  printf("\nName of input file (without extension .dat): ");
  scanf("%s",name);
  strcpy(inname,name);
  strcpy(outname,name);
  strcat(inname,".dat");
  strcat(outname,".chi");
  indatei = fopen(inname,"r");

  printf("Where should I put the Output to (file/screen) ?");
  scanf("%s",name);
  if (name[0]=='f' || name[0]=='F')
  {
     outdatei = fopen(outname,"w");
     wohin = outdatei;
  }
  else { wohin = stdout; }

  if ((indatei==NULL) && (outdatei==NULL))
  {
    printf(" Error while fileoperation on %s, %s\n",inname, outname);
    exit(1);
  }
  else
  {
     printf("Lese Datei %s\n",inname);
     fscanf(indatei,"%i",&n);
     fscanf(indatei,"%i",&d);
     for(z=1;z<=n;z++)
     {
        for(s=1;s<=d;s++)
        {
           fscanf(indatei,"%f",&inwert);
           p[z][s] = (double) inwert;
        }
     }
     fclose(indatei);
  }
  fprintf(wohin,"%i\n",n);
  fprintf(wohin,"%i\n",d);
  cnt = 0;
  omat(1,0);
  fprintf(wohin,"*");
}
