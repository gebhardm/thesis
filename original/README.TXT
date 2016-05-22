ANSI-C Programme zur Diplomarbeit von
Markus Gebhard, THD, FB Mathematik, AG3
bei Herrn Prof. Dr. J. Bokowski

DRSYM   .C  -- Berechnet die Symmetriegruppe zu einem simplizialen 2-Komplex

MATRTEST.C  -- Testet eine Matroidliste auf Erfuellung der
               Matroid-Basisdefinition

ORIMAT  .C  -- Versucht eine Matroidliste unter einer Symmetriebedingung zu
               orientieren

SUREBASE.C  -- Gibt die "Sicherlich-" und "Sicherlich-Nicht-" Basen zu einem
               Matroid zu einem CW-Komplex mit polygonaler Zellenberandung aus.

SYM2MAT .C  -- Erzeugt zu einer Symmetriegruppe vertraegliche Matroide

AUTONOM .C  -- Testet ein Vorzeichenliste auf ErfÅllung einer
               Symmetrieeigenschaft

VRZSYM  .C  -- Berechnet zu einer Vorzeichenliste derern Symmetriegruppe

AUTONMAT.C  -- Testet eine Matroidliste auf ErfÅllung einer
               Symmetrieeigenschaft

GONSYM  .C  -- Berechnet zu einem CW-Komplex mit polygonaler Zellenberandung
               dessen Symmetriegruppe

MATSYM  .C  -- Berechnet zu einer Matroidliste deren Symmetriegruppe

SHOW_GPR.C  -- Zeigt k-summandige Grassmann-Pluecker-Relationen an.

CHIROTOP.C  -- Berechnet zu einer (n x d)-Matrix eine Vorzeichenliste

Formate von Eingabedateien:

*.gon :
4                                % Anzahl der 0-Zellen pro Facette
1264 2586 5378 3147 4687 1253*   % Die Facetteliste

*.drl :
hex                                  % 0-Zellen im Format 0..9A..Z
12C 23C 34C 45C 56C ... 16B 27B 38B* % Dreiecksliste

*.aut :
8                    % Anzahl der Punkte
48                   % Anzahl der folgenden Symmetrieelemente
1 2 3 4 5 6 7 8      % Identitaet
1 2 4 3 6 5 7 8      % erste Permutation
...
8 7 5 6 3 4 2 1
8 7 6 5 4 3 2 1      % letzte Permutation
*

*.bas :
8                    % Punktanzahl
4                    % Rang
10111101111111?11011111?111?111?111111?111?111?11111011?11111110111101*

*.mat :
8                    % Punktanzahl
4                    % Rang
1011110111111101101111101110111011111101110111011111011011111110111101*

*.chi :
8                    % Punktanzahl
4                    % Rang
+0+++-0--+++--0++0+----0+-+0++---+-++++---0++-0-++--0+-0++++---0---+0-*

*.dat :
8                    % Punktanzahl
4                    % Rang
1 0 0 0
1 1 0 0
1 0 1 0
1 0 0 1
1 1 1 0
1 1 0 1
1 0 1 1
1 1 1 1
*
