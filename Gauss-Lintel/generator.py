from gauss_lintel_wrapper import GaussLintel
from draw import draw_lintel 
import matplotlib.pyplot as plt
from typing import Dict
import csv

def save_lintels_as_csv(filename: str, data: list):
    with open(filename, "w", newline="", encoding="utf-8") as f:
        wr = csv.writer(f, delimiter=";")  # z.B. Semikolon oder Tab ('\t')
        wr.writerows([str(m)] for m in data)  # jede Liste als EIN Feld/Zeile



Lintels : Dict[int, list] = {}

gl = GaussLintel()

# Generiert alle odd-even-matchings modulo Rotationen und Reflektionen (äquivalenz)
# Siehe https://oeis.org/A357442
m=10
for n in range(m+1):
    N = 2*n
    gl.generate_lintels(N, filter="all")

    Lintels[n] = gl.get_lintels(N)
    print(f"n={n}, Anzahl Diagramme: {len(Lintels[n])}")
    save_lintels_as_csv(f"{n}-odd_even_matchings_mod.csv", Lintels[n])

    # Filterung nach realisierbaren Diagrammen (is_realizable() aus gauss-lintel funktioniert nur für Prim-Diagramme -- steht im Prolog-Code)
    # Prüfe, ob die Ergebnisse korrekt sind mit https://oeis.org/A008987

