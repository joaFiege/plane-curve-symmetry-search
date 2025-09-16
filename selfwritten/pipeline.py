from __future__ import annotations
from typing import FrozenSet, Dict, Any, List, Callable, Iterable, Set, Dict, Sequence, Tuple, Union
from collections import defaultdict
from functools import partial

import ast
import csv
from pathlib import Path

from datatypes import *
from utils import all_signings, lintel_to_gauss, compute_plane_structures, chords_from_word, regions_from_oriented_regions
from planarity import *
from symmetries import *
from Arnold import whitney_index, St_Jpm

def read_csv(path):
    result = []
    with open(path, "r") as f:
        for line in f:
            line = line.strip()
            if line:  # leere Zeilen überspringen
                result.append(ast.literal_eval(line))
    return result

def format_word(word: Word, show_plus: bool = False) -> str:
    """
    Formatiert ein Gauss-Wort als '[(a, s), (b, t), ...]'.
    show_plus=True schreibt Vorzeichen als +1/-1, sonst 1/-1.
    """
    def fmt_letter(ltr: Letter) -> str:
        a, s = ltr
        return f"({a}, {s:+d})" if show_plus else f"({a}, {s})"
    return "[" + ", ".join(fmt_letter(l) for l in word) + "]"

def save_gauss_words_csv(
    words: List[Word],
    path: str,
    *,
    header: bool = False,
    show_plus: bool = False,
    delimiter: str = ";"
) -> None:
    """
    Schreibt words nach 'path', eine Zeile pro Wort.
    Die komplette Wortdarstellung steht in einer Spalte namens 'word' (wenn header=True).
    """
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f, delimiter=delimiter, quoting=csv.QUOTE_MINIMAL)
        if header:
            writer.writerow(["word"])
        for w in words:
            writer.writerow([format_word(w, show_plus=show_plus)])


# ---- Formatter (wie bisher, plus Regions) ----
def format_word(word: Word, show_plus: bool = False) -> str:
    """'[(a, s), (b, t), ...]'; show_plus=True schreibt +1/-1."""
    def fmt_letter(ltr: Letter) -> str:
        a, s = ltr
        return f"({a}, {s:+d})" if show_plus else f"({a}, {s})"
    return "[" + ", ".join(fmt_letter(l) for l in word) + "]"

def format_arcs(arcs: Sequence[Arc]) -> str:
    """'[(i, j), (k, l), ...]'"""
    return "[" + ", ".join(f"({i}, {j})" for (i, j) in arcs) + "]"

def format_regions(regions: Sequence[Structure]) -> str:
    """'[[...arcs...], [...arcs...], ...]' — jede Region als eigene Arc-Liste."""
    return "[" + ", ".join(format_arcs(r.arcs) for r in regions) + "]"

# ---- CSV-Writer für Computation ----
def save_computations_csv(
    computations,                      # Iterable von Computation-Objekten
    path: Union[str, Path],
    *,
    header: bool = True,
    show_plus: bool = False,
    delimiter: str = ";",
) -> Path:
    """
    Schreibt pro Zeile eine Computation:
      Word ; regions ; idx_unbounded ; whitney ; St ; Jp ; Jm

    - Legt fehlende Ordner automatisch an.
    - Überschreibt bestehende Dateien.
    - Word/regions als Python-Literale ohne Quotes, mit []/() wie oben formatiert.
    """
    p = Path(path)
    if p.parent and not p.parent.exists():
        p.parent.mkdir(parents=True, exist_ok=True)

    with p.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f, delimiter=delimiter, quoting=csv.QUOTE_MINIMAL, lineterminator="\n")
        if header:
            w.writerow(["Word", "regions", "idx_unbounded", "whitney", "St", "Jp", "Jm"])
        for comp in computations:
            w.writerow([
                format_word(list(comp.word), show_plus=show_plus),   # tuple/list beides ok
                format_regions(list(comp.regions)),
                int(comp.idx_unbounded),
                int(comp.whitney),
                int(comp.St),
                int(comp.Jp),
                int(comp.Jm),
            ])
    return p


def load_computations_csv(path: Union[str, Path]) -> List[Computation]:
    """
    Liest eine CSV-Datei im Format von save_computations_csv ein
    und gibt eine Liste von Computation-Objekten zurück.
    """
    computations: List[Computation] = []
    with open(path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f, delimiter=";")
        for row in reader:
            # Strings aus der CSV wieder in Python-Objekte parsen
            word = ast.literal_eval(row["Word"])
            regions_raw = ast.literal_eval(row["regions"])
            regions = [Structure(arcs) for arcs in regions_raw]

            comp = Computation(
                word=word,
                regions=tuple(regions),
                idx_unbounded=int(row["idx_unbounded"]),
                whitney=int(row["whitney"]),
                St=int(row["St"]),
                Jp=int(row["Jp"]),
                Jm=int(row["Jm"]),
            )
            computations.append(comp)
    return computations

def _key_invariants(c: Computation) -> Tuple[int, int, int, int]:
    return (c.whitney, c.St, c.Jp, c.Jm)


def are_equiv_PSGD_pair(
    p1: Tuple[Word, List[OrientedArc]],
    p2: Tuple[Word, List[OrientedArc]],
) -> bool:
    w1, ps1 = p1
    w2, ps2 = p2
    return are_equiv_PSGD(w1, ps1, w2, ps2)


# Abspeichern der Kurvenpaare:
import os, csv
from typing import Iterable

def plane_structure_of(c: Computation) -> List[Arc]:
    # unbeschränkte Region liefert die plane-structure als Liste von Arcs
    return list(c.regions[c.idx_unbounded].arcs)

def word_to_str(word: Iterable[Letter], show_plus: bool = True) -> str:
    # z.B. [(1,+1),(1,-1)] -> "1+ 1-"
    out = []
    for (lbl, sgn) in word:
        if sgn > 0:
            out.append(f"{lbl}{'+' if show_plus else ''}")
        else:
            out.append(f"{lbl}-")
    return " ".join(out)

def arcs_to_str(arcs: Iterable[OrientedArc]) -> str:
    # z.B. [(0,1),(2,3)] -> "(0,1) (2,3)"
    return " ".join(f"({a},{b})" for (a,b) in arcs)

def dump_conflict_pairs_csv(
    n: int,
    point_multiset: Dict[Tuple[int,int,int,int], List[Computation]],
    mirror_multiset: Dict[Tuple[int,int,int,int], List[Computation]],
    out_dir: str = "new_data",
) -> str:
    """
    Schreibt NUR Paare (I,J) in eine CSV, bei denen:
      - I punkt-symmetrisch,
      - J spiegel-symmetrisch,
      - gleiche Invarianten,
      - und KEIN Diagramm in diesem Invarianten-Bucket beide Symmetrien erfüllt.
    """
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, f"curve_pairs_{n}.csv")

    both_keys = set(point_multiset.keys()) & set(mirror_multiset.keys())

    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f, delimiter=";", quoting=csv.QUOTE_MINIMAL, lineterminator="\n")
        # Header
        w.writerow([
            "n", "N",
            "whitney", "St", "Jp", "Jm",
            # I = point-symmetric
            "I_word", "I_idx_unbounded", "I_plane_structure",
            # J = mirror-symmetric
            "J_word", "J_idx_unbounded", "J_plane_structure",
        ])

        for key in sorted(both_keys):
            pts = point_multiset[key]
            mrs = mirror_multiset[key]

            # Prüfe, ob in diesem Bucket ein Diagramm existiert, das beide Symmetrien hat.
            exists_both = (
                any(is_mirror_symmetric(list(c.word), plane_structure_of(c)) for c in pts) or
                any(is_point_symmetric(list(c.word), plane_structure_of(c)) for c in mrs)
            )
            if exists_both:
                continue  # Wir wollen nur Konflikt-Paare ohne beides

            w_idx, St, Jp, Jm = key
            # Alle Paare I x J (kartesisches Produkt) exportieren
            for I in pts:
                wI  = list(I.word)
                psI = plane_structure_of(I)
                for J in mrs:
                    wJ  = list(J.word)
                    psJ = plane_structure_of(J)
                    w.writerow([
                        n, 2*n,
                        w_idx, St, Jp, Jm,
                        word_to_str(wI, show_plus=True), I.idx_unbounded, arcs_to_str(psI),
                        word_to_str(wJ, show_plus=True), J.idx_unbounded, arcs_to_str(psJ),
                    ])
    return path


if __name__=='__main__':
	N_MIN, N_MAX = 2,5
	PATH = "./new_data"
	to_compute = ['filter for symmetries']

	if 'compute spherical curves' in to_compute:
		# https://oeis.org/A008987

		# Lintels einlesen
		Lintels : Dict[int, list] = {}
		for n in range(N_MIN,N_MAX+1):
			Lintels[n] = read_csv(f"../Gauss-Lintel/data/{n}-odd_even_matchings_mod.csv")

		# Lintels zu Gauss Diagrammen casten
		GDs: Dict[int, List[int]] = {n: [] for n in Lintels}
		for n, L in Lintels.items():
		    for lintel in L:  # jedes Element in der Liste
		        GDs[n].append(lintel_to_gauss(lintel))


		# Gauss Diagramme signieren und planarity checken
		spherical_curves : Dict[int, List] = {n: [] for n in Lintels}
		for n in Lintels:
			for word in GDs[n]:
				candidates = all_signings(word)

				planar_spherical_curves = []
				for candidate in candidates:
					if check_planar(candidate): # and candidate[0][1] == 1: # Zusatzbedingung, damit ich die Spiegelung einer Signierung nicht werte (einfügen, wenn nicht beide betrachtet werden sollen)
						planar_spherical_curves.append(candidate)

				# Äquivalente Diagramme rausfiltern, bis pro Klasse nur eins übrig ist:
				# Konfiguriere, welche Symmetrien zählen:

				spherical_curves[n] += class_representatives(planar_spherical_curves, are_equiv_SGD) 
			
			print(f"n={n}: ", len(spherical_curves[n]))

			# Saving the spherical curves:
			save_gauss_words_csv(spherical_curves[n], f"{PATH}/spherical_curves_{n}.csv", header=False, show_plus=False)

		print("------------------")

	if 'compute plane curves and their invariants' in to_compute:
		# Wahrscheinlich wäre es sinnvoll den ganzen Spaß für UU, UO, OU, OO zu machen un nicht nur für UO
		# https://oeis.org/A008981

		spherical_curves: Dict[int, List[Word]] = {}
		computations : Dict[int, Computation] = {}
		for n in range(N_MIN,N_MAX+1):
			spherical_curves[n] = read_csv(f"{PATH}/spherical_curves_{n}.csv")
			computations[n] = []

			for s_curve in spherical_curves[n]:
				oriented_regions : List[OrientedArc] = compute_plane_structures(s_curve)
				# print("oriented_regions: ", oriented_regions, "\n")
				regions = regions_from_oriented_regions(oriented_regions, N=2*n)
				if len(regions)!=n+2:
					raise RuntimeError("miscalculated regions -- probably the new fix, I introduced 25/08/2025 in order to eliminate duplicates")

				plane_curves = class_representatives(
				    [(s_curve, plane_structure) for plane_structure in regions],
				    are_equiv_PSGD_pair,   # <-- use the adapter
				)

				for p_curve in plane_curves:
					word, plane_structure = p_curve

					idx = regions.index(plane_structure)

					w = whitney_index(word, oriented_regions, outside_idx=idx)
					St, Jp, Jm = St_Jpm(s_curve, w)

					computations[n].append(Computation(
					    word=word,
					    regions=regions,
					    idx_unbounded=idx,
					    whitney=w,
					    St=St,
					    Jp=Jp,
					    Jm=Jm,
					))



			print(f"n={n}: ", len(computations[n]))
			p = save_computations_csv(computations[n], f"{PATH}/plane_curves_and_their_invariants_{n}.csv", header=True, show_plus=False)
			print(f"geschrieben nach: ", p)

	if 'filter for symmetries' in to_compute:
	    for n in range(N_MIN, N_MAX+1):
	        print(n)
	        all_comps: List[Computation] = load_computations_csv(
	            f"{PATH}/plane_curves_and_their_invariants_{n}.csv"
	        )

	        # Multimengen (Invarianten -> Liste von Computations)
	        point_multiset: Dict[Tuple[int, int, int, int], List[Computation]] = defaultdict(list)
	        mirror_multiset: Dict[Tuple[int, int, int, int], List[Computation]] = defaultdict(list)

	        # kleine Hilfsfunktion für Lesbarkeit
	        def plane_structure_of(c: Computation) -> List[Arc]:
	            return list(c.regions[c.idx_unbounded].arcs)  # <- idx_unbounded gemäß datatypes.py

	        for comp in all_comps:
	            w  = list(comp.word)
	            ps = plane_structure_of(comp)

	            if is_point_symmetric(w, ps):
	                point_multiset[_key_invariants(comp)].append(comp)
	            if is_mirror_symmetric(w, ps):
	                mirror_multiset[_key_invariants(comp)].append(comp)

	        # Schnitt der Schlüssel (gleiche Invarianten)
	        both_keys = set(point_multiset.keys()) & set(mirror_multiset.keys())

	        # Für jeden gemeinsamen Schlüssel  prüfen, ob es ein Diagramm gibt, das BEIDES erfüllt.
	        for key in sorted(both_keys):
	            pts = point_multiset[key]
	            mrs = mirror_multiset[key]

	            # Existiert ein Diagramm, das zusätzlich auch die jeweils andere Symmetrie erfüllt?
	            exists_both = (
	                any(is_mirror_symmetric(list(c.word), plane_structure_of(c)) for c in pts)
	                or
	                any(is_point_symmetric(list(c.word), plane_structure_of(c)) for c in mrs)
	            )

	            if not exists_both:
	                w_idx, St, Jp, Jm = key  # key ist (whitney, St, Jp, Jm)
	                print("\n--- Kein Diagramm gleichzeitig punkt- und spiegelsymmetrisch ---")
	                print(f"Invarianten: whitney={w_idx}, St={St}, Jp={Jp}, Jm={Jm}")
	                print("Punktsymmetrische Diagramme (als (word, idx_unbounded)):")
	                for c in pts:
	                    print(c)
	                print("Spiegelsymmetrische Diagramme (als (word, idx_unbounded)):")
	                for c in mrs:
	                    print(c)

	        out_path = dump_conflict_pairs_csv(n, point_multiset, mirror_multiset, out_dir=PATH)
	        print("geschrieben nach:", out_path)



