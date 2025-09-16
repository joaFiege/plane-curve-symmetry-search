# utils.py
from __future__ import annotations
import re
from typing import List, Tuple, Sequence, Dict, Iterator, Any
from dataclasses import dataclass
from datatypes import *
from collections import deque

def parse_word(raw: str | Sequence[Tuple[int, int]]) -> Word:
    """'1+ 1- 2+ 2-'  →  [(1,+1), (1,-1), (2,+1), (2,-1)]."""
    if isinstance(raw, list):
        return [(int(l), int(s)) for l, s in raw]

    tokens = re.findall(r"(\d+)([+-])", raw)
    if not tokens:
        raise ValueError("Leeres oder ungültiges Gauss-Wort")

    return [(int(lbl), 1 if sig == "+" else -1) for lbl, sig in tokens]

def chords_from_word(word: Word) -> List[Chord]:
    """
    Liefert die kanonische Chord-Liste eines Gaussworts.
    Beispiel:
        [(0,+1), (1,+1), (1,-1), (0,-1)]  ➜  [(0,3), (1,2)]
    Reihenfolge der Rückgabe: sortiert nach dem kleineren Index.
    """
    first_pos: Dict[Label, int] = {}
    chords: List[Chord] = []

    for idx, (lab, _) in enumerate(word):
        if lab not in first_pos:
            first_pos[lab] = idx            # erstes Vorkommen merken
        else:
            p, q = first_pos.pop(lab), idx  # zweites Vorkommen: Chord fertig
            canon = (p, q) if p < q else (q, p)
            chords.append(canon)

    # Optional: prüfen, ob alle Labels paarweise auftraten
    if first_pos:
        raise ValueError(f"Label(s) ohne Partner gefunden: {list(first_pos.keys())}")

    return sorted(chords, key=lambda t: t[0])

def get_chord_sign(word: Word, chord: Chord) -> Sign:
    idx, _ = chord
    return -word[idx][1]

def check_signing(word: Word) -> None:
    # raises value error, if signing is incorrect
    ...

# ---------------------------------------------------------------------------
# Hauptalgorithmus nach Prop. 8.7 und Porp 9.3
# ---------------------------------------------------------------------------

# ACHTUNG: In der Rückgabe können Werte doppelt auftreten! Ich habe für diesen Zweck eliminate_duplicates geschrieben
# Das lässt sich vermutlich dadurch vermeiden, dass ich (j,\delta) in visited_starts mit aufnehme (siehe BA) - habe ich noch nicht gemacht, da ich den Code schon laufen lassen habe
def walking_algo(word: Word, flip_sign: bool, *, provide_orientations : bool = False) -> Iterator[Any]:
    """Generator, der jede "Plane-Structure/Seifert-Zykel" einmal liefert.
       flip_sign = True um Plane-Structure zu generieren
       flip_sign = False um Seifert-Zykel zu generieren
    """

    N = len(word)
    if N % 2:
        raise ValueError("Ein Gauss‑Wort muss gerade Länge haben (2n)")

    # Endpunkte der Chords: label → [position1, position2]
    occurrences: Dict[Label, List[int]] = {}
    for idx, (lbl, _) in enumerate(word):
        # occurences[lbl] wird auf [] gesetzt, falls unter dem Label noch kein Wert gespeichert ist
        occurrences.setdefault(lbl, []).append(idx) 

    if any(len(v) != 2 for v in occurrences.values()):
        raise ValueError("Jedes Label muss genau zweimal vorkommen")


    visited_starts: set[Tuple[int, int]] = set()
    for start_idx in range(N):
        for direction in [+1,-1]:

            # Wir wollen jedes Tupel (Startpunkt, Startrichtung) nur einmal betrachten
            if (start_idx, direction) in visited_starts:
                continue

            structure_arcs: List[Arc] = []

            # oriented: List[tuple[Arc,Sign]] = []
            idx = start_idx
            dir_now = direction

            while True:
                nxt = (idx + dir_now) % N  # benachbarte Position
                
                
                if not provide_orientations:
                    arc = (idx, nxt) if dir_now > 0 else (nxt, idx) # Wir speichern die arcs in der Form (k, k+1) (jeweils mod 2n)
                else:
                    arc = (nxt, idx)

                structure_arcs.append(arc)
                # oriented.append((arc, dir_now))

                label, sign = word[nxt] # label vom Chord mit nxt als einen der Endpunkte
                a, b = occurrences[label]
                idx = b if nxt == a else a  # zum Gegenstück springen; siehe Prop. 8.7 (1) bzw Prop. 9.3

                # Kein VZ-Wechsel für Prop. 9.3 
                if flip_sign and sign < 0:
                    dir_now = -dir_now  # Vorzeichensprung; siehe Prop. 8.7 (2), (3)

                if idx == start_idx and dir_now == direction:
                    break  # plane_structure vollständig

            # gemeinsam sortieren
            # oriented.sort(key=lambda t: t[0][0]) # nach erstem Arc-Endpunkt sortieren
            structure_arcs.sort(key=lambda t: t[0])
            # norm_arcs  = [arc  for arc, _dir in oriented]
            
            yield Structure(structure_arcs)
            visited_starts.add((start_idx, direction))


def label_positions(word: Word) -> Dict[Label, List[int]]:
    """
    Liefert für jedes Chordlabel die beiden Vorkommens-Indizes im Gauss-Wort.
    """
    pos: Dict[Label, List[int]] = {}
    for idx, (lbl, _) in enumerate(word):
        pos.setdefault(lbl, []).append(idx)
    return pos

def chords_touching_arc(word: Word, arc: Arc) -> List[Chord]:
    """
    Liefert alle Chords (pos_i, pos_j), die an den Endpunkten des
    gegebenen Arcs liegen.
    """

    # Label → [pos1,pos2]
    lab2pospair = label_positions(word)

    touching: List[Chord] = []
    for pos1, pos2 in lab2pospair.values():
        if pos1 in arc or pos2 in arc:
            canon = (pos1, pos2) if pos1 < pos2 else (pos2, pos1)
            touching.append(canon)

    # Duplikate entfernen & sortieren
    return sorted(set(touching), key=lambda p: p[0])

def eliminate_duplicates(oriented_regions: List[List[Any]]) -> List[List[Any]]:
    """
    Entfernt Duplikate unter orientierten Regionen.
    Zwei Regionen gelten als gleich, wenn sie genau dieselben *orientierten* Arcs enthalten
    (Reihenfolge egal; (a,b) ≠ (b,a)).

    Gibt für jede Äquivalenzklasse genau einen Repräsentanten zurück (stabil:
    das erste Auftreten bleibt).
    """
    seen: Dict[FrozenSet[OrientedArc], List[OrientedArc]] = {}
    for reg in oriented_regions:
        key = frozenset(reg)   # Menge orientierter Arcs (hashbar, Reihenfolge egal)
        if key not in seen:
            seen[key] = reg
    return list(seen.values())

def compute_plane_structures(raw: str | Word) -> List[List[OrientedArc]]:
    """Gibt alle Plane Structures des übergebenen signierten Gauss‑Worts zurück."""
    w = parse_word(raw)
    uniq: Dict[Tuple[Arc, ...], Region] = {}
    for ps in walking_algo(w, flip_sign=True, provide_orientations=True):
        uniq[tuple(ps.arcs)] = ps  # doppelt auftretende Strukturen eliminieren
    return eliminate_duplicates(list(uniq.values()))

def incidence_map(structures: List[Structure]) -> Dict[int, Set[int]]:
    """
    Liefert Dict: Index → {struct_id, …}  (welche Strukturen berühren die Kreis-Position Index?)
    """
    pos2struct: Dict[int, Set[int]] = {}
    for sid, struct in enumerate(structures):
        for a, b in struct.arcs:
            pos2struct.setdefault(a, set()).add(sid)
            pos2struct.setdefault(b, set()).add(sid)
    return pos2struct

def get_arc2cid(cycles: List[SeifertCycle]) -> Dict[Arc, int]:
    """
    Liefert Dict: Arc → Cycle-ID.
    Wirft ValueError, falls derselbe Arc in zwei Zykeln auftaucht
    (sollte laut Lemma 9.6 nie passieren).
    """
    arc2cid: Dict[Arc, int] = {}
    for cid, cyc in enumerate(cycles):
        for arc in cyc.arcs:
            if arc in arc2cid:
                raise ValueError(
                    f"Arc {arc} liegt in zwei Zykeln "
                    f"({arc2cid[arc]} und {cid}).")
            arc2cid[arc] = cid
    return arc2cid


def lintel_to_gauss(
        lintel: Sequence[Sequence[int]],
        *,
        base: int = 0,
        start: int = 0,
        clockwise: bool = True,
        labeling: str = "index",     # "index" oder "appearance"
        signed: bool = False
    ) -> List[int] | List[Tuple[int, int]]:
        """
        Konvertiere ein Lintel in ein (un)signiertes Gausswort.

        Parameter
        ---------
        lintel : Liste von Paaren [i,j] der Endpunkte (jede Zahl genau einmal),
                 typischerweise i,j ∈ {0,...,2n-1}.
        base :   0 falls Endpunkte 0-basiert (Standard), 1 falls 1-basiert.
        start :  Startposition auf dem Kreis (in derselben Basis wie `base`).
        clockwise : Laufrichtung beim Ablesen.
        labeling :  "index"      → Label = Reihenindex in `lintel` (1..n)
                    "appearance" → Label = Reihenfolge der ersten Begegnung beim Umlauf
        signed :   False → unsigniertes Wort [1,1,2,2,...]
                   True  → signiertes Wort [(1,+1),(1,-1),(2,+1),(2,-1),...]

        Rückgabe
        --------
        Liste der Labels (unsigniert) oder Liste von (Label, Vorzeichen)-Tupeln.
        """
        # --- Validierung & Normalisierung ---
        if any(len(e) != 2 for e in lintel):
            raise ValueError("Jedes Lintel-Element muss ein Paar [i,j] sein.")
        n = len(lintel)
        m = 2 * n

        # Basisnormalisierung (0-basiert intern)
        pairs = []
        for a, b in lintel:
            a0, b0 = a - base, b - base
            pairs.append((a0, b0))
        start0 = start - base

        # Prüfen, dass die Endpunkte genau {0,...,2n-1} bilden
        used = [u for p in pairs for u in p]
        if sorted(used) != list(range(m)):
            raise ValueError(
                f"Endpunkte müssen genau die Menge {{0,...,{m-1}}} bilden (0-basiert)."
                " Prüfe `base` oder die Eingabe."
            )

        # position → pair_id (0..n-1)
        pos2pair = [-1] * m
        for pid, (u, v) in enumerate(pairs):
            if pos2pair[u] != -1 or pos2pair[v] != -1:
                raise ValueError("Ein Endpunkt kommt mehrfach vor.")
            pos2pair[u] = pos2pair[v] = pid

        # Umlaufliste der Positionen
        step = 1 if clockwise else -1
        order = [(start0 + step * k) % m for k in range(m)]

        # Label-Zuordnung
        if labeling not in {"index", "appearance"}:
            raise ValueError("labeling muss 'index' oder 'appearance' sein.")

        pair2label: Dict[int, int] = {}
        next_label = 1
        if labeling == "index":
            # feste Label: pair_id 0..n-1 ↦ 1..n
            pair2label = {pid: pid + 1 for pid in range(n)}

        # (optional) Sign-Berechnung: +1 beim ersten, -1 beim zweiten Auftreten
        seen_count = [0] * n

        out_unsig: List[int] = []
        out_sig: List[Tuple[int, int]] = []

        for pos in order:
            pid = pos2pair[pos]
            if labeling == "appearance":
                if pid not in pair2label:
                    pair2label[pid] = next_label
                    next_label += 1
            lab = pair2label[pid]

            if signed:
                seen_count[pid] += 1
                sgn = +1 if seen_count[pid] == 1 else -1
                out_sig.append((lab, sgn))
            else:
                out_unsig.append(lab)

        return out_sig if signed else out_unsig


def regions_from_oriented_regions(oriented_regions: List[List[OrientedArc]], N: int):
    if N<=2:
        raise NotImplementedError("Trivial cases might lead to errors when normalizing")

    regions = []
    for o_reg in oriented_regions:
        reg = []
        for arc in o_reg:
            a, b = arc

            if b==(a+1) % N:
                reg.append((a,b))
            else:
                reg.append((b,a))
        reg.sort(key=lambda r: r[0])
        regions.append(Region(reg))
    return regions


if __name__=='__main__':
    # TEST: compute_plane_structures() ---------------
    demo = "1- 1+ 2+ 2-"
    structures = compute_plane_structures(demo)
    print(f"Gauss‑Wort: {demo}\nGefundene Plane Structures ({len(structures)}):")
    for s in structures:
        print("  ", s)

    """ Gewünschtes Ergebnis:
    Structure([(0, 1)])
    Structure([(1, 2), (2, 3), (3, 0)])
    Structure([(0, 1), (1, 2), (3, 0)])
    Structure([(2, 3)])
   """

    demo = "1- 2+ 2- 1+ 3+ 3-"
    structures = compute_plane_structures(demo)
    print(f"Gauss‑Wort: {demo}\nGefundene Plane Structures ({len(structures)}):")
    for s in structures:
        print("  ", s)

    """ Gewünschtes Ergebnis:
    Structure([(0, 1), (2, 3)])
    Structure([(3, 4), (4, 5), (5, 0)])
    Structure([(0, 1), (1, 2), (2, 3), (3, 4), (5, 0)])
    Structure([(1, 2)])
    Structure([(4, 5)])
    """



def all_signings(word: Sequence[int]) -> List[List[Tuple[int, int]]]:
    """
    Erzeuge alle 2^n möglichen Signierungen eines unsignierten Gaussworts.
    Für jede Marke k werden ihre beiden Vorkommen mit (+1,-1) oder (-1,+1)
    (in Positionsreihenfolge) belegt.

    Parameters
    ----------
    word : Sequenz von Marken (z.B. [1,1,2,2]); jede Marke genau 2×.

    Returns
    -------
    List[List[Tuple[int,int]]]
        Liste von signierten Wörtern, jeweils als Liste von (Marke, Sign) mit Sign ∈ {+1,-1}.

    Raises
    ------
    ValueError, falls eine Marke ≠ 2× vorkommt oder die Länge ungerade ist.
    """
    m = len(word)
    if m % 2 != 0:
        raise ValueError("Länge muss gerade sein (2n).")

    # Positionen jeder Marke sammeln, in Auftretensreihenfolge
    pos: Dict[int, List[int]] = {}
    order: List[int] = []  # Marken in Reihenfolge des ersten Auftretens
    for i, a in enumerate(word):
        if a not in pos:
            pos[a] = [i]
            order.append(a)
        else:
            pos[a].append(i)
            if len(pos[a]) > 2:
                raise ValueError(f"Marke {a} erscheint mehr als zweimal.")

    if not all(len(p) == 2 for p in pos.values()):
        raise ValueError("Nicht jede Marke erscheint genau zweimal.")

    n = len(order)
    results: List[List[Tuple[int, int]]] = []

    # Für jede Bitmaske: 0 → (+1,-1), 1 → (-1,+1) für die beiden Vorkommen der Marke
    for mask in range(1 << n):
        signed: List[Tuple[int, int]] = [None] * m  # type: ignore
        for j, a in enumerate(order):
            i1, i2 = pos[a]
            if ((mask >> j) & 1) == 0:
                signed[i1] = (a, +1)
                signed[i2] = (a, -1)
            else:
                signed[i1] = (a, -1)
                signed[i2] = (a, +1)
        results.append(signed)
    return results
