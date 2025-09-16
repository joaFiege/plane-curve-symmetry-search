# Imports ----------------------------------------------------------------------------
from __future__ import annotations

from collections import deque, defaultdict
from typing import Dict, Iterator, List, Set, Tuple, Sequence
from dataclasses import dataclass
from itertools import combinations

# Zentrale Typen & Helferroutinen
from datatypes import *
from utils import parse_word, label_positions, walking_algo, chords_touching_arc, incidence_map, chords_from_word, get_arc2cid, get_chord_sign, regions_from_oriented_regions

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

# Seifert ----------------------------------------------------------------------------

class SeifertDecomposition:

    # ---------- public -------------------------------------------------
    def __init__(self, word: Word) -> None:
        self.word                        = word
        self.cycles: List[SeifertCycle]  = self._build_cycles()

        self.connectedness_graph         = self._build_connectedness_graph()
        self.connectedness_matrix        = self._to_matrix(self.connectedness_graph)

    def get_word(self):
        return self.word

    def get_cycles(self) -> Sequence[SeifertCycle]:
        """Read-only view auf alle Seifert-Zykel."""
        return tuple(self.cycles)

    def are_connected(self, i: int, j: int) -> bool:
        """True ⟺ Zykel i & j teilen ≥ 1 Doppelpunkt."""
        return self.connectedness_matrix[i][j]

    def get_N(self):
        return len(self.word)

    def get_connected_neighbours(self, cid):
        return self.connectedness_graph[cid]

    # ---------- private -----------------------------------------------

    # Build-Methoden  ..........................................
    def _build_cycles(self) -> List[SeifertCycle]:
        """Berechnet alle Seifert-Zykel eines signierten Gauss-Worts."""
        uniq: Dict[Tuple[Arc, ...], SeifertCycle] = {}
        for sc in walking_algo(self.word, flip_sign=False):
            uniq[tuple(sc.arcs)] = sc # Duplikate eliminieren
        return eliminate_duplicates(list(uniq.values()))

    def _build_connectedness_graph(self) -> Dict[int, Set[int]]:
        """Einmal über alle Chords laufen → Adjazenz-Liste."""

        graph = {i: set() for i in range(len(self.cycles))}

        pos2cyc = incidence_map(self.cycles)          # Wort-Index → {cycle-IDs}
        for p, q in label_positions(self.word).values():
            cs_p = pos2cyc[p]
            cs_q = pos2cyc[q]

            # Lemma 9.6: Genau zwei Seifert-Zykel pro Chord-Endpunkt
            if len(cs_p) != 2 or len(cs_q) != 2:
                raise RuntimeError(
                    f"Chord endpoints {p},{q} touch {len(cs_p)}/{len(cs_q)} cycles "
                    "— violates Lemma 9.6 (expected 2).")

            # Kante nur, wenn BEIDE Enden dieselben zwei Zykel sehen
            if cs_p == cs_q:
                u, v = tuple(cs_p)       # garantiert u ≠ v
                graph[u].add(v)
                graph[v].add(u)

        return graph

    @staticmethod
    def _to_matrix(graph: Dict[int, Set[int]]) -> List[List[bool]]:
        n   = len(graph)
        mat = [[False]*n for _ in range(n)]
        for u, nbrs in graph.items():
            for v in nbrs:
                mat[u][v] = mat[v][u] = True
        return mat

# Whitney ----------------------------------------------------------------------------

class OrientedSeifertDecomposition:
    def __init__(self, unoriented_seifert_decomposition: SeifertDecomposition, oriented_regions: List[List[OrientedArc]],  unbounded_idx: int):
        self.decomp = unoriented_seifert_decomposition
        self.cycles = self.decomp.get_cycles()
        self.word = self.decomp.get_word()
        self.N = self.decomp.get_N()
        self.chords = chords_from_word(self.word)

        # print(regions)

        self.oriented_regions   = oriented_regions
        self.regions            = regions_from_oriented_regions(oriented_regions, self.N)
        # print("Regions:", self.regions)

        '''side-effects:
            creates: self.prov_of - prov_of[region_id] = province_id containing that region (unique)
            and: self.uf - disjoint set of regions by equivalence relation of joinedness
        '''
        self.provinces : List[Province] = self._build_provinces()
        # print("Provinces: ", self.provinces)

        self.unbounded_province : Province = self.provinces[self.prov_of[unbounded_idx]]
        # print("unbounded region: ", self.regions[unbounded_idx])
        # print("unbounded province: ", self.unbounded_province)



        # self.province_graph : Dict[int, Set[int]] = self._build_province_graph() # Adjazenzliste der Provinz-Ids

        self.arc2cid = get_arc2cid(self.cycles)

        # Orient cycles
        self.orientations : Dict[SeifertCycle, Sign]= self._render_orientations()


    def _test_provinces(self, provinces) -> bool:
        for rid, reg in enumerate(self.regions):
            dpts = set()
            for arc in reg.arcs:
                dpts.update(chords_touching_arc(self.word, arc))

            for dpt in dpts:
                print(f"is_orientation_reversing(SP={dpt}, region_id={rid})=", self._is_orientation_reversing(dpt, reg))
        print(provinces)
        return True

    def get_orientations(self):
        return self.orientations


    def _is_orientation_reversing(self, sp: Chord, edges: List[OrientedArc]) -> bool:
        a, b = sp
        arcs_touching_sp = [((a-1) % self.N, a), (a, (a+1) % self.N), ((b-1) % self.N, b), (b, (b+1) % self.N)]
        
        # print("arcs_touching_sp=", arcs_touching_sp)
        # print("intersection point =", sp, "\nedges/region = ", edges)

        arrows_bordering_reg = []
        for arc in arcs_touching_sp:
            s,t = arc
            if ((s,t) in edges) or ((t,s) in edges):
                arrows_bordering_reg.append(arc)

        if len(arrows_bordering_reg)==4:
            # print("case len==4")
            # Region grenzt von zwei Seiten an Schnittpunkt an
            arcs_left = [((a-1) % self.N, a), ((b-1) % self.N, b)]
            arcs_right = [(a, (a+1) % self.N), (b, (b+1) % self.N)]

            ret = True
            for arcs in [arcs_left, arcs_right]:
                s1, e1 = arcs[0]
                s2, e2 = arcs[1]
                dir1 = 1 if (e1 - s1) % self.N == 1 else -1
                dir2 = 1 if (e2 - s2) % self.N == 1 else -1
                # print(f"dir1={dir1}, dir2={dir2}")
                ret = ret and ((dir1*dir2)== -1)
            # print("is_orientation_reversing=", ret)
            # print()
            return ret
        else:
            # print("case len==2")
            partial_boundary = []
            for arc in arcs_touching_sp:
                start, end = arc

                if ((start, end) in edges):
                    partial_boundary.append((start, end))
                elif ((end, start) in edges):
                    partial_boundary.append((end, start))

            if len(partial_boundary)!=2:
                print(f"arcs_touching_sp={arcs_touching_sp}\nedges={edges}\nchord={sp}\npartial_boundary={partial_boundary}")
                raise RuntimeError("plane structure invalid -- region must neighbour at least 2 arrows for every intersection")
            else:
                # print("partial_boundary=", partial_boundary)
                s1, e1 = partial_boundary[0]
                s2, e2 = partial_boundary[1]
                dir1 = 1 if (e1 - s1) % self.N == 1 else -1
                dir2 = 1 if (e2 - s2) % self.N == 1 else -1
                # print(f"dir1={dir1}, dir2={dir2}")
                # print("is_orientation_reversing=", dir1*dir2==-1)
                # print()
                return ((dir1*dir2) == -1 )

    def _build_provinces(self) -> List[Province]:
        R = len(self.regions)
        self.uf = DSU(R)

        # 1) Regionen paarweise mergen
        for i in range(R):
            for j in range(i + 1, R):
                shared = self._get_shared_double_points(self.regions[i], self.regions[j])
                if not shared:
                    continue
                if all(self._is_orientation_reversing(dp, self.oriented_regions[i]) and
                       self._is_orientation_reversing(dp, self.oriented_regions[j])
                       for dp in shared):
                    self.uf.union(i, j)

        # 2) Repräsentanten → Listen von Region-IDs (deterministische Reihenfolge)
        reps: Dict[int, List[int]] = defaultdict(list)
        for rid in range(R):
            reps[self.uf.find(rid)].append(rid)

        province_regions: List[List[int]] = [
            sorted(members) for _rep, members in sorted(reps.items())
        ]

        # 3) Vorläufiges rid→pid (vor Dedup, "alte" pids)
        prov_of = [None] * R
        for pid, members in enumerate(province_regions):
            for rid in members:
                prov_of[rid] = pid

        # 4) Provinz-Objekte bauen (kanonische, lexikographisch sortierte Kanten)
        tmp_provinces: List[Province] = []
        for members in province_regions:
            arcs: Set[Arc] = set()
            for rid in members:
                arcs.update(self.regions[rid].arcs)
            arcs_sorted = tuple(sorted(arcs))  # lexikographisch (s,t)
            tmp_provinces.append(Structure(arcs_sorted))

        # 5) STABILE Dedup: erstes Vorkommen gewinnt; remap alte pid → kanonische pid
        unique_provinces: List[Province] = []
        canon_pid_of: Dict[int, int] = {}
        seen: Dict[Province, int] = {}

        for old_pid, P in enumerate(tmp_provinces):
            if P in seen:
                canon = seen[P]
            else:
                canon = len(unique_provinces)
                seen[P] = canon
                unique_provinces.append(P)
            canon_pid_of[old_pid] = canon

        # 6) rid→pid mittels Kanonisierung neu schreiben
        for rid in range(R):
            prov_of[rid] = canon_pid_of[prov_of[rid]]

        # 7) Zustände setzen
        self.prov_of = prov_of
        return unique_provinces


    def _build_province_graph(self) -> Dict[int, Set[int]]:
        """
        Liefert:  Dict[pid -> {pid_nachbar, …}]
        Kante (pid₁,pid₂)  ⇔  Provinzen pid₁ und pid₂ teilen ≥1 Rand-Bogen.
        """
        P = len(self.provinces)

        # ------------------------------------------------------------
        # 1)  arc  ->  Liste[pid]      invertierter Index
        # ------------------------------------------------------------
        arc2pids: Dict[Arc, List[int]] = defaultdict(list)

        for pid, prov in enumerate(self.provinces):
            for arc in prov.arcs:
                arc2pids[arc].append(pid)

        # ------------------------------------------------------------
        # 2)  Provinz-Graph aufbauen
        # ------------------------------------------------------------
        graph: Dict[int, Set[int]] = {pid: set() for pid in range(P)}

        for pids in arc2pids.values():                   # jede Arc-Bucket-Liste
            k = len(pids)
            if k < 2:                                    # Arc liegt nur an einer Provinz
                continue
            # vollständige Clique über alle Provinzen, die diesen Arc teilen
            for i in range(k):
                a = pids[i]
                for j in range(i + 1, k):
                    b = pids[j]
                    graph[a].add(b)
                    graph[b].add(a)
        # print(graph)
        return graph


    #  Orientierungen per BFS
    def _render_orientations(self) -> Dict[SeifertCycle, Sign]:
        """
        Breitensuche: Propagiert Orientierung vom Startzyklus
        entlang des Verbindungs-Graphen.
        """
        orient = {0: +1}                       # beliebiger Start: Zyklus 0
        q      = deque([0])

        while q: # bricht ab, wenn die queue leer ist
            cid = q.popleft()
            for nbr in self.decomp.get_connected_neighbours(cid):
                # orientierte Zykel werden nicht erneut betrachtet und landen auch nicht in der queue (essentiell für Schleifenabbruch)
                if nbr in orient:  
                    continue
                sign = self._orient(cid, nbr)            # +1 / −1
                orient[nbr] = orient[cid] * sign
                q.append(nbr)

        if len(orient) != len(self.decomp.get_cycles()):
            raise RuntimeError("Seifert-Graph ist nicht zusammenhängend")

        return orient

    #  Lokale Innen/Außen-Regel
    def _orient(self, src: int, dst: int) -> Sign:
        """
        +1  → Orientierung gleich   (Innen/Außen-Paar)
        −1  → Orientierung gegensätzlich (Außen/Außen-Paar)
        """
        # Wird nur im Debug-Mode ausgeführt
        assert self.decomp.are_connected(src, dst), \
               f"Internal error: {src}–{dst} not connected"

        c_src, c_dst = self.decomp.get_cycles()[src], self.decomp.get_cycles()[dst]
        if self.contains(c_src, c_dst) or self.contains(c_dst, c_src):
            return +1
        return -1

    def contains(self, c_outer: SeifertCycle, c_inner: SeifertCycle) -> bool:
        """True, falls c_inner im Inneren von c_outer liegt."""
        interior, exterior = self.get_interior_exterior(c_outer)
        return self.dist(c_inner, interior) < self.dist(c_inner, exterior)

    def get_interior_exterior(self, c: SeifertCycle) -> tuple[Province, Province]:
        pA, pB = self._provinces_touching(c)
        dA = self._prov_distance(pA, self.unbounded_province)
        dB = self._prov_distance(pB, self.unbounded_province)
        return (pA, pB) if dA > dB else (pB, pA)

    def _prov_distance(self, src: Province, dst: Province) -> int:
        # print(f"p_dist(src={src}, dst={dst})")

        """Kürzeste Zahl an Seifert-Zykeln zwischen Provinzen (vgl. Prop. 9.7)."""
        if src == dst:
            return 0

        q = deque([src])
        dist = {src: 0}           # Provinz-Objekte als Schlüssel – Identity ist ok

        while q:
            prov = q.popleft()
            d = dist[prov]

            # Nachbarn = „andere Seite“ jedes Seifert-Zyklus, der prov berührt
            for cyc in self._cycles_touching(prov):
                neigh = self._other_side(prov, cyc)   # liefert die eindeutige Gegenprovinz
                if neigh in dist:
                    continue
                if neigh == dst:
                    return d + 1
                dist[neigh] = d + 1
                q.append(neigh)

        # print("p_dist=",dist)
        raise RuntimeError("Province graph disconnected")



    # Zur Verbesserung der Effizienz könnte man alle Distanzen dist(c,p) in einer map self.dist_map abspeichern, um mehrfaches Rechnen zu vermeiden
    def dist(self, c: SeifertCycle, p: Province) -> int:
        # print(f"dist(cycle={c}, province={p})")

        # Startprovinzen am Zyklus c
        pA, pB = self._provinces_touching(c)
        # print("pA=", pA, " pB=", pB)
        if p == pA or p == pB:
            return 0

        q = deque([(pA,0), (pB,0)])
        seen = {pA, pB}

        while q:
            prov, d = q.popleft()
            for cyc in self._cycles_touching(prov):
                neigh = self._other_side(prov, cyc)
                if neigh in seen:
                    continue
                if neigh is p:
                    return d+1
                seen.add(neigh)
                q.append((neigh, d+1))

        raise RuntimeError("Province graph disconnected")

    def _provinces_touching(self, c: SeifertCycle) -> Tuple[Province, Province]:
        """
        Liefert die beiden (einzig möglichen) Provinzen, deren Rand
        irgendeinen Bogen des Seifert-Zyklus c enthält.
        """
        cycle_arcs = set(c.arcs)                   # Menge der Bögen des Zyklus
        touching: List[Province] = []

        for pid, prov in enumerate(self.provinces):
            if set(cycle_arcs) & set(prov.arcs):  # Schnitt ≠ ∅ ?
                touching.append(prov)
                if len(touching) == 2:             # mehr braucht es nicht
                    break

        num = len(touching)
        if num != 2:
            raise RuntimeError(
                f"Seifert cycle {c} touches {num} provinces, "
                "but it should touch exactly 2."
            )

        return touching[0], touching[1]


    def _cycles_touching(self, prov: Province) -> List[SeifertCycle]:
        """Alle Seifert-Zykeln, die die Provinz berühren (k ≥ 2)."""
        cids = { self.arc2cid[arc] for arc in prov.arcs }
        return [self.cycles[cid] for cid in cids]

    def _other_side(self, prov: Province, cyc: SeifertCycle) -> Province:
        a, b = self._provinces_touching(cyc)
        return b if prov is a else a

    def _get_shared_double_points(self, r1: Region, r2: Region) -> List[Chord]:
        """Alle Chords, an denen beide Regionen anliegen."""

        r1_double_pts = set()
        r2_double_pts = set()

        for arc in r1.arcs:
            r1_double_pts.update(chords_touching_arc(self.word, arc))

        for arc in r2.arcs:
            r2_double_pts.update(chords_touching_arc(self.word, arc))

        return list(r1_double_pts & r2_double_pts)

# Berechnung des Whitney-Index
def whitney_index(word: Word, oriented_regions: List[List[OrientedArc]], outside_idx: int) -> int:
    seifert : SeifertDecomposition = SeifertDecomposition(word)
    oriented = OrientedSeifertDecomposition(seifert, oriented_regions, outside_idx)

    return abs(sum(oriented.get_orientations().values()))  


# Polyak ----------------------------------------------------------------------------

# ---------- elementare Tests ----------
def crosses(c1: Chord, c2: Chord) -> bool:
    x, y = c1
    u, v = c2
    return (x < u < y < v) or (u < x < v < y)

def _between(c1: Chord, c2: Chord) -> bool:
    a1, b1 = c1
    a2, b2 = c2
    if a1 < a2:
        return b1 > b2
    return b2 > b1

def sub_sign(word, c1: Chord, c2: Chord) -> Sign:
    return get_chord_sign(word, c1) * get_chord_sign(word, c2)

# ---------- Zählungen ----------
def count_B2_B3_B4(word, chords) -> Tuple[int, int, int]:
    """liefert (B2, B3, B4) gemäß Polyak; Basispunkt = 0."""
    B2 = B3 = B4 = 0
    combis = list(combinations(chords, 2))

    for c1, c2 in combis:
        if crosses(c1, c2):
            B4 += sub_sign(word, c1, c2)
        elif _between(c1,c2):
            B3 += sub_sign(word, c1,c2)
        else:
            B2 += sub_sign(word, c1, c2)
    return B2, B3, B4

# ---------- Arnold-Invarianten ----------
def St_Jpm(word: Word, ind: int = 0) -> Tuple[int, int, int]:
    chords = chords_from_word(word)

    B2, B3, B4 = count_B2_B3_B4(word, chords)
    n = len(chords)
    J_plus  = round((B2 - B3 - 3*B4) - (n-1)/2 - (ind**2)/2)
    J_minus = round((B2 - B3 - 3*B4) - (3*n-1)/2 - (ind**2)/2)
    St      = round((-B2 + B3 + B4)/2 + (n-1)/4 + (ind**2)/4)

    return St, J_plus, J_minus


