from __future__ import annotations
from dataclasses import dataclass

from typing import List, Tuple



Label = int
Sign  = int      # +1 / -1
Signing = List[Sign]
Letter = Tuple[Label, Sign]
Word  = List[Letter]
Arc   = Tuple[int, int] # Speichern im Uhrzeigersinn (k,k+1) jeweils mod N
OrientedArc = Tuple[int,int]
Chord = Tuple[int,int] # Speichern als (min,max)

@dataclass(frozen=True)
class Structure:
    arcs: Tuple[Arc]

    def __post_init__(self):
        # akzeptiert list, set, tuple – wandelt immer in Tuple um
        object.__setattr__(self, "arcs", tuple(self.arcs))

    # macht das Objekt iterierbar
    def __iter__(self) -> Iterator[Arc]:
        return iter(self.arcs)

    def __len__(self) -> int:
        return len(self.arcs)

    def __contains__(self, item: Arc) -> bool:
        return item in self.arcs

    def __repr__(self) -> str:
        return f"Structure({[arc for arc in self.arcs]})"

Region = Structure
SeifertCycle = Structure
Region = Structure
Province = Structure

PlaneCurve = Tuple[Word, Structure]

@dataclass(frozen=True, slots=True)
class Computation:
    # Für echte Immutability hier Tuples verwenden:
    word: Tuple[Letter, ...]
    regions: Tuple[Region, ...]
    idx_unbounded: int
    whitney: int
    St: int
    Jp: int
    Jm: int

    def __post_init__(self):
        # Eingaben tolerant behandeln: auch wenn List übergeben wurde, in Tuple casten.
        object.__setattr__(self, "word", tuple(self.word))
        object.__setattr__(self, "regions", tuple(self.regions))

        # minimale Validierung
        if not (0 <= self.idx_unbounded < len(self.regions)):
            raise ValueError(
                f"idx_unbounded={self.idx_unbounded} liegt außerhalb von [0, {len(self.regions)-1}]"
            )

class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.rank   = [0]*n

    def find(self, x: int) -> int:
        while x != self.parent[x]:
            self.parent[x] = self.parent[self.parent[x]]   # Path compression
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> None:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        if self.rank[ra] < self.rank[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        if self.rank[ra] == self.rank[rb]:
            self.rank[ra] += 1