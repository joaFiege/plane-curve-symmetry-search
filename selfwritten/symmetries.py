from typing import List, Tuple, Iterator
from datatypes import *
# Note, that there is no implementation of pure rotation (without realigning the base point).
# It is not necessary, since we already moded rotation out, when generating CDs


# --------------------------------------------------------------------
# Klassenrepräsentanten – kann für Wörter ODER PlanarCurves benutzt werden
# --------------------------------------------------------------------

def class_representatives(objs: List[Word], are_equivalent):
    reps: List[Word] = []
    for x in objs:
        if not any(are_equivalent(x, r) for r in reps):
            reps.append(x)          # x wird Repräsentant einer neuen Klasse
    return reps

# ---------------------------------------------------------------------


# Note, that rotate already moves the base point through chords, since signs get rotated as well
def rotate(w: Word, k: int):
    k = k % len(w)
    return w[k:] +  w[:k]

def rotate_ps(ps: List[OrientedArc], k: int, *, N: int):
    return [( (p1-k) % N, (p2-k) % N ) for p1, p2 in ps]

def relabel(w: Word):
    labels = {}
    relabeled = []

    new_label = 1
    for (label, sign) in w:
        if not label in labels:
            labels[label] = new_label
            new_label += 1

        relabeled.append((labels[label],sign))
    return relabeled     


def eq_mod_rot(w1: Word, ps1: List[OrientedArc], w2: Word, ps2: List[OrientedArc]):
    if len(w1) != len(w2):
        return False

    N = len(w1)
    w2_canon = relabel(w2)  # nur Labels, Arcs bleiben positionsbasiert

    for k in range(N):
        rw1 = rotate(w1, k)
        rps1 = rotate_ps(ps1, k, N=N)

        # wichtig: beide Wörter relabeln (kanonische Labelreduktion nach Erstauftreten)
        if relabel(rw1) == w2_canon and set(rps1) == set(ps2):
            return True
    return False

def eq_mod_rot_words(w1: Word, w2: Word) -> bool:
    """Equality of signed Gauss words up to rotation + relabeling."""
    if len(w1) != len(w2):
        return False
    N = len(w1)
    w2_canon = relabel(w2)
    for k in range(N):
        if relabel(rotate(w1, k)) == w2_canon:
            return True
    return False



def reverse_ps(ps: List[OrientedArc], *, N: int):
    return [( (-p2-1) % N, (-p1-1) % N) for p1, p2 in ps]


def reverse(w: Word):
    # This is not reversing S^1, since signs of chords are not changed
    return [(l,-s) for (l,s) in w[::-1]] # we change the sign of the node, that keeps the sign of the chord unchagned (c+=a+a- backwards is c-=a-a+)

def reverse_S_one(w: Word):
    return w[::-1]

def reverse_S_one_ps(ps: List[OrientedArc], *, N: int) -> List[OrientedArc]:
    """
    Reverse the underlying circle S^1 on the plane-structure.
    Index map: i ↦ N-1-i. For an oriented arc (p1,p2) this yields ((-p2-1) mod N, (-p1-1) mod N),
    which again has the canonical 'next' orientation.
    """
    return [((-p2 - 1) % N, (-p1 - 1) % N) for (p1, p2) in ps]


def are_equiv_SGD(w1: Word, w2: Word) -> bool:
    """Equality of signed Gauss diagrams (no plane-structure) mod rotation and S^1-reversal."""
    if len(w1) != len(w2):
        return False
    # rotation or rotation after reversing S^1
    return eq_mod_rot_words(w1, w2) or eq_mod_rot_words(reverse_S_one(w1), w2)



def are_equiv_PSGD(w1: Word, ps1: List[OrientedArc], w2: Word, ps2: List[OrientedArc]) -> bool:
    """
    Equality of plane-structured signed Gauss diagrams mod:
      - rotation on S^1, and
      - reversal of S^1 (i ↦ N-1-i), applied to both word and plane-structure.
    Uses your eq_mod_rot which already handles rotation + relabeling for words,
    and set-equality for oriented arcs.
    """
    if len(w1) != len(w2):
        return False
    N = len(w1)

    # Case 1: match via rotation
    if eq_mod_rot(w1, ps1, w2, ps2):
        return True

    # Case 2: match via rotation after reversing S^1
    rw1  = reverse_S_one(w1)
    rps1 = reverse_S_one_ps(ps1, N=N)
    return eq_mod_rot(rw1, rps1, w2, ps2)

def is_mirror_symmetric(w: Word, ps: List[OrientedArc]) -> bool:
    wR  = reverse(w)
    psR = reverse_ps(ps, N=len(w))# Arcs positionsgetreu spiegeln
    return eq_mod_rot(w, ps, wR, psR)

def move_bp(w: Word):
    # moves bp through n points
    n = len(w)//2

    w1 = w[:n]
    # w2 = w[n:]

    crossing_num = dict.fromkeys([label for label, _ in w], 0)

    for l, _ in w1:
        crossing_num[l] += 1

    w = [( l, s* ( (-1)**crossing_num[l] ) ) for l,s in w]
    flip = [(l,-s) for l,s in w]
    
    return w, flip

def eq_mod_orientation(arcs1, arcs2):
    # Orientierung ignorieren: {i,j} statt (i,j)
    A = set(map(frozenset, arcs1))
    B = set(map(frozenset, arcs2))
    return A == B


def is_point_symmetric(w: Word, ps: List[OrientedArc]) -> bool:
    N = len(w)
    if N % 2 != 0:
        return False
    n = N // 2

    # 180°-Rotation
    w180  = rotate(w, n)
    ps180 = rotate_ps(ps, n, N=N)

    # Vergleich bis auf Relabeling und globales Vorzeichenflip
    w0_canon    = relabel(w)
    w180_canon  = relabel(w180)
    w180_flip   = [(l, -s) for (l, s) in w180_canon]

    ps_ok = eq_mod_orientation(ps, ps180)
    return ps_ok and (w0_canon == w180_canon or w0_canon == w180_flip)



if __name__=='__main__':
    from utils import parse_word, compute_plane_structures
    from pipeline import load_computations_csv

    # print(relabel(rotate([(1, 1), (1, -1), (2, 1), (2, -1), (3, 1), (3, -1), (4, 1), (4, -1), (5, 1), (5, -1)], 3)))
    # # ---

    # w= parse_word("1+2-3+1-2+3-4-4+")
    # ps = compute_plane_structures(w)[2]
    # print(ps)

    # print(w)
    # k = 2
    # rot_w = rotate(w,k)
    # print(rot_w)
    # w = relabel(w)
    # print(w)

    # rot_ps = rotate_ps(ps,k,N=len(w))
    # print(rot_ps)
    # # ---


    w= parse_word("1+2-3+1-2+3-4-4+")
    ps = [(0, 7), (2, 1), (4, 3), (6, 5), (6, 7)]

    b = is_mirror_symmetric(w, ps)
    print(b)

    w = parse_word("1+ 2+ 3- 1- 4+ 3+ 2- 4-")
    print(w)
    
    ps = [(7,0),(3,4)]
    print(is_mirror_symmetric(w,ps), "should be true")

    for n in range(2, 6+1):
        all_comps : List[Computation] = load_computations_csv(f"./new_data/plane_curves_and_their_invariants_{n}.csv")

        # Teste, rotierte Computations als gleich erkannt werden
        for k in range(2*n):
            for comp in all_comps:
                w1 = comp.word
                ps1 = comp.regions[comp.idx_unbounded]

                w2 = rotate(w1, k)
                ps2 = rotate_ps(ps1, k, N=len(w1))

                if not (eq_mod_rot(w1,ps1,w2,ps2)):
                    print("Hier ist was schief gelaufen")
    print("Test successful")



    for n in range(2, 6+1):
        all_comps : List[Computation] = load_computations_csv(f"./new_data/plane_curves_and_their_invariants_{n}.csv")

        mirror_sym = 0
        point_sym = 0
        for comp in all_comps:
            if is_mirror_symmetric(comp.word, comp.regions[comp.idx_unbounded]):
                # print("found mirror symmetric one")
                mirror_sym += 1
            if is_point_symmetric(comp.word, comp.regions[comp.idx_unbounded]):
                point_sym += 1

        print(f"There are {mirror_sym} mirror symmetric immersions for n={n}")
        print(f"There are {point_sym} point symmetric immersions for n={n}")
