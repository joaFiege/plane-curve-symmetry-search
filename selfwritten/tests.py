from Arnold import * 
from utils import lintel_to_gauss
from datatypes import *
from typing import List, Dict

# tests = ["Seifert", "Whitney", "Polak"]
tests = ["test_example"]

if "load example"  in tests:
	from pipeline import load_computations_csv, _key_invariants, save_computations_csv
	from symmetries import * 

	all_comps : List[Computation] = load_computations_csv(f"./data/plane_curves_and_their_invariants_8.csv")

	lst = []
	for comp in all_comps:
		if comp.St==16 and comp.Jp==-32 and comp.Jm==-40: # and comp.whitney==11:
			lst.append(comp)
	save_computations_csv(lst, f"./data/myexample.csv", header=True, show_plus=False)

if "test_example" in tests:
	from pipeline import load_computations_csv, _key_invariants, save_computations_csv
	from symmetries import * 


	all_comps : List[Computation] = load_computations_csv(f"./data/myexample.csv")

	whitney_indeces = set()
	for comp in all_comps:
		whitney_indeces.add(comp.whitney)
	print(whitney_indeces)

	result = [comp for comp in all_comps if comp.whitney == 9]
	print(len(result))

	pt_syms = []
	mirror_syms = []
	for comp in result:
		if is_point_symmetric(comp):
			pt_syms.append(comp)
		if is_mirror_symmetric(comp):
			mirror_syms.append(comp)

	print([pt.word for pt in pt_syms])

	print("number of point-symmetric curves: ", len(pt_syms))
	print("number of mirror-symmetric curves: ", len(mirror_syms))

	def find_equivalent_computations(
	    computations: List[Computation],
	    target_word: List[Letter],
	) -> List[Computation]:
	    """
	    Sucht alle Computations, deren word (mit Signs) klassisch äquivalent
	    zum target_word ist (Rotation/Reflexion; KEIN globaler Signflip; KEIN Basepoint-Kram).
	    """
	    matches: List[Computation] = []
	    for comp in computations:
	        if are_equivalent(
	            comp.word,
	            target_word,
	            ignore_signs=False,
	            allow_reflection=True,
	            allow_mirror=False,           # klassisch: kein globaler T-Flip
	        ):
	            matches.append(comp)
	    return matches

	# --- Beispielaufruf ---
	target_word = [
	    (1, 1), (2, 1), (3, 1), (3, -1), (2, -1), (4, 1), (4, -1), (1, -1),
	    (5, 1), (6, 1), (7, 1), (7, -1), (6, -1), (8, 1), (8, -1), (5, -1)
	]

	# angenommen: all_comps: List[Computation]
	hits = find_equivalent_computations(all_comps, target_word)

	if hits:
	    print(f"Gefunden: {len(hits)} äquivalente(s) Diagramm(e).")
	    for c in hits:
	        print("word=", list(c.word), " idx_unbounded=", c.idx_unbounded)
	else:
	    print("Kein äquivalentes Diagramm gefunden.")


	hit = hits[0] # len(hits)==1
	print(hit.word)

	print(is_point_symmetric(hit))

if "symmetries" in tests:
	from pipeline import load_computations_csv, _key_invariants
	from symmetries import * 

	all_comps : List[Computation] = load_computations_csv(f"./data/plane_curves_and_their_invariants_3.csv")

	# Multimengen (Invarianten -> Liste von Computations)
	point_multiset: Dict[Tuple[int,int,int,int], List[Computation]] = defaultdict(list)
	mirror_multiset: Dict[Tuple[int,int,int,int], List[Computation]] = defaultdict(list)

	point_counter = 0
	mirror_counter = 0 
	for comp in all_comps:
		if is_point_symmetric(comp):
			point_multiset[_key_invariants(comp)].append(comp)
			point_counter += 1
		if is_mirror_symmetric(comp):
			mirror_multiset[_key_invariants(comp)].append(comp)
			mirror_counter += 1

	print(point_counter, " point-symmetric curves")
	print(mirror_counter, " mirror-symmetric curves")

	# Schnitt der Schlüssel
	both_keys = set(point_multiset.keys()) & set(mirror_multiset.keys())

	# Für jeden gemeinsamen Schlüssel prüfen, ob es ein Diagramm gibt, das BEIDES erfüllt.
	# Falls NICHT: gib die Invarianten und alle Diagramme (aus beiden Multimengen) aus.
	for key in sorted(both_keys):
		pts = point_multiset[key]
		mrs = mirror_multiset[key]

		exists_both = any(is_mirror_symmetric(c) for c in pts) or any(is_point_symmetric(c) for c in mrs)

		if not exists_both:
			w, St, Jp, Jm = key  # key ist (whitney, St, Jp, Jm)
			print("\n--- Kein Diagramm gleichzeitig punkt- und spiegelsymmetrisch ---")
			print(f"Invarianten: whitney={w}, St={St}, Jp={Jp}, Jm={Jm}")
			print("Punktsymmetrische Diagramme (als (word, idx_unbounded)):")
			for c in pts:
				print(format_word(list(c.word)), "; idx_unbounded=", c.idx_unbounded)
			print("Spiegelsymmetrische Diagramme (als (word, idx_unbounded)):")
			for c in mrs:
				print(format_word(list(c.word)), "; idx_unbounded=", c.idx_unbounded)

if "Debugging" in tests:
	word= [(1, -1), (2, 1), (3, -1), (1, 1), (2, -1), (3, 1)] # hierfür korrektes Ergebnis
	word= [(letter, -sign) for letter, sign in word] # hierfür leider falsches
	
	oriented_regions : List[OrientedArc] = compute_plane_structures(word)
	w= 1
	idx = 3

	print(oriented_regions)
	w = whitney_index(word, oriented_regions, outside_idx=idx)
	print("whitney: ", w)
	print(St_Jpm(word, w))

	# regions = regions_from_oriented_regions(oriented_regions, len(word)) # Regionen korrekt

	# seifert : SeifertDecomposition = SeifertDecomposition(word) # Zykel korrekt
	# decomp = OrientedSeifertDecomposition(seifert, oriented_regions, idx) # Provinzen korrekt

	# print("Seifert-Zykel: ", seifert.get_cycles())

	# for prov in decomp.provinces:
	# 	for cyc in decomp._cycles_touching(prov):
	# 		print(f"prov={prov}, cyc={cyc}, other_side={decomp._other_side(prov, cyc)}") # _other_side() korrekt


























if "Seifert" in tests:
    def verify_seifert_partition(word: Word, cycles: List[SeifertCycle]) -> None:
        """
        Prüft drei Eigenschaften (vgl. Lemma 9.6 + Text vor Def. 9.2):

        1. *Disjunktheit* – kein Bogen gehört zu zwei Zykeln.
        2. *Vollständigkeit* – Vereinigung aller Bögen = gesamter Kreis (alle 2n Kanten).
        3. *Endpunkt-Inzidenz* – an **jedem** Chord liegen genau zwei Seifert-Zykel an.

        Wirft `ValueError`, falls eine Bedingung verletzt ist.
        """
        N = len(word)
        # Erwartete Menge aller Circle-Bögen (ungerichtete Paare (i, i+1) mod N)
        full_circle: Set[Arc] = {(i, (i + 1) % N) for i in range(N)}

        # 1 & 2 – Bogen-Menge der Zykel sammeln
        seen_arcs: Set[Arc] = set()
        for cyc in cycles:
            for arc in cyc.arcs:
                # kanonische Ordnung (kleinerer Index zuerst)
                canon = (arc[0] % N, arc[1] % N)
                if canon in seen_arcs:
                    raise ValueError("Zykel überschneiden sich (Lemma 9.6 verletz – doppelte Bögen).")
                seen_arcs.add(canon)

        if seen_arcs != full_circle:
            missing = full_circle - seen_arcs
            extra   = seen_arcs   - full_circle
            raise ValueError(
                f"Seifert-Zykel ergeben keine vollständige Zerlegung:\n"
                f"  fehlende Bögen: {missing}\n  unerwartete Bögen: {extra}"
            )

        # 3 – Endpunkt-Inzidenz  (Chord-Version)

        # Map: Position → {cycle-IDs}
        pos2cyc = incidence_map(cycles)

        # Map: Label → [i, j]   (die beiden Endpunkte des Chords)
        label_pos = label_positions(word)

        chord_errors: Dict[Label, str] = {}

        for lbl, endpoints in label_pos.items():
            # Guard: jedes Label muss *genau* zweimal auftauchen
            if len(endpoints) != 2:
                chord_errors[lbl] = f"Endpunkte = {endpoints} (≠ 2)"
                continue

            i, j = endpoints
            set_i = pos2cyc.get(i, set())
            set_j = pos2cyc.get(j, set())

            # Bedingung 1: beide Mengen haben Größe 2
            # Bedingung 2: Mengen sind identisch
            if len(set_i) != 2 or len(set_j) != 2 or set_i != set_j:
                chord_errors[lbl] = f"{i}:{sorted(set_i)}  vs  {j}:{sorted(set_j)}"

        if chord_errors:
            err_lines = "\n".join(
                f"Label {lbl}: {info}" for lbl, info in sorted(chord_errors.items())
            )
            raise ValueError(
                "Lemma 9.6 verletzt – folgende Chords haben nicht exakt dieselben "
                "zwei Seifert-Zykel an beiden Endpunkten:\n" + err_lines
            )

        # Falls alle Tests bestanden: still durchlaufen

    # ---------- TEST: Berechnung der (unorientierten) Seifertzykel ---------
    demo = "1- 2+ 3- 1+ 2- 3+"  # Beispiel-Gauss-Wort
    w = parse_word(demo)

    seifert = SeifertDecomposition(w)
    cycles = seifert.get_cycles()

    # Test
    verify_seifert_partition(w, cycles)
    print("Seifert-Strukturen valide!")

    print(f"Gauss‑Wort: {demo}\nGefundene Seifert‑Zykel ({len(cycles)}):")
    for c in cycles:
        print("  ", c)

    print(seifert.get_N())

    """Es sollte folgendes Ergebnis herauskommen:
        Structure([(0, 1), (2, 3), (4, 5)])
        Structure([(1, 2), (3, 4), (5, 0)])
    """

    # --------- TEST: Orientierung der Zykel und Whiteny-Index --------------
    regions = compute_plane_structures(w)
    unbounded_region = regions[0] # for demo puroses
    # seifert.whitney_index(unbounded_regions)



if "Whitney" in tests:
    print("########################################################################\n")
    # # TEST: is:_orientation_reversing for Fig. 40
    # word = parse_word("1+ 1-")
    # A_regions = [[(0,1),(2,3)], [(0,1),(2,3)], [(1,2), (2,3)]]
    # B_regions = [[(1,2),(3,0)], [(0,1), (3,0)], [(0,1),(3,0)]]

    # A_bool_train = [True, True, False]
    # B_bool_train = [True, False, False]


    # for i in range(3):
    #     match_A = is_orientation_reversing(4, (1,3), A_regions[i])==A_bool_train[i]
    #     match_B = is_orientation_reversing(4, (1,3), B_regions[i])==B_bool_train[i]
    #     match = match_A and match_B
    #     print(f"passed {i+1}/3" if match else f"failed {i+1}/3 due to error (marked as False) in A ({match_A}) or B ({match_B})")

    # print("passed" if is_orientation_reversing(2, (0,1), [(0,1),(1,0)]) else "failed", "case N=2")


    word = parse_word("1- 2+ 3- 1+ 2- 3+")  # Beispiel-Gauss-Wort
    regions = compute_plane_structures(word)

    w = whitney_index(word, regions, 0)
    print("Finally, the calculation of the Whitney index (should be 2): ", w)


if "Polyak" in tests:
	print("########################################################################\n")
	
	from utils import compute_plane_structures

	# TEST B2, B3 & B4 ----------------------------------------
	# alle Diagramme mit 2 Chords (bis auf VZ)
	B2 = parse_word("1+ 1- 2+ 2-")
	B3 = parse_word("1+ 2+ 2- 1-")
	B4 = parse_word("1+ 2+ 1- 2-")

	words = [B2, B3, B4]
	for word in words:
		chords = chords_from_word(word)
		print(count_B2_B3_B4(word, chords))
	# ---------------------------------------------------------

	word = parse_word("1- 2+ 3- 1+ 2- 3+")  # Beispiel-Gauss-Wort
	# chords = chords_from_word(word)
	# for chord in chords:
	#     print(chord)
	#     sgn = get_chord_sign(word, chord)
	#     print(sgn)

	for c1,c2 in [((0, 3), (1, 4)), ((0, 3), (2, 5)), ((1, 4), (2, 5))]:
		print(f"c1 = {c1}, c2 = {c2}, sign_c1 = {get_chord_sign(word, c1)}, sign_c2 = {get_chord_sign(word, c2)}")

	w = whitney_index(word, compute_plane_structures(word), 0)
	print(word)
	print("whitney = ", w)
	print("calc st, j+, j- (should be (1,0,-3)): ", St_Jpm(word, w))


if "planarity" in tests:
	print("########################################################################\n")

	from planarity import check_planar


# Hier bereits generierte Gauss-Diagramme einlesen und auf Planarität testen
# Die Anzahl der realisierbaren Gauss-Diagramme für gegebenes n dann mit OEIS überprüfen

	from typing import Iterable, List, Sequence, Tuple, Dict
	from pipeline import all_signings

	# def test_diagrams():
	# 	unsigned_dias = []
	# 	for n in range(1,10):
	# 		unsigned_dia = []
	# 		for i in range(1,n):
	# 			unsigned_dia += [i,i]
	# 		unsigned_dias.append(unsigned_dia)

	# 	dias = []
	# 	for unsigned_dia in unsigned_dias:
	# 		dias += all_signings(unsigned_dia)
	# 	return dias

	# def get_khan_lisitsa(n=9):
	# 	if n==9:
	# 		lintel = [[0,5],[1,8],[2,9],[3,14],[4,15],[6,13],[7,12],[10,17],[11,16]]
	# 		return [lintel_to_gauss(lintel)]
	# 	if n==10:
	# 		lintels = [[[0,3],[1,10],[2,9],[4,15],[5,16],[6,19],[7,14],[8,13],[11,18],[12,17]],
	# 					[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,12],[10,17],[11,18],[14,19]],
	# 					[[0,3],[1,10],[2,9],[4,17],[5,16],[6,11],[7,14],[8,15],[12,19],[13,18]],
	# 					[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,14],[10,15],[11,18],[12,19]],
	# 					[[0,5],[1,10],[2,15],[3,16],[4,9],[6,13],[7,14],[8,19],[11,18],[12,17]],
	# 					[[0,5],[1,16],[2,15],[3,10],[4,9],[6,19],[7,14],[8,13],[11,18],[12,17]]]
	# 		return [lintel_to_gauss(lintel) for lintel in lintels]

	# # ----------------------------------------------------------------------------------------------

	# # Passed tests
	# planar_diagrams = [[(1, 1), (2, -1), (3, 1), (1, -1), (2, 1), (3, -1)]]

	# planar_diagrams.append([(1,-1), (2,-1), (3,1), (1,1), (4,-1), (3,-1), (2,1), (4,1)])
	# planar_diagrams.append([(1,-1), (2,-1), (3,1), (1,1), (4,-1), (3,-1), (5,-1), (5,1), (2,1), (4,1)])

	# for G in planar_diagrams:
	# 	# G = to_signed(w)
	# 	#print("connected?", check_connected(G))
	# 	print("planar?    ", check_planar(G))
	# 	#print("prime+planar?", is_prime_and_planar(G))


	# print("all test diagrams planar?", not any([not check_planar(dia) for dia in test_diagrams()]))
	# planar_diagrams += test_diagrams()


	# print("--------------------------------------")
	# # Passed test
	# # non_planar_words = [[1,2,1,2]]

	# # non-realizable Gauss diagram, that satisfies B and GL condition
	# # print(get_khan_lisitsa(n=9)[0])
	# # print(all_signings([1,1]))

	# # non_planar_dias = all_signings(get_khan_lisitsa(n=9)[0])

	# # print("all signings of khan-listsa non-realizable?", not any([check_planar(dia) for dia in non_planar_dias]))

	# for counterexample in get_khan_lisitsa(n=10):

	# 	composite_dias = []
	# 	diagrams = all_signings(counterexample)
	# 	for dia in diagrams:
	# 		dias = []
	# 		for i, G in enumerate(planar_diagrams):
	# 			dias.append(dia + [(x+19, s) for (x, s) in G])
	# 		composite_dias += dias

	# 	print("all signings of khan-listsa non-realizable?", not any([check_planar(dia) for dia in diagrams]))
	# 	print("all signings of composite_dias non-realizable?", not any([check_planar(dia) for dia in diagrams]))

	prime_gauss_7 = [
	[1,2,3,4,5,6,7,5,4,1,2,7,6,3],
	[1,2,3,4,5,6,4,7,2,1,6,5,7,3],
	[1,2,3,4,5,6,4,7,2,1,7,5,6,3],
	[1,2,3,4,5,6,7,5,2,1,4,7,6,3],
	[1,2,3,4,5,6,7,1,2,5,6,7,4,3],

	[1,2,3,4,5,6,7,1,2,7,4,5,6,3],
	[1,2,3,4,5,6,7,1,2,7,6,5,4,3],
	[1,2,3,4,5,6,7,1,2,5,4,3,6,7],
	[1,2,3,4,5,1,6,7,2,5,4,3,7,6],
	[1,2,3,4,5,6,7,1,2,3,4,5,6,7]
	]

	for word in prime_gauss_7:
		words = []
		for x in all_signings(word):
			if check_planar(x):
				words.append(x)
		print(len(words))