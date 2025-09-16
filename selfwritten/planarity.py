from __future__ import annotations
from typing import Dict, Any, List, Callable, Iterable, Set, Dict, Sequence, Tuple



def _positions(G: Sequence[Letter], a: int) -> Tuple[int, int]:
	"""Return the indices of (a,+1) and (a,-1) in G (0-based)."""
	pp = G.index((a, +1))
	pm = G.index((a, -1))
	return pp, pm


def bet(G: Sequence[Letter], a: int) -> Word:
	"""
	Betweenness-Set zwischen den beiden Auftritten des Buchstabens a.
	Exakte Übersetzung von 'bet' im GAP-Code.  (Appendix A)
	"""
	pp, pm = _positions(G, a)
	# Subwort zwischen den beiden Vorkommen von a (inklusive Endpunkte)
	if pp <	pm:
		result: Word = list(G[pp:pm+1])
	else:
		result = list(G[pm:pp+1])

	# Paare derselben Marke mit entgegengesetztem Vorzeichen, die beide in 'result' liegen,
	# werden herausgekürzt (wie im GAP-Code: Remove(result, p); Remove(result, Position(...))).
	i = 0
	while i < len(result):
		k, s = result[i]
		dbl = (k, -s)
		if dbl in result:
			# entferne aktuelles Element und sein Gegenstück
			del result[i]
			j = result.index(dbl)
			del result[j]
			# einen Schritt zurück (falls möglich), um erneut zu prüfen
			i = max(i - 1, 0)
			continue
		i += 1
	return result


def closure_f(G: Sequence[Letter], A: Iterable[Letter]) -> Word:
	"""
	f(G, A): Vereinigung von A mit allen bet(G, l[0]) für l in A.
	1:1 zu 'f' im GAP-Code.  → :contentReference[oaicite:2]{index=2}
	"""
	res: Set[Letter] = set(A)
	for l in A:
		res.update(bet(G, l[0]))
	# Reihenfolge ist egal; wir geben eine Liste zurück
	return list(res)


def check_connected(G: Sequence[Letter]) -> bool:
	"""
	Prüft, ob alle Marken in derselben Komponente liegen (Primheit der chord space).
	Entspricht 'check_connected' im GAP-Code.
	"""
	if not G:
		return True
	# Iteriere f, bis Fixpunkt erreicht ist (Start mit erstem Buchstaben)
	f_prev = closure_f(G, [G[0]])
	while True:
		f_new = closure_f(G, f_prev)
		if set(f_new) == set(f_prev):
			break
		f_prev = f_new
	# Sammle die Marken-Labels der erreichten Menge
	reached = {k for (k, _s) in f_new}
	labels = {k for (k, _s) in G}
	return reached == labels


def check_planar(G: Sequence[Letter]) -> bool:
	"""
	Cairns–Elton Planarity-Check für *signierte* Gau	rter.
	Exakte Übersetzung von 'check_planar' im GAP-Code (Appendix A).
	"""
	# Anzahl verschiedener Marken
	labels = sorted({k for (k, _s) in G})
	kmax = len(labels)
	if labels != list(range(1, kmax + 1)):
		# Optional: normiere Erwartung {1..k}
		label_map = {lab: i+1 for i, lab in enumerate(labels)}
		G = [(label_map[a], s) for (a, s) in G]
		labels = list(range(1, kmax + 1))

	# S_bar[i]: Subwort zwischen den beiden Vorkommen von i (zyklisch, inkl. Endpunkte)
	# S[i]: S_bar[i] ohne die beiden i-Endpunkte
	# S_inv[i]: S[i] mit invertierten Vorzeichen
	S_bar: List[Word] = [None] * (kmax + 1)  # 1-basiert
	S: List[Word] = [None] * (kmax + 1)
	S_inv: List[Word] = [None] * (kmax + 1)

	n2 = len(G)
	assert n2 % 2 == 0
	for i in range(1, kmax + 1):
		pp, pm = _positions(G, i)
		if pp < pm:
			S_bar[i] = list(G[pp:pm+1])
		else:
			S_bar[i] = list(G[:pm+1] + G[pp:])
		Si = [x for x in S_bar[i] if x != (i, +1) and x != (i, -1)]
		S[i] = Si
		S_inv[i] = [(a, -s) for (a, s) in Si]

	# Planar genau dann, wenn für alle i,j die Summe der Vorzeichen
	# über Intersection(S_bar[i], S_inv[j]) gleich 0 ist.
	for i in range(1, kmax + 1):
		sbar_i = S_bar[i]
		for j in range(1, kmax + 1):
			sinv_j = set(S_inv[j])  # set reicht, da GAP-Intersection auch Mengen schneidet
			inter = [x for x in sbar_i if x in sinv_j]
			if sum(s for (_a, s) in inter) != 0:
				return False
	return True

