from pyswip import Prolog


class GaussLintel:
    def __init__(self, prolog_file="gauss-lint.pl"):
        self.prolog = Prolog()
        self.prolog.consult(prolog_file)

    def generate_lintels(self, N, filter="all"):
        X = list(range(1, N // 2 + 1))
        cmd = f"lintel_generate_{filter}({N}, {X})" if filter != "all" else f"lintel_generate({N}, {X})"
        for _ in self.prolog.query(cmd):
            pass  # Trigger vollständige Backtracking-Ausführung
            
    def get_lintels(self, N):
        """
        Holt alle gespeicherten Lintels der Größe N
        """
        return [r["L"] for r in self.prolog.query(f"lintel({N}, L)")]

    # Funktioniert nur für Prim-Lintels
    def is_realizable(self, N, lintel):
        """
        Prüft, ob ein gegebenes Lintel realisierbar ist.
        """
        return bool(list(self.prolog.query(f"realizable({N}, {lintel})")))

    def get_connected_lintels(self, N):
        """
        Gibt alle Lintels zurück, die connected sind.
        """
        return [l for l in self.get_lintels(N) if self.is_connected(N, l)]

    def is_connected(self, N, lintel):
        """
        Prüft, ob ein Lintel verbunden ist.
        """
        return bool(list(self.prolog.query(f"connected({N//2}, {lintel})")))

    def canonical_form(self, N, lintel):
        """
        Gibt die kanonische Form eines Lintels (Rotation + Reflektion)
        """
        q = list(self.prolog.query(f"lintel_canonical({N}, {lintel}, C)"))
        return q[0]["C"] if q else None
