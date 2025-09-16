# plot_curve_pairs.py
import csv
from pathlib import Path
from typing import List, Tuple

import numpy as np
import matplotlib.pyplot as plt

# --------------------------
# Pfade & Optionen
# --------------------------
BASE = Path(__file__).resolve().parent
INPUT_DIR = BASE / "new_data"
SAVE_DIR  = BASE / "pair_plots"
SAVE_DIR.mkdir(parents=True, exist_ok=True)

SAVE_FIGS = True   # speichern aktiv
SHOW_FIGS = False  # keine GUI-Popups

# --------------------------
# Typen
# --------------------------
Letter = Tuple[int, int]         # (label, sign)
Word   = List[Letter]
OrientedArc = Tuple[int, int]

# --------------------------
# CSV-Parser
# --------------------------
def parse_word(s: str) -> Word:
    """
    "1+ 1- 2+ ..." -> [(1,+1),(1,-1),(2,+1),...]
    """
    s = s.strip()
    if not s:
        return []
    out: Word = []
    for tok in s.split():
        if tok.endswith('-'):
            out.append((int(tok[:-1]), -1))
        elif tok.endswith('+'):
            out.append((int(tok[:-1]), +1))
        else:  # falls mal ohne '+'
            out.append((int(tok), +1))
    return out

def parse_arcs(s: str) -> List[OrientedArc]:
    """
    "(0,1) (2,3) ..." -> [(0,1),(2,3),...]
    """
    s = s.strip()
    if not s:
        return []
    arcs: List[OrientedArc] = []
    for part in s.split():
        a, b = part.strip("()").split(",")
        arcs.append((int(a), int(b)))
    return arcs

# --------------------------
# Geometrie-Helfer
# --------------------------
def chord_list_from_word(word: Word) -> List[Tuple[int, int, int]]:
    """
    Erzeuge Chords als (i, j, sign), i<j Positionsindizes, sign in {+1,-1}.
    """
    pos = {}
    sign_by_label = {}
    for idx, (lbl, sgn) in enumerate(word):
        if lbl not in pos:
            pos[lbl] = [idx]
            sign_by_label[lbl] = sgn
        else:
            pos[lbl].append(idx)
            # Falls inkonsistente Vorzeichen auftreten, nimm -1 bevorzugt
            if sign_by_label[lbl] != sgn:
                sign_by_label[lbl] = -1 if -1 in (sign_by_label[lbl], sgn) else +1

    chords = []
    for _, inds in pos.items():
        i, j = sorted(inds)
        chords.append((i, j, sign_by_label[_]))
    return chords

def circle_points(N: int):
    ang = np.linspace(0, 2*np.pi, N, endpoint=False)
    xy = np.c_[np.cos(ang), np.sin(ang)]
    return ang, xy

def draw_circle(ax, r=1.0, lw=1.0, color="0.85"):
    t = np.linspace(0, 2*np.pi, 512)
    ax.plot(np.cos(t)*r, np.sin(t)*r, linewidth=lw, color=color)

def draw_plane_structure(ax, N: int, ps: List[OrientedArc], radius=1.0, lw=3.0, color="tab:orange"):
    """
    Hebt die plane-structure-Arcs auf dem Kreis hervor (als Kreisbögen p->q).
    """
    angles = np.linspace(0, 2*np.pi, N, endpoint=False)
    for (p, q) in ps:
        a0 = angles[p]
        a1 = angles[q]
        if a1 <= a0:
            a1 += 2*np.pi
        tt = np.linspace(a0, a1, 32)
        ax.plot(np.cos(tt)*radius, np.sin(tt)*radius, linewidth=lw, color=color, solid_capstyle="round")

def draw_gauss_diagram(word: Word, ps: List[OrientedArc], ax, title: str = ""):
    """
    Zeichnet:
    - Grundkreis,
    - plane-structure-Arcs farbig,
    - Punkte,
    - Chords (negativ: fett).
    """
    N = len(word)
    _, pts = circle_points(N)

    draw_circle(ax, r=1.0, lw=1.0, color="0.85")
    draw_plane_structure(ax, N, ps, radius=1.0, lw=3.0, color="tab:orange")

    ax.plot(pts[:,0], pts[:,1], "o", markersize=2, color="black")

    for i, j, sgn in chord_list_from_word(word):
        (x1, y1) = pts[i]
        (x2, y2) = pts[j]
        lw = 3.0 if sgn < 0 else 1.5
        ax.plot([x1, x2], [y1, y2], linewidth=lw, color="k")

    if title:
        ax.set_title(title, fontsize=10)
    ax.set_aspect("equal")
    ax.axis("off")

# --------------------------
# Verarbeitung einer CSV-Datei
# --------------------------
def process_curve_pairs_csv(csv_path: Path) -> int:
    rows = []
    with csv_path.open(newline="", encoding="utf-8") as f:
        r = csv.DictReader(f, delimiter=";")
        for row in r:
            rows.append(row)

    if not rows:
        return 0

    file_stem = csv_path.stem  # z.B. "curve_pairs_7"
    count = 0

    for idx, row in enumerate(rows, start=1):
        n_val = int(row["n"])
        N_val = int(row["N"])
        inv   = (int(row["whitney"]), int(row["St"]), int(row["Jp"]), int(row["Jm"]))

        # I (punkt-symmetrisch)
        I_word = parse_word(row["I_word"])
        I_ps   = parse_arcs(row["I_plane_structure"])
        I_idxU = int(row["I_idx_unbounded"])

        # J (spiegel-symmetrisch)
        J_word = parse_word(row["J_word"])
        J_ps   = parse_arcs(row["J_plane_structure"])
        J_idxU = int(row["J_idx_unbounded"])

        fig, axes = plt.subplots(1, 2, figsize=(8, 4))
        fig.suptitle(f"{file_stem} | n={n_val}, N={N_val}, inv=(ω={inv[0]}, St={inv[1]}, J⁺={inv[2]}, J⁻={inv[3]})",
                     fontsize=11)

        draw_gauss_diagram(I_word, I_ps, axes[0], title=f"I (point), idxU={I_idxU}")
        draw_gauss_diagram(J_word, J_ps, axes[1], title=f"J (mirror), idxU={J_idxU}")

        fig.tight_layout(rect=[0, 0.02, 1, 0.92])

        if SAVE_FIGS:
            out_file = SAVE_DIR / f"{file_stem}_row{idx}.png"
            fig.savefig(out_file, dpi=200)
            print("saved:", out_file)

        count += 1

        if SHOW_FIGS:
            plt.show()
        else:
            plt.close(fig)

    return count

# --------------------------
# main
# --------------------------
def main():
    csvs = sorted(INPUT_DIR.glob("curve_pairs_*.csv"))
    if not csvs:
        print(f"Keine Dateien gefunden unter: {INPUT_DIR}/curve_pairs_*.csv")
        return

    total = 0
    for csv_path in csvs:
        c = process_curve_pairs_csv(csv_path)
        print(f"{csv_path.name}: geplottete Paare = {c}")
        total += c

    print(f"Fertig. Gesamt geplottete Paare: {total}. Bilder liegen in: {SAVE_DIR}")

if __name__ == "__main__":
    main()
