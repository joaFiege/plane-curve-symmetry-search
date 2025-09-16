import math
import matplotlib.pyplot as plt
import numpy as np

def draw_lintel(lintel, ax=None):
    """
    Zeichnet ein Lintel als Gauss-Diagramm auf einem Kreis.
    'lintel' ist eine Liste von Paaren (z. B. [[0,3],[1,4],...]), die Punkte auf dem Kreis verbinden.
    """
    n = 2 * len(lintel)
    pts = [(math.cos(2 * math.pi * i / n),
            math.sin(2 * math.pi * i / n))
           for i in range(n)]

    # Plot-Vorbereitung
    if ax is None:
        fig, ax = plt.subplots(figsize=(4, 4))

    # Kreis
    t = np.linspace(0, 2 * math.pi, 400)
    ax.plot(np.cos(t), np.sin(t), linewidth=2)

    # Chords zeichnen
    for a, b in lintel:
        x1, y1 = pts[a]
        x2, y2 = pts[b]
        ax.plot([x1, x2], [y1, y2], linewidth=2)

    # Kreis als Punktemarkierung (optional)
    for (x, y) in pts:
        ax.plot(x, y, "o", markersize=2, color="black")

    ax.set_aspect("equal")
    ax.axis("off")
    return ax