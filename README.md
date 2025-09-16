# Plane-Curve Invariants

Code accompanying the bachelor thesis  
**“Symmetries and Invariants of Plane Curves: An Algorithmic Search for Obstructions”**  
RWTH Aachen University, 2025 — Joa Fiege

This repository implements a complete pipeline to **enumerate plane-structured signed Gauss diagrams (PSGDs)**,  
compute **Arnold invariants** \(J^+, J^-, St\) and the **Whitney index**, and filter for **mirror** and **point** symmetries.  
The algorithms are used to detect *critical pairs* of plane curve types that share the same invariants but admit incomparable symmetry groups.

## Features
- Generation of all PSGDs up to a chosen crossing number
- Computation of Arnold invariants via **Polyak’s formulas**
- Automatic detection of mirror and point symmetries
- Search for *critical pairs* with identical invariants but incompatible symmetry classes

## Credits
Parts of this code build on earlier work:
- **planarity.py** adapts routines from  
  *Michael Chmutov, Thomas Hulse, Andrew Lum, and Peter Rowell.*  
  *Plane and spherical curves: an investigation of their invariants.*  
  Proceedings of the REU Program in Mathematics, Oregon State University (2006), pp. 1–92.
- The folder **Gauss-Lintel** contains code from  
  *Abdullah Khan, Alexei Lisitsa, and Alexei Vernitski.*  
  *Gauss-lint algorithms suite for Gauss diagrams generation and analysis.*  
  2021. [doi:10.5281/zenodo.4574590](https://doi.org/10.5281/zenodo.4574590).

Large parts of the **theoretical construction of the algorithms** draw on ideas and
results developed by many authors in the literature.  
For a full account and complete bibliography, please refer to my bachelor thesis  
*Symmetries and Invariants of Plane Curves: An Algorithmic Search for Obstructions*.

## Citation
If you use this code, please cite the Zenodo release of this repository [![DOI](https://zenodo.org/badge/1057697473.svg)](https://doi.org/10.5281/zenodo.17129349) and the references above.
