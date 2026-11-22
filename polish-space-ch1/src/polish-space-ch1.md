---
title: "Definability and Realizability in Polish Spaces"
author: "\\texttt{\\@sunaemon0}"
bibliography: polish-space-ch1/tex/references.bib
csl: polish-space-ch1/tex/ams-numeric.csl
reference-section-title: References
macros-file: polish-space-ch1/tex/macros.tex
link-citations: true
documentclass: book
classoption:
  - 10pt
  - a5paper
  - twoside
  - openright
geometry:
  - paper=a5paper
  - inner=18mm
  - outer=16mm
  - top=18mm
  - bottom=20mm
toc: true
toc-depth: 3
numbersections: true
header-includes:
  - \usepackage{makeidx}
  - \makeindex
  - \input{polish-space-ch1/tex/macros.tex}
  - \raggedbottom
include-after:
  - \printindex
# Terms forwarded in the shared chapter sources whose \termdefine lives in a
# chapter the excerpt does not include (cylinder, Brouwer, Alexandrov--Urysohn:
# cantor-baire-space.md; Hilbert-cube embedding:
# polish-embeddings-borel-refinements.md of the full book).
term-forward-external:
  - cylinder
  - Brouwer's Cantor-space characterization
  - Alexandrov--Urysohn theorem
  - Hilbert-cube embedding
notation-watch:
  - Sequence
  - IndexedFamily
  - Fsigma
  - Gdelta
  - BaireSpace
  - CantorSpace
  - TwoPointSpace
  - Homeomorphic
  - HilbertCube
  - RealSequenceSpace
---

<!-- The full book defines these notations in its preface, which this excerpt omits. -->
\begin{mathmeta}
  \define{Sequence,IndexedFamily}
\end{mathmeta}
