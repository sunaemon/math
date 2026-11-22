---
macros-file: polish-space/tex/macros.tex
notation-watch:
  - IncludedIn
  - StrictlyIncludedIn
  - prefixOf
  - BorelReducesTo
  - disjointUnion
  - concat
  - ExternalDisjointUnion
  - SetDifference
  - BaireSpace
---

\begin{mathmeta}
  \define{IncludedIn,StrictlyIncludedIn,prefixOf,BorelReducesTo,disjointUnion,concat,ExternalDisjointUnion,SetDifference,BaireSpace}
\end{mathmeta}

Relations: $\{B\IncludedIn Y\}$, $A\StrictlyIncludedIn B$, $s\prefixOf t$, and $E\BorelReducesTo F$.

Binary operators: $A\disjointUnion B$, $s\concat t$, $\disjointUnion A$, and $A_{s\concat t}$.

Large operators: $\ExternalDisjointUnion_{n\in\NN}X_n$.

$$\ExternalDisjointUnion_{n\in\NN}X_n.$$

Compound constructions: $\SetDifference{A}{B}\IncludedIn\BaireSpace$.

\begin{align*}
A &\IncludedIn B\\
s\concat t &\prefixOf u.
\end{align*}

Emphasized: *$A\IncludedIn B$*.
