# Polish Spaces {#sec:polish-spaces}

<!-- chapter-correspondence
{
  "scope": "polish-spaces",
  "bindings": {}
}
-->

<!-- formalization: skip-begin (chapter overview and reading guide, not a proof obligation) -->
This chapter studies the basic properties of Polish spaces and develops methods for constructing and recognizing them.
We begin with concrete examples to clarify the definition, then show that the class of Polish spaces is closed under
taking open and closed subspaces, countable disjoint unions, and countable products. We then prove the Baire category
theorem, revealing a topological consequence of completeness.

One of the chapter's main themes is Alexandrov's theorem, which gives a necessary and sufficient condition for a
subspace of a Polish space to be Polish. This theorem explains why, as subspaces of the real line, the irrationals are
Polish while the rationals are not. Finally, we introduce sequence spaces as important examples of Polish spaces that
will be used repeatedly in later chapters.
<!-- formalization: skip-end -->

<!-- chapter-correspondence-end: polish-spaces -->

## Definition {#sec:polish-definition}

<!-- chapter-correspondence
{
  "scope": "polish-definition",
  "bindings": {
    "var-D": {
      "symbol": "D",
      "target": "D"
    },
    "var-X": {
      "symbol": "X",
      "target": "PolishSpaceBook.IsSeparableByCountableDense/Y"
    }
  },
  "context": {
    "declaration": "PolishSpaceBook.IsSeparableByCountableDense",
    "path": "root.body.body.arg"
  }
}
-->

<!-- formalization: skip (Polish-space definition lead-in; the definition is formalized as the mathlib
  PolishSpace class) -->
A topological space $X$ is a \termdefine{Polish space} if:

1.  $X$ is \termdefine{separable}: there exists a countable dense subset $D \IncludedIn X$.

2.  $X$ is \termdefine{completely metrizable}: there exists a complete metric compatible with the topology of $X$.

<!-- formalization: skip (definitional remark, not a separate proof obligation) -->
The metric is not part of the data — only the topology is. A given Polish space can admit many
distinct complete compatible metrics; no particular metric is specified by the definition.

<!-- chapter-correspondence-end: polish-definition -->

## Examples {#sec:polish-examples}

<!-- chapter-correspondence
{
  "scope": "polish-examples",
  "bindings": {
    "var-C": {
      "symbol": "C",
      "target": {
        "constant": "PolishSpaceBook.real_continuous_functions"
      }
    },
    "var-d": {
      "symbol": "d",
      "target": {
        "constant": "Real.metricSpace"
      }
    },
    "var-n": {
      "symbol": "n",
      "target": "PolishSpaceBook.euclidean_space_polish/n"
    },
    "var-p": {
      "symbol": "p",
      "target": "PolishSpaceBook.real_lp_polish/p"
    },
    "var-x": {
      "symbol": "x",
      "target": "Real.dist_eq/x"
    },
    "var-y": {
      "symbol": "y",
      "target": "Real.dist_eq/y"
    }
  }
}
-->

\begin{mathmeta}
  \forward{Fsigma,Gdelta}
\end{mathmeta}

*   \termdefine{Euclidean space} $\R^n$. For $n=1$, the rationals $\QQ \IncludedIn \R$ are
    countable and dense in $\R$, while the standard metric $d(x, y) = \Abs{x - y}$ is complete on $\R$. The
    higher-dimensional cases use the Euclidean metric and the countable dense set $\QQ^n$.
*   The \termdefineas{irrational}{irrationals} $\SetDifference{\R}{\QQ}$ with the subspace topology from $\R$.
    See §{sec:alexandrov-theorem} for the proof.
*   Every \termdefine{separable Banach space} with its norm topology, for example the real sequence spaces $\ell^p$ for
    $1\le p<\infty$ and the space $C(\ClosedInterval{0}{1})$ of real-valued continuous functions.

The irrationals also illustrate that subspaces need not preserve completeness of the inherited metric: the Euclidean
metric inherited from $\R$ is not complete on $\SetDifference{\R}{\QQ}$, since Cauchy sequences of irrationals can
converge to rationals. Yet a different complete metric induces the
same topology. So a non-closed Polish subspace of a Polish space
may require a metric different from the inherited one; §{sec:alexandrov-theorem} gives the
general criterion for which subspaces are Polish.

<!-- chapter-correspondence-end: polish-examples -->

## Non-examples {#sec:polish-non-examples}

<!-- chapter-correspondence
{
  "scope": "polish-non-examples",
  "numerals": {"type": "Real", "from": "distance"},
  "bindings": {
    "distance": {"symbol": "d", "target": {"constant": "Dist.dist"}}
  }
}
-->

<!-- formalization: skip (the rationals' non-Polishness follows from the proposition on rationals and irrationals and
Alexandrov's theorem
  in §{sec:alexandrov-theorem}) -->

*   The rationals $\QQ$ with the subspace topology from $\R$ are separable but *not* completely metrizable, hence not
    Polish. This follows from Alexandrov's theorem and the proposition on rationals and irrationals in
    §{sec:alexandrov-theorem}.

*   The Banach space $\ell^\infty$ with the sup norm is complete but not separable, hence not Polish. Indeed, the binary
    sequences in $\seqPower{\{0,1\}}{\omega}$ are pairwise distance $1$ apart, so the balls of radius $1/3$ around them
    are pairwise disjoint. A countable dense set would have to meet each of these uncountably many disjoint balls,
    which is impossible.

<!-- chapter-correspondence-end: polish-non-examples -->

## Key Properties {#sec:polish-key-properties}

<!-- chapter-correspondence
{
  "scope": "polish-key-properties",
  "bindings": {}
}
-->

<!-- formalization: skip (sectioning/motivation prose) -->
We first collect the tools used in the proofs, then record which operations preserve Polish spaces. These
constructions recur in the concrete models and coding arguments below. The deeper $\Gdelta$-characterization
is proved in §{sec:alexandrov-theorem}.

<!-- chapter-correspondence-end: polish-key-properties -->

### Tools for the Proofs {#sec:polish-proof-tools}

<!-- chapter-correspondence
{
  "scope": "polish-proof-tools",
  "bindings": {
    "var-X": {
      "symbol": "X",
      "target": "PolishSpaceBook.metrizable_continuous_iff_seqContinuous/Y"
    },
    "var-Y": {
      "symbol": "Y",
      "target": "PolishSpaceBook.metrizable_continuous_iff_seqContinuous/Z"
    },
    "var-hat-d": {
      "symbol": "\\hat d",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-f": {
      "symbol": "f",
      "target": "PolishSpaceBook.metrizable_continuous_iff_seqContinuous/f"
    },
    "var-n": {
      "symbol": "n",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-x": {
      "symbol": "x",
      "occurrence": "unsubscripted",
      "target": "x"
    },
    "var-y": {
      "symbol": "y",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "sequence-x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": "u"
    }
  },
  "context": {
    "declaration": "PolishSpaceBook.metrizable_continuous_iff_seqContinuous",
    "path": "root.body.body.body.body.body.body.fn.arg.body.body.body"
  }
}
-->

<!-- formalization: skip (lead-in to elementary facts) -->
We use the following facts.

\begin{mathmeta}
  \forward{Sequence,IndexedFamily}
\end{mathmeta}

\begin{recall*}[Two facts about metrizable spaces]
Let $X$ and $Y$ be metrizable spaces.

1.  If $X$ is separable, every subspace of $X$ is separable.
2.  A map $f:X\to Y$ is continuous iff it preserves convergence of sequences: whenever
    $x_n\to x$ in $X$, one has $f(x_n)\to f(x)$ in $Y$.
\end{recall*}

<!-- formalization: skip (reading guide to the bounded-metric lemma) -->
The next lemma lets us use bounded complete metrics when forming disjoint unions and products.

<!-- chapter-correspondence
{
  "scope": "bounded-metric",
  "context": {
    "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
    "path": "root.body.body.body.body.body.value.body"
  },
  "bindings": {
    "var-hat-d": {"symbol": "\\hat d", "target": "boundedDist"},
    "var-y": {"symbol": "y", "target": "y"},
    "var-x": {"symbol": "x", "target": "x"},
    "var-X": {"symbol": "X", "target": "PolishSpaceBook.complete_compatible_metric_bounded_by_one/Y"},
    "var-d": {"symbol": "d", "target": "PolishSpaceBook.complete_compatible_metric_bounded_by_one/originalMetric"}
  }
}
-->

\begin{lemma*}[\termdefineas{bounded complete compatible metric lemma}{Bounded complete compatible metric}]
If a complete metric $d$ induces the topology of $X$, then
$$
\hat d(x,y) := \frac{d(x,y)}{1+d(x,y)}
$$
is also a complete metric inducing the same topology, and $\hat d(x,y)\le 1$ for all $x,y\in X$.
\end{lemma*}

<!-- chapter-correspondence
{
  "scope": "bounded-metric-proof",
  "numerals": {"type": "Real", "from": "var-phi"},
  "context": {
    "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
    "path": "root.body.body.body.body.body.value.body"
  },
  "bindings": {
    "var-epsilon": {
      "symbol": "\\epsilon",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-hat-d": {
      "symbol": "\\hat d",
      "target": "boundedDist"
    },
    "var-phi": {
      "symbol": "\\phi",
      "target": {
        "constant": "PolishSpaceBook.boundedMetricTransform"
      }
    },
    "var-a": {
      "symbol": "a",
      "target": "_private.PolishSpaceBook.PolishSpaces.0.PolishSpaceBook.phi_add_le_phi_add_phi/a"
    },
    "var-b": {
      "symbol": "b",
      "target": "_private.PolishSpaceBook.PolishSpaces.0.PolishSpaceBook.phi_add_le_phi_add_phi/b"
    },
    "var-m": {
      "symbol": "m",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-n": {
      "symbol": "n",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-r": {
      "symbol": "r",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-t": {
      "symbol": "t",
      "target": "PolishSpaceBook.boundedMetricTransform/t"
    },
    "var-x": {
      "symbol": "x",
      "target": "x"
    },
    "var-y": {
      "symbol": "y",
      "target": "y"
    },
    "var-z": {
      "symbol": "z",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    }
  }
}
-->

\begin{proof}[Proof]
Write $\phi(t):=t/(1+t)$ for $t\ge 0$, so that $\hat d=\phi\circ d$. The map $\phi$ is strictly increasing, vanishes
only at $0$, and is subadditive: for $a,b\ge 0$,
$$
\phi(a+b)=\frac{a+b}{1+a+b}=\frac{a}{1+a+b}+\frac{b}{1+a+b}\le\frac{a}{1+a}+\frac{b}{1+b}=\phi(a)+\phi(b).
$$
<!-- chapter-correspondence
{
  "scope": "bounded-metric-triangle",
  "context": {
    "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
    "path": "root.body.body.body.body.body.body.body.value.fn.fn.arg.body.body"
  },
  "bindings": {
    "var-hat-d": {
      "symbol": "\\hat d",
      "target": "boundedDist"
    },
    "var-x": {
      "symbol": "x",
      "target": "x"
    },
    "var-y": {
      "symbol": "y",
      "target": "y"
    },
    "var-z": {
      "symbol": "z",
      "target": "z"
    }
  }
}
-->

Hence $\hat d$ is symmetric, vanishes exactly on the diagonal, and satisfies the triangle inequality
$$
\hat d(x,z)=\phi(d(x,z))\le\phi\bigl(d(x,y)+d(y,z)\bigr)\le\hat d(x,y)+\hat d(y,z),
$$
where the first step uses monotonicity and the second subadditivity.

<!-- chapter-correspondence-end: bounded-metric-triangle -->

<!-- chapter-correspondence
{
  "scope": "bounded-metric-radius",
  "numerals": {"type": "Real", "from": "var-r"},
  "context": {
    "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
    "path": "root.body.body.body.body.body.body.body.value.fn.arg.body.value.body.body.body.body"
  },
  "bindings": {
    "var-hat-d": {
      "symbol": "\\hat d",
      "target": "boundedDist"
    },
    "var-x": {
      "symbol": "x",
      "target": "x"
    },
    "var-y": {
      "symbol": "y",
      "target": "y"
    },
    "var-r": {
      "symbol": "r",
      "target": "r"
    }
  }
}
-->

Since $\phi$ is a strictly increasing bijection of $\LeftClosedInterval{0}{\infty}$ onto
$\LeftClosedInterval{0}{1}$, for every $0<r<1$ the inequality
$\hat d(x,y)<r$ is equivalent to $d(x,y)<r/(1-r)$, so the $\hat d$-ball of radius $r$ about a point equals the
$d$-ball of radius $r/(1-r)$ about it. As $r$ ranges over $\OpenInterval{0}{1}$ the radius $r/(1-r)$ ranges over all of
$\OpenInterval{0}{\infty}$. Thus the $\hat d$-balls of radius less than $1$ coincide with the $d$-balls;
these balls form a base
for both metric topologies, so the two metrics induce the same topology.

<!-- chapter-correspondence-end: bounded-metric-radius -->

<!-- chapter-correspondence
{
  "scope": "bounded-metric-completeness",
  "context": {
    "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
    "path": "root.body.body.body.body.body.body.body.body.body.value.body.body.body.body.body.arg.body"
  },
  "bindings": {
    "sequence-x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": {
        "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
        "path": [
          "root.body.body.body.body.body.body.body",
          "body.body.value.body"
        ],
        "binder": "u"
      }
    },
    "limit-x": {
      "symbol": "x",
      "occurrence": "unsubscripted",
      "target": "x"
    },
    "bounded-distance": {
      "symbol": "\\hat d",
      "target": {
        "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
        "path": [
          "root.body.body.body.body.body.body.body",
          "body.body.value.body"
        ],
        "binder": "boundedDist"
      }
    },
    "original-distance": {
      "symbol": "d",
      "target": {
        "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
        "path": [
          "root.body.body.body.body.body.body.body",
          "body.body.value.body"
        ],
        "binder": "originalMetric"
      }
    },
    "epsilon": {
      "symbol": "\\epsilon",
      "target": {
        "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
        "path": [
          "root.body.body.body.body.body.body.body",
          "body.body.value.body.body.body.body.value",
          "body.arg.body.body.body.arg.body.body",
          "arg.body.body.body"
        ],
        "binder": "ε"
      }
    },
    "index-m": {
      "symbol": "m",
      "target": {
        "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
        "path": [
          "root.body.body.body.body.body.body.body",
          "body.body.value.body.body.body.body.value",
          "body.arg.body.body.body.arg.body.body",
          "arg.body.body.body"
        ],
        "binder": "m"
      }
    },
    "index-n": {
      "symbol": "n",
      "target": {
        "declaration": "PolishSpaceBook.complete_compatible_metric_bounded_by_one",
        "path": [
          "root.body.body.body.body.body.body.body",
          "body.body.value.body.body.body.body.value",
          "body.arg.body.body.body.arg.body.body",
          "arg.body.body.body"
        ],
        "binder": "n"
      }
    }
  }
}
-->

It remains to check completeness. Since $\phi(t)\le t$, we have $\hat d\le d$, so every $d$-Cauchy sequence is
$\hat d$-Cauchy. Conversely, let $\Sequence{x_n}{n\in\omega}$ be $\hat d$-Cauchy and fix $\epsilon>0$. Eventually
$\hat d(x_m,x_n)<\phi(\epsilon)$, and since $\phi$ is strictly increasing this gives $d(x_m,x_n)<\epsilon$. Thus
$\Sequence{x_n}{n\in\omega}$ is $d$-Cauchy, so it $d$-converges to some $x$, and since $\hat d\le d$ it $\hat
d$-converges to $x$ as well.

<!-- chapter-correspondence-end: bounded-metric-completeness -->
\end{proof}

<!-- chapter-correspondence-end: bounded-metric-proof -->

<!-- formalization: skip (prose restatement of the preceding lemma, which is itself formalized) -->
In other words, we may assume without loss of generality that a complete metric compatible with the topology of a
Polish space satisfies $d\le 1$.

<!-- chapter-correspondence-end: bounded-metric -->

<!-- chapter-correspondence-end: polish-proof-tools -->

### Basic Constructions {#sec:polish-basic-constructions}

<!-- chapter-correspondence
{
  "scope": "polish-basic-constructions",
  "bindings": {}
}
-->

<!-- formalization: skip (sectioning/motivation prose) -->
The class of Polish spaces is closed under the following operations; these are the routine ways new Polish spaces are
built from old ones. The proofs all have the same
shape: construct a complete compatible metric, then check separability using the subspace fact above or an explicit
countable dense set.

\begin{proposition*}[Closed subspaces]
Closed subspaces of Polish spaces are Polish.
\end{proposition*}

<!-- chapter-correspondence
{
  "scope": "closed-subspace-proof",
  "bindings": {
    "var-C": {
      "symbol": "C",
      "target": "PolishSpaceBook.closed_subspace_polish/C"
    },
    "var-X": {
      "symbol": "X",
      "target": "PolishSpaceBook.closed_subspace_polish/X"
    },
    "var-d": {
      "symbol": "d",
      "target": "this"
    }
  },
  "context": {
    "declaration": "PolishSpaceBook.closed_subspace_polish",
    "path": "root.body.body.body.body.body.body"
  }
}
-->

\begin{proof}[Proof]
Let $X$ be a Polish space, choose a complete compatible metric $d$ on $X$, and let $C \IncludedIn X$ be closed. The
restriction $\restrict{d}{C\times C}$ induces the subspace topology and is complete: a Cauchy sequence in $C$ is Cauchy
in $X$, hence converges in $X$, and the limit lies in $C$ because $C$ is closed. The subspace $C$ is separable.
\end{proof}

<!-- chapter-correspondence-end: closed-subspace-proof -->

\begin{proposition*}[Open subspaces]
Open subspaces of Polish spaces are Polish.
\end{proposition*}

<!-- formalization: skip (motivation for the metric used in the following proof) -->
The difficulty is that a Cauchy sequence for the restricted metric may escape to the boundary. We add a term that
measures changes in the reciprocal distance to the complement. That reciprocal grows without bound near the boundary,
so a Cauchy sequence for the new metric must stay away from it.

<!-- chapter-correspondence
{
  "scope": "open-subspace-proof",
  "bindings": {
    "var-S": {
      "symbol": "S",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-U": {
      "symbol": "U",
      "target": "PolishSpaceBook.open_subspace_polish/U"
    },
    "var-X": {
      "symbol": "X",
      "target": "PolishSpaceBook.open_subspace_polish/X"
    },
    "var-d": {
      "symbol": "d",
      "target": "this"
    },
    "var-n": {
      "symbol": "n",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-s": {
      "symbol": "s",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-x": {
      "symbol": "x",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-y": {
      "symbol": "y",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-z": {
      "symbol": "z",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-d-prime": {
      "symbol": "d'",
      "target": "d'"
    }
  },
  "context": {
    "declaration": "PolishSpaceBook.open_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg.body",
      "body.body.body.body.body.arg"
    ]
  }
}
-->

<!-- chapter-correspondence
{
  "scope": "open-metric-definition",
  "context": {
    "declaration": "PolishSpaceBook.open_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg.body",
      "body.body.body.body.body.arg.body.value",
      "body"
    ]
  },
  "bindings": {
    "var-x": {
      "symbol": "x",
      "target": "x"
    },
    "var-y": {
      "symbol": "y",
      "target": "y"
    },
    "function-z": {
      "symbol": "z",
      "target": "x"
    }
  }
}
-->

\begin{proof}[Proof]
Choose a complete compatible metric $d$ on $X$, and let $U \IncludedIn X$ be open.
The case $U = X$ is trivial, so assume $U \ne X$. The restricted metric
$\restrict{d}{U\times U}$ is generally not complete, because a Cauchy sequence in $U$ may converge in $X$ to a boundary
point. Define a new metric on $U$ by
$$d'(x, y) \;:=\; d(x, y) \;+\; \Abs{\frac{1}{d(x,\, \SetDifference{X}{U})} - \frac{1}{d(y,\, \SetDifference{X}{U})}
}.$$

<!-- chapter-correspondence
{
  "scope": "open-distance-definition",
  "context": {
    "declaration": "PolishSpaceBook.open_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg.body",
      "body.body.body.body.body.arg.body.body",
      "body.body.body.body.body.body.value.body",
      "body"
    ]
  },
  "bindings": {
    "point-z": {
      "symbol": "z",
      "target": "z"
    },
    "set-S": {
      "symbol": "S",
      "target": "S"
    }
  }
}
-->

Here the distance to a nonempty set is defined by $d(z,S):=\inf\{d(z,s):s\in S\}$.

<!-- chapter-correspondence-end: open-distance-definition -->

This is well-defined because $d(x, \SetDifference{X}{U})>0$ for every $x\in U$.
The absolute-value term is a pseudometric obtained by pulling back the Euclidean metric along
$z \mapsto 1/d(z, \SetDifference{X}{U})$, so adding it to $d$ gives a metric. Since $d \le d'$, convergence in
$d'$ implies convergence in $d$.

<!-- chapter-correspondence-end: open-metric-definition -->

<!-- chapter-correspondence
{
  "scope": "open-metric-topology",
  "context": {
    "declaration": "PolishSpaceBook.open_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg.body",
      "body.body.body.body.body.arg.body.body",
      "value.fn.arg.arg.body.arg.body.arg",
      "body.body.arg.body.body.arg.body.body",
      "value.body"
    ]
  },
  "bindings": {
    "sequence-x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": "u"
    },
    "limit-x": {
      "symbol": "x",
      "occurrence": "unsubscripted",
      "target": "x"
    },
    "function-z": {
      "symbol": "z",
      "target": {
        "declaration": "PolishSpaceBook.open_subspace_polish",
        "path": [
          "root.body.body.body.body.body.arg.body",
          "body.body.body.body.body.arg.body.body",
          "body.body.body.body.body.body.value.body",
          "body"
        ],
        "binder": "z"
      }
    },
    "sequence-index": {
      "symbol": "n",
      "target": {
        "declaration": "PolishSpaceBook.open_subspace_polish",
        "path": [
          "root.body.body.body.body.body.arg.body",
          "body.body.body.body.body.arg.body.body",
          "value.fn.arg.arg.body.arg.body.arg",
          "body.body.arg.body.body.arg.body.body",
          "value.body.body.body.value.fn.fn.arg",
          "fn.fn.arg"
        ],
        "binder": "n"
      }
    }
  }
}
-->

Conversely, suppose $x_n \to x$ in $d$ and all $x_n,x$ lie in $U$. The function
$z \mapsto d(z, \SetDifference{X}{U})$ is continuous by the distance estimate in
\BookSectionLink{sec:appendix-distance-to-set}{the appendix section on distance to a set} and is positive at $x$, so
$$\frac{1}{d(x_n, \SetDifference{X}{U})} \longrightarrow \frac{1}{d(x, \SetDifference{X}{U})}.$$
Hence $d'(x_n,x)\to 0$. The identity maps between the two metric topologies therefore preserve convergence of
sequences in both directions, so both maps are continuous and $d'$ induces the subspace topology.

<!-- chapter-correspondence-end: open-metric-topology -->

<!-- chapter-correspondence
{
  "scope": "open-completeness",
  "context": {
    "declaration": "PolishSpaceBook.open_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg.body",
      "body.body.body.body.body.arg.body.body",
      "body.body.body.body.body.value.body.body",
      "body.arg.body.body.arg.body.body.arg",
      "body.body.body.arg.body.body.body.body",
      "value.body"
    ]
  },
  "bindings": {
    "sequence-x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": "u"
    },
    "limit-x": {
      "symbol": "x",
      "occurrence": "unsubscripted",
      "target": "x"
    },
    "index-n": {
      "symbol": "n",
      "target": "n"
    }
  }
}
-->

The metric $d'$ is complete. Suppose $\Sequence{x_n}{n\in\omega}$ is $d'$-Cauchy in $U$. Then the sequence
$$\Sequence{1/d(x_n,\SetDifference{X}{U})}{n\in\omega}$$
is Cauchy in $\R$ and hence bounded. Thus the points $x_n$ stay a positive distance from $\SetDifference{X}{U}$. The
sequence is also $d$-Cauchy, so it converges in $X$ to some point $x$. The positive distance from
$\SetDifference{X}{U}$ forces $x \in U$.

<!-- chapter-correspondence-end: open-completeness -->

<!-- chapter-correspondence
{
  "scope": "open-completeness-limit",
  "context": {
    "declaration": "PolishSpaceBook.open_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg.body",
      "body.body.body.body.body.arg.body.body",
      "body.body.body.body.body.value.body.body",
      "body.arg.body.body.arg.body.body.arg",
      "body.body.body.arg.body.body.body.body",
      "body.body.body"
    ]
  },
  "bindings": {
    "sequence-x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": "u"
    },
    "limit-x": {
      "symbol": "x",
      "occurrence": "unsubscripted",
      "target": "limitInU"
    }
  }
}
-->

The preceding topology comparison gives $x_n \to x$ in $d'$.
The subspace $U$ is separable.
\end{proof}

<!-- chapter-correspondence-end: open-completeness-limit -->

<!-- chapter-correspondence-end: open-subspace-proof -->

\begin{proposition*}[Countable disjoint unions]
Countable disjoint unions of Polish spaces are Polish.
\end{proposition*}

<!-- chapter-correspondence
{
  "scope": "disjoint-union-proof",
  "bindings": {
    "var-X": {"symbol": "X", "target": "PolishSpaceBook.countable_disjoint_union_polish_nat/Y"},
    "var-d": {"symbol": "d", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-k": {"symbol": "k", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-m": {"symbol": "m", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-n": {"symbol": "n", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-p": {"symbol": "p", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-q": {"symbol": "q", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-r": {"symbol": "r", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-x": {"symbol": "x", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-y": {"symbol": "y", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-z": {"symbol": "z", "reason": "Local symbol has no reviewed Lean binder mapping."}
  }
}
-->

<!-- chapter-correspondence
{
  "scope": "disjoint-union-bounded-metrics",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body.body",
      "fn.fn.body.body.body.body.body.body",
      "value"
    ]
  },
  "bindings": {
    "family-X": {
      "symbol": "X",
      "target": "Y"
    },
    "family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    },
    "coordinate-n": {
      "symbol": "n",
      "target": "i"
    }
  }
}
-->

\begin{proof}[Proof]
Given Polish spaces $\Sequence{X_n}{n\in\omega}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$.

<!-- chapter-correspondence-end: disjoint-union-bounded-metrics -->

<!-- chapter-correspondence
{
  "scope": "disjoint-union-metric-definition",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.value.body",
      "arg.body.body.body.arg.body"
    ]
  },
  "bindings": {
    "X": {
      "symbol": "X",
      "target": "Y"
    },
    "n": {
      "symbol": "n",
      "target": "i"
    },
    "m": {
      "symbol": "m",
      "target": "j"
    },
    "x": {
      "symbol": "x",
      "target": "x"
    },
    "y": {
      "symbol": "y",
      "target": "y"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "dSigma"
    },
    "metric-family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    }
  }
}
-->

On the
topological sum $\ExternalDisjointUnion_{n \in \omega} X_n$, define
$$d(\Pair{n}{x}, \Pair{m}{y}) \;=\;
\begin{cases}
d_n(x, y), & n = m, \\
1, & n \ne m.
\end{cases}$$

<!-- chapter-correspondence-end: disjoint-union-metric-definition -->

<!-- chapter-correspondence
{
  "scope": "disjoint-triangle",
  "numerals": {"type": "Real", "from": "metric-d"},
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "value.body.arg.body.body.body.arg",
      "body.body.body.arg.body.body.body",
      "body"
    ]
  },
  "bindings": {
    "n": {
      "symbol": "n",
      "target": "i"
    },
    "m": {
      "symbol": "m",
      "target": "j"
    },
    "k": {
      "symbol": "k",
      "target": "k"
    },
    "p": {
      "symbol": "p",
      "target": "p"
    },
    "q": {
      "symbol": "q",
      "target": "q"
    },
    "r": {
      "symbol": "r",
      "target": "r"
    },
    "x": {
      "symbol": "x",
      "target": "x"
    },
    "y": {
      "symbol": "y",
      "target": "y"
    },
    "z": {
      "symbol": "z",
      "target": "z"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "dSigma"
    },
    "metric-family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    }
  }
}
-->

Nonnegativity, symmetry, and separation of distinct points follow directly from the definition.
For the triangle inequality, write $p=\Pair{n}{x}$, $q=\Pair{m}{y}$, and $r=\Pair{k}{z}$.
If $n=m=k$, then

<!-- chapter-correspondence
{
  "scope": "disjoint-triangle-same",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "value.body.arg.body.body.body.arg",
      "body.body.body.arg.body.body.body",
      "body.body.arg.arg.fn.arg.body",
      "fn.fn.fn.arg.body.body.fn",
      "arg.body.fn.fn.fn.arg.body"
    ]
  },
  "bindings": {
    "n": {
      "symbol": "n",
      "target": "i"
    },
    "m": {
      "symbol": "m",
      "target": "i"
    },
    "k": {
      "symbol": "k",
      "target": "i"
    },
    "p": {
      "symbol": "p",
      "target": "p"
    },
    "q": {
      "symbol": "q",
      "target": "q_book_34"
    },
    "r": {
      "symbol": "r",
      "target": "r_book_31"
    },
    "x": {
      "symbol": "x",
      "target": "x"
    },
    "y": {
      "symbol": "y",
      "target": "y_book_33"
    },
    "z": {
      "symbol": "z",
      "target": "z_book_30"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "dSigma"
    },
    "metric-family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    }
  }
}
-->

$$d(p,r)=d_n(x,z)\le d_n(x,y)+d_n(y,z)=d(p,q)+d(q,r).$$

<!-- chapter-correspondence-end: disjoint-triangle-same -->

If $n=k\ne m$, then

<!-- chapter-correspondence
{
  "scope": "disjoint-triangle-return",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "value.body.arg.body.body.body.arg",
      "body.body.body.arg.body.body.body",
      "body.body.arg.arg.fn.arg.body",
      "fn.fn.fn.arg.body.body.arg",
      "body"
    ]
  },
  "bindings": {
    "n": {
      "symbol": "n",
      "target": "i"
    },
    "m": {
      "symbol": "m",
      "target": "j"
    },
    "k": {
      "symbol": "k",
      "target": "i"
    },
    "p": {
      "symbol": "p",
      "target": "p"
    },
    "q": {
      "symbol": "q",
      "target": "q"
    },
    "r": {
      "symbol": "r",
      "target": "r_book_31"
    },
    "x": {
      "symbol": "x",
      "target": "x"
    },
    "y": {
      "symbol": "y",
      "target": "y"
    },
    "z": {
      "symbol": "z",
      "target": "z_book_30"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "dSigma"
    },
    "metric-family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    }
  }
}
-->

$$d(p,r)=d_n(x,z)\le 1\le 1+1=d(p,q)+d(q,r).$$

<!-- chapter-correspondence-end: disjoint-triangle-return -->

If $n\ne k$, then $n\ne m$ or $m\ne k$, so at least one of $d(p,q)$ and $d(q,r)$ equals $1$. Hence

<!-- chapter-correspondence
{
  "scope": "disjoint-triangle-distinct",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "value.body.arg.body.body.body.arg",
      "body.body.body.arg.body.body.body",
      "body.body.arg.arg.arg"
    ]
  },
  "bindings": {
    "n": {
      "symbol": "n",
      "target": "i"
    },
    "m": {
      "symbol": "m",
      "target": "j"
    },
    "k": {
      "symbol": "k",
      "target": "k"
    },
    "p": {
      "symbol": "p",
      "target": "p"
    },
    "q": {
      "symbol": "q",
      "target": "q"
    },
    "r": {
      "symbol": "r",
      "target": "r"
    },
    "x": {
      "symbol": "x",
      "target": "x"
    },
    "y": {
      "symbol": "y",
      "target": "y"
    },
    "z": {
      "symbol": "z",
      "target": "z"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "dSigma"
    },
    "metric-family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    }
  }
}
-->

$$d(p,r)=1\le d(p,q)+d(q,r).$$

<!-- chapter-correspondence-end: disjoint-triangle-distinct -->

<!-- chapter-correspondence-end: disjoint-triangle -->

<!-- chapter-correspondence
{
  "scope": "disjoint-topology",
  "predicates": {"type": "Real", "witness": "dSigma"},
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body"
    ]
  },
  "bindings": {
    "metric-d": {
      "symbol": "d",
      "target": "sigmaMetric"
    }
  }
}
-->

These cases exhaust all possibilities, so $d$ is a metric. It induces the disjoint-union topology: each
summand is clopen, and balls of radius $< 1$ stay inside a single summand.

<!-- chapter-correspondence-end: disjoint-topology -->

<!-- chapter-correspondence
{
  "scope": "disjoint-completeness",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body"
    ]
  },
  "bindings": {}
}
-->

<!-- chapter-correspondence
{
  "scope": "disjoint-completeness-tail",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.value.body",
      "body.arg.body.body.fn.arg.body",
      "body.body.body.body.body.body"
    ]
  },
  "bindings": {
    "metric-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    },
    "index-n": {
      "symbol": "n",
      "target": "i"
    }
  }
}
-->

It is complete because a Cauchy sequence is
eventually trapped in one summand, where it converges by completeness of $d_n$.

<!-- chapter-correspondence-end: disjoint-completeness-tail -->

<!-- chapter-correspondence-end: disjoint-completeness -->

<!-- chapter-correspondence
{
  "scope": "disjoint-separability",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body"
    ]
  },
  "bindings": {}
}
-->

<!-- chapter-correspondence
{
  "scope": "disjoint-separability-dense-union",
  "context": {
    "declaration": "PolishSpaceBook.countable_disjoint_union_polish_nat",
    "path": [
      "root.body.body.body.unfold.body.body",
      "body.fn.fn.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.value",
      "fn.fn.body.body"
    ]
  },
  "bindings": {}
}
-->

It is separable because a countable
union of countable dense subsets is countable and dense.

<!-- chapter-correspondence-end: disjoint-separability-dense-union -->

<!-- chapter-correspondence-end: disjoint-separability -->

\end{proof}

<!-- chapter-correspondence-end: disjoint-union-proof -->

\begin{proposition*}[Countable products]
Countable products of Polish spaces are Polish.
\end{proposition*}

<!-- chapter-correspondence
{
  "scope": "product-proof",
  "bindings": {
    "var-D": {
      "symbol": "D",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-M": {
      "symbol": "M",
      "target": {
        "declaration": "PolishSpaceBook.countable_product_polish",
        "path": [
          "root.body.body.body.body.body.body.fn",
          "fn.body.body.body.body.body.body.body",
          "body.body.body.body.body.body.body.body",
          "body.body.body.body.body.value.body.body",
          "body.arg.body.body.body.body.arg.arg",
          "arg.arg.arg.arg.body.body.body.arg",
          "arg"
        ],
        "binder": "M"
      }
    },
    "var-V": {
      "symbol": "V",
      "target": {
        "declaration": "PolishSpaceBook.countable_product_polish",
        "path": [
          "root.body.body.body.body.body.body.fn",
          "fn.body.body.body.body.body.body.body",
          "body.body.body.body.body.body.body.body",
          "body.body.body.body.body.value.body.body",
          "body.arg.body.body.body.body.arg.arg",
          "arg.arg.arg.arg.body.body.body.arg",
          "arg"
        ],
        "binder": "V"
      }
    },
    "var-X": {
      "symbol": "X",
      "target": "PolishSpaceBook.countable_product_polish/Y"
    },
    "var-varepsilon": {
      "symbol": "\\varepsilon",
      "target": {
        "declaration": "PolishSpaceBook.countable_product_polish",
        "path": [
          "root.body.body.body.body.body.body.fn",
          "fn.body.body.body.body.body.body.body",
          "body.body.body.body.body.body.body.body",
          "body.body.body.body.body.value.body.body",
          "body.arg.body.body.body.body.arg.arg",
          "arg.arg.arg.arg.body.body.body.arg",
          "arg"
        ],
        "binder": "ε"
      }
    },
    "var-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": {
        "declaration": "PolishSpaceBook.countable_product_polish",
        "path": [
          "root.body.body.body.body.body.body.fn",
          "fn.body.body.body.body.body.body.body",
          "body.body"
        ],
        "binder": "dPi"
      }
    },
    "var-k": {
      "symbol": "k",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-n": {
      "symbol": "n",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-x": {
      "symbol": "x",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-y": {
      "symbol": "y",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": {
        "declaration": "PolishSpaceBook.countable_product_polish",
        "path": [
          "root.body.body.body.body.body.body.fn",
          "fn.body.body.body.body.body.body.body",
          "body.body"
        ],
        "binder": "boundedMetricOn"
      }
    }
  }
}
-->

<!-- chapter-correspondence
{
  "scope": "product-metric-construction",
  "context": {
    "declaration": "PolishSpaceBook.countable_product_polish",
    "path": [
      "root.body.body.body.body.body.body.fn",
      "fn.body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body.body",
      "body.body.value.body.body.arg.arg.arg",
      "fn.arg"
    ]
  },
  "bindings": {
    "family-X": {
      "symbol": "X",
      "target": "Y"
    },
    "family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "dPi"
    },
    "point-x": {
      "symbol": "x",
      "target": "x"
    },
    "point-y": {
      "symbol": "y",
      "target": "y"
    },
    "index-n": {
      "symbol": "n",
      "target": "n"
    }
  }
}
-->

\begin{proof}[Proof]
Given Polish spaces $\Sequence{X_n}{n\in\omega}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$ and define
on
$\prod_{n \in \omega} X_n$
$$d\big(\Sequence{x_n}{n\in\omega},\Sequence{y_n}{n\in\omega}\big) \;=\; \sum_{n \in \omega} 2^{-n}d_n(x_n,y_n).$$
Each summand $2^{-n}d_n(x_n,y_n)$ is at most $2^{-n}$, so the series converges, and the metric axioms follow
term by term from the metric axioms for the $d_n$. Thus $d$ is a metric.

This metric induces the product topology. For each coordinate $n$,
$$2^{-n}d_n(x_n,y_n)\le d(x,y),$$
so each coordinate projection is continuous for $d$. Hence the identity map from the $d$-topology to the product
topology is continuous.

<!-- chapter-correspondence-end: product-metric-construction -->

<!-- chapter-correspondence
{
  "scope": "product-topology-neighborhood",
  "context": {
    "declaration": "PolishSpaceBook.countable_product_polish",
    "path": [
      "root.body.body.body.body.body.body.fn",
      "fn.body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body.body",
      "body.body.body.body.body.value.body.body",
      "body.arg.body.body.body.body.arg.arg",
      "arg.arg.arg.arg.body.body.body.arg",
      "arg"
    ]
  },
  "bindings": {
    "family-X": {
      "symbol": "X",
      "target": "Y"
    },
    "family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "dPi"
    },
    "point-x": {
      "symbol": "x",
      "target": "x"
    },
    "point-y": {
      "symbol": "y",
      "target": "y"
    },
    "cutoff-M": {
      "symbol": "M",
      "target": "M"
    },
    "neighborhood-V": {
      "symbol": "V",
      "target": "V"
    },
    "radius": {
      "symbol": "\\varepsilon",
      "target": "ε"
    }
  }
}
-->

Conversely, fix $x$ and $\varepsilon>0$. Choose $M$ so that
$\sum_{n\ge M}2^{-n}<\varepsilon/2$. The set
$$V=\left\{y:\sum_{n<M}2^{-n}d_n(x_n,y_n)<\varepsilon/2\right\}$$
is a product-open neighborhood of $x$, since the finite sum is a continuous function of finitely many coordinates.
For $y\in V$,
$$d(x,y)\le\sum_{n<M}2^{-n}d_n(x_n,y_n)+\sum_{n\ge M}2^{-n}<\varepsilon.$$
Thus every $d$-ball about $x$ contains a product-open neighborhood of $x$, proving continuity of the identity in
the other direction. The two topologies agree. In particular, convergence for $d$ is exactly coordinate-wise
convergence.

<!-- chapter-correspondence-end: product-topology-neighborhood -->

<!-- chapter-correspondence
{
  "scope": "product-completeness",
  "context": {
    "declaration": "PolishSpaceBook.countable_product_polish",
    "path": [
      "root.body.body.body.body.body.body.fn",
      "fn.body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body.body",
      "body.value.body.body.body.body.fn.fn",
      "body.body.value"
    ]
  },
  "bindings": {
    "family-X": {
      "symbol": "X",
      "target": "Y"
    },
    "family-d": {
      "symbol": "d",
      "occurrence": "subscript-base",
      "target": "boundedMetricOn"
    },
    "metric-d": {
      "symbol": "d",
      "occurrence": "unsubscripted",
      "target": "productMetric"
    },
    "sequence-x": {
      "symbol": "x",
      "occurrence": "superscript-base",
      "target": "u"
    },
    "limit-coordinate-x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": "x"
    },
    "limit-x": {
      "symbol": "x",
      "occurrence": "unsubscripted",
      "target": "x"
    },
    "coordinate-n": {
      "symbol": "n",
      "target": "n"
    }
  }
}
-->

For completeness, let $\Sequence{x^k}{k\in\omega}$ be $d$-Cauchy. Then each coordinate sequence
$\Sequence{x^k_n}{k\in\omega}$ is Cauchy for $d_n$,
so it converges to some $x_n \in X_n$. By the convergence criterion just proved, the point
$x=\Sequence{x_n}{n\in\omega}$ is the
$d$-limit of $\Sequence{x^k}{k\in\omega}$.

<!-- chapter-correspondence-end: product-completeness -->

<!-- chapter-correspondence
{
  "scope": "product-separability",
  "context": {
    "declaration": "PolishSpaceBook.countable_product_polish",
    "path": [
      "root.body.body.body.body.body.body.fn",
      "fn.body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body.body",
      "body.body.value.fn.arg.body.body.body",
      "body.body.body.body.value"
    ]
  },
  "bindings": {
    "family-X": {
      "symbol": "X",
      "target": "Y"
    },
    "dense-D": {
      "symbol": "D",
      "target": "coordinateDense"
    },
    "reference-x": {
      "symbol": "x^*",
      "target": "x0"
    },
    "coordinate-n": {
      "symbol": "n",
      "target": "n"
    }
  }
}
-->

For separability, if the product is empty there is nothing to prove.
Otherwise fix countable dense sets
$D_n \IncludedIn X_n$ and a reference point $x^* \in \prod X_n$. The countable set of sequences agreeing with $x^*$ in
all but finitely many coordinates, with the differing coordinates ranging over the corresponding $D_n$, is dense.

<!-- chapter-correspondence-end: product-separability -->
\end{proof}

<!-- chapter-correspondence-end: product-proof -->

<!-- formalization: skip (illustrative non-closure warnings; no local quotient construction or proof) -->

\begin{remark*}[Important example: quotients need not be Polish]
A quotient of a Polish space need not be Polish: the quotient topology may fail to be Hausdorff or metrizable. Likewise,
a continuous image of a Polish space need not be Polish, even inside a Polish space: $\QQ$ is a continuous image of the
discrete space $\omega$ but is not Polish, as noted in §{sec:polish-non-examples}. Continuous images are the subject of
the later theory of analytic sets. This is why classification problems are usually studied through their equivalence
relations and Borel reductions rather than by forming topological quotient spaces directly.
\end{remark*}

<!-- chapter-correspondence-end: polish-basic-constructions -->

## Baire Category {#sec:baire-category}

<!-- chapter-correspondence
{
  "scope": "baire-category",
  "bindings": {}
}
-->

Completeness has a strong topological consequence: nonempty Polish spaces cannot be exhausted by countably many closed
nowhere-dense pieces. This is the Baire-category principle, and it is one of the main reasons complete metrizability
matters.

For Baire-category arguments, a set is \termdefineas{nowhere dense set}{nowhere dense} if the interior of its closure is
empty, \termdefineas{meager set}{meager} if it is a countable union of nowhere-dense sets, and
\termdefineas{comeager set}{comeager} if its complement is meager. All three notions depend on the ambient space; we
leave it implicit when
context fixes it.


\begin{theorem*}[\termdefineas{Baire category theorem}{Theorem (Baire category)}]
Every Polish space is a \termdefineas{Baire space (category sense)}{Baire space} in the category sense: countable
intersections of dense open sets are dense. In particular, no nonempty open subset of a Polish space is meager in
itself.
\end{theorem*}

<!-- chapter-correspondence
{
  "scope": "baire-proof",
  "bindings": {
    "var-G": {
      "symbol": "G",
      "target": "G"
    },
    "var-N": {
      "symbol": "N",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-U": {
      "symbol": "U",
      "target": "U"
    },
    "var-V": {
      "symbol": "V",
      "target": "V"
    },
    "var-X": {
      "symbol": "X",
      "target": "Y"
    },
    "var-d": {
      "symbol": "d",
      "target": "book_hyg_1"
    },
    "var-m": {
      "symbol": "m",
      "reason": "Local symbol has no reviewed Lean binder mapping."
    },
    "var-n": {
      "symbol": "n",
      "target": "n"
    },
    "var-r": {
      "symbol": "r",
      "target": {
        "declaration": "PolishSpaceBook.baire_nested_open_sets",
        "path": [
          "root.body.body.body.body.body.body",
          "body.body.body.body.body.value.body",
          "body.body.body.unfold.body.body.body",
          "body.body.body.body"
        ],
        "binder": "r"
      }
    },
    "var-x": {
      "symbol": "x",
      "target": {
        "declaration": "PolishSpaceBook.baire_nested_open_sets",
        "path": [
          "root.body.body.body.body.body.body",
          "body.body.body.body.body.value.body",
          "body.body.body.unfold.body.body.body",
          "body.body.body.body"
        ],
        "binder": "x"
      }
    },
    "var-r0": {
      "symbol": "r_0",
      "target": {
        "declaration": "PolishSpaceBook.baire_nested_open_sets",
        "path": [
          "root.body.body.body.body.body.body",
          "body.body.body.body.body.value.body",
          "body.body.body.unfold.body.body.body",
          "body.body.body.body"
        ],
        "binder": "r₀"
      }
    }
  },
  "context": {
    "declaration": "PolishSpaceBook.baire_open_intersection",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.arg.body.body.arg",
      "body.body.fn.fn.body.body.body",
      "value"
    ]
  }
}
-->

\begin{proof}[Proof] Let $X$ be Polish, fix a complete compatible metric $d$, let $U\IncludedIn X$ be nonempty open, and
let $\Sequence{G_n}{n\in\omega}$ be dense open subsets of $U$ in the relative topology. We show that $U\cap\bigcap_n
G_n$ is
nonempty.

Construct nonempty open sets $V_n\IncludedIn U$ recursively so that
$$
\begin{aligned}
\Closure{V_{n+1}} &\IncludedIn V_n\cap G_n,\\
\MetricDiameter{d}{\Closure{V_n}} &\le 2^{-n}.
\end{aligned}
$$
Start with any nonempty open $V_0\IncludedIn U$ whose closure has diameter at most <!-- chapter-correspondence
{
  "scope": "baire-first-bound",
  "context": {
    "declaration": "PolishSpaceBook.baire_nested_open_sets",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.value.unfold.body.body",
      "body.body.body"
    ]
  },
  "bindings": {
    "radius": {
      "symbol": "r",
      "target": "r"
    }
  },
  "numerals": {
    "type": "Real",
    "from": "radius"
  }
}
-->$1$<!-- chapter-correspondence-end: baire-first-bound -->. Given $V_n$, the set $V_n\cap
G_n$ is nonempty because $G_n$ is dense in $U$. Since $U$ is open in $X$, the set $V_n\cap G_n$ is open in $X$, so it
contains some ball $\Ball{x}{r_0}$. Choose $0<r<r_0$ small enough that
$\Closure{\Ball{x}{r}}\IncludedIn \Ball{x}{r_0}$ and <!-- chapter-correspondence
{
  "scope": "baire-diam",
  "context": {
    "declaration": "PolishSpaceBook.baire_nested_open_sets",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.value.body",
      "body.body.body.unfold.body.body.body",
      "body.body.body.body"
    ]
  },
  "bindings": {
    "d": {
      "symbol": "d",
      "target": "book_hyg_1"
    },
    "x": {
      "symbol": "x",
      "target": "x"
    },
    "r": {
      "symbol": "r",
      "target": "r"
    },
    "n": {
      "symbol": "n",
      "target": "n"
    }
  }
}
-->$\MetricDiameter{d}{\Closure{\Ball{x}{r}}}\le 2^{-(n+1)}$<!-- chapter-correspondence-end: baire-diam -->,
and put <!-- chapter-correspondence
{
  "scope": "baire-next",
  "context": {
    "declaration": "PolishSpaceBook.baire_nested_open_sets",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.arg.arg.body.body.body",
      "body"
    ]
  },
  "bindings": {
    "V": {
      "symbol": "V",
      "target": "V"
    },
    "n": {
      "symbol": "n",
      "target": "n"
    },
    "x": {
      "symbol": "x",
      "target": "x"
    },
    "r": {
      "symbol": "r",
      "target": "r"
    }
  }
}
-->$V_{n+1}:=\Ball{x}{r}$<!-- chapter-correspondence-end: baire-next -->.

<!-- chapter-correspondence
{
  "scope": "baire-selected-sequence",
  "context": {
    "declaration": "PolishSpaceBook.baire_open_intersection",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.arg.body.body.arg",
      "body.body.fn.fn.body.body.body",
      "body.body.body.arg.body.body.value"
    ]
  },
  "bindings": {
    "sequence-x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": "x"
    },
    "limit-x": {
      "symbol": "x",
      "occurrence": "unsubscripted",
      "target": "y"
    },
    "var-n": {
      "symbol": "n",
      "target": "n"
    },
    "var-G": {
      "symbol": "G",
      "target": "G"
    },
    "var-V": {
      "symbol": "V",
      "target": "V"
    },
    "var-U": {
      "symbol": "U",
      "target": "U"
    },
    "var-X": {
      "symbol": "X",
      "target": "Y"
    },
    "var-d": {
      "symbol": "d",
      "target": "book_hyg_1"
    }
  }
}
-->

Pick $x_n\in V_n$. The nesting and diameter bounds make $\Sequence{x_n}{n\in\omega}$ Cauchy:
for <!-- chapter-correspondence
{
  "scope": "baire-tail",
  "context": {
    "declaration": "PolishSpaceBook.baire_open_intersection",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.arg.body.body.arg",
      "body.body.fn.fn.body.body.body",
      "value.body.body"
    ]
  },
  "bindings": {
    "n": {
      "symbol": "n",
      "target": "n"
    },
    "m": {
      "symbol": "m",
      "target": "m"
    },
    "V": {
      "symbol": "V",
      "target": "V"
    },
    "x": {
      "symbol": "x",
      "occurrence": "subscript-base",
      "target": "x"
    }
  }
}
-->$m\ge n$, both $x_m$
and $x_n$ lie in
$\Closure{V_n}$, whose diameter is at most $2^{-n}$<!-- chapter-correspondence-end: baire-tail -->.
Completeness gives a limit $x\in X$. Since each $\Closure{V_n}$ is
closed and contains the tail of the sequence, $x\in\Closure{V_n}$ for every $n$. The nesting also gives
$\Closure{V_{n+1}}\IncludedIn G_n$, so $x\in G_n$ for every $n$, and $x\in U$. Thus $U\cap\bigcap_n G_n\ne\emptyset$
whenever $\Sequence{G_n}{n\in\omega}$ are dense open in $U$'s relative topology.

<!-- chapter-correspondence-end: baire-selected-sequence -->

<!-- chapter-correspondence
{
  "scope": "baire-global-family",
  "bindings": {
    "var-G": {
      "symbol": "G",
      "target": "G"
    },
    "var-U": {
      "symbol": "U",
      "target": "U"
    },
    "var-n": {
      "symbol": "n",
      "reason": "Local index binding has no reviewed extraction rule."
    },
    "var-X": {
      "symbol": "X",
      "target": "Y"
    }
  },
  "context": {
    "declaration": "PolishSpaceBook.completely_metrizable_baire_space_book",
    "path": [
      "root.body.body.body.body.body.body",
      "arg.body.body.body.body.arg.body",
      "body.body.body.body.body"
    ]
  }
}
-->

To prove the theorem, fix $\Sequence{G_n}{n\in\omega}$ dense open in $X$ and let $U$ be an arbitrary nonempty open set.
The traces
<!-- chapter-correspondence
{
  "scope": "baire-trace",
  "context": {
    "declaration": "PolishSpaceBook.completely_metrizable_baire_space_book",
    "path": [
      "root.body.body.body.body.body.body",
      "arg.body.body.body.body.arg.body",
      "body.body.body.value"
    ]
  },
  "bindings": {
    "n": {
      "symbol": "n",
      "target": "n"
    },
    "G": {
      "symbol": "G",
      "target": "G"
    },
    "U": {
      "symbol": "U",
      "target": "U"
    }
  }
}
-->$G_n\cap U$<!-- chapter-correspondence-end: baire-trace --> are dense open in $U$'s relative topology,
and $U\cap\bigcap_n(G_n\cap U)=U\cap\bigcap_n G_n$, so the
construction above gives $U\cap\bigcap_n G_n\ne\emptyset$. Since $U$ was arbitrary, $\bigcap_n G_n$ is dense in $X$.

<!-- chapter-correspondence-end: baire-global-family -->

<!-- chapter-correspondence
{
  "scope": "baire-meager-open",
  "bindings": {
    "var-U": {
      "symbol": "U",
      "target": "relativeSpace"
    },
    "var-N": {
      "symbol": "N",
      "target": "N"
    },
    "var-n": {
      "symbol": "n",
      "target": "n"
    }
  },
  "context": {
    "declaration": "PolishSpaceBook.nonempty_open_not_meagre_in_itself",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.arg.body.arg",
      "body.body.arg.body.body.arg.body",
      "body.fn.arg.body.arg.body.body",
      "body.body.body.body.body.value"
    ]
  }
}
-->

Now suppose a nonempty open $U$ were meager in itself, say $U=\bigcup_n N_n$ with each $N_n$ nowhere dense in $U$. Then
$\SetDifference{U}{\AmbientClosure{U}{N_n}}$ is dense open in $U$ for each $n$, so the first part gives a point in their
intersection, contradicting $U=\bigcup_n N_n$.
\end{proof}

<!-- chapter-correspondence-end: baire-meager-open -->

<!-- chapter-correspondence-end: baire-proof -->

\begin{mathmeta}
  \forward{BaireSpace}
\end{mathmeta}

<!-- formalization: skip (terminology clarification, not a proof obligation) -->
This use of "Baire" is distinct from the specific \termforward{Baire space} $\BaireSpace$ introduced in
§{sec:sequence-spaces}. The theorem says every Polish space is a
\termuseas{Baire space (category sense)}{Baire space} in the category sense; Baire space is one particular Polish space
that serves as a universal coding space.

<!-- chapter-correspondence-end: baire-category -->

## Alexandrov's Theorem {#sec:alexandrov-theorem}

<!-- chapter-correspondence
{
  "scope": "alexandrov-theorem",
  "bindings": {
    "var-A": {"symbol": "A", "target": "PolishSpaceBook.alexandrov_theorem/A"},
    "var-X": {"symbol": "X", "target": "PolishSpaceBook.alexandrov_theorem/X"}
  }
}
-->

\begin{mathmeta}
  \define{Fsigma,Gdelta}
\end{mathmeta}

A subset of a topological space is \termdefineas{Fsigma set@$\Fsigma$ set}{$\Fsigma$} if it is a countable union of
closed sets, and \termdefineas{Gdelta set@$\Gdelta$ set}{$\Gdelta$} if it is a countable intersection of open sets.


\begin{theorem*}[\termdefineas{Alexandrov's theorem}{Theorem (Alexandrov)}]
Let $X$ be a Polish space and $A \IncludedIn X$. Then $A$ is Polish in the subspace topology if and only if $A$ is
$\Gdelta$ in $X$.

\end{theorem*}


<!-- formalization: skip (prose restatement of Alexandrov's theorem, which is itself formalized) -->
Thus $\Gdelta$ subsets are exactly the Polish subspaces of Polish spaces. This is why the irrationals are Polish
although the inherited Euclidean metric on $\SetDifference{\R}{\QQ}$ is incomplete.

<!-- chapter-correspondence
{
  "scope": "alexandrov-proof",
  "bindings": {
    "var-B": {"symbol": "B", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-F": {"symbol": "F", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-U": {"symbol": "U", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-V": {"symbol": "V", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-delta": {"symbol": "\\delta", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-iota": {"symbol": "\\iota", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-rho": {"symbol": "\\rho", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-a": {"symbol": "a", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-b": {"symbol": "b", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-d": {"symbol": "d", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-k": {"symbol": "k", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-n": {"symbol": "n", "reason": "Local symbol has no reviewed Lean binder mapping."},
    "var-x": {"symbol": "x", "reason": "Local symbol has no reviewed Lean binder mapping."}
  }
}
-->

\begin{proof}[Proof]

\textbf{From $\Gdelta$ to Polish.} <!-- chapter-correspondence
{
  "scope": "alexandrov-forward",
  "context": {
    "declaration": "PolishSpaceBook.gdelta_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg",
      "body.body.arg.body.body.body.body",
      "value.arg"
    ]
  },
  "bindings": {
    "var-A": {
      "symbol": "A",
      "target": "s"
    },
    "var-X": {
      "symbol": "X",
      "target": "X"
    },
    "var-U": {
      "symbol": "U",
      "target": "U"
    },
    "var-\\iota": {
      "symbol": "\\iota",
      "target": "diag"
    },
    "var-n": {
      "symbol": "n",
      "target": "n"
    }
  }
}
--> Write
$$A = \bigcap_{n \in \omega} U_n$$
with each $U_n \IncludedIn X$ open. By the open-subspace result above, each $U_n$ is Polish.

The diagonal embedding
$$\iota : A \to \prod_{n} U_n, \qquad \iota(x) = \Tuple{x, x, x, \ldots}$$
is a homeomorphism onto its image. By the universal property of the product topology, the coordinate inclusions
$A \hookrightarrow U_n$ assemble into the continuous map $\iota$; by the universal property of the subspace topology,
the zeroth-coordinate projection restricts to a continuous inverse on $\iota(A)$.
The product $\prod_n U_n$ is Polish.

We show that $\iota(A)$ is closed in <!-- chapter-correspondence
{
  "scope": "alexandrov-closed-sequence",
  "context": {
    "declaration": "PolishSpaceBook.gdelta_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg",
      "body.body.arg.body.body.body.body",
      "body.body.body.body.value.arg.body",
      "body.body.body.fn.fn.body.body",
      "value.body.body.value.arg"
    ]
  },
  "bindings": {
    "var-A": {
      "symbol": "A",
      "target": "s"
    },
    "var-X": {
      "symbol": "X",
      "target": "X"
    },
    "var-U": {
      "symbol": "U",
      "target": "U"
    },
    "var-\\iota": {
      "symbol": "\\iota",
      "target": "diag"
    },
    "var-n": {
      "symbol": "n",
      "target": "n"
    },
    "var-b": {
      "symbol": "b",
      "target": "b"
    },
    "var-a": {
      "symbol": "a",
      "target": "a",
      "occurrence": "superscript-base"
    },
    "var-k": {
      "symbol": "k",
      "target": "k"
    }
  }
}
-->$\prod_n U_n$; since the product is metrizable, it suffices to check closedness on
convergent sequences. Suppose
$$\iota(a^k)=\Tuple{a^k,a^k,\ldots}$$
converges in the product to $\Sequence{b_n}{n\in\omega}$. Then $a^k \to b_n$ in each $U_n$, hence also in $X$.
<!-- chapter-correspondence
{
  "scope": "alexandrov-common-limit",
  "context": {
    "declaration": "PolishSpaceBook.gdelta_subspace_polish",
    "path": [
      "root.body.body.body.body.body.arg",
      "body.body.arg.body.body.body.body",
      "body.body.body.body.value.arg.body",
      "body.body.body.fn.fn.body.body",
      "body.body.body.body.body.value.arg"
    ]
  },
  "bindings": {
    "var-A": {
      "symbol": "A",
      "target": "s"
    },
    "var-X": {
      "symbol": "X",
      "target": "X"
    },
    "var-U": {
      "symbol": "U",
      "target": "U"
    },
    "var-\\iota": {
      "symbol": "\\iota",
      "target": "diag"
    },
    "var-n": {
      "symbol": "n",
      "target": "n"
    },
    "var-b": {
      "symbol": "b",
      "target": "b"
    },
    "var-x": {
      "symbol": "x",
      "target": "x"
    }
  }
}
-->Since $X$
is
Hausdorff, limits in $X$ are unique, so all $b_n$ are one and the same point $x$. Because $x=b_n \in U_n$ for every $n$,
we have $x \in A$, hence $\Sequence{b_n}{n\in\omega} = \iota(x) \in \iota(A)$.
<!-- chapter-correspondence-end: alexandrov-common-limit -->
<!-- chapter-correspondence-end: alexandrov-closed-sequence -->

Thus $\iota(A)$ is closed. Hence $A$ is homeomorphic to a closed subspace of a Polish space, and is Polish.
<!-- chapter-correspondence-end: alexandrov-forward -->

<!-- chapter-correspondence
{
  "scope": "alexandrov-converse-metrics",
  "context": {
    "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body"
    ]
  },
  "bindings": {
    "var-A": {
      "symbol": "A",
      "target": "A"
    },
    "var-X": {
      "symbol": "X",
      "target": "X"
    },
    "var-d": {
      "symbol": "d",
      "target": "this"
    },
    "var-\\rho": {
      "symbol": "\\rho",
      "target": "this_book_9"
    },
    "var-V": {
      "symbol": "V",
      "target": "V"
    },
    "var-n": {
      "symbol": "n",
      "target": {
        "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
        "path": [
          "root.body.body.body.body.body.body",
          "body.body.body.body.body.body.body",
          "body.body.body.body.body.body.body",
          "body.value"
        ],
        "binder": "n"
      }
    }
  }
}
-->
\textbf{From Polish to $\Gdelta$.} Suppose $A$ carries a complete metric $\rho$ inducing the subspace topology from $X$,
and fix a compatible metric $d$ on $X$. For each $n \in \omega$, using explicit $d$-balls in $X$, define
<!-- chapter-correspondence
{
  "scope": "alexandrov-ball-union",
  "context": {
    "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.value"
    ]
  },
  "bindings": {
    "A": {
      "symbol": "A",
      "target": "A"
    },
    "X": {
      "symbol": "X",
      "target": "X"
    },
    "d": {
      "symbol": "d",
      "target": "this"
    },
    "rho": {
      "symbol": "\\rho",
      "target": "this_book_9"
    },
    "V": {
      "symbol": "V",
      "target": "V"
    },
    "n": {
      "symbol": "n",
      "target": "n"
    }
  },
  "restrictions": [
    {
      "kind": "bounded-trace",
      "premise": "alexandrov-bounded-traces",
      "metric": "rho",
      "subset": "A"
    }
  ]
}
-->
$$V_n \;=\; \bigcup\, \{\MetricBall{d}{x}{\delta} \,:\, x \in X,\; \delta > 0,\;
\MetricDiameter{\rho}{\MetricBall{d}{x}{\delta} \cap A} < 1/(n+1)\},$$
<!-- chapter-correspondence-premise: alexandrov-bounded-traces -->
where only balls whose trace on $A$ is $\rho$-bounded are included in the union.
<!-- chapter-correspondence-premise-end: alexandrov-bounded-traces -->
<!-- chapter-correspondence-end: alexandrov-ball-union --> Each $V_n$ is open, being a union
of open $d$-balls in $X$. Since $\rho$ induces the subspace topology on $A$, every
point of $A$ has arbitrarily small $X$-neighborhoods whose trace on $A$ has small $\rho$-diameter, so
$A \IncludedIn V_n$ for every $n \in \omega$.

We claim $A = \AmbientClosure{X}{A} \cap \bigcap_{n\in\omega} V_n$,
where $\AmbientClosure{X}{A}$ denotes the closure of $A$
in $X$.
The closure factor excludes points away from $A$; the $V_n$'s force nearby traces of $A$ to have vanishing
$\rho$-diameter.

The inclusion $A \IncludedIn \AmbientClosure{X}{A} \cap \bigcap_{n\in\omega} V_n$ follows immediately from the preceding
paragraph.

<!-- chapter-correspondence
{
  "scope": "alexandrov-converse-point",
  "context": {
    "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.value.body.body"
    ]
  },
  "bindings": {
    "var-x": {
      "symbol": "x",
      "target": "x"
    }
  }
}
-->
For the reverse inclusion, take
$$x \in \AmbientClosure{X}{A} \cap \bigcap_{n\in\omega} V_n.$$
<!-- chapter-correspondence
{
  "scope": "alexandrov-chosen-neighborhoods",
  "context": {
    "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.value.body.body.body",
      "body.body.fn.fn.body.body.body",
      "body.body.body.body.body.body.body",
      "value"
    ]
  },
  "bindings": {
    "B": {
      "symbol": "B",
      "target": "U"
    },
    "n": {
      "symbol": "n",
      "target": "N"
    }
  }
}
-->
For each $n \in \omega$, choose an open neighborhood $B_n$ of $x$ in $X$ such that
$$\MetricDiameter{\rho}{B_n \cap A} < 1/(n+1).$$
Replacing $B_n$ by
$$B_0 \cap \cdots \cap B_n \cap \MetricBall{d}{x}{1/(n+1)},$$
we may assume
<!-- chapter-correspondence-end: alexandrov-chosen-neighborhoods -->
<!-- chapter-correspondence
{
  "scope": "alexandrov-shrunk-neighborhoods",
  "context": {
    "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.value.body.body.body",
      "body.body.fn.fn.body.body.body",
      "body.body.body.body.body.body.body",
      "value"
    ]
  },
  "bindings": {
    "B": {
      "symbol": "B",
      "target": "W"
    },
    "n": {
      "symbol": "n",
      "target": "N"
    },
    "a": {
      "symbol": "a",
      "target": "aSeq",
      "occurrence": "subscript-base"
    }
  }
}
-->
$$B_0 \supseteq B_1 \supseteq \cdots
\qquad\text{and}\qquad
\MetricDiameter{d}{B_n}\to 0.$$
Since $x \in \AmbientClosure{X}{A}$, every $B_n$ meets $A$. Choose $a_n \in B_n \cap A$.
<!-- chapter-correspondence-end: alexandrov-shrunk-neighborhoods -->


<!-- chapter-correspondence
{
  "scope": "alexandrov-converse-limits",
  "context": {
    "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.value.body.body.body",
      "body.body.fn.fn.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.arg.body.body"
    ]
  },
  "bindings": {
    "a-sequence": {
      "symbol": "a",
      "occurrence": "subscript-base",
      "target": "aSeq"
    },
    "a-limit": {
      "symbol": "a",
      "occurrence": "unsubscripted",
      "target": "a"
    },
    "B": {
      "symbol": "B",
      "target": "W"
    },
    "n": {
      "symbol": "n",
      "target": {
        "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
        "path": [
          "root.body.body.body.body.body.body",
          "body.body.body.body.body.body.body",
          "body.body.body.body.body.body.body",
          "body.body.body.value.body.body.body",
          "body.body.fn.fn.body.body.body",
          "body.body.body.body.body.body.body",
          "body.body.arg.body.body.body.value",
          "arg.body.body.arg.body.body.arg",
          "body.body"
        ],
        "binder": "n"
      }
    },
    "bound-witness": {
      "symbol": "bound",
      "target": "bound"
    }
  },
  "numerals": {
    "type": "Real",
    "from": "bound-witness"
  }
}
-->
The sequence $\Sequence{a_n}{n\in\omega}$ is $\rho$-Cauchy because
the $\rho$-diameters of the traces $B_n \cap A$ tend to
$0$. Since $\rho$
is complete, $a_n \to a$ in $\rho$ for some $a \in A$. <!-- chapter-correspondence
{
  "scope": "alexandrov-converse-ambient-limit",
  "context": {
    "declaration": "PolishSpaceBook.polish_subspace_isGdelta",
    "path": [
      "root.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.body.value.body.body.body",
      "body.body.fn.fn.body.body.body",
      "body.body.body.body.body.body.body",
      "body.body.arg.body.body"
    ]
  },
  "bindings": {
    "a-limit": {
      "symbol": "a",
      "occurrence": "unsubscripted",
      "target": "a",
      "projection": "Subtype.val"
    }
  }
}
-->
The $\rho$-topology agrees with the subspace topology, so $a_n
\to a$ in $X$. On the other hand, $\MetricDiameter{d}{B_n}\to 0$ and $a_n \in B_n$ force $a_n \to x$ in $X$. Uniqueness
of limits in the metric space $X$ gives $a=x$, hence $x \in A$.
<!-- chapter-correspondence-end: alexandrov-converse-ambient-limit -->
<!-- chapter-correspondence-end: alexandrov-converse-limits -->
<!-- chapter-correspondence-end: alexandrov-converse-point -->


The set $\AmbientClosure{X}{A}$ is closed, and closed subsets of metric spaces are $\Gdelta$. The empty set is open and
hence $\Gdelta$. <!-- chapter-correspondence
{
  "scope": "alexandrov-closed-distance",
  "context": {
    "declaration": "PolishSpaceBook.isGδ_of_isClosed_metric_neighborhoods",
    "path": [
      "root.body.body.body.body.arg.body"
    ]
  },
  "bindings": {
    "set-F": {
      "symbol": "F",
      "target": "s"
    },
    "space-X": {
      "symbol": "X",
      "target": "Z"
    },
    "metric-d": {
      "symbol": "d",
      "target": "book_hyg_1"
    }
  }
}
-->
If $F\ne\emptyset$ is closed, then
$$
F = \bigcap_{n \in \omega} \{x \in X : d(x,F) < 1/(n+1)\},
$$
a countable intersection of open sets.
<!-- chapter-correspondence-end: alexandrov-closed-distance -->
Also, $\bigcap_{n\in\omega} V_n$ is $\Gdelta$ because each $V_n$ is open. Therefore
$$A=\AmbientClosure{X}{A}\cap\bigcap_{n\in\omega} V_n$$
is $\Gdelta$ in $X$.
<!-- chapter-correspondence-end: alexandrov-converse-metrics -->
\end{proof}

<!-- chapter-correspondence-end: alexandrov-proof -->

\begin{proposition*}[Rationals and irrationals]
In $\R$ with its usual topology, the rationals $\QQ$ are $\Fsigma$ but not $\Gdelta$, and the irrationals
$\SetDifference{\R}{\QQ}$ are $\Gdelta$ but not
$\Fsigma$.
\end{proposition*}

<!-- chapter-correspondence
{
  "scope": "rationals-proof",
  "rationalSingletons": {"ambient": "Real"},
  "bindings": {}
}
-->

\begin{proof}[Proof]
The rationals $\QQ = \bigcup_{q \in \QQ} \{q\}$ are $\Fsigma$, since singletons are closed. They are not $\Gdelta$:
$\QQ$ is meager, since each singleton is closed and nowhere dense, while a dense $\Gdelta$ subset of $\R$ is comeager
since its complement is a countable union of closed sets with empty interior. If $\QQ$ were $\Gdelta$, it would be
both meager and comeager, so its complement $\SetDifference{\R}{\QQ}$ would also be meager. Then $\R$ would be a
union of two \termuseas{meager set}{meager sets}, contradicting the \termuse{Baire category theorem} in
§{sec:baire-category}. By duality, the irrationals $\SetDifference{\R}{\QQ}$ are $\Gdelta$ but not $\Fsigma$.
\end{proof}

<!-- chapter-correspondence-end: rationals-proof -->

<!-- formalization: skip (discussion linking the example/non-example to Alexandrov's theorem) -->
Thus \termuse{Alexandrov's theorem} proves that $\SetDifference{\R}{\QQ}$ is Polish in the subspace topology, while
$\QQ$ is not
Polish in the subspace topology. This supplies the example and non-example recorded at the start of the chapter.

<!-- chapter-correspondence-end: alexandrov-theorem -->

## Sequence Spaces {#sec:sequence-spaces}

<!-- chapter-correspondence
{
  "scope": "sequence-spaces",
  "bindings": {
    "var-x": {
      "symbol": "x",
      "target": "PolishSpaceBook.IsIsolatedPointByOpenSingleton/x"
    }
  }
}
-->

\begin{mathmeta}
  \define{BaireSpace,CantorSpace,TwoPointSpace,HilbertCube,RealSequenceSpace,Homeomorphic}
\end{mathmeta}

A topological space is \termdefine{zero-dimensional} if it has a base
of clopen sets.

The name zero-dimensional reflects the equivalence of this condition with having small inductive dimension
at most $\NonnegativeDimensionLevel{0}$.
For separable metrizable spaces, having large inductive dimension at most
 $\NonnegativeDimensionLevel{0}$ and having Lebesgue covering dimension at most
 $\NonnegativeDimensionLevel{0}$ are also equivalent to this condition.
<!-- formalization: skip-begin (dimension-theory reference and appendix navigation) -->
<!-- formalization: skip (reference for dimension theory) -->
The definitions and the equivalence at dimension $\NonnegativeDimensionLevel{0}$ are explained in
\BookSectionLink{sec:appendix-zero-dimension}{the section on zero dimension}.
For the general theory, see [@Engelking1995].
<!-- formalization: skip-end -->


A point $x$ of a topological space is an \termdefine{isolated point} if $\{x\}$ is open. A space is
\termdefineas{perfect space}{perfect} if it has no isolated points.


Here $\TwoPointSpace$ and $\omega$ are countable discrete spaces, hence Polish because their discrete
metrics are complete and the
spaces are countable. Also $\ClosedInterval{0}{1}$ is a closed subspace of $\R$, and $\R$ itself is Polish.
Hence the countable-products
proposition gives the following standard Polish product spaces, each with the product topology:

*   The \termdefine{Cantor space} $\CantorSpace$.
    \termforwardas{Brouwer's Cantor-space characterization}{Brouwer's characterization} in
    \BookSectionLink{sec:clopen-scheme-characterizations}{the next chapter} identifies it as the compact
    zero-dimensional \termuseas{perfect space}{perfect} model.
*   The \termdefine{Baire space} $\BaireSpace$. The
    \termforwardas{Alexandrov--Urysohn theorem}{Alexandrov--Urysohn characterization} in
    \BookSectionLink{sec:clopen-scheme-characterizations}{the next chapter} identifies it as the nowhere
    locally compact analogue of Cantor space.
*   The \termdefine{Hilbert cube} $\HilbertCube$. The Hilbert cube is compact by Tychonoff, and it is the
    universal compact target for Polish spaces: the
    \termforwardas{Hilbert-cube embedding}{Hilbert-cube embedding theorem} in
    \BookSectionLink{sec:hilbert-cube-embedding}{The Hilbert Cube and Universal Compact Embedding} shows that every
    Polish space is
    homeomorphic to a subspace of $\HilbertCube$.
*   The \termdefine{space of real sequences} $\RealSequenceSpace$. Anderson's theorem gives a homeomorphism
    $\Homeomorphic{\RealSequenceSpace}{\ell^2}$, and
    Anderson--Kadec says that every infinite-dimensional separable Fréchet
    space, hence every infinite-dimensional separable Banach space, is homeomorphic to $\ell^2$; see
    [@BessagaPelczynski1975] for the infinite-dimensional topology behind these statements. Thus every
    infinite-dimensional separable Banach space from §{sec:polish-examples} is homeomorphic to
    $\RealSequenceSpace$.

The following quick invariants separate the four examples up to homeomorphism. Tychonoff's theorem makes $\CantorSpace$
and $\HilbertCube$ compact, because $\TwoPointSpace$ and $\ClosedInterval{0}{1}$ are compact.
The spaces $\BaireSpace$ and
$\RealSequenceSpace$ are not compact: if either product were compact, then each coordinate projection would have
compact image, forcing $\omega$ or $\R$ to be compact. The spaces $\CantorSpace$ and $\BaireSpace$ have clopen
\termforward{cylinder} bases, so they are zero-dimensional. Products of connected spaces are connected, so
$\HilbertCube$ and $\RealSequenceSpace$ are connected. Since both products are Hausdorff and have more than one point,
neither can be zero-dimensional: a clopen basic neighborhood of one point inside the complement of another would
disconnect the space.
In each of $\CantorSpace$ and $\BaireSpace$, the \termforward{cylinder} consisting of sequences whose initial term is
<!-- chapter-correspondence
{
  "scope": "initial-zero",
  "bindings": {},
  "literalInterpretations": [
    {
      "id": "cantor",
      "constant": "Bool.false",
      "consumer": {
        "declaration": "PolishSpaceBook.cantor_space_not_connected",
        "callee": "PolishSpaceBook.not_connected_of_initialSymbolCylinder",
        "argumentPosition": 3
      }
    },
    {
      "id": "baire",
      "constant": "Nat.zero",
      "consumer": {
        "declaration": "PolishSpaceBook.baire_space_not_connected",
        "callee": "PolishSpaceBook.not_connected_of_initialSymbolCylinder",
        "argumentPosition": 3
      }
    }
  ]
}
-->$0$<!-- chapter-correspondence-end: initial-zero -->
is nonempty, proper, and clopen, so both spaces are disconnected.


<!-- formalization: skip (comparison-table markup; the entries restate the facts proved just above) -->

| space | compact? | zero-dimensional? | connected? |
|:---:|:---:|:---:|:---:|
| $\CantorSpace$ | yes | yes | no |
| $\BaireSpace$ | no | yes | no |
| $\HilbertCube$ | yes | no | yes |
| $\RealSequenceSpace$ | no | no | yes |

<!-- formalization: skip (concluding outlook paragraph; motivational, not a proof obligation) -->
These sequence spaces recur throughout the book. We use Cantor space to study compact zero-dimensional spaces and
Baire space to encode objects by finite information. The Hilbert cube serves as an ambient space for embeddings of
Polish spaces, and $\RealSequenceSpace$ is used in the analysis of infinite-dimensional separable spaces.
Baire space plays the central role,
because a Cauchy-name representation gives a continuous surjection from a closed subspace of $\BaireSpace$ onto
any Polish space.

<!-- chapter-correspondence-end: sequence-spaces -->
