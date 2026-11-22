module

public import PolishSpaceBook.SetTheoryCountableOrdinals

@[expose] public section

/-! # Cardinals, beth recursion, and the first uncountable ordinal -/

namespace PolishSpaceBook.SetTheoryModels
open Cardinal Ordinal Order
universe u

/-- Cardinal comparison is exactly the existence of an injection. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
    cardinal, defined as the least ordinal of that cardinality.
    \begin{mathmeta}
      \define{alephNull,alephCard}
    \end{mathmeta}
    The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
    \begin{mathmeta}
      \define{bethCard}
    \end{mathmeta}
    The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
    $$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
    \sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
    A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
    and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
    §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem cardinality_le_iff_embedding (X Y : Type u) :
    Cardinal.mk X ≤ Cardinal.mk Y ↔ Nonempty (X ↪ Y) := Cardinal.le_def X Y

/-- Every type is bijective with the representative of exactly one cardinal. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
    cardinal, defined as the least ordinal of that cardinality.
    \begin{mathmeta}
      \define{alephNull,alephCard}
    \end{mathmeta}
    The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
    \begin{mathmeta}
      \define{bethCard}
    \end{mathmeta}
    The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
    $$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
    \sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
    A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
    and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
    §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem unique_cardinal_representative (X : Type u) :
    ∃! c : Cardinal.{u}, Nonempty (X ≃ c.out) := by
  refine ⟨Cardinal.mk X, Cardinal.eq.mp (by simp), ?_⟩
  intro c hc
  simpa using (Cardinal.eq.mpr hc).symm

/-- The ordinal representative of a cardinal is the least ordinal with that cardinality. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
    cardinal, defined as the least ordinal of that cardinality.
    \begin{mathmeta}
      \define{alephNull,alephCard}
    \end{mathmeta}
    The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
    \begin{mathmeta}
      \define{bethCard}
    \end{mathmeta}
    The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
    $$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
    \sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
    A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
    and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
    §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem cardinal_ordinal_least (c : Cardinal.{u}) :
    c.ord.card = c ∧ ∀ a : Ordinal.{u}, a.card = c → c.ord ≤ a := by
  refine ⟨Cardinal.card_ord c, ?_⟩
  intro a ha
  simpa only [ha] using Cardinal.ord_card_le a

/-- Alephs enumerate precisely the infinite cardinals and increase strictly. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
    cardinal, defined as the least ordinal of that cardinality.
    \begin{mathmeta}
      \define{alephNull,alephCard}
    \end{mathmeta}
    The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
    \begin{mathmeta}
      \define{bethCard}
    \end{mathmeta}
    The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
    $$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
    \sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
    A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
    and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
    §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem infinite_cardinals_aleph (c : Cardinal.{u}) :
    (ℵ₀ ≤ c ↔ ∃ a : Ordinal.{u}, Cardinal.aleph a = c) ∧ StrictMono Cardinal.aleph := by
  exact ⟨(Cardinal.mem_range_aleph_iff).symm, Cardinal.isNormal_aleph.strictMono⟩

/-- The zero and successor clauses of beth recursion. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
    cardinal, defined as the least ordinal of that cardinality.
    \begin{mathmeta}
      \define{alephNull,alephCard}
    \end{mathmeta}
    The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
    \begin{mathmeta}
      \define{bethCard}
    \end{mathmeta}
    The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
    $$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
    \sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
    A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
    and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
    §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem beth_recursion (a : Ordinal.{u}) :
    Cardinal.beth 0 = ℵ₀ ∧ Cardinal.beth (a + 1) = 2 ^ Cardinal.beth a :=
  ⟨Cardinal.beth_zero, Cardinal.beth_add_one a⟩

/-- The limit clause of beth recursion takes the cardinal supremum. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
    cardinal, defined as the least ordinal of that cardinality.
    \begin{mathmeta}
      \define{alephNull,alephCard}
    \end{mathmeta}
    The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
    \begin{mathmeta}
      \define{bethCard}
    \end{mathmeta}
    The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
    $$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
    \sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
    A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
    and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
    §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem beth_limit_recursion (l : Ordinal.{u}) (hl : IsSuccLimit l) :
    Cardinal.beth l = ⨆ a : Set.Iio l, Cardinal.beth a.val := Cardinal.beth_limit hl

/-- Countability allows finite sets: it means injection into the natural numbers. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
    cardinal, defined as the least ordinal of that cardinality.
    \begin{mathmeta}
      \define{alephNull,alephCard}
    \end{mathmeta}
    The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
    \begin{mathmeta}
      \define{bethCard}
    \end{mathmeta}
    The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
    $$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
    \sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
    A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
    and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
    §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem countable_iff_injection_omega (X : Type u) :
    Countable X ↔ Nonempty (X ↪ ℕ) := countable_iff_nonempty_embedding

/-- Countability of an ordinal as a set is exactly the cardinal bound. -/
theorem ordinal_set_countable_iff (a : Ordinal.{u}) :
    Countable a.toZFSet ↔ a.card ≤ ℵ₀ := by
  refine ⟨?_, countable_ordinal_set⟩
  intro h
  have hmk := Cardinal.mk_le_aleph0_iff.mpr h
  rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet] at hmk
  exact Cardinal.lift_le.{u + 1}.mp (by simpa using hmk)

/-- The first uncountable ordinal is the cutoff for countable ordinal sets. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The first infinite ordinal $\omega$ has cardinality $\alephNull$ and is countably infinite. All ordinals between
    $\omega$ and the **first uncountable ordinal** $\omegaOneOrd$ — that is, $\omega, \omega+1, \omega \cdot 2,
    \omega^\omega, \varepsilon_0, \ldots$ — are countable as sets, however baroque their order type. The ordinal
    $\omegaOneOrd$ itself is uncountable, of cardinality $\alephCard{1}$, and equals the set of all countable
    ordinals.
-/
theorem ordinal_set_countable_iff_lt_omega_one (a : Ordinal.{u}) :
    Countable a.toZFSet ↔ a < Ordinal.omega 1 := by
  rw [ordinal_set_countable_iff, Cardinal.lt_omega_iff_card_lt]
  exact Cardinal.lt_aleph_one_iff.symm

/-- The members of omega-one are precisely the countable von Neumann ordinals. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The first infinite ordinal $\omega$ has cardinality $\alephNull$ and is countably infinite. All ordinals between
    $\omega$ and the **first uncountable ordinal** $\omegaOneOrd$ — that is, $\omega, \omega+1, \omega \cdot 2,
    \omega^\omega, \varepsilon_0, \ldots$ — are countable as sets, however baroque their order type. The ordinal
    $\omegaOneOrd$ itself is uncountable, of cardinality $\alephCard{1}$, and equals the set of all countable
    ordinals.
-/
theorem mem_omega_one_iff_countable_ordinal (x : ZFSet.{u}) :
    x ∈ (Ordinal.omega (1 : Ordinal.{u})).toZFSet ↔ x.IsOrdinal ∧ Countable x := by
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    exact ⟨ZFSet.isOrdinal_toZFSet a, (ordinal_set_countable_iff_lt_omega_one a).mpr ha⟩
  · rintro ⟨hx, hc⟩
    apply Ordinal.mem_toZFSet_iff.mpr
    refine ⟨x.rank, ?_, hx.toZFSet_rank_eq⟩
    apply (ordinal_set_countable_iff_lt_omega_one x.rank).mp
    simpa only [hx.toZFSet_rank_eq] using hc

/-- Omega is countably infinite, and omega-one is uncountable with cardinal aleph-one. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The first infinite ordinal $\omega$ has cardinality $\alephNull$ and is countably infinite. All ordinals between
    $\omega$ and the **first uncountable ordinal** $\omegaOneOrd$ — that is, $\omega, \omega+1, \omega \cdot 2,
    \omega^\omega, \varepsilon_0, \ldots$ — are countable as sets, however baroque their order type. The ordinal
    $\omegaOneOrd$ itself is uncountable, of cardinality $\alephCard{1}$, and equals the set of all countable
    ordinals.
-/
theorem omega_and_omega_one_cardinality :
    (Ordinal.omega0 : Ordinal.{u}).card = ℵ₀ ∧
    (Ordinal.omega (1 : Ordinal.{u})).card = Cardinal.aleph 1 ∧
    ¬Countable (Ordinal.omega (1 : Ordinal.{u})).toZFSet := by
  refine ⟨Ordinal.card_omega0, Ordinal.card_omega 1, ?_⟩
  rw [ordinal_set_countable_iff_lt_omega_one]
  exact lt_irrefl _

end PolishSpaceBook.SetTheoryModels
