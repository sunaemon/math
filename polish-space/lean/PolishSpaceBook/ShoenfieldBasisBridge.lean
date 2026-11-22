module

public import PolishSpaceBook.AnalyticTreeAbsoluteness
public import PolishSpaceBook.LambdaPairTrees
public import PolishSpaceBook.ForcingOrdinalPreservation

@[expose] public section

/-! # Shoenfield's local deduction from the cited basis and constructibility inputs

The coanalytic kernel has an actual lambda-decided pair-tree code at the fixed
real parameter. Its old-witness absoluteness is proved by internal section ranks.
The cited Kondo--Addison theorem supplies a constructible witness, and the cited
agreement of relative constructible hierarchies puts that witness in the smaller
model. Neither cited theorem is replaced by an axiom or claimed as proved here.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BorelExpression ForcingNames
universe u

/-- The models contain exactly the same actual ordinals. -/
def SameOrdinals (M N : ZFSet.{u}) : Prop :=
  ∀ α : ZFSet.{u}, α.IsOrdinal → (α ∈ M ↔ α ∈ N)

/-- Semantic reals of the two relative constructible universes, supplied by the
cited constructibility result. This is an input interface, not a definition of L[a]. -/
structure RelativeConstructibleInput (M N : ZFSet.{u}) (a : ℕ → ℕ) where
  smallReals : Set (ℕ → ℕ)
  largeReals : Set (ℕ → ℕ)
  small_internal : ∀ x ∈ smallReals, pointGraph x ∈ M
  large_internal : ∀ x ∈ largeReals, pointGraph x ∈ N
  agree : SameOrdinals M N → pointGraph a ∈ M → smallReals = largeReals

/-- The Σ¹₂ normal form is an existential old real followed by a coanalytic
kernel. The tree's decision program uses the original parameter a. -/
def InternalSigmaTwoTruth (K : ZFSet.{u}) {a : ℕ → ℕ} (T : LambdaTree.PairTree a) : Prop :=
  ∃ x : ℕ → ℕ, pointGraph x ∈ K ∧ ¬ InternalAnalyticTruth K T.tree x

/-- The cited basis theorem, specialized to this coanalytic kernel in N. -/
def CoanalyticBasisInput (N : ZFSet.{u}) {a : ℕ → ℕ} (T : LambdaTree.PairTree a)
    (constructibleReals : Set (ℕ → ℕ)) : Prop :=
  InternalSigmaTwoTruth N T →
    ∃ x ∈ constructibleReals, ¬ InternalAnalyticTruth N T.tree x

variable {M N : ZFSet.{u}} (hM : M.IsTransitive) (hN : N.IsTransitive) (hMN : M ⊆ N)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence)
include hM hN hMN hinf hpair hunion hpower hsep hrep hchoice

/-- A large-model witness is replaced by the constructible witness before
applying coanalytic absoluteness at an old real. -/
theorem sigma_two_absolute_from_basis {a : ℕ → ℕ} (T : LambdaTree.PairTree a)
    (hT : pairWordTreeSet T.tree ∈ M) (ha : pointGraph a ∈ M) (hord : SameOrdinals M N)
    (L : RelativeConstructibleInput M N a) (hbasis : CoanalyticBasisInput N T L.largeReals) :
    InternalSigmaTwoTruth M T ↔ InternalSigmaTwoTruth N T := by
  have hc (x : ℕ → ℕ) (hx : pointGraph x ∈ M) :
      (¬ InternalAnalyticTruth M T.tree x) ↔ ¬ InternalAnalyticTruth N T.tree x :=
    coanalytic_tree_absolute hM hN hMN hinf hpair hunion hpower hsep hrep hchoice
      T.tree T.synchronized T.downward hT x hx
  constructor
  · rintro ⟨x, hx, hkernel⟩
    exact ⟨x, hMN hx, (hc x hx).mp hkernel⟩
  · intro hlarge
    obtain ⟨x, hxL, hkernel⟩ := hbasis hlarge
    have hsame := L.agree hord ha
    have hxsmall : x ∈ L.smallReals := hsame.symm ▸ hxL
    have hx := L.small_internal x hxsmall
    exact ⟨x, hx, (hc x hx).mpr hkernel⟩

/-- Negating the Σ¹₂ normal form gives the Π¹₂ clause of the theorem. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{Shoenfield absoluteness theorem}{Shoenfield absoluteness}] If $M\IncludedIn N$ are
    transitive models of enough ZFC with the same ordinals, then $\bSigma^1_2$ and $\bPi^1_2$ formulas are
    \termuseas{absoluteness}{absolute} between $M$ and $N$ on real parameters from $M$. A forcing extension $M[G]$ has the
    same ordinals as $M$ by §{sec:generic-extension}, so the theorem applies to the pair $M\IncludedIn M[G]$.
    \end{theorem*}
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Assuming these cited inputs, suppose $N\models \exists x\,\forall y\,\psi(x,y,a)$. Then $A_a$ is nonempty in
    $N$. By the basis theorem inside $N$, choose $x\in A_a\cap L[a]^N$. Since $M$ and $N$ have the same ordinals and both
    contain $a$, the relative constructible hierarchy is the same in the two models [@Kunen1980]:
    $$
    L[a]^M=L[a]^N.
    $$
    Thus $x\in M$. The statement $x\in A_a$ is coanalytic, so by the analytic/coanalytic absoluteness proved above, $M$ also
    sees $x\in A_a$. Hence\termref{absoluteness}
    $$
    M\models \exists x\,\forall y\,\psi(x,y,a).
    $$
    The converse direction is easier: if $M$ has such an $x$, then $x\in N$, and coanalytic absoluteness transfers $\forall
    y\,\psi(x,y,a)$ from $M$ to $N$. Therefore $\bSigma^1_2$ formulas are \termuseas{absoluteness}{absolute} between $M$
    and $N$ on parameters from $M$. Applying this result to the negation proves $\bPi^1_2$
    absoluteness.\termref{absoluteness}
-/
theorem shoenfield_from_cited_inputs {a : ℕ → ℕ} (T : LambdaTree.PairTree a)
    (hT : pairWordTreeSet T.tree ∈ M) (ha : pointGraph a ∈ M) (hord : SameOrdinals M N)
    (L : RelativeConstructibleInput M N a) (hbasis : CoanalyticBasisInput N T L.largeReals) :
    (InternalSigmaTwoTruth M T ↔ InternalSigmaTwoTruth N T) ∧
      ((¬ InternalSigmaTwoTruth M T) ↔ ¬ InternalSigmaTwoTruth N T) := by
  have h := sigma_two_absolute_from_basis hM hN hMN hinf hpair hunion hpower hsep hrep hchoice
    T hT ha hord L hbasis
  exact ⟨h, not_congr h⟩

omit hN hMN hchoice in
/-- The existing forcing ordinal theorem supplies the same-ordinals premise. -/
theorem sameOrdinals_forcing_extension {P : ZFSet.{u}} (hP : P ∈ M)
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P) : SameOrdinals M (extension P M G) := by
  intro α hα
  exact (ordinal_mem_extension_iff_of_axioms hM hinf hpair hunion hpower hsep hrep hP G hG hα).symm

omit hN hMN in
/-- Apply the same local deduction to the actual name-evaluation extension,
using its proved transitivity, ground inclusion, and ordinal preservation. -/
theorem shoenfield_forcing_from_cited_inputs {P : ZFSet.{u}} (hP : P ∈ M)
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P)
    {a : ℕ → ℕ} (T : LambdaTree.PairTree a) (hT : pairWordTreeSet T.tree ∈ M)
    (ha : pointGraph a ∈ M) (L : RelativeConstructibleInput M (extension P M G) a)
    (hbasis : CoanalyticBasisInput (extension P M G) T L.largeReals) :
    (InternalSigmaTwoTruth M T ↔ InternalSigmaTwoTruth (extension P M G) T) ∧
      ((¬ InternalSigmaTwoTruth M T) ↔ ¬ InternalSigmaTwoTruth (extension P M G) T) := by
  exact shoenfield_from_cited_inputs hM (extension_isTransitive P M G hM)
    (ground_subset_extension_of_axioms hM hinf hpair hunion hpower hsep hrep hP G hG)
    hinf hpair hunion hpower hsep hrep hchoice T hT ha
    (sameOrdinals_forcing_extension hM hinf hpair hunion hpower hsep hrep hP G hG) L hbasis

end PolishSpaceBook.SetTheoryModels
