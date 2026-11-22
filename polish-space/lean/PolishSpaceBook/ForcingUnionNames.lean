module

public import PolishSpaceBook.ForcingAtomicTruth

@[expose] public section

/-! # A name for the union of an arbitrary name's valuation -/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open ZFSet ForcingAtomic
universe u

/-- A set containing every first coordinate occurring in a name. -/
def childBound (τ : ZFSet.{u}) : ZFSet.{u} := ZFSet.sUnion (ZFSet.sUnion τ)

/-- A set containing every first coordinate in a first-coordinate name. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Fix a name $\tau\in M^P$ and form
    $$A=\bigcup\bigcup\tau,\qquad D=\bigcup\bigcup\bigcup A.$$
-/
def grandchildBound (τ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (childBound τ)))

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Whenever $\langle\pi,p\rangle\in\tau$, we have $\pi\in A$.
    If also $\langle\sigma,r\rangle\in\pi$, then
    $$\sigma\in\{\sigma\}\in\langle\sigma,r\rangle\in\pi\in A,$$
    so $\sigma\in D$. These bounds depend only on $\tau$, not on the filter.
-/
lemma mem_grandchildBound {τ π σ p r : ZFSet.{u}}
    (hπ : pair π p ∈ τ) (hσ : pair σ r ∈ π) : σ ∈ grandchildBound τ := by
  have hπA : π ∈ childBound τ := child_mem_doubleUnion hπ
  have h₁ : pair σ r ∈ ZFSet.sUnion (childBound τ) := ZFSet.mem_sUnion.mpr ⟨π, hπA, hσ⟩
  have h₂ : ({σ} : ZFSet.{u}) ∈ ZFSet.sUnion (ZFSet.sUnion (childBound τ)) :=
    ZFSet.mem_sUnion.mpr ⟨pair σ r, h₁, by simp [pair]⟩
  exact ZFSet.mem_sUnion.mpr ⟨{σ}, h₂, by simp⟩

/-- All quantifiers in this predicate have explicit set bounds. R codes the refinement order. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Let $\rho$ be the subset of $D\times P$ consisting of the pairs $\langle\sigma,q\rangle$ for which
    $$\begin{aligned}
    \exists\pi\in A\,\exists p\in P\,\exists r\in P\,\bigl(
    &\langle\pi,p\rangle\in\tau\land\langle\sigma,r\rangle\in\pi\\
    &{}\land\langle q,p\rangle\in R\land\langle q,r\rangle\in R\bigr).
    \end{aligned}$$
    Thus $q$ simultaneously strengthens the two labels $p,r$.
-/
def unionPredicate (τ P R A D z : ZFSet.{u}) : Prop :=
  ∃ σ ∈ D, ∃ q ∈ P, ∃ π ∈ A, ∃ p ∈ P, ∃ r ∈ P,
    z = pair σ q ∧ pair π p ∈ τ ∧ pair σ r ∈ π ∧ pair q p ∈ R ∧ pair q r ∈ R

def unionOfName (P R τ : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod (grandchildBound τ) P).sep
    (unionPredicate τ P R (childBound τ) (grandchildBound τ))

lemma pair_mem_unionOfName {P R τ σ q : ZFSet.{u}} (hτ : IsName P τ) :
    pair σ q ∈ unionOfName P R τ ↔ q ∈ P ∧ ∃ π p r,
      pair π p ∈ τ ∧ pair σ r ∈ π ∧ pair q p ∈ R ∧ pair q r ∈ R := by
  rw [unionOfName, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, σ', _, q', hqP, π, _, p, _, r, _, heq, hπ, hσ, hqp, hqr⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp heq
    exact ⟨hqP, π, p, r, hπ, hσ, hqp, hqr⟩
  · rintro ⟨hqP, π, p, r, hπ, hσ, hqp, hqr⟩
    have hσD := mem_grandchildBound hπ hσ
    refine ⟨ZFSet.pair_mem_prod.mpr ⟨hσD, hqP⟩, ?_⟩
    exact ⟨σ, hσD, q, hqP, π, child_mem_doubleUnion hπ, p, hτ.condition hπ,
      r, (hτ.child hπ).condition hσ, rfl, hπ, hσ, hqp, hqr⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For a pair in $\rho$, the first coordinate is a name because $\tau$ is a name and the two displayed membership
    relations lead to its successive first-coordinate names. The second coordinate belongs to $P$, so $\rho$ is a
    $P$-name. Its definition does not require a separate test for being a name.
-/
lemma unionOfName_isName {P R τ : ZFSet.{u}} (hτ : IsName P τ) : IsName P (unionOfName P R τ) := by
  rw [isName_iff]
  constructor
  · intro z hz
    obtain ⟨σ, _, q, _, heq⟩ := ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
    exact ⟨σ, q, heq⟩
  · intro σ q h
    obtain ⟨hqP, π, p, r, hπ, hσ, _, _⟩ := (pair_mem_unionOfName hτ).mp h
    exact ⟨hqP, (hτ.child hπ).child hσ⟩

/-- Directedness supplies a common strengthening; upward closure recovers both active labels. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    We verify that $\rho^G=\bigcup\tau^G$ in both directions.
    If $x\in\rho^G$, take $\langle\sigma,q\rangle\in\rho$ with $q\in G$ and $x=\sigma^G$,
    and choose $\pi,p,r$ from the defining predicate. Since $q\le p,r$, upward closure puts $p,r$ in $G$.
    Consequently
    $$x=\sigma^G\in\pi^G\in\tau^G,$$
    so $x\in\bigcup\tau^G$.

    Conversely, if $x\in\bigcup\tau^G$, the valuation equation applied twice gives
    $\langle\pi,p\rangle\in\tau$ and $\langle\sigma,r\rangle\in\pi$ with $p,r\in G$ and $x=\sigma^G$.
    Choose a common strengthening $q\in G$ with $q\le p,r$, using downward directedness.
    The previously verified bounds give $\pi\in A$ and $\sigma\in D$, so $\langle\sigma,q\rangle\in\rho$.
    It follows that $x\in\rho^G$.
-/
theorem value_unionOfName (P R τ : ZFSet.{u}) [Preorder (Condition P)]
    (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q)
    (G : Order.PFilter (Condition P)) (hτ : IsName P τ) :
    value P G (unionOfName P R τ) = ZFSet.sUnion (value P G τ) := by
  apply ZFSet.ext
  intro x
  rw [mem_value, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨σ, q, hqG, hσq, hx⟩
    obtain ⟨_, π, p, r, hπ, hσ, hqp, hqr⟩ := (pair_mem_unionOfName hτ).mp hσq
    let pc : Condition P := ⟨p, hτ.condition hπ⟩
    let rc : Condition P := ⟨r, (hτ.child hπ).condition hσ⟩
    have hpG : pc ∈ G := G.mem_of_le ((hR q pc).mp hqp) hqG
    have hrG : rc ∈ G := G.mem_of_le ((hR q rc).mp hqr) hqG
    exact ⟨value P G π, (mem_value P G τ _).mpr ⟨π, pc, hpG, hπ, rfl⟩,
      (mem_value P G π x).mpr ⟨σ, rc, hrG, hσ, hx⟩⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨π, p, hpG, hπ, rfl⟩ := (mem_value P G τ y).mp hy
    obtain ⟨σ, r, hrG, hσ, hx⟩ := (mem_value P G π x).mp hxy
    obtain ⟨q, hqG, hqp, hqr⟩ := G.directed p hpG r hrG
    refine ⟨σ, q, hqG, (pair_mem_unionOfName hτ).mpr ?_, hx⟩
    exact ⟨q.property, π, p.val, r.val, hπ, hσ, (hR q p).mpr hqp, (hR q r).mpr hqr⟩

end PolishSpaceBook.ForcingNames
