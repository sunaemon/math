module

public import PolishSpaceBook.ForcingGenericTruth
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # Testing model genericity with open dense sets

The downward closure of a dense set is obtained by bounded Separation using the
actual internal order relation. Upward closure of the filter then recovers a
member of the original dense set. No external power-set closure is assumed.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic
universe u

/-- Parameters order relation, dense set, input condition. -/
def forcingLowerPredicate : BoundedSetPredicate 3 := .ex 1 (.pairMember 0 2 3)

def forcingLowerClosure (P R D : ZFSet.{u}) : ZFSet.{u} :=
  P.sep (fun q => ∃ p ∈ D, pair q p ∈ R)

lemma forcingLowerClosure_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : M ⊨ separationSentence forcingLowerPredicate.compile) (P R D : M) :
    forcingLowerClosure P.val R.val D.val ∈ M := by
  exact forcingLowerPredicate.separation_mem hM hsep ![R, D] P.property

lemma mem_forcingLowerClosure {P R D : ZFSet.{u}} [Preorder (Condition P)]
    (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q)
    (hDP : D ⊆ P) (q : Condition P) :
    q.val ∈ forcingLowerClosure P R D ↔ ∃ p : Condition P, p.val ∈ D ∧ q ≤ p := by
  rw [forcingLowerClosure, mem_sep]
  constructor
  · rintro ⟨_, p, hp, hqp⟩
    exact ⟨⟨p, hDP hp⟩, hp, (hR q ⟨p, hDP hp⟩).mp hqp⟩
  · rintro ⟨p, hp, hqp⟩
    exact ⟨q.property, p.val, hp, (hR q p).mpr hqp⟩

lemma forcingLowerClosure_dense_lower {P R D : ZFSet.{u}} [Preorder (Condition P)]
    (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q) (hDP : D ⊆ P)
    (hd : IsCoinitial {p : Condition P | p.val ∈ D}) :
    IsCoinitial {p : Condition P | p.val ∈ forcingLowerClosure P R D} ∧
      IsLowerSet {p : Condition P | p.val ∈ forcingLowerClosure P R D} := by
  constructor
  · intro p
    obtain ⟨q, hq, hqp⟩ := hd p
    exact ⟨q, (mem_forcingLowerClosure hR hDP q).mpr ⟨q, hq, le_rfl⟩, hqp⟩
  · intro p q hqp hp
    obtain ⟨r, hr, hpr⟩ := (mem_forcingLowerClosure hR hDP p).mp hp
    exact (mem_forcingLowerClosure hR hDP q).mpr ⟨r, hr, hqp.trans hpr⟩

/-- The internal lower closure makes open dense tests equivalent to all dense tests. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Open dense test for genericity
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    One implication is immediate. For the converse, let $D\IncludedIn P$ be dense and belong to $M$. Put
    $$U:=\{q\in P:\exists p\in D\,(\langle q,p\rangle\in R)\}.$$
    The displayed predicate is bounded, so Separation gives $U\in M$. Reflexivity gives $D\IncludedIn U$,
    hence $U$ is dense; transitivity of the order makes $U$ downward closed.
    Choose $q\in G\cap U$ and a witness $p\in D$ with $q\le p$.
    Upward closure of the filter gives $p\in G$, so $G$ meets $D$.
    \end{proof}
-/
theorem modelGeneric_iff_open_dense {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : M ⊨ separationSentence forcingLowerPredicate.compile) (P R : M)
    [Preorder (Condition P.val)]
    (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
    (G : Order.PFilter (Condition P.val)) :
    ModelGeneric P.val M G ↔
      ∀ D : ZFSet.{u}, D ∈ M → D ⊆ P.val →
        IsCoinitial {p : Condition P.val | p.val ∈ D} →
        IsLowerSet {p : Condition P.val | p.val ∈ D} → ∃ p ∈ G, p.val ∈ D := by
  constructor
  · intro h D hD hDP hd _
    exact h D hD hDP hd
  · intro h D hD hDP hd
    let U := forcingLowerClosure P.val R.val D
    have hU := forcingLowerClosure_mem hM hsep P R ⟨D, hD⟩
    have hUP : U ⊆ P.val := fun _ hx => (mem_sep.mp hx).1
    obtain ⟨hUd, hUl⟩ := forcingLowerClosure_dense_lower hR hDP hd
    obtain ⟨q, hqG, hqU⟩ := h U hU hUP hUd hUl
    obtain ⟨p, hp, hqp⟩ := (mem_forcingLowerClosure hR hDP q).mp hqU
    exact ⟨p, G.mem_of_le hqp hqG, hp⟩

end PolishSpaceBook.SetTheoryModels
