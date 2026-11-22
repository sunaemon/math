module

public import PolishSpaceBook.ForcingRelabelTables

@[expose] public section

/-! # Ground-model closure of the recursive name translation -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames BoundedSetPredicate
universe u

/-- First-order definition of the concrete relabelling step. All four witnesses
are recovered from the input sets and their ordered pairs. -/
def relabelStepFormula : ForcingFormulas.Formula 6 :=
  ((memberAt (6 : Fin 7) 5).iff
    ((memberAt (8 : Fin 11) 0 ⊓ memberAt 9 1 ⊓ pairMemberFormula 3 7 8 ⊓
      pairMemberFormula 2 8 9 ⊓ pairMemberFormula 4 7 10 ⊓ orderedPairFormula 6 10 9).ex.ex.ex.ex)).all

lemma mem_relabelStep_unbounded (P Q E a t z : ZFSet.{u}) :
    z ∈ relabelStep P Q E a t ↔ ∃ σ p q y, p ∈ P ∧ q ∈ Q ∧
      pair σ p ∈ a ∧ pair p q ∈ E ∧ pair σ y ∈ t ∧ z = pair y q := by
  rw [mem_relabelStep]
  constructor
  · rintro ⟨y, _, q, hq, he, σ, _, p, hp, hσp, hpq, hσy⟩
    exact ⟨σ, p, q, y, hp, hq, hσp, hpq, hσy, he⟩
  · rintro ⟨σ, p, q, y, hp, hq, hσp, hpq, hσy, he⟩
    exact ⟨y, second_mem_doubleUnion hσy, q, hq, he,
      σ, child_mem_doubleUnion hσy, p, hp, hσp, hpq, hσy⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hpair hunion in
lemma realize_relabelStepFormula (P Q E a t b : M) :
    relabelStepFormula.Realize Empty.elim ![P, Q, E, a, t, b] ↔
      b.val = relabelStep P.val Q.val E.val a.val t.val := by
  have hp {n : ℕ} (r x y : Fin n) (xs : Fin n → M) :
      (pairMemberFormula r x y).Realize Empty.elim xs ↔ pair (xs x).val (xs y).val ∈ (xs r).val :=
    realize_pairMemberFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) r x y xs
  have ho {n : ℕ} (z x y : Fin n) (xs : Fin n → M) :
      (orderedPairFormula z x y).Realize Empty.elim xs ↔ (xs z).val = pair (xs x).val (xs y).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) z x y xs
  simp only [relabelStepFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, realize_memberAt_model, hp, ho, Fin.snoc, and_assoc]
  change (∀ z : M, z.val ∈ b.val ↔ ∃ σ p q y : M, p.val ∈ P.val ∧ q.val ∈ Q.val ∧
    pair σ.val p.val ∈ a.val ∧ pair p.val q.val ∈ E.val ∧ pair σ.val y.val ∈ t.val ∧
      z.val = pair y.val q.val) ↔ _
  have hw (z : M) :
      (∃ σ p q y : M, p.val ∈ P.val ∧ q.val ∈ Q.val ∧ pair σ.val p.val ∈ a.val ∧
        pair p.val q.val ∈ E.val ∧ pair σ.val y.val ∈ t.val ∧ z.val = pair y.val q.val) ↔
      z.val ∈ relabelStep P.val Q.val E.val a.val t.val := by
    rw [mem_relabelStep_unbounded]
    constructor
    · rintro ⟨σ, p, q, y, hp, hq, hσp, hpq, hσy, he⟩
      exact ⟨σ.val, p.val, q.val, y.val, hp, hq, hσp, hpq, hσy, he⟩
    · rintro ⟨σ, p, q, y, hp, hq, hσp, hpq, hσy, he⟩
      have hyM := hM.mem_trans (second_mem_doubleUnion hσy)
        (union_mem hM hunion (union_mem hM hunion t.property))
      exact ⟨⟨σ, child_mem_ground hM a.property hσp⟩, ⟨p, hM.mem_trans hp P.property⟩,
        ⟨q, hM.mem_trans hq Q.property⟩, ⟨y, hyM⟩, hp, hq, hσp, hpq, hσy, he⟩
  simp only [hw]
  constructor
  · intro h
    ext z
    constructor
    · intro hz; exact (h ⟨z, hM.mem_trans hz b.property⟩).mp hz
    · intro hz
      obtain ⟨σ, p, q, y, _, hq, _, _, hσy, rfl⟩ := (mem_relabelStep_unbounded _ _ _ _ _ _).mp hz
      have hyM := hM.mem_trans (second_mem_doubleUnion hσy)
        (union_mem hM hunion (union_mem hM hunion t.property))
      exact (h ⟨pair y q, orderedPair_mem hM hpair hyM (hM.mem_trans hq Q.property)⟩).mpr hz
  · intro he z; rw [he]

include hM hpair hunion in
lemma realize_relabelStepInstance {n : ℕ} (ρ : Fin 3 → Fin n) (a t b : Fin n) (xs : Fin n → M) :
    (stepInstance relabelStepFormula ρ a t b).Realize Empty.elim xs ↔
      (xs b).val = relabelStep (xs (ρ 0)).val (xs (ρ 1)).val (xs (ρ 2)).val (xs a).val (xs t).val := by
  rw [realize_stepInstance]
  have he : Fin.snoc (Fin.snoc (Fin.snoc (xs ∘ ρ) (xs a)) (xs t)) (xs b) =
      ![xs (ρ 0), xs (ρ 1), xs (ρ 2), xs a, xs t, xs b] := by
    funext i; fin_cases i <;> rfl
  rw [he]
  exact realize_relabelStepFormula hM hpair hunion _ _ _ _ _ _

def relabelTableStep (P Q E a g : ZFSet.{u}) : ZFSet.{u} :=
  let t := ZFSet.sUnion (graphRange g)
  insert (pair a (relabelStep P Q E a t)) t

/-- The recursive step retains the preceding tables and inserts the new value. -/
def relabelTableStepFormula : ForcingFormulas.Formula 6 :=
  (rangeFormula (4 : Fin 10) 6 ⊓ unionFormula 6 7 ⊓
    stepInstance relabelStepFormula ![0, 1, 2] 3 7 8 ⊓
    orderedPairFormula 9 3 8 ⊓ insertFormula 9 7 5).ex.ex.ex.ex

include hM hpair hunion hpower hsep in
lemma relabelTableStep_mem (P Q E a g : M) : relabelTableStep P.val Q.val E.val a.val g.val ∈ M := by
  have ht := union_mem hM hunion (graphRange_mem hM hunion (hsep _) g.property)
  have hv := relabelStep_mem hM hpair hunion hpower hsep P Q E a ⟨_, ht⟩
  simpa only [relabelTableStep, insert_eq] using binaryUnion_mem hM hpair hunion
    (singleton_mem hM hpair (orderedPair_mem hM hpair a.property hv)) ht

include hM hpair hunion hpower hsep in
lemma realize_relabelTableStepFormula (P Q E a g b : M) :
    relabelTableStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ![P, Q, E] a) g) b) ↔
      b.val = relabelTableStep P.val Q.val E.val a.val g.val := by
  have ho {n : ℕ} (z x y : Fin n) (xs : Fin n → M) :
      (orderedPairFormula z x y).Realize Empty.elim xs ↔ (xs z).val = pair (xs x).val (xs y).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) z x y xs
  simp only [relabelTableStepFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_rangeFormula hM hunion, realize_unionFormula hM, realize_insertFormula hM,
    realize_relabelStepInstance hM hpair hunion, ho, Fin.snoc, and_assoc]
  change (∃ r t v w : M, r.val = graphRange g.val ∧ t.val = ZFSet.sUnion r.val ∧
    v.val = relabelStep P.val Q.val E.val a.val t.val ∧
      w.val = pair a.val v.val ∧ b.val = insert w.val t.val) ↔ _
  constructor
  · rintro ⟨r, t, v, w, hr, ht, hv, hw, hb⟩
    simpa only [relabelTableStep, hw, hv, ht, hr] using hb
  · intro hb
    let r : M := ⟨graphRange g.val, graphRange_mem hM hunion (hsep _) g.property⟩
    let t : M := ⟨ZFSet.sUnion r.val, union_mem hM hunion r.property⟩
    let v : M := ⟨relabelStep P.val Q.val E.val a.val t.val, relabelStep_mem hM hpair hunion hpower hsep P Q E a t⟩
    exact ⟨r, t, v, ⟨pair a.val v.val, orderedPair_mem hM hpair a.property v.property⟩,
      rfl, rfl, rfl, rfl, hb⟩

lemma relabelTable_step_equation (P Q E a : ZFSet.{u}) :
    hereditaryTable (relabelName P Q E) a = relabelTableStep P Q E a
      (functionGraph (fun x : a => hereditaryTable (relabelName P Q E) x.val)) := by
  rw [hereditaryTable_eq, relabelTableStep, graphRange_functionGraph]
  change insert (pair a (relabelName P Q E a)) (precedingTables (relabelName P Q E) a) = _
  exact congrArg (fun v => insert (pair a v) (precedingTables (relabelName P Q E) a))
    (relabelStep_equation P Q E a).symm

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The recursions are well founded because each child name has smaller rank. To verify internality,
    retain at each set a table of the translated values of its hereditary members. The preceding tables
    contain the values for every child name. The displayed pair collections are obtained by Separation
    from products of sets bounding their ranges and the condition sets. Pairing and Union then adjoin the new table entry.
    This gives an internally definable membership-recursion step closed in $M$. The comparison theorem in
    §{sec:internal-transitive-bounds} puts the specified recursive translations in $M$.
-/
include hM hinf hpair hunion hpower hsep hrep in
 theorem relabelName_mem (P Q E a : M) : relabelName P.val Q.val E.val a.val ∈ M := by
  have ht := external_recursive_value_mem hM hinf hpair hunion hpower hsep hrep relabelTableStepFormula ![P, Q, E]
    (relabelTableStep P.val Q.val E.val)
    (fun a g b => realize_relabelTableStepFormula hM hpair hunion hpower hsep P Q E a g b)
    (fun a g => relabelTableStep_mem hM hpair hunion hpower hsep P Q E a g)
    (hereditaryTable (relabelName P.val Q.val E.val)) (relabelTable_step_equation P.val Q.val E.val) a
  exact hM.mem_trans (second_mem_doubleUnion (hereditaryTable_self (relabelName P.val Q.val E.val) a.val))
    (union_mem hM hunion (union_mem hM hunion ht))

end PolishSpaceBook.SetTheoryModels
