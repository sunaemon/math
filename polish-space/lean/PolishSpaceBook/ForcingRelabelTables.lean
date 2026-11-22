module

public import PolishSpaceBook.ForcingRelabelNames
public import PolishSpaceBook.ForcingCheckClosure
public import PolishSpaceBook.SetTheoryPredicateComposition

@[expose] public section

/-! # Hereditary tables for internal name relabelling -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames BoundedSetPredicate
universe u

/-- Store every value at a member and recursively at all its ancestors. This
turns name recursion along first coordinates into ordinary membership recursion. -/
def hereditaryTable (K : ZFSet.{u} → ZFSet.{u}) (a : ZFSet.{u}) : ZFSet.{u} :=
  insert (pair a (K a)) (ZFSet.sUnion (ZFSet.range (fun x : a => hereditaryTable K x.val)))
termination_by a.rank
decreasing_by exact rank_lt_of_mem x.property

lemma hereditaryTable_eq (K : ZFSet.{u} → ZFSet.{u}) (a : ZFSet.{u}) :
    hereditaryTable K a = insert (pair a (K a)) (ZFSet.sUnion (ZFSet.range (fun x : a => hereditaryTable K x.val))) := by
  rw [hereditaryTable]

lemma hereditaryTable_self (K : ZFSet.{u} → ZFSet.{u}) (a : ZFSet.{u}) :
    pair a (K a) ∈ hereditaryTable K a := by rw [hereditaryTable_eq]; simp

lemma hereditaryTable_mono (K : ZFSet.{u} → ZFSet.{u}) {x a : ZFSet.{u}} (hx : x ∈ a) :
    hereditaryTable K x ⊆ hereditaryTable K a := by
  intro z hz
  rw [hereditaryTable_eq]
  exact mem_insert_iff.mpr (Or.inr (mem_sUnion.mpr ⟨hereditaryTable K x, mem_range.mpr ⟨⟨x, hx⟩, rfl⟩, hz⟩))

lemma hereditaryTable_correct (K : ZFSet.{u} → ZFSet.{u}) (a : ZFSet.{u}) {x y : ZFSet.{u}}
    (h : pair x y ∈ hereditaryTable K a) : y = K x := by
  rw [hereditaryTable_eq, mem_insert_iff] at h
  rcases h with he | h
  · obtain ⟨rfl, he⟩ := pair_inj.mp he; exact he
  · obtain ⟨t, ht, hp⟩ := mem_sUnion.mp h
    obtain ⟨z, rfl⟩ := mem_range.mp ht
    exact hereditaryTable_correct K z.val hp
termination_by a.rank
decreasing_by exact rank_lt_of_mem z.property

def precedingTables (K : ZFSet.{u} → ZFSet.{u}) (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun x : a => hereditaryTable K x.val))

lemma precedingTables_correct (K : ZFSet.{u} → ZFSet.{u}) {a x y : ZFSet.{u}}
    (h : pair x y ∈ precedingTables K a) : y = K x := by
  obtain ⟨t, ht, hp⟩ := mem_sUnion.mp h
  obtain ⟨z, rfl⟩ := mem_range.mp ht
  exact hereditaryTable_correct K z.val hp

lemma child_mem_precedingTables (K : ZFSet.{u} → ZFSet.{u}) {a σ p : ZFSet.{u}}
    (h : pair σ p ∈ a) : pair σ (K σ) ∈ precedingTables K a := by
  apply mem_sUnion.mpr
  refine ⟨hereditaryTable K (pair σ p), mem_range.mpr ⟨⟨pair σ p, h⟩, rfl⟩, ?_⟩
  exact hereditaryTable_mono K (by simp [pair] : ({σ} : ZFSet) ∈ pair σ p)
    (hereditaryTable_mono K (by simp : σ ∈ ({σ} : ZFSet)) (hereditaryTable_self K σ))

/-- P, Q, E, input name, preceding table, double union of that table, candidate pair. -/
def relabelPairsPredicate : BoundedSetPredicate 7 :=
  .ex 5 (.ex 1 (.conj (.orderedPair 6 7 8)
    (.ex 5 (.ex 0 (.conj (.pairMember 3 9 10)
      (.conj (.pairMember 2 10 8) (.pairMember 4 9 7)))))))

def relabelStep (P Q E a t : ZFSet.{u}) : ZFSet.{u} :=
  (prod (ZFSet.sUnion (ZFSet.sUnion t)) Q).sep
    (fun z => relabelPairsPredicate.eval ![P, Q, E, a, t, ZFSet.sUnion (ZFSet.sUnion t), z])

lemma mem_relabelStep (P Q E a t z : ZFSet.{u}) :
    z ∈ relabelStep P Q E a t ↔ ∃ y ∈ ZFSet.sUnion (ZFSet.sUnion t), ∃ q ∈ Q,
      z = pair y q ∧ ∃ σ ∈ ZFSet.sUnion (ZFSet.sUnion t), ∃ p ∈ P,
        pair σ p ∈ a ∧ pair p q ∈ E ∧ pair σ y ∈ t := by
  simp only [relabelStep, mem_sep]
  have he : relabelPairsPredicate.eval ![P, Q, E, a, t, ZFSet.sUnion (ZFSet.sUnion t), z] ↔
      ∃ y ∈ ZFSet.sUnion (ZFSet.sUnion t), ∃ q ∈ Q, z = pair y q ∧
        ∃ σ ∈ ZFSet.sUnion (ZFSet.sUnion t), ∃ p ∈ P,
          pair σ p ∈ a ∧ pair p q ∈ E ∧ pair σ y ∈ t := by rfl
  rw [he]
  exact and_iff_right_of_imp (fun ⟨y, hy, q, hq, he, _⟩ => mem_prod.mpr ⟨y, hy, q, hq, he⟩)

lemma relabelStep_equation (P Q E a : ZFSet.{u}) :
    relabelStep P Q E a (precedingTables (relabelName P Q E) a) = relabelName P Q E a := by
  ext z
  rw [mem_relabelStep, mem_relabelName]
  constructor
  · rintro ⟨y, _, q, hq, rfl, σ, _, p, hp, hσp, hpq, hσy⟩
    have he := precedingTables_correct (relabelName P Q E) hσy
    exact ⟨σ, p, q, hp, hq, hσp, hpq, by rw [he]⟩
  · rintro ⟨σ, p, q, hp, hq, hσp, hpq, rfl⟩
    have hσ := child_mem_precedingTables (relabelName P Q E) hσp
    exact ⟨relabelName P Q E σ, second_mem_doubleUnion hσ, q, hq, rfl,
      σ, child_mem_doubleUnion hσ, p, hp, hσp, hpq, hσ⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

include hM hpair hunion hpower hsep in
lemma relabelStep_mem (P Q E a t : M) : relabelStep P.val Q.val E.val a.val t.val ∈ M := by
  let U : M := ⟨ZFSet.sUnion (ZFSet.sUnion t.val), union_mem hM hunion (union_mem hM hunion t.property)⟩
  have he (z : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![P, Q, E, a, t, U]) z =
      ![P.val, Q.val, E.val, a.val, t.val, U.val, z] := by funext i; fin_cases i <;> rfl
  simpa only [relabelStep, he] using relabelPairsPredicate.separation_mem hM (hsep _) ![P, Q, E, a, t, U]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) U.property Q.property)

end PolishSpaceBook.SetTheoryModels
