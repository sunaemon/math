module

public import PolishSpaceBook.ForcingRelabelClosure
public import PolishSpaceBook.ForcingDenseFilterTransport
public import PolishSpaceBook.ForcingRegularEmbedding

@[expose] public section

/-! # Name and extension transport through an internally represented embedding -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames ForcingAtomic BoundedSetPredicate
universe u

lemma chosen_condition_iff {P : ZFSet.{u}} [Preorder (Condition P)]
    (G : Order.PFilter (Condition P)) (p : Condition P) : p.val ∈ chosen P G ↔ p ∈ G := by
  exact ⟨fun ⟨q, hq, he⟩ => condition_eq_of_val_eq he ▸ hq, fun hp => ⟨p, hp, rfl⟩⟩

/-- The inverse name translation expands a target label into every source
condition whose image lies below it. -/
def inverseLabelPredicate : BoundedSetPredicate 5 :=
  .ex 1 (.ex 0 (.conj (.orderedPair 4 5 6)
    (.ex 1 (.conj (.pairMember 3 6 7) (.pairMember 2 7 5)))))

def inverseLabelGraph (P Q S E : ZFSet.{u}) : ZFSet.{u} :=
  (prod Q P).sep (fun z => inverseLabelPredicate.eval ![P, Q, S, E, z])

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P Q S E : M) [Preorder (Condition P.val)] [Preorder (Condition Q.val)]
  (e : Condition P.val ↪o Condition Q.val)
  (hS : ∀ p q : Condition Q.val, pair p.val q.val ∈ S.val ↔ p ≤ q)
  (hE : ∀ p : Condition P.val, ∀ q : Condition Q.val, pair p.val q.val ∈ E.val ↔ e p = q)

include hM hpair hunion hpower hsep in
omit [Preorder (Condition P.val)] [Preorder (Condition Q.val)] in
lemma inverseLabelGraph_mem : inverseLabelGraph P.val Q.val S.val E.val ∈ M := by
  have he (z : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![P, Q, S, E]) z = ![P.val, Q.val, S.val, E.val, z] := by
    funext i; fin_cases i <;> rfl
  simpa only [inverseLabelGraph, he] using inverseLabelPredicate.separation_mem hM (hsep _) ![P, Q, S, E]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Q.property P.property)

include hS hE in
lemma inverseLabelGraph_correct (q : Condition Q.val) (p : Condition P.val) :
    pair q.val p.val ∈ inverseLabelGraph P.val Q.val S.val E.val ↔ e p ≤ q := by
  simp only [inverseLabelGraph, mem_sep, pair_mem_prod, p.property, q.property, true_and]
  change (∃ b ∈ Q.val, ∃ a ∈ P.val, pair q.val p.val = pair b a ∧
    ∃ r ∈ Q.val, pair a r ∈ E.val ∧ pair r b ∈ S.val) ↔ _
  constructor
  · rintro ⟨b, _, a, _, he, r, hr, hpr, hrq⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.mp he
    have her := (hE p ⟨r, hr⟩).mp hpr
    exact her ▸ (hS ⟨r, hr⟩ q).mp hrq
  · intro hpq
    exact ⟨q.val, q.property, p.val, p.property, rfl, (e p).val, (e p).property,
      (hE p (e p)).mpr rfl, (hS (e p) q).mpr hpq⟩

include hE in
 theorem value_forwardName (G : Order.PFilter (Condition P.val)) (τ : ZFSet.{u}) (hτ : IsName P.val τ) :
    value Q.val (transportPFilter e G) (relabelName P.val Q.val E.val τ) = value P.val G τ := by
  apply valuation_relabelName _ _ _ _ _ _ τ hτ
  intro p hp
  let pc : Condition P.val := ⟨p, hp⟩
  change pc.val ∈ chosen P.val G ↔ _
  rw [chosen_condition_iff]
  constructor
  · intro hpG
    exact ⟨(e pc).val, (e pc).property,
      (chosen_condition_iff (transportPFilter e G) (e pc)).mpr ((image_mem_transportPFilter e G pc).mpr hpG),
      (hE pc (e pc)).mpr rfl⟩
  · rintro ⟨q, hqQ, hqH, hpq⟩
    have heq := (hE pc ⟨q, hqQ⟩).mp hpq
    apply (image_mem_transportPFilter e G pc).mp
    rw [heq]
    exact (chosen_condition_iff (transportPFilter e G) ⟨q, hqQ⟩).mp hqH

include hS hE in
 theorem value_inverseName (G : Order.PFilter (Condition P.val)) (τ : ZFSet.{u}) (hτ : IsName Q.val τ) :
    value P.val G (relabelName Q.val P.val (inverseLabelGraph P.val Q.val S.val E.val) τ) =
      value Q.val (transportPFilter e G) τ := by
  apply valuation_relabelName _ _ _ _ _ _ τ hτ
  intro q hq
  let qc : Condition Q.val := ⟨q, hq⟩
  change qc.val ∈ chosen Q.val (transportPFilter e G) ↔ _
  rw [chosen_condition_iff, mem_transportPFilter]
  constructor
  · rintro ⟨p, hpG, hpq⟩
    exact ⟨p.val, p.property, (chosen_condition_iff G p).mpr hpG,
      (inverseLabelGraph_correct P Q S E e hS hE qc p).mpr hpq⟩
  · rintro ⟨p, hp, hpG, hqp⟩
    exact ⟨⟨p, hp⟩, (chosen_condition_iff G ⟨p, hp⟩).mp hpG,
      (inverseLabelGraph_correct P Q S E e hS hE qc ⟨p, hp⟩).mp hqp⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Induction on names proves both valuation identities: in the forward direction a label belongs to $G$
    exactly when its image belongs to $H$; in the reverse direction a label belongs to $H$ exactly when
    some image of a condition in $G$ lies below it. Applying both translations gives equality of extensions.
-/
include hM hinf hpair hunion hpower hsep hrep hS hE in
/-- Every name in either extension has an explicitly recursively translated
name in the other extension. Neither genericity nor countability is needed. -/
 theorem extension_transport (G : Order.PFilter (Condition P.val)) :
    extension Q.val M (chosen Q.val (transportPFilter e G)) = extension P.val M (chosen P.val G) := by
  let I : M := ⟨inverseLabelGraph P.val Q.val S.val E.val, inverseLabelGraph_mem hM hpair hunion hpower hsep P Q S E⟩
  ext x
  rw [mem_extension, mem_extension]
  constructor
  · rintro ⟨τ, hτM, hτ, hx⟩
    refine ⟨relabelName Q.val P.val I.val τ,
      relabelName_mem hM hinf hpair hunion hpower hsep hrep Q P I ⟨τ, hτM⟩,
      relabelName_isName _ _ _ _ hτ, ?_⟩
    exact (value_inverseName P Q S E e hS hE G τ hτ).trans hx
  · rintro ⟨τ, hτM, hτ, hx⟩
    refine ⟨relabelName P.val Q.val E.val τ,
      relabelName_mem hM hinf hpair hunion hpower hsep hrep P Q E ⟨τ, hτM⟩,
      relabelName_isName _ _ _ _ hτ, ?_⟩
    exact (value_forwardName P Q E e hE G τ hτ).trans hx

end PolishSpaceBook.SetTheoryModels
