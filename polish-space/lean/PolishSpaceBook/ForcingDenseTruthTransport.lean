module

public import PolishSpaceBook.ForcingDenseNameTransport

@[expose] public section

/-! # Satisfaction and semantic forcing under represented dense embeddings -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames ForcingAtomic
universe u

lemma realize_equal_domains {A B : ZFSet.{u}} (hAB : A = B) {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → A) (ys : Fin n → B) (hxy : ∀ i, (xs i).val = (ys i).val) :
    φ.Realize Empty.elim xs ↔ φ.Realize Empty.elim ys := by
  subst B
  have he : xs = ys := funext (fun i => Subtype.ext (hxy i))
  rw [he]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P Q S E : M) [Preorder (Condition P.val)] [Preorder (Condition Q.val)]
  (e : Condition P.val ↪o Condition Q.val)
  (hS : ∀ p q : Condition Q.val, pair p.val q.val ∈ S.val ↔ p ≤ q)
  (hE : ∀ p : Condition P.val, ∀ q : Condition Q.val, pair p.val q.val ∈ E.val ↔ e p = q)
  (hd : ∀ q : Condition Q.val, ∃ p, e p ≤ q)

/-- The actual recursively translated name, with ground-model membership proved. -/
def forwardName (τ : Name P.val M) : Name Q.val M :=
  ⟨relabelName P.val Q.val E.val τ.val,
    relabelName_mem hM hinf hpair hunion hpower hsep hrep P Q E ⟨τ.val, τ.property.1⟩,
    relabelName_isName _ _ _ _ τ.property.2⟩

include hS hE in
 theorem realize_forwardNames (G : Order.PFilter (Condition P.val)) {n : ℕ}
    (φ : ForcingFormulas.Formula n) (xs : Fin n → Name P.val M) :
    φ.Realize Empty.elim (fun i => evalName Q.val M (transportPFilter e G)
      (forwardName hM hinf hpair hunion hpower hsep hrep P Q E (xs i))) ↔
    φ.Realize Empty.elim (fun i => evalName P.val M G (xs i)) := by
  apply realize_equal_domains (extension_transport hM hinf hpair hunion hpower hsep hrep P Q S E e hS hE G)
  intro i
  exact value_forwardName P Q E e hE G (xs i).val (xs i).property.2

include hS hE hd in
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    For the semantic relation $\forces$ of §{sec:forcing-relation}, quantify over corresponding generic filters
    and use the valuation identities to obtain preservation as well.
-/
 theorem semantic_forcing_transport {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name P.val M) (p : Condition P.val) :
    (∀ G : Order.PFilter (Condition P.val), ModelGeneric P.val M G → p ∈ G →
      φ.Realize Empty.elim (fun i => evalName P.val M G (xs i))) ↔
    (∀ H : Order.PFilter (Condition Q.val), ModelGeneric Q.val M H → e p ∈ H →
      φ.Realize Empty.elim (fun i => evalName Q.val M H
        (forwardName hM hinf hpair hunion hpower hsep hrep P Q E (xs i)))) := by
  constructor
  · intro h H hH hpH
    have hco := modelGeneric_image_coinitial hM hsep P Q S E e hS hE hd H hH
    let G := pullbackPFilter P Q e H hco
    have hG := modelGeneric_pullback hM hsep P Q E e hE hd H hH hco
    have ht := (realize_forwardNames hM hinf hpair hunion hpower hsep hrep P Q S E e hS hE G φ xs).mpr
      (h G hG hpH)
    have he : transportPFilter e G = H := transport_pullbackPFilter P Q e H hco
    rw [he] at ht
    exact ht
  · intro h G hG hpG
    apply (realize_forwardNames hM hinf hpair hunion hpower hsep hrep P Q S E e hS hE G φ xs).mp
    exact h (transportPFilter e G) (modelGeneric_transport hM hsep P Q S E e hS hE hd G hG)
      ((image_mem_transportPFilter e G p).mpr hpG)

end PolishSpaceBook.SetTheoryModels
