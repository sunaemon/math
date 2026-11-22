module

public import PolishSpaceBook.ForcingDenseAtomicTransport
public import PolishSpaceBook.ForcingDenseTruthTransport

@[expose] public section

/-! # Direct transport of every first-order recursive forcing clause -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames ForcingAtomic
universe u

lemma termName_match {P Q M : ZFSet.{u}} [Preorder (Condition P)] [Preorder (Condition Q)]
    (e : Condition P ↪o Condition Q) {n : ℕ} (t : membershipLanguage.Term (Empty ⊕ Fin n))
    (xs : Fin n → Name P M) (ys : Fin n → Name Q M)
    (hxy : ∀ i, DenseNameMatch e (xs i).val (ys i).val) :
    DenseNameMatch e (termName P M t xs).val (termName Q M t ys).val := by
  cases t with
  | var a => cases a with
    | inl e => exact e.elim
    | inr i => exact hxy i
  | func f _ => exact f.elim

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

def inverseName (τ : Name Q.val M) : Name P.val M :=
  ⟨relabelName Q.val P.val (inverseLabelGraph P.val Q.val S.val E.val) τ.val,
    relabelName_mem hM hinf hpair hunion hpower hsep hrep Q P
      ⟨_, inverseLabelGraph_mem hM hpair hunion hpower hsep P Q S E⟩ ⟨τ.val, τ.property.1⟩,
    relabelName_isName _ _ _ _ τ.property.2⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now induct on formulas. Atomic formulas use the preceding argument. For implication, test image
    conditions using the induction hypothesis; density and saturation extend the result to all target
    conditions. For a universal quantifier, translate any target name back by $R$ in one direction, and
    any source name forward by $F$ in the other. The translated names belong to $M$ and match, so the
    induction hypothesis applies with the enlarged parameter tuple. This proves the forcing equivalence
    without generic existence. The Boolean inequality follows from the construction of Boolean values above.
-/
include hM hinf hpair hunion hpower hsep hrep hS hE hd in
/-- Structural forcing correspondence for actual recursively matched names.
Universal quantification uses the two concrete internal name translations. -/
theorem force_dense_matched {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name P.val M) (ys : Fin n → Name Q.val M)
    (hxy : ∀ i, DenseNameMatch e (xs i).val (ys i).val) (p : Condition P.val) :
    p ∈ force P.val M φ xs ↔ e p ∈ force Q.val M φ ys := by
  induction φ generalizing p with
  | falsum => rfl
  | equal s t =>
    exact atomic_dense_transport e hd true _ _ _ _
      (termName_match e s xs ys hxy) (termName_match e t xs ys hxy) p
  | rel r ts =>
    cases r
    exact atomic_dense_transport e hd false _ _ _ _
      (termName_match e (ts 0) xs ys hxy) (termName_match e (ts 1) xs ys hxy) p
  | imp φ ψ ihφ ihψ =>
    change p ∈ forcingImp (force P.val M φ xs) (force P.val M ψ xs) ↔
      e p ∈ forcingImp (force Q.val M φ ys) (force Q.val M ψ ys)
    constructor
    · intro hp q hqp hqφ
      apply force_saturated Q.val M ψ ys
      intro t htq
      obtain ⟨r, hrt⟩ := hd t
      have hrp : r ≤ p := e.le_iff_le.mp (hrt.trans (htq.trans hqp))
      have hrφ := (ihφ xs ys hxy r).mpr (force_lower Q.val M φ ys (hrt.trans htq) hqφ)
      exact ⟨e r, hrt, (ihψ xs ys hxy r).mp (hp r hrp hrφ)⟩
    · intro hp r hrp hrφ
      exact (ihψ xs ys hxy r).mpr (hp (e r) (e.monotone hrp) ((ihφ xs ys hxy r).mp hrφ))
  | all φ ih =>
    change (∀ σ : Name P.val M, p ∈ force P.val M φ (Fin.snoc xs σ)) ↔
      (∀ τ : Name Q.val M, e p ∈ force Q.val M φ (Fin.snoc ys τ))
    constructor
    · intro hp τ
      let σ := inverseName hM hinf hpair hunion hpower hsep hrep P Q S E τ
      have hστ : DenseNameMatch e σ.val τ.val := inverseName_match e E.val S.val hE hS τ.val
      apply (ih (Fin.snoc xs σ) (Fin.snoc ys τ) _ p).mp (hp σ)
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hστ
      · simpa only [Fin.snoc_castSucc] using hxy j
    · intro hp σ
      let τ := forwardName hM hinf hpair hunion hpower hsep hrep P Q E σ
      have hστ : DenseNameMatch e σ.val τ.val := forwardName_match e E.val hE σ.val
      apply (ih (Fin.snoc xs σ) (Fin.snoc ys τ) _ p).mpr (hp τ)
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hστ
      · simpa only [Fin.snoc_castSucc] using hxy j

include hS hE hd in
 theorem force_forwardNames {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name P.val M) (p : Condition P.val) :
    p ∈ force P.val M φ xs ↔ e p ∈ force Q.val M φ
      (fun i => forwardName hM hinf hpair hunion hpower hsep hrep P Q E (xs i)) :=
  force_dense_matched hM hinf hpair hunion hpower hsep hrep P Q S E e hS hE hd φ xs _
    (fun i => forwardName_match e E.val hE (xs i).val) p

end PolishSpaceBook.SetTheoryModels
