module

public import PolishSpaceBook.CohenInternalCompletion
public import PolishSpaceBook.ForcingDenseRecursiveTransport

@[expose] public section

/-! # Cohen forcing, its internal Boolean values, and generic truth -/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas ForcingNames ForcingAtomic SetTheoryModels InternalBooleanAlgebra
universe u

local instance cohenBooleanForcingOrder : PartialOrder (Condition (cohenConditionSet.{u} Set.univ)) :=
  cohenCodePartialOrder

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

local notation "P" => cohenConditionsInModel hM hinf hpair hunion hpower hsep
local notation "B" => cohenCompletionCarrier hM hinf hpair hunion hpower hsep
local notation "Alg" => cohenCompletionBooleanAlgebra hM hinf hpair hunion hpower hsep
local notation "A" => cohenCompletionAlgebra hM hinf hpair hunion hpower hsep
local notation "E" => cohenEmbeddingGraphInModel hM hinf hpair hunion hpower hsep
local notation "emb" => cohenCompletionEmbedding hM hinf hpair hunion hpower hsep

def cohenBooleanName :
    letI := Alg
    Name (P).val M → Name (positiveSet B) M := by
  letI := Alg
  exact forwardName hM hinf hpair hunion hpower hsep hrep P (positiveInModel B hM hsep) E

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{proposition*}[Names and forcing under the dense embedding]
    For the internally represented dense order embedding $e:P\to Q$, define translations of names by
    $$\begin{aligned}
    F(\tau)&=\{\langle F(\sigma),e(p)\rangle:\langle\sigma,p\rangle\in\tau\},\\
    R(\eta)&=\{\langle R(\delta),p\rangle:\exists q\in Q
    \ (\langle\delta,q\rangle\in\eta\land p\in P\land e(p)\le q)\}.
    \end{aligned}$$
    These send names in $M$ to names in $M$. For corresponding filters $G,H$ as above,
    $$F(\tau)^H=\tau^G,\qquad R(\eta)^G=\eta^H.$$
    Consequently, the two generic extensions are equal. Recursive forcing is preserved before choosing
    any filter:
    $$p\forces_P^*\varphi(\vec\tau)
    \quad\Longleftrightarrow\quad
    e(p)\forces_Q^*\varphi(F(\vec\tau)).$$
    Here $F$ acts on each name parameter. In the Boolean completion this becomes
    $$p\forces_P^*\varphi(\vec\tau)
    \quad\Longleftrightarrow\quad
    e(p)\le[\![\varphi(F(\vec\tau))]\!].$$
    \end{proposition*}
-/
/-- The original Cohen condition forces the formula precisely when its
principal ideal lies below the actual internally constructed Boolean value. -/
theorem cohen_force_iff_booleanValue {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (P).val M) (p : Condition (P).val) :
    letI := Alg
    p ∈ force (P).val M φ xs ↔ element B (emb p) ≤
      booleanValue B A hM hinf hpair hunion hpower hsep hrep φ
        (fun i => cohenBooleanName hM hinf hpair hunion hpower hsep hrep (xs i)) := by
  let _ := Alg
  exact (force_forwardNames hM hinf hpair hunion hpower hsep hrep P (positiveInModel B hM hsep)
    (A).orderCode E emb ((A).positive_order_iff B)
    (cohenCompletionEmbedding_represented hM hinf hpair hunion hpower hsep)
    (cohenCompletionEmbedding_dense hM hinf hpair hunion hpower hsep) φ xs p).trans
    (force_iff_le_booleanValue B A hM hinf hpair hunion hpower hsep hrep φ _ (emb p))

theorem cohen_transport_generic (G : Order.PFilter (Condition (P).val)) (hG : ModelGeneric (P).val M G) :
    letI := Alg
    ModelGeneric (positiveSet B) M (transportPFilter emb G) := by
  let _ := Alg
  exact modelGeneric_transport hM hsep P (positiveInModel B hM hsep) (A).orderCode E emb
    ((A).positive_order_iff B) (cohenCompletionEmbedding_represented hM hinf hpair hunion hpower hsep)
    (cohenCompletionEmbedding_dense hM hinf hpair hunion hpower hsep) G hG

/-- Evaluation commutes for every formula and every existing generic filter.
No countability hypothesis is required. -/
theorem cohen_boolean_generic_truth (G : Order.PFilter (Condition (P).val)) (hG : ModelGeneric (P).val M G)
    {n : ℕ} (φ : ForcingFormulas.Formula n) (xs : Fin n → Name (P).val M) :
    letI := Alg
    φ.Realize Empty.elim (fun i => evalName (P).val M G (xs i)) ↔
      booleanValue B A hM hinf hpair hunion hpower hsep hrep φ
        (fun i => cohenBooleanName hM hinf hpair hunion hpower hsep hrep (xs i)) ∈
          liftedFilter B (transportPFilter emb G) := by
  let _ := Alg
  exact (realize_forwardNames hM hinf hpair hunion hpower hsep hrep P (positiveInModel B hM hsep)
    (A).orderCode E emb ((A).positive_order_iff B)
    (cohenCompletionEmbedding_represented hM hinf hpair hunion hpower hsep) G φ xs).symm.trans
    (boolean_generic_truth B A hM hinf hpair hunion hpower hsep hrep (transportPFilter emb G)
      (cohen_transport_generic hM hinf hpair hunion hpower hsep G hG) φ _)

include hrep in
theorem cohen_extension_completion (G : Order.PFilter (Condition (P).val)) :
    letI := Alg
    extension (positiveSet B) M (chosen (positiveSet B) (transportPFilter emb G)) =
      extension (P).val M (chosen (P).val G) := by
  let _ := Alg
  exact extension_transport hM hinf hpair hunion hpower hsep hrep P (positiveInModel B hM hsep)
    (A).orderCode E emb ((A).positive_order_iff B)
    (cohenCompletionEmbedding_represented hM hinf hpair hunion hpower hsep) G

end PolishSpaceBook
