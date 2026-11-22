module

public import PolishSpaceBook.BorelGraphValidity

@[expose] public section

/-! # Internal recognition of the full validity condition for Borel codes -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters omega, words, zero, label graph, square of words, candidate child graph. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Put
    $$R_\ell:=\{\langle t,s\rangle\in T\times T:
    J(t,s)\land\ell(t)\ne0\land\ell(s)\ne0\}.$$
    The relation graph belongs to $M$ when $\ell\in M$. Let $W(T,R)$ be the internal subset-minimum formula
    of §{sec:internal-rank-existence}: every nonempty subset of $T$ belonging to the model has an $R$-minimal
    member. Define a first-order formula $\Phi(\ell)$ by requiring that $\ell:T\to\omega$, that $L(\ell)$ holds,
    and that there exists a relation graph $R=R_\ell$ satisfying $W(T,R)$.
    The relation equation is bounded, using a subset of $T\times T$ and tests on all pairs of nodes.
    The well-foundedness clause uses the subset-minimum formula; we do not regard it as a local bounded test.
-/
def childGraphPredicate : BoundedSetPredicate 6 :=
  .conj (.subset 5 4) (.all 1 (.all 1 (.iff (.pairMember 5 6 7)
    (.conj (syntaxChildAt 0 3 2 6 7) (.neg (.pairMember 3 7 2))))))

lemma eval_childGraphPredicate (c : BorelExpression) (R : ZFSet.{u}) :
    childGraphPredicate.eval ![Ordinal.omega0.toZFSet, finiteSequences, natOrdinal 0,
      c.labelGraph, ZFSet.prod finiteSequences finiteSequences, R] ↔ R = childRelation c.labelGraph := by
  have hj (s t : List ℕ) :
      (syntaxChildAt (0 : Fin 8) 3 2 6 7).eval (Fin.snoc (Fin.snoc
        ![Ordinal.omega0.toZFSet, finiteSequences, natOrdinal 0, c.labelGraph,
          ZFSet.prod finiteSequences finiteSequences, R] (wordGraph s)) (wordGraph t)) ↔
        (∃ k, s = t ++ [k]) ∧ c s ≠ 0 :=
    eval_syntaxChildAt _ _ _ _ _ _ c s t rfl rfl rfl rfl rfl
  simp only [childGraphPredicate, eval]
  dsimp [Fin.snoc, Fin.castPred, Fin.castLT]
  simp only [forall_mem_finiteSequences, hj, pair_mem_labelGraph, natOrdinal_injective.eq_iff]
  have he (s t : List ℕ) :
      ((∃ k, s = t ++ [k]) ∧ c s ≠ 0) ∧ ¬0 = c t ↔ c.Child s t := by
    simp only [Child]
    constructor
    · rintro ⟨⟨⟨k, hk⟩, hs⟩, ht⟩
      exact ⟨Ne.symm ht, k, hk, hs⟩
    · rintro ⟨ht, k, hk, hs⟩
      exact ⟨⟨⟨k, hk⟩, hs⟩, Ne.symm ht⟩
  simp only [he]
  constructor
  · rintro ⟨hsub, h⟩
    apply ZFSet.ext
    intro p
    by_cases hp : p ∈ ZFSet.prod (finiteSequences : ZFSet.{u}) finiteSequences
    · obtain ⟨s, hs, t, ht, rfl⟩ := ZFSet.mem_prod.mp hp
      obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hs
      obtain ⟨t, rfl⟩ := mem_finiteSequences.mp ht
      exact (h s t).trans (pair_mem_childRelation c s t).symm
    · exact ⟨fun hR => False.elim (hp (hsub hR)),
        fun hR => False.elim (hp (ZFSet.mem_sep.mp hR).1)⟩
  · rintro rfl
    exact ⟨fun _ hp => (ZFSet.mem_sep.mp hp).1, fun s t => pair_mem_childRelation c s t⟩

lemma wellFounded_childRelation_iff (c : BorelExpression) :
    WellFounded (fun t s : (finiteSequences : ZFSet.{u}) =>
      pair t.val s.val ∈ childRelation c.labelGraph) ↔ WellFounded c.Child := by
  constructor
  · intro hw
    apply (InvImage.wf wordEquiv.{u} hw).mono
    intro t s hts
    exact (pair_mem_childRelation c t s).mpr hts
  · intro hw
    apply (InvImage.wf wordEquiv.{u}.symm hw).mono
    intro t s hts
    apply (pair_mem_childRelation c (wordEquiv.{u}.symm t) (wordEquiv.{u}.symm s)).mp
    change pair (wordEquiv.{u} (wordEquiv.{u}.symm t)).val
      (wordEquiv.{u} (wordEquiv.{u}.symm s)).val ∈ _
    simpa only [Equiv.apply_symm_apply] using hts

/-- Parameters omega, words, zero, one, two, root word, square of words, candidate label graph. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Put
    $$R_\ell:=\{\langle t,s\rangle\in T\times T:
    J(t,s)\land\ell(t)\ne0\land\ell(s)\ne0\}.$$
    The relation graph belongs to $M$ when $\ell\in M$. Let $W(T,R)$ be the internal subset-minimum formula
    of §{sec:internal-rank-existence}: every nonempty subset of $T$ belonging to the model has an $R$-minimal
    member. Define a first-order formula $\Phi(\ell)$ by requiring that $\ell:T\to\omega$, that $L(\ell)$ holds,
    and that there exists a relation graph $R=R_\ell$ satisfying $W(T,R)$.
    The relation equation is bounded, using a subset of $T\times T$ and tests on all pairs of nodes.
    The well-foundedness clause uses the subset-minimum formula; we do not regard it as a local bounded test.
-/
def validLabelFormula : ForcingFormulas.Formula 8 :=
  functionFormula 1 0 7 ⊓ reindex localShapePredicate.compile ![0, 1, 2, 3, 4, 5, 7] ⊓
    (reindex childGraphPredicate.compile ![0, 1, 2, 7, 6, 8] ⊓
      reindex internalOrderMinimaFormula ![1, 8]).ex

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence)

include hM hinf hpair hunion hpower hsep hrep hchoice in
/-- Internal recognition includes actual well-foundedness, not merely the local label clauses. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal recognition of Borel validity
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The bounded function and local-rule predicates have their actual meanings in the transitive model.
    The preceding lemma therefore recovers the expression and its local rules. Bounded recognition of the relation
    graph identifies $R$ with $R_\ell$, whose edges are exactly the live-child edges under the bijection $e$.
    By §{sec:internal-rank-existence}, $M\models W(T,R_\ell)$ is equivalent to actual well-foundedness of this
    relation. Pulling the relation back along $e$ gives precisely the remaining validity clause for the expression.
    Conversely, an externally valid expression supplies the local rules and actual well-foundedness.
    Its relation graph belongs to $M$, and actual well-foundedness supplies minima for all internal nonempty
    subsets. Thus the same graph witnesses $\Phi(\ell)$ in $M$.
-/
theorem realize_validLabelFormula (Ω T z o b e K l : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hT : T.val = finiteSequences)
    (hz : z.val = natOrdinal 0) (ho : o.val = natOrdinal 1) (hb : b.val = natOrdinal 2)
    (he : e.val = wordGraph []) (hK : K.val = ZFSet.prod finiteSequences finiteSequences) :
    validLabelFormula.Realize Empty.elim ![Ω, T, z, o, b, e, K, l] ↔
      ∃ c : BorelExpression, c.Valid ∧ c.labelGraph = l.val := by
  have hf : (functionFormula (1 : Fin 8) 0 7).Realize Empty.elim ![Ω,T,z,o,b,e,K,l] ↔
      IsFunc finiteSequences Ordinal.omega0.toZFSet l.val := by
    have hf0 : (functionFormula (1 : Fin 8) 0 7).Realize Empty.elim ![Ω,T,z,o,b,e,K,l] ↔
        IsFunc T.val Ω.val l.val :=
      realize_functionFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) 1 0 7 _
    simpa only [hT, hΩ] using hf0
  have hs : (reindex localShapePredicate.compile ![0,1,2,3,4,5,7]).Realize Empty.elim
      ![Ω,T,z,o,b,e,K,l] ↔ localShapePredicate.eval ![Ordinal.omega0.toZFSet, finiteSequences,
        natOrdinal 0, natOrdinal 1, natOrdinal 2, wordGraph [], l.val] := by
    rw [realize_reindex, localShapePredicate.realize_compile hM]
    have hv : Subtype.val ∘ (![Ω,T,z,o,b,e,K,l] ∘ ![0,1,2,3,4,5,7]) =
        ![Ω.val,T.val,z.val,o.val,b.val,e.val,l.val] := by funext i; fin_cases i <;> rfl
    rw [hv, hΩ, hT, hz, ho, hb, he]
  have hr (R : M) : (reindex childGraphPredicate.compile ![0,1,2,7,6,8]).Realize Empty.elim
      (Fin.snoc ![Ω,T,z,o,b,e,K,l] R) ↔ childGraphPredicate.eval
        ![Ordinal.omega0.toZFSet, finiteSequences, natOrdinal 0, l.val,
          ZFSet.prod finiteSequences finiteSequences, R.val] := by
    rw [realize_reindex, childGraphPredicate.realize_compile hM]
    have hv : Subtype.val ∘ (Fin.snoc ![Ω,T,z,o,b,e,K,l] R ∘ ![0,1,2,7,6,8]) =
        ![Ω.val,T.val,z.val,l.val,K.val,R.val] := by funext i; fin_cases i <;> rfl
    rw [hv, hΩ, hT, hz, hK]
  have hm (R : M) : (reindex internalOrderMinimaFormula ![1,8]).Realize Empty.elim
      (Fin.snoc ![Ω,T,z,o,b,e,K,l] R) ↔
        internalOrderMinimaFormula.Realize Empty.elim ![T,R] := by
    rw [realize_reindex]
    have hv : Fin.snoc ![Ω,T,z,o,b,e,K,l] R ∘ ![1,8] = ![T,R] := by
      funext i; fin_cases i <;> rfl
    rw [hv]
  simp only [validLabelFormula, BoundedFormula.realize_inf, BoundedFormula.realize_ex, hf, hs, hr, hm]
  constructor
  · rintro ⟨⟨hl, hshape⟩, R, hR, hmin⟩
    obtain ⟨c, hc⟩ := exists_labelGraph_of_isFunc hl
    rw [← hc, eval_childGraphPredicate] at hR
    have hw := (internal_minima_iff_wellFounded hM hinf hpair hunion hpower hsep hrep hchoice T R).mp hmin
    rw [hT, hR, wellFounded_childRelation_iff] at hw
    rw [← hc, eval_localShapePredicate] at hshape
    obtain ⟨h0, hp, hl, hu, hco⟩ := hshape
    exact ⟨c, ⟨h0, hp, hl, hu, hco, hw⟩, hc⟩
  · rintro ⟨c, hc, hcl⟩
    refine ⟨⟨hcl ▸ labelGraph_isFunc c, ?_⟩, ?_⟩
    · rw [← hcl, eval_localShapePredicate]
      exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1⟩
    · let R : M := ⟨_, childRelation_mem hM hinf hpair hunion hpower hsep l.property⟩
      refine ⟨R, ?_, ?_⟩
      · rw [← hcl, eval_childGraphPredicate]
        simp only [R, hcl]
      · have hw : WellFounded (fun t s : T.val => pair t.val s.val ∈ R.val) := by
          change WellFounded (fun t s : T.val => pair t.val s.val ∈ childRelation l.val)
          rw [hT, ← hcl, wellFounded_childRelation_iff]
          exact hc.2.2.2.2.2
        exact internal_minima_of_wellFounded hM T R hw

/-- The internal set of all label graphs of valid Borel expressions. -/
def internalValidCodes (M : ZFSet.{u}) : ZFSet.{u} :=
  (internalPowerSet M (ZFSet.prod finiteSequences Ordinal.omega0.toZFSet)).sep
    (fun l => ∃ c : BorelExpression, c.Valid ∧ c.labelGraph = l)

lemma mem_internalValidCodes {M l : ZFSet.{u}} :
    l ∈ internalValidCodes M ↔ l ∈ M ∧ ∃ c : BorelExpression, c.Valid ∧ c.labelGraph = l := by
  simp only [internalValidCodes, internalPowerSet, ZFSet.mem_sep]
  constructor
  · rintro ⟨⟨hl, _⟩, hc⟩
    exact ⟨hl, hc⟩
  · rintro ⟨hl, c, hc, rfl⟩
    exact ⟨⟨hl, (labelGraph_isFunc c).1⟩, c, hc, rfl⟩

include hM hinf hpair hunion hpower hsep hrep hchoice in
/-- Separation uses the recognition formula and the internal powerset, without an external enumeration. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Internal set of valid Borel codes
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Form the internal power set $P:=\InternalPowerSet{M}{T\times\omega}$ and apply Separation to $\Phi$ on $P$.
    Every actual label graph in $M$ lies in $P$, since it is a subset of $T\times\omega$.
    The recognition theorem identifies the resulting set exactly as claimed.
-/
theorem internalValidCodes_mem : internalValidCodes M ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let T : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let K : M := ⟨_, prod_mem_of_separation hM hpair hunion hpower (hsep _) T.property T.property⟩
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let z : M := ⟨_, hn 0⟩
  let o : M := ⟨_, hn 1⟩
  let b : M := ⟨_, hn 2⟩
  let e : M := ⟨_, hM.mem_trans (mem_finiteSequences.mpr ⟨[], rfl⟩) T.property⟩
  have hP : internalPowerSet M (ZFSet.prod finiteSequences Ordinal.omega0.toZFSet) ∈ M :=
    internalPowerSet_mem hM hpower
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) T.property Ω.property)
  change (internalPowerSet M (ZFSet.prod finiteSequences Ordinal.omega0.toZFSet)).sep
    (fun l => ∃ c : BorelExpression, c.Valid ∧ c.labelGraph = l) ∈ M
  apply separation_mem_of_absolute hM validLabelFormula (hsep _) ![Ω,T,z,o,b,e,K] hP
  intro l _
  have hv : Fin.snoc ![Ω,T,z,o,b,e,K] l = ![Ω,T,z,o,b,e,K,l] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  exact realize_validLabelFormula hM hinf hpair hunion hpower hsep hrep hchoice
    Ω T z o b e K l rfl rfl rfl rfl rfl rfl rfl

end PolishSpaceBook.BorelExpression
