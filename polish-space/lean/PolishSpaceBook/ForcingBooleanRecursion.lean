module

public import PolishSpaceBook.ForcingBooleanValues

@[expose] public section

/-! # Recursive Boolean clauses and internally collected quantifier values -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic
universe u

variable {M : ZFSet.{u}} (B : M) [BooleanAlgebra (BooleanElement B.val)]
  (A : InternalBooleanAlgebra B)
  (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

local notation "V" => booleanValue B A hM hinf hpair hunion hpower hsep hrep
local notation "force_le" => force_iff_le_booleanValue B A hM hinf hpair hunion hpower hsep hrep

lemma booleanValue_le_iff {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) (b : BooleanElement B.val) :
    V φ xs ≤ b ↔ ∀ p ∈ force (positiveSet B) M φ xs, element B p ≤ b := by
  constructor
  · intro h p hp
    exact ((force_le φ xs p).mp hp).trans h
  · intro h
    by_cases hz : V φ xs = ⊥
    · rw [hz]; exact bot_le
    · exact h (positive B (V φ xs) hz) ((force_le φ xs _).mpr le_rfl)

theorem booleanValue_falsum {n : ℕ} (xs : Fin n → Name (positiveSet B) M) :
    V .falsum xs = ⊥ := by
  apply le_antisymm _ bot_le
  rw [booleanValue_le_iff]
  intro p hp
  exact hp.elim

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The recursive clauses for $[\![\varphi]\!]$ are the Boolean-algebra versions of the tripos operations: conjunction is
    meet, disjunction is join, implication is Boolean implication, $\exists$ is a join over witnesses, and $\forall$ is a
    meet over witnesses.
-/
theorem booleanValue_imp {n : ℕ} (φ ψ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : V (φ.imp ψ) xs = V φ xs ⇨ V ψ xs := by
  apply eq_of_positive_le_iff B
  intro p
  rw [← force_le, le_himp_iff]
  change (∀ q ≤ p, q ∈ force (positiveSet B) M φ xs → q ∈ force (positiveSet B) M ψ xs) ↔ _
  constructor
  · intro h
    by_cases hz : element B p ⊓ V φ xs = ⊥
    · rw [hz]; exact bot_le
    · let q := positive B (element B p ⊓ V φ xs) hz
      exact (force_le ψ xs q).mp (h q inf_le_left ((force_le φ xs q).mpr inf_le_right))
  · intro h q hqp hφ
    exact (force_le ψ xs q).mpr ((le_inf hqp ((force_le φ xs q).mp hφ)).trans h)

theorem booleanValue_not {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : V φ.not xs = (V φ xs)ᶜ := by
  change V (φ.imp .falsum) xs = _
  rw [booleanValue_imp, booleanValue_falsum, himp_bot]

theorem booleanValue_top {n : ℕ} (xs : Fin n → Name (positiveSet B) M) :
    V (⊤ : ForcingFormulas.Formula n) xs = ⊤ := by
  change V (BoundedFormula.not (.falsum : ForcingFormulas.Formula n)) xs = ⊤
  rw [booleanValue_not, booleanValue_falsum, compl_bot]

theorem booleanValue_and {n : ℕ} (φ ψ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : V (φ ⊓ ψ) xs = V φ xs ⊓ V ψ xs := by
  apply eq_of_positive_le_iff B
  intro p
  rw [← force_le, force_and, Set.mem_inter_iff, le_inf_iff, ← force_le, ← force_le]

theorem booleanValue_or {n : ℕ} (φ ψ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : V (φ ⊔ ψ) xs = V φ xs ⊔ V ψ xs := by
  change V (φ.not.imp ψ) xs = _
  rw [booleanValue_imp, booleanValue_not, himp_eq, compl_compl, sup_comm]

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a complete Boolean algebra $\mathbb B$, forcing is classical. The Boolean operations decide every truth value by
    $$
    [\![\varphi\lor\neg\varphi]\!]=1_{\mathbb B}.
    $$
-/
theorem booleanValue_excluded_middle {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) : V (φ ⊔ φ.not) xs = ⊤ := by
  rw [booleanValue_or, booleanValue_not, sup_compl_eq_top]

/-- The all-clause is an actual greatest lower bound, without postulating
completeness for the externally indexed type of all ground-model names. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    In particular, a Boolean element is below the value of
    $\forall x\,\psi(x)$ exactly when it is below every value of $\psi(\tau)$ for a name $\tau$ in $M$;
    the existential clause follows by complements.
-/
theorem booleanValue_all_isGLB {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) :
    IsGLB (Set.range (fun τ => V φ (Fin.snoc xs τ))) (V φ.all xs) := by
  constructor
  · rintro b ⟨τ, rfl⟩
    rw [booleanValue_le_iff]
    intro p hp
    exact (force_le φ (Fin.snoc xs τ) p).mp (hp τ)
  · intro b hb
    by_cases hz : b = ⊥
    · rw [hz]; exact bot_le
    · apply (force_le φ.all xs (positive B b hz)).mp
      intro τ
      exact (force_le φ (Fin.snoc xs τ) _).mpr (hb ⟨τ, rfl⟩)

theorem booleanValue_exists_isLUB {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) :
    IsLUB (Set.range (fun τ => V φ (Fin.snoc xs τ))) (V φ.ex xs) := by
  have hall := booleanValue_all_isGLB B A hM hinf hpair hunion hpower hsep hrep φ.not xs
  change IsLUB _ (V φ.not.all.not xs)
  rw [booleanValue_not]
  constructor
  · rintro b ⟨τ, rfl⟩
    apply le_compl_comm.mp
    simpa only [booleanValue_not] using hall.1 ⟨τ, rfl⟩
  · intro b hb
    apply compl_le_iff_compl_le.mpr
    apply hall.2
    rintro a ⟨τ, rfl⟩
    change bᶜ ≤ V φ.not (Fin.snoc xs τ)
    rw [booleanValue_not]
    exact compl_le_compl (hb ⟨τ, rfl⟩)

/-- For a fixed formula, its Boolean value is defined by its positive principal
ideal. The final parameter is a Boolean element, not a condition. -/
def booleanValueFormula {n : ℕ} (φ : ForcingFormulas.Formula n) : ForcingFormulas.Formula (n + 3) :=
  boundedAll (Fin.last n).castSucc.castSucc
    ((reindex (forcingTranslation φ) (conditionBinderIndex n)).iff
      (pairMemberFormula (Fin.last (n + 1)).castSucc.castSucc (Fin.last (n + 3))
        (Fin.last (n + 2)).castSucc))

def elementInModel (b : BooleanElement B.val) : M :=
  ⟨b.val, hM.mem_trans b.property B.property⟩

theorem booleanValue_definable {n : ℕ} (φ : ForcingFormulas.Formula n)
    (xs : Fin n → Name (positiveSet B) M) (b : BooleanElement B.val) :
    (booleanValueFormula φ).Realize Empty.elim
      (forcingAssignment (fun i => nameInModel (xs i)) (positiveInModel B hM hsep)
        A.orderCode (elementInModel B hM b)) ↔ b = V φ xs := by
  simp only [booleanValueFormula, realize_boundedAll_model, BoundedFormula.realize_iff,
    realize_reindex, forcingAssignment_condition, realize_pairMemberFormula_model hM]
  simp only [forcingAssignment, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply eq_of_positive_le_iff B
    intro p
    have hpM : p.val ∈ M := hM.mem_trans p.property (positiveSet_mem B hM hsep)
    have hh := h ⟨p.val, hpM⟩ p.property
    have hf := forcing_definable hM hinf hpair hunion hpower hsep hrep
      (positiveInModel B hM hsep) A.orderCode (A.positive_order_iff B) φ xs p
    exact ((A.order_iff (element B p) b).symm.trans hh.symm).trans (hf.trans (force_le φ xs p))
  · rintro rfl p hp
    let q : Condition (positiveSet B) := ⟨p.val, hp⟩
    exact (forcing_definable hM hinf hpair hunion hpower hsep hrep
      (positiveInModel B hM hsep) A.orderCode (A.positive_order_iff B) φ xs q).trans
      ((force_le φ xs q).trans (A.order_iff (element B q) _).symm)

/-- The quantified variable is a name; reindexing moves it beside the existing
name parameters while keeping P, R and the candidate value fixed. -/
def witnessValueFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    ForcingFormulas.Formula (n + 3) :=
  ((reindex nameFormula ![(Fin.last n).castSucc.castSucc.castSucc, Fin.last (n + 3)]) ⊓
    (reindex (booleanValueFormula φ) (nameBinderIndex n))).ex

def witnessValues {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) : ZFSet.{u} :=
  B.val.sep (fun b => ∃ τ : Name (positiveSet B) M, (V φ (Fin.snoc xs τ)).val = b)

theorem witnessValue_definable {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) (b : BooleanElement B.val) :
    (witnessValueFormula φ).Realize Empty.elim
      (forcingAssignment (fun i => nameInModel (xs i)) (positiveInModel B hM hsep)
        A.orderCode (elementInModel B hM b)) ↔
      ∃ τ : Name (positiveSet B) M, (V φ (Fin.snoc xs τ)).val = b.val := by
  simp only [witnessValueFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, forcingAssignment_name, forcingAssignment_name_test]
  constructor
  · rintro ⟨τ, hτ, hv⟩
    let τN : Name (positiveSet B) M := ⟨τ.val, τ.property,
      (name_definable hM hinf hpair hunion hpower hsep hrep (positiveInModel B hM hsep) τ).mp hτ⟩
    refine ⟨τN, ?_⟩
    have he : (nameInModel ∘ Fin.snoc xs τN) =
        Fin.snoc (fun i => nameInModel (xs i)) τ := apply_snoc nameInModel xs τN
    dsimp only [Function.comp_def] at he
    have hh := (booleanValue_definable B A hM hinf hpair hunion hpower hsep hrep φ (Fin.snoc xs τN) b)
    rw [he] at hh
    exact congrArg BooleanElement.val (hh.mp hv).symm
  · rintro ⟨τ, hτ⟩
    refine ⟨nameInModel τ,
      (name_definable hM hinf hpair hunion hpower hsep hrep
        (positiveInModel B hM hsep) (nameInModel τ)).mpr τ.property.2, ?_⟩
    have hh := (booleanValue_definable B A hM hinf hpair hunion hpower hsep hrep φ (Fin.snoc xs τ) b).mpr
      (BooleanElement.ext hτ.symm)
    simpa only [apply_snoc] using hh

/-- Separation on B collects all witness values, even though the class of
names itself is not assumed to be a set inside M. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    The witness values also form an actual set in $M$. Indeed, the value relation is definable by
    the displayed equivalence between forcing and the Boolean order. Applying Separation inside
    $\mathbb B$ to the assertion that some name $\tau$ has value $b$ for $\psi(\tau)$ gives a set
    $W_\psi\in M$. The existential value is the supremum of $W_\psi$ computed in $M$.
    This uses an internally defined set of Boolean values, without requiring a set of all names in $M$.
-/
theorem witnessValues_mem {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) : witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs ∈ M := by
  apply separation_mem_of_absolute hM (witnessValueFormula φ) (hsep _)
    (Fin.snoc (Fin.snoc (fun i => nameInModel (xs i)) (positiveInModel B hM hsep)) A.orderCode) B.property
  intro b hb
  exact witnessValue_definable B A hM hinf hpair hunion hpower hsep hrep φ xs ⟨b.val, hb⟩

lemma witnessValues_subset {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) :
    witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs ⊆ B.val := by
  intro b hb
  exact (mem_sep.mp hb).1

theorem booleanValue_exists_internalSup {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) :
    V φ.ex xs = A.internalSup B
      ⟨witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs,
        witnessValues_mem B A hM hinf hpair hunion hpower hsep hrep φ xs⟩
      (witnessValues_subset B A hM hinf hpair hunion hpower hsep hrep φ xs) := by
  apply (booleanValue_exists_isLUB B A hM hinf hpair hunion hpower hsep hrep φ xs).unique
  have he : {a : BooleanElement B.val | a.val ∈ witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs} =
      Set.range (fun τ => V φ (Fin.snoc xs τ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, witnessValues, mem_sep, Set.mem_range]
    constructor
    · rintro ⟨_, τ, hτ⟩
      exact ⟨τ, BooleanElement.ext hτ⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨(V φ (Fin.snoc xs τ)).property, τ, rfl⟩
  have hh := A.internalSup_isLUB B
    ⟨witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs,
      witnessValues_mem B A hM hinf hpair hunion hpower hsep hrep φ xs⟩
    (witnessValues_subset B A hM hinf hpair hunion hpower hsep hrep φ xs)
  rw [he] at hh
  exact hh

end PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
