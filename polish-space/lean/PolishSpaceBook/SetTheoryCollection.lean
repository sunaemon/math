module

public import PolishSpaceBook.SetTheoryInternalHierarchy

@[expose] public section

/-! # Collection from Replacement using least witness stages, without internal Choice -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

lemma apply_pair_assignment {α β : Type*} (f : α → β) (a b : α) :
    (fun i : Fin 2 => f (![a, b] i)) = ![f a, f b] := by
  ext i
  fin_cases i <;> rfl

lemma realize_ordinalFormula_model {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (x : Fin n) (xs : Fin n → M) :
    (ordinalFormula x).Realize Empty.elim xs ↔ (xs x).val.IsOrdinal :=
  realize_ordinalFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) x xs

/-- Parameters, input a, ordinal α; V and b are existentially bound. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Let $\vartheta(\alpha,V)$ be the defining formula for the internal cumulative stage from
    §{sec:internal-model-hierarchy}. With the fixed parameters understood, put
    $$\begin{aligned}
    \chi(a,\alpha)\;:\equiv\;&\mathrm{Ord}(\alpha)\land
     \exists V\,\bigl(\vartheta(\alpha,V)\\
     &{}\land\exists b\in V\,\varphi(\vec p,a,b)\bigr),\\
    \mu(a,\alpha)\;:\equiv\;&\chi(a,\alpha)\land\forall\beta\in\alpha\,\neg\chi(a,\beta).
    \end{aligned}$$
-/
def witnessStageFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 2) :=
  ordinalFormula (Fin.last (n + 1)) ⊓
    (reindex internalHierarchyFormula ![(Fin.last (n + 1)).castSucc, Fin.last (n + 2)] ⊓
      boundedExists (Fin.last (n + 2))
        (reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc.castSucc)
          (Fin.last n).castSucc.castSucc.castSucc) (Fin.last (n + 3))))).ex

lemma realize_witnessStageFormula_aux {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a α : M) :
    (witnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) ↔
      α.val.IsOrdinal ∧ ∃ V : M,
        internalHierarchyFormula.Realize Empty.elim ![α, V] ∧
        ∃ b : M, b.val ∈ V.val ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  simp only [witnessStageFormula, BoundedFormula.realize_inf, BoundedFormula.realize_ex,
    realize_ordinalFormula_model hM,
    realize_boundedExists_model, realize_reindex, apply_snoc, Function.comp_def,
    Fin.snoc_castSucc, Fin.snoc_last, apply_pair_assignment]

/-- A stage containing a witness, with no earlier stage containing one. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Let $\vartheta(\alpha,V)$ be the defining formula for the internal cumulative stage from
    §{sec:internal-model-hierarchy}. With the fixed parameters understood, put
    $$\begin{aligned}
    \chi(a,\alpha)\;:\equiv\;&\mathrm{Ord}(\alpha)\land
     \exists V\,\bigl(\vartheta(\alpha,V)\\
     &{}\land\exists b\in V\,\varphi(\vec p,a,b)\bigr),\\
    \mu(a,\alpha)\;:\equiv\;&\chi(a,\alpha)\land\forall\beta\in\alpha\,\neg\chi(a,\beta).
    \end{aligned}$$
-/
def leastWitnessStageFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    ForcingFormulas.Formula (n + 2) :=
  witnessStageFormula φ ⊓ boundedAll (Fin.last (n + 1))
    (reindex (witnessStageFormula φ)
      (Fin.snoc (fun i : Fin (n + 1) => i.castSucc.castSucc) (Fin.last (n + 2)))).not

lemma realize_leastWitnessStageFormula (M : ZFSet.{u}) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a α : M) :
    (leastWitnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) ↔
      (witnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) ∧
      ∀ β : M, β.val ∈ α.val →
        ¬ (witnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) β) := by
  simp only [leastWitnessStageFormula, BoundedFormula.realize_inf, realize_boundedAll_model,
    BoundedFormula.realize_not, realize_reindex, Function.comp_def, apply_snoc,
    Fin.snoc_castSucc, Fin.snoc_last]

/-- Return the entire least witness stage, rather than selecting one witness. -/
def witnessBoundFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 2) :=
  (reindex (leastWitnessStageFormula φ)
      (Fin.snoc (fun i : Fin (n + 1) => i.castSucc.castSucc) (Fin.last (n + 2))) ⊓
    reindex internalHierarchyFormula ![Fin.last (n + 2), (Fin.last (n + 1)).castSucc]).ex

lemma realize_witnessBoundFormula (M : ZFSet.{u}) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a V : M) :
    (witnessBoundFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) V) ↔
      ∃ α : M, (leastWitnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) ∧
        internalHierarchyFormula.Realize Empty.elim ![α, V] := by
  simp only [witnessBoundFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, Function.comp_def, apply_snoc, Fin.snoc_castSucc, Fin.snoc_last, apply_pair_assignment]

section Model
variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
include hM hinf hpair hunion hpower hsep hrep

lemma hierarchyFormula_iff (a V : M) (ha : a.val.IsOrdinal) :
    internalHierarchyFormula.Realize Empty.elim ![a, V] ↔ V.val = ZFSet.vonNeumann a.val.rank ∩ M := by
  have he : Fin.snoc (Fin.snoc Fin.elim0 a) V = ![a, V] := by ext i; fin_cases i <;> rfl
  rw [← he]
  exact realize_internalHierarchyFormula hM hinf hpair hunion hpower hsep hrep a V ha

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The defining-formula theorem and transitivity show that, for $a,\alpha\in M$,
    $$\begin{aligned}
    &M\models\chi(a,\alpha)\\
    &\quad\Longleftrightarrow\mathrm{Ord}(\alpha)\land\exists b\in M\,
     \bigl(\mathrm{rank}(b)<\alpha\\
    &\hspace{8em}{}\land M\models\varphi(\vec p,a,b)\bigr).
    \end{aligned}$$
-/
lemma realize_witnessStageFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (a α : M) :
    (witnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) ↔
      α.val.IsOrdinal ∧ ∃ b : M, b.val.rank < α.val.rank ∧
        φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  rw [realize_witnessStageFormula_aux hM]
  constructor
  · rintro ⟨hα, V, hV, b, hb, hφ⟩
    rw [(hierarchyFormula_iff hM hinf hpair hunion hpower hsep hrep α V hα).mp hV] at hb
    exact ⟨hα, b, ZFSet.mem_vonNeumann.mp (ZFSet.mem_inter.mp hb).1, hφ⟩
  · rintro ⟨hα, b, hb, hφ⟩
    have hαM : α.val.rank.toZFSet ∈ M := hα.toZFSet_rank_eq.symm ▸ α.property
    let V : M := ⟨ZFSet.vonNeumann α.val.rank ∩ M,
      internal_rank_segment_mem hM hinf hpair hunion hpower hsep hrep hαM⟩
    exact ⟨hα, V, (hierarchyFormula_iff hM hinf hpair hunion hpower hsep hrep α V hα).mpr rfl,
      b, ZFSet.mem_inter.mpr ⟨ZFSet.mem_vonNeumann.mpr hb, b.property⟩, hφ⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    If $b\in M$ is any witness, rank closure and successor closure put $\mathrm{rank}(b)+1$ in $M$.
    This ordinal satisfies the right side, so the set of ordinals of $M$ satisfying $\chi(a,\alpha)$ is nonempty.
    Its least member $\alpha_a$ satisfies $\mu(a,\alpha_a)$ internally.
    Conversely, ordinal comparison shows that any two internal solutions of $\mu(a,\alpha)$ are equal.
    Thus the least stage is uniquely defined, although the witnesses themselves need not be unique.
-/
lemma leastWitnessStage_existsUnique {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (a : M)
    (hex : ∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃! α : M, (leastWitnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) := by
  let S : Set Ordinal.{u} := {α | α.toZFSet ∈ M ∧ ∃ b : M, b.val.rank < α ∧
    φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)}
  have hS : S.Nonempty := by
    obtain ⟨b, hb⟩ := hex
    have hr := rank_mem_of_axioms hM hinf hpair hunion hpower hsep hrep b
    refine ⟨Order.succ b.val.rank, ?_, b, Order.lt_succ _, hb⟩
    change (b.val.rank + 1).toZFSet ∈ M
    rw [Ordinal.toZFSet_add_one]
    exact insert_mem hM hpair hunion hr hr
  obtain ⟨α, hα, hmin⟩ := wellFounded_lt.has_min S hS
  let αM : M := ⟨α.toZFSet, hα.1⟩
  have hleast : (leastWitnessStageFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) αM) := by
    rw [realize_leastWitnessStageFormula]
    constructor
    · apply (realize_witnessStageFormula hM hinf hpair hunion hpower hsep hrep φ ps a αM).mpr
      exact ⟨ZFSet.isOrdinal_toZFSet α, by simpa only [αM, Ordinal.rank_toZFSet] using hα.2⟩
    · intro β hβα hβ
      obtain ⟨hβord, b, hb, hφ⟩ :=
        (realize_witnessStageFormula hM hinf hpair hunion hpower hsep hrep φ ps a β).mp hβ
      have hβS : β.val.rank ∈ S := ⟨hβord.toZFSet_rank_eq.symm ▸ β.property, b, hb, hφ⟩
      apply hmin β.val.rank hβS
      have hlt := ZFSet.rank_lt_of_mem hβα
      simpa only [αM, Ordinal.rank_toZFSet] using hlt
  refine ⟨αM, hleast, ?_⟩
  intro β hβ
  obtain ⟨hw, hno⟩ := (realize_leastWitnessStageFormula M φ ps a β).mp hβ
  obtain ⟨hβord, b, hb, hφ⟩ :=
    (realize_witnessStageFormula hM hinf hpair hunion hpower hsep hrep φ ps a β).mp hw
  have hβS : β.val.rank ∈ S := ⟨hβord.toZFSet_rank_eq.symm ▸ β.property, b, hb, hφ⟩
  have he : β.val.rank = α := le_antisymm (le_of_not_gt (by
      intro hlt
      apply hno αM
      · rw [← hβord.toZFSet_rank_eq]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt
      · exact ((realize_leastWitnessStageFormula M φ ps a αM).mp hleast).1))
    (le_of_not_gt (hmin β.val.rank hβS))
  apply Subtype.ext
  change β.val = α.toZFSet
  rw [← hβord.toZFSet_rank_eq, he]

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    The first-order formula
    $$\zeta(a,V)\;:\equiv\;\exists\alpha\,\bigl(\mu(a,\alpha)\land\vartheta(\alpha,V)\bigr)$$
    therefore defines the unique set $V=\InternalHierarchy{M}{\alpha_a}\in M$.
-/
lemma witnessBound_existsUnique {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (a : M)
    (hex : ∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃! V : M, (witnessBoundFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) V) := by
  obtain ⟨α, hα, huniq⟩ := leastWitnessStage_existsUnique hM hinf hpair hunion hpower hsep hrep φ ps a hex
  have hw := ((realize_leastWitnessStageFormula M φ ps a α).mp hα).1
  have hαord := ((realize_witnessStageFormula hM hinf hpair hunion hpower hsep hrep φ ps a α).mp hw).1
  let V : M := ⟨ZFSet.vonNeumann α.val.rank ∩ M,
    internal_rank_segment_mem hM hinf hpair hunion hpower hsep hrep
      (hαord.toZFSet_rank_eq.symm ▸ α.property)⟩
  refine ⟨V, (realize_witnessBoundFormula M φ ps a V).mpr
    ⟨α, hα, (hierarchyFormula_iff hM hinf hpair hunion hpower hsep hrep α V hαord).mpr rfl⟩, ?_⟩
  intro W hW
  obtain ⟨β, hβ, hbW⟩ := (realize_witnessBoundFormula M φ ps a W).mp hW
  have he := huniq β hβ
  subst β
  exact Subtype.ext ((hierarchyFormula_iff hM hinf hpair hunion hpower hsep hrep α W hαord).mp hbW)

/-- Collect witnesses in a ground-model set without choosing a witness for each input. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Apply Replacement in $M$ to this set-valued function and then Union:
    $$Y:=\{\InternalHierarchy{M}{\alpha_a}:a\in x\}\in M,\qquad W:=\bigcup Y\in M.$$
    For each $a\in x$, some witness belongs to $\InternalHierarchy{M}{\alpha_a}$ and hence to $W$.
    We have collected entire stages; no choice of one witness per input was used.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    First suppose that every $a\in x$ has a witness in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Collection bounds witnesses to a relation that need not be single-valued.
    The internal cumulative stages provide such a bound without choosing one witness for each input.
-/
theorem collection_in_model {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (x : M)
    (htotal : ∀ a : M, a.val ∈ x.val → ∃ b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃ B : M, ∀ a : M, a.val ∈ x.val → ∃ b : M, b.val ∈ B.val ∧
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  have ht := fun a ha => witnessBound_existsUnique hM hinf hpair hunion hpower hsep hrep φ ps a (htotal a ha)
  obtain ⟨Y, hY⟩ := (realize_replacement M (witnessBoundFormula φ)).mp (hrep _) ps x ht
  refine ⟨⟨ZFSet.sUnion Y.val, union_mem hM hunion Y.property⟩, ?_⟩
  intro a ha
  obtain ⟨V, hV, _⟩ := ht a ha
  have hVY := (hY V).mpr ⟨a, ha, hV⟩
  obtain ⟨α, hα, hαV⟩ := (realize_witnessBoundFormula M φ ps a V).mp hV
  have hw := ((realize_leastWitnessStageFormula M φ ps a α).mp hα).1
  obtain ⟨hαord, b, hb, hφ⟩ :=
    (realize_witnessStageFormula hM hinf hpair hunion hpower hsep hrep φ ps a α).mp hw
  refine ⟨b, ZFSet.mem_sUnion.mpr ⟨V.val, hVY, ?_⟩, hφ⟩
  rw [(hierarchyFormula_iff hM hinf hpair hunion hpower hsep hrep α V hαord).mp hαV]
  exact ZFSet.mem_inter.mpr ⟨ZFSet.mem_vonNeumann.mpr hb, b.property⟩

/-- Inputs with no witness impose no requirement on the collected set. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    For the general case, first separate
    $$D:=\{a\in x:M\models\exists b\,\varphi(\vec p,a,b)\}\in M.$$
    Apply the total case to $D$. Inputs outside $D$ impose no condition, so the same $W$ proves the displayed assertion.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Collection in transitive models
-/
theorem strong_collection_in_model {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (x : M) :
    ∃ B : M, ∀ a : M, a.val ∈ x.val →
      (∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) →
      ∃ b : M, b.val ∈ B.val ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  obtain ⟨D, hD⟩ := (realize_separation M φ.ex).mp (hsep _) ps x
  have hd (a : M) : a.val ∈ D.val ↔ a.val ∈ x.val ∧
      ∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
    simpa only [BoundedFormula.realize_ex] using hD a
  obtain ⟨B, hB⟩ := collection_in_model hM hinf hpair hunion hpower hsep hrep φ ps D
    (fun a ha => ((hd a).mp ha).2)
  exact ⟨B, fun a ha hex => hB a ((hd a).mpr ⟨ha, hex⟩)⟩

end Model
end PolishSpaceBook.SetTheoryModels
