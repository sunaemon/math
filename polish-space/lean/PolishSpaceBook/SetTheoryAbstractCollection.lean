module

public import PolishSpaceBook.SetTheoryAbstractHierarchy

@[expose] public section

/-! # Collection from the literal ZFC axioms in arbitrary membership models

Definable internal ranks and hierarchy stages supply a least witness stage.
Replacement collects these uniquely determined bounds; Union collects witnesses.
No transitivity or external well-foundedness of the model is assumed.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

def witnessStageBody {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 2) :=
  ordinalFormula (Fin.last (n + 1)) ⊓
    (reindex hierarchyValueBody ![(Fin.last (n + 1)).castSucc, Fin.last (n + 2)] ⊓
      boundedExists (Fin.last (n + 2))
        (reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc.castSucc)
          (Fin.last n).castSucc.castSucc.castSucc) (Fin.last (n + 3))))).ex

def WitnessStage (hM : M ⊨ fullZFCTheory) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (a α : M) : Prop :=
  IsOrdinalObject α ∧ ∃ b : M, member b (internalHierarchyObject hM α) ∧
    φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)

theorem realize_witnessStageBody (hM : M ⊨ fullZFCTheory) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a α : M) :
    (witnessStageBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) ↔ WitnessStage hM φ ps a α := by
  simp only [witnessStageBody, WitnessStage, BoundedFormula.realize_inf, BoundedFormula.realize_ex,
    realize_ordinalFormula, realize_boundedExists, realize_reindex, realize_hierarchyValueBody hM,
    Fin.comp_snoc, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.snoc_castSucc, Fin.snoc_last]
  simp only [Function.comp_def, Fin.snoc_castSucc, exists_eq_left]

def leastWitnessStageBody {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 2) :=
  witnessStageBody φ ⊓ boundedAll (Fin.last (n + 1))
    (reindex (witnessStageBody φ) (Fin.snoc (Fin.snoc
      (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc) (Fin.last (n + 2)))).not

def LeastWitnessStage (hM : M ⊨ fullZFCTheory) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (a α : M) : Prop :=
  WitnessStage hM φ ps a α ∧ ∀ β : M, member β α → ¬WitnessStage hM φ ps a β

theorem realize_leastWitnessStageBody (hM : M ⊨ fullZFCTheory) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a α : M) :
    (leastWitnessStageBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) α) ↔
      LeastWitnessStage hM φ ps a α := by
  simp only [leastWitnessStageBody, LeastWitnessStage, BoundedFormula.realize_inf,
    realize_boundedAll, BoundedFormula.realize_not, realize_reindex, Fin.comp_snoc,
    Fin.snoc_castSucc, Fin.snoc_last]
  simp only [Function.comp_def, Fin.snoc_castSucc, realize_witnessStageBody hM]

theorem leastWitnessStage_unique (hM : M ⊨ fullZFCTheory) {n : ℕ}
    {φ : ForcingFormulas.Formula (n + 2)} {ps : Fin n → M} {a α β : M}
    (hα : LeastWitnessStage hM φ ps a α) (hβ : LeastWitnessStage hM φ ps a β) : α = β := by
  rcases ordinalObject_comparable hM hα.1.1 hβ.1.1 with hαβ | he | hβα
  · exact (hβ.2 α hαβ hα.1).elim
  · exact he
  · exact (hα.2 β hβα hβ.1).elim

theorem leastWitnessStage_existsUnique (hM : M ⊨ fullZFCTheory) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a : M)
    (hex : ∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃! α : M, LeastWitnessStage hM φ ps a α := by
  obtain ⟨b, hb⟩ := hex
  obtain ⟨α, hα, hbα⟩ := exists_ordinal_hierarchy_stage hM b
  have hχ := (realize_witnessStageBody hM φ ps a α).mpr ⟨hα, b, hbα, hb⟩
  obtain ⟨β, hβ, hmin⟩ := fullZFC_definable_minimum hM (witnessStageBody φ) (Fin.snoc ps a) ⟨α, hχ⟩
  have hleast : LeastWitnessStage hM φ ps a β :=
    ⟨(realize_witnessStageBody hM φ ps a β).mp hβ,
      fun γ hγβ hγ => hmin γ hγβ ((realize_witnessStageBody hM φ ps a γ).mpr hγ)⟩
  exact ⟨β, hleast, fun γ hγ => leastWitnessStage_unique hM hγ hleast⟩

def witnessBoundBody {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 2) :=
  (reindex (leastWitnessStageBody φ) (Fin.snoc (Fin.snoc
      (fun i => i.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc) (Fin.last (n + 2))) ⊓
    reindex hierarchyValueBody ![Fin.last (n + 2), (Fin.last (n + 1)).castSucc]).ex

theorem realize_witnessBoundBody (hM : M ⊨ fullZFCTheory) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a V : M) :
    (witnessBoundBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) V) ↔
      ∃ α : M, LeastWitnessStage hM φ ps a α ∧ V = internalHierarchyObject hM α := by
  simp only [witnessBoundBody, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_reindex, realize_hierarchyValueBody hM, Fin.comp_snoc, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.snoc_castSucc, Fin.snoc_last]
  simp only [Function.comp_def, Fin.snoc_castSucc, realize_leastWitnessStageBody hM]

theorem witnessBound_existsUnique (hM : M ⊨ fullZFCTheory) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (a : M)
    (hex : ∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃! V : M, (witnessBoundBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) V) := by
  obtain ⟨α, hα, huniq⟩ := leastWitnessStage_existsUnique hM φ ps a hex
  refine ⟨internalHierarchyObject hM α,
    (realize_witnessBoundBody hM φ ps a _).mpr ⟨α, hα, rfl⟩, ?_⟩
  intro V hV
  obtain ⟨β, hβ, he⟩ := (realize_witnessBoundBody hM φ ps a V).mp hV
  exact he.trans (congrArg (internalHierarchyObject hM) (huniq β hβ))

/-- Full Collection in every model of the literal ZFC axioms, with the given
formula and all parameters retained. No internal Choice is used to select witnesses. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We first derive the instance of Collection needed for the prenex conversion. Fix a formula
    $\theta(x,y,\vec p)$ and suppose $\forall x\in a\,\exists y\,\theta(x,y,\vec p)$.
    For each $x\in a$, let $\alpha_x$ be the least ordinal such that some $y\in V_{\alpha_x}$ satisfies
    $\theta(x,y,\vec p)$. Such a stage exists by the cumulative hierarchy in §{sec:zfc-cumulative-hierarchy}.
    To find the least stage, start with any stage containing a witness and put its ordinal index inside a transitive
    set. Separate the qualifying ordinals from that set and apply Foundation. Transitivity makes the resulting
    member minimal among all qualifying ordinals; ordinal comparison makes it the unique least one.
    Replacement collects the uniquely defined sets $V_{\alpha_x}$; their union $B$ contains a witness for every
    $x\in a$. Consequently ZFC proves
    $$
    \forall x\in a\,\exists y\,\theta(x,y,\vec p)
    \quad\Longleftrightarrow\quad
    \exists B\,\forall x\in a\,\exists y\in B\,\theta(x,y,\vec p).
    $$
    The reverse implication is immediate. This argument selects least stages, without selecting individual witnesses.
    The constructions take place inside any model of ZFC: ordinal comparison and induction follow from its
    Foundation and Separation axioms, and the hierarchy is given by internal definable recursion. No external
    well-foundedness of the model's membership relation is required.
-/
theorem fullZFC_collection (hM : M ⊨ fullZFCTheory) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (A : M)
    (htotal : ∀ a : M, member a A → ∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃ B : M, ∀ a : M, member a A → ∃ b : M,
      member b B ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  obtain ⟨Y, hY⟩ := (realize_replacement M (witnessBoundBody φ)).mp
    (hM.realize_of_mem _ (ZFCAxiom.replacement _)) ps A
    (fun a ha => witnessBound_existsUnique hM φ ps a (htotal a ha))
  obtain ⟨B, hB⟩ := (models_union_iff M).mp (hM.realize_of_mem _ ZFCAxiom.union) Y
  refine ⟨B, ?_⟩
  intro a ha
  obtain ⟨V, hV, _⟩ := witnessBound_existsUnique hM φ ps a (htotal a ha)
  obtain ⟨α, hα, rfl⟩ := (realize_witnessBoundBody hM φ ps a V).mp hV
  obtain ⟨b, hb, hφ⟩ := hα.1.2
  exact ⟨b, (hB b).mpr ⟨_, hb, (hY _).mpr ⟨a, ha, hV⟩⟩, hφ⟩

/-- Strong Collection drops totality by separating the inputs with witnesses. -/
theorem fullZFC_strong_collection (hM : M ⊨ fullZFCTheory) {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (A : M) :
    ∃ B : M, ∀ a : M, member a A →
      (∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) →
      ∃ b : M, member b B ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  obtain ⟨D, hD⟩ := (realize_separation M φ.ex).mp (fullZFC_model_separation hM _) ps A
  have hd (a : M) : member a D ↔ member a A ∧
      ∃ b : M, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
    simpa only [BoundedFormula.realize_ex] using hD a
  obtain ⟨B, hB⟩ := fullZFC_collection hM φ ps D (fun a ha => ((hd a).mp ha).2)
  exact ⟨B, fun a ha hex => hB a ((hd a).mpr ⟨ha, hex⟩)⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
