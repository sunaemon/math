module

public import PolishSpaceBook.FirstOrderHenkinStages

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# One language containing all Henkin stages

New constants are tagged by their birth stage. Retractions into any positive
stage preserve its symbols and send later constants to a fixed existing one.
They reflect contradictions back into that stage without using completeness.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v w u' v'

/-- Interpret a pure constant language by constant symbols of another language. -/
def constantsToSymbols {A : Type w} {K : Language.{u',v'}} (f : A → K.Constants) :
    Language.constantsOn A →ᴸ K where
  onFunction {n} c := match n with
    | 0 => f c
    | _ + 1 => isEmptyElim c
  onRelation {_} r := isEmptyElim r

def henkinLabels (L : Language.{u,v}) := (n : ℕ) × HenkinRequest (henkinStage L n)
def henkinLanguage (L : Language.{u,v}) := (henkinStage L 0)[[henkinLabels L]]

variable (L : Language.{u,v})

def henkinInclusion : (n : ℕ) → henkinStage L n →ᴸ henkinLanguage L
  | 0 => (henkinStage L 0).lhomWithConstants _
  | n + 1 => (henkinInclusion n).sumElim
      (constantsToSymbols (fun r => (henkinStage L 0).con (⟨n, r⟩ : henkinLabels L)))

theorem henkinInclusion_step (n : ℕ) :
    (henkinInclusion L (n + 1)).comp (henkinStep L n) = henkinInclusion L n := by
  exact LHom.sumElim_comp_inl _ _

theorem henkinInclusion_stageMap {n m : ℕ} (h : n ≤ m) :
    (henkinInclusion L m).comp (henkinStageMap L h) = henkinInclusion L n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | @succ m h ih =>
    rw [henkinStageMap_succ L h, ← LHom.comp_assoc, henkinInclusion_step, ih]

/-- A closed contradiction formula supplies an available request even in an empty language. -/
def defaultHenkinRequest : HenkinRequest (henkinStage L 0) :=
  ⟨0, falsum, by simp⟩

/-- Use the actual constant if it has been born; otherwise use the stage-one default. -/
def henkinConstantAt (n : ℕ) (a : henkinLabels L) : (henkinStage L (n + 1)).Constants :=
  if h : a.1 + 1 ≤ n + 1 then
    (henkinStageMap L h).onFunction ((henkinStage L a.1).con a.2)
  else
    (henkinStageMap L (Nat.succ_le_succ (Nat.zero_le n))).onFunction
      ((henkinStage L 0).con (defaultHenkinRequest L))

def henkinRetraction (n : ℕ) : henkinLanguage L →ᴸ henkinStage L (n + 1) :=
  (henkinStageMap L (Nat.zero_le (n + 1))).sumElim (constantsToSymbols (henkinConstantAt L n))

theorem henkinRetraction_stage (n k : ℕ) (h : k ≤ n + 1) :
    (henkinRetraction L n).comp (henkinInclusion L k) = henkinStageMap L h := by
  induction k with
  | zero => exact LHom.sumElim_comp_inl _ _
  | succ k ih =>
    have hk : k ≤ n + 1 := Nat.le_trans (Nat.le_succ k) h
    apply LHom.funext
    · funext ar f
      rcases f with f | c
      · change ((henkinRetraction L n).comp (henkinInclusion L k)).onFunction f =
          ((henkinStageMap L h).comp (henkinStep L k)).onFunction f
        rw [ih hk, henkinStageMap_step]
      · cases ar with
        | zero => simp [LHom.comp, henkinInclusion, LHom.sumElim, constantsToSymbols,
            henkinRetraction, henkinConstantAt, Language.con, Nat.le_of_succ_le_succ h]
        | succ ar => exact isEmptyElim c
    · funext ar r
      rcases r with r | r
      · change ((henkinRetraction L n).comp (henkinInclusion L k)).onRelation r =
          ((henkinStageMap L h).comp (henkinStep L k)).onRelation r
        rw [ih hk, henkinStageMap_step]
      · exact isEmptyElim r

@[simp] theorem henkinRetraction_inclusion (n : ℕ) :
    (henkinRetraction L n).comp (henkinInclusion L (n + 1)) = LHom.id _ := by
  simpa using henkinRetraction_stage L n (n + 1) (Nat.le_refl _)

/-- Each stage theory, now regarded inside the single final language. -/
def henkinImageTheory (T : Set (AlphaFormula L)) (n : ℕ) : Set (AlphaFormula (henkinLanguage L)) :=
  AlphaFormula.mapLanguage (henkinInclusion L n) '' henkinStageTheory L T n

variable {L}

theorem Consistent.henkinImageTheory {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) (n : ℕ) : Consistent (henkinImageTheory L T n) := by
  cases n with
  | zero => exact (hT.henkinStageTheory hclosed 0).withConstants
  | succ n =>
    intro hbad
    have hm := hbad.mapLanguage (henkinRetraction L n)
    apply hT.henkinStageTheory hclosed (n + 1)
    simpa [NamedFirstOrder.henkinImageTheory, Set.image_image, Function.comp_def, mapLanguage_comp] using hm

theorem henkinImageTheory_mono (T : Set (AlphaFormula L)) : Monotone (henkinImageTheory L T) := by
  apply monotone_nat_of_le_succ
  intro n ψ hψ
  obtain ⟨φ, hφ, rfl⟩ := hψ
  refine ⟨φ.mapLanguage (henkinStep L n), henkinStageTheory_step hφ, ?_⟩
  simp only [mapLanguage_comp, henkinInclusion_step]


/-- All stage theories in the fixed final language. -/
def henkinLimitTheory (T : Set (AlphaFormula L)) : Set (AlphaFormula (henkinLanguage L)) :=
  ⋃₀ Set.range (henkinImageTheory L T)

theorem henkinImageTheory_subset_limit (T : Set (AlphaFormula L)) (n : ℕ) :
    henkinImageTheory L T n ⊆ henkinLimitTheory T :=
  Set.subset_sUnion_of_mem ⟨n, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The \termuse{Henkin witness family lemma} proves by induction that $T_n$ is consistent in $L_n$ for every $n$.
    It remains consistent when regarded as a theory in $L_H$. For $n=0$, this follows from the
    \termuse{constant extension lemma}. For $n\ge 1$, one can also see it directly: $L_1$ already has a constant,
    since $\bot$ is eligible at stage zero. Fix a constant of $L_n$, fix every symbol of $L_n$, and send every
    later constant to the chosen one. This defines a symbol map from $L_H$ to $L_n$ whose restriction to $L_n$
    is the identity. Transporting a putative derivation of falsity from $T_n$ along this map gives a contradiction
    in $L_n$. Finally, any derivation from $S$ uses finitely many axioms, all contained in one $T_n$.
    Thus $S$ is consistent.
-/
theorem Consistent.henkinLimitTheory {T : Set (AlphaFormula L)} (hT : Consistent T)
    (hclosed : T ⊆ Sentences L) : Consistent (henkinLimitTheory T) := by
  apply Consistent.sUnion (henkinImageTheory_mono T).isChain_range
  · exact ⟨_, ⟨0, rfl⟩⟩
  · rintro _ ⟨n, rfl⟩
    exact hT.henkinImageTheory hclosed n

theorem henkinLimitTheory_sentences {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L) :
    henkinLimitTheory T ⊆ Sentences (henkinLanguage L) := by
  rintro φ ⟨_, ⟨n, rfl⟩, ψ, hψ, rfl⟩
  simpa [Sentences] using henkinStageTheory_sentences hT n hψ

end PolishSpaceBook.NamedFirstOrder
