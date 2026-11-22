module

public import PolishSpaceBook.InternalCohenClosedSets

@[expose] public section

/-! # The first-order assertion that an internal set is meager

Witness a countable cover by internally closed nowhere-dense sets with its whole
sequence graph. The bounded matrix is compiled by the shared reflection layer;
only the two witnesses (range and sequence graph) are unbounded quantifiers.
-/

noncomputable section
namespace PolishSpaceBook
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
open CantorTreeMeasure
universe u

/-- Parameters omega, conditions, binary points, covered set, range, sequence graph. -/
def cohenMeagerCoverPredicate : BoundedSetPredicate 6 :=
  .conj (.function 0 4 5)
    (.conj (.all 4 (.ex 0 (.pairMember 5 7 6)))
      (.conj (.all 4 (.conj (cohenClosedPredicate.rename ![1, 2, 6])
        (cohenNowhereDensePredicate.rename ![1, 6])))
        (.all 3 (.ex 4 (.member 6 7)))))

/-- Parameters omega, conditions, binary points, covered set; witnesses range and graph. -/
def cohenMeagerFormula : ForcingFormulas.Formula 4 := cohenMeagerCoverPredicate.compile.ex.ex

/-- An internal countable closed nowhere-dense cover, without a preselected list of Borel codes. -/
def InternalMeagerWitness (M A : ZFSet.{u}) : Prop :=
  ∃ V : ℕ → ZFSet.{u}, sequenceGraph V ∈ M ∧
    (∀ n, cohenClosedPredicate.eval ![cohenConditionSet Set.univ, internalCantor M, V n]) ∧
    (∀ n, cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, V n]) ∧
    A ⊆ sequenceUnion V

private lemma exists_sequenceGraph_of_isFunc {S F : ZFSet.{u}}
    (hf : IsFunc Ordinal.omega0.toZFSet S F) : ∃ V : ℕ → ZFSet.{u}, F = sequenceGraph V := by
  have hv (n : ℕ) : ∃ y, pair (natOrdinal n) y ∈ F :=
    (hf.2 _ (mem_omegaOrdinal.mpr ⟨n, rfl⟩)).exists
  choose V hV using hv
  refine ⟨V, ZFSet.ext fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp ha
    exact (pair_mem_sequenceGraph V n b).mpr
      ((hf.2 _ (mem_omegaOrdinal.mpr ⟨n, rfl⟩)).unique hp (hV n))
  · intro hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact hV n

private lemma eval_cohenMeagerCoverPredicate (M A S F : ZFSet.{u}) :
    cohenMeagerCoverPredicate.eval ![Ordinal.omega0.toZFSet, cohenConditionSet Set.univ,
      internalCantor M, A, S, F] ↔
      IsFunc Ordinal.omega0.toZFSet S F ∧
      (∀ B ∈ S, ∃ n, pair (natOrdinal n) B ∈ F) ∧
      (∀ B ∈ S, cohenClosedPredicate.eval ![cohenConditionSet Set.univ, internalCantor M, B] ∧
        cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, B]) ∧
      ∀ g ∈ A, ∃ B ∈ S, g ∈ B := by
  change (IsFunc Ordinal.omega0.toZFSet S F ∧
    (∀ B ∈ S, ∃ n ∈ Ordinal.omega0.toZFSet, pair n B ∈ F) ∧
    (∀ B ∈ S, cohenClosedPredicate.eval ![cohenConditionSet Set.univ, internalCantor M, B] ∧
      cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, B]) ∧
    ∀ g ∈ A, ∃ B ∈ S, g ∈ B) ↔ _
  simp only [exists_mem_omegaOrdinal]

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hunion : M ⊨ unionSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Internal meager-cover witnesses
-/
include hM hunion hsep
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    An internal witnessing function gives $A_n:=F(n)$; surjectivity identifies its range with $R$.
    Conversely, the range of an internal sequence graph belongs to the model by Union and Separation.
    Use that range as $R$ and the sequence graph as $F$.
    The bounded interpretation principle identifies the model's tests with the same tests on these sets.
-/
/-- Actual first-order satisfaction is equivalent to the internal-cover witnesses used in the proof. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    To express that an internal set $A$ is meager, use the first-order assertion
    $$
    \exists R\ \exists F\quad
    \begin{cases}
    F:\omega\twoheadrightarrow R,\\
    \forall B\in R\ \bigl(C(B)\land N(B)\bigr),\\
    A\IncludedIn\bigcup R.
    \end{cases}
    $$
    Here the function is represented by its graph, and the quantifiers over $R,F$ range over the model.
    After these two quantifiers, all quantifiers can be bounded by the displayed parameters.
-/
theorem realize_cohenMeagerFormula (Ω P Y A : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hP : P.val = cohenConditionSet Set.univ)
    (hY : Y.val = internalCantor M) :
    cohenMeagerFormula.Realize Empty.elim ![Ω, P, Y, A] ↔ InternalMeagerWitness M A.val := by
  have he (S F : M) :
      cohenMeagerCoverPredicate.compile.Realize Empty.elim
        (Fin.snoc (Fin.snoc ![Ω, P, Y, A] S) F) ↔
      cohenMeagerCoverPredicate.eval ![Ordinal.omega0.toZFSet, cohenConditionSet Set.univ,
        internalCantor M, A.val, S.val, F.val] := by
    rw [cohenMeagerCoverPredicate.realize_compile hM]
    have hv : Subtype.val ∘ Fin.snoc (Fin.snoc ![Ω, P, Y, A] S) F =
        ![Ordinal.omega0.toZFSet, cohenConditionSet Set.univ, internalCantor M, A.val, S.val, F.val] := by
      funext i
      fin_cases i <;> simp [hΩ, hP, hY]
    rw [hv]
  simp only [cohenMeagerFormula, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨S, F, hF⟩
    obtain ⟨hf, hsur, hsets, hcover⟩ := (eval_cohenMeagerCoverPredicate M A.val S.val F.val).mp ((he S F).mp hF)
    obtain ⟨V, hVG⟩ := exists_sequenceGraph_of_isFunc hf
    have hvS (n : ℕ) : V n ∈ S.val :=
      (ZFSet.pair_mem_prod.mp (hf.1 (hVG.symm ▸ (pair_mem_sequenceGraph V n _).mpr rfl))).2
    refine ⟨V, hVG ▸ F.property, fun n => (hsets _ (hvS n)).1,
      fun n => (hsets _ (hvS n)).2, ?_⟩
    intro g hg
    obtain ⟨B, hBS, hgB⟩ := hcover g hg
    obtain ⟨n, hn⟩ := hsur B hBS
    rw [hVG, pair_mem_sequenceGraph] at hn
    exact (mem_sequenceUnion V g).mpr ⟨n, hn ▸ hgB⟩
  · rintro ⟨V, hV, hclosed, hnd, hcover⟩
    let S : M := ⟨_, graphRange_mem hM hunion (hsep _) hV⟩
    let F : M := ⟨_, hV⟩
    refine ⟨S, F, (he S F).mpr ((eval_cohenMeagerCoverPredicate M A.val S.val F.val).mpr ?_)⟩
    refine ⟨sequenceGraph_isFunc V (fun n => (mem_sequenceRange V _).mpr ⟨n, rfl⟩), ?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨n, rfl⟩ := (mem_sequenceRange V B).mp hB
      exact ⟨n, (pair_mem_sequenceGraph V n _).mpr rfl⟩
    · intro B hB
      obtain ⟨n, rfl⟩ := (mem_sequenceRange V B).mp hB
      exact ⟨hclosed n, hnd n⟩
    · intro g hg
      obtain ⟨n, hn⟩ := (mem_sequenceUnion V g).mp (hcover hg)
      exact ⟨V n, (mem_sequenceRange V _).mpr ⟨n, rfl⟩, hn⟩

end PolishSpaceBook
