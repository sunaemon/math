module

public import PolishSpaceBook.FirstOrderLanguageSemantics

@[expose] public section

/-!
# Completeness by the constructed Henkin term model

A nonderivable sentence can be negated consistently. Henkin expansion and
maximal extension give a nonempty term model, and the truth lemma makes it
satisfy the theory while refuting that sentence. Taking a reduct returns to
the original language. The countermodel has the universe size of the syntax;
no semantic completeness theorem is imported to obtain it.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Apply the \termuse{term-model construction lemma} to form $\mathcal M_{T^*}$.
    Since $T\IncludedIn T^*$ and $\neg\varphi\in T^*$, the \termuse{Henkin truth lemma} shows that this model
    satisfies $T$ and falsifies $\varphi$.
-/
theorem termModel_satisfies {T : Set (AlphaFormula L)} (hT : MaximallyConsistent T)
    (hH : HasHenkinWitnesses T) : Nonempty (TermModel T) ∧ ∀ (s : ℕ → TermModel T) φ, φ ∈ T → φ.Realize s :=
  ⟨hH.nonempty_termModel, fun s φ hφ => (φ.termModel_truth_sentence hT hH (hT.sentences hφ) s).mpr hφ⟩

/-- The contrapositive of completeness, with an actual small countermodel. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For \emph{completeness}, prove the contrapositive. Suppose $T \nvdash \varphi$, where $T$ is a theory in a language $L$.
    The \termuse{first-order deduction and consistency lemma} shows that $T\cup\{\neg\varphi\}$ is consistent.
    Apply the \termuse{Henkin extension lemma} to obtain a consistent theory $S$ extending
    $T\cup\{\neg\varphi\}$ in a language $L_H$, with all Henkin witnesses.
-/
theorem exists_countermodel_of_not_proves {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    {φ : AlphaFormula L} (hφ : φ ∈ Sentences L) (hn : ¬ProvesFrom T φ) :
    ∃ (M : Type (max u v)) (inst : L.Structure M), Nonempty M ∧
      (∀ (s : ℕ → M) ψ, ψ ∈ T → @AlphaFormula.Realize L M inst ψ s) ∧
      (∀ s : ℕ → M, ¬@AlphaFormula.Realize L M inst φ s) := by
  have hc : Consistent (insert (neg φ) T) := by
    intro hbad
    exact hn (ProvesFrom.deduction.mp hbad).doubleNegElim
  have hs : insert (neg φ) T ⊆ Sentences L :=
    Set.insert_subset (by simpa [Sentences] using hφ) hT
  obtain ⟨U, hU, hH, hsub⟩ := exists_maximalHenkinExtension hc hs
  obtain ⟨hne, hmodel⟩ := termModel_satisfies hU hH
  let M := TermModel U
  let f := henkinBaseInclusion L
  refine ⟨M, f.reduct M, hne, ?_, ?_⟩
  · intro s ψ hψ
    apply (ψ.mapLanguage_realize_reduct f s).mp
    exact hmodel s _ (hsub ⟨ψ, Set.mem_insert_of_mem _ hψ, rfl⟩)
  · intro s
    have hneg : @AlphaFormula.Realize L M (f.reduct M) (neg φ) s :=
      ((neg φ).mapLanguage_realize_reduct f s).mp (hmodel s _ (hsub ⟨neg φ, Set.mem_insert _ _, rfl⟩))
    let : L.Structure M := f.reduct M
    exact (realize_neg φ s).mp hneg

/-- A consistent sentence theory has a nonempty model, constructed above. -/
theorem Consistent.exists_model {T : Set (AlphaFormula L)} (hT : Consistent T) (hclosed : T ⊆ Sentences L) :
    ∃ (M : Type (max u v)) (inst : L.Structure M), Nonempty M ∧
      ∀ (s : ℕ → M) ψ, ψ ∈ T → @AlphaFormula.Realize L M inst ψ s := by
  obtain ⟨M, inst, hne, hm, _⟩ := exists_countermodel_of_not_proves hclosed (φ := falsum) (by simp [Sentences]) hT
  exact ⟨M, inst, hne, hm⟩

/-- All models of the size of the syntax already suffice to test sentence consequence. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: Gödel completeness theorem
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Thus syntactic and semantic consequence coincide for models; the proper-class case is handled informally as noted in the
    Semantics paragraph.
-/
theorem proves_iff_small_model_consequence {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    {φ : AlphaFormula L} (hφ : φ ∈ Sentences L) :
    ProvesFrom T φ ↔ ∀ (M : Type (max u v)) (inst : L.Structure M), Nonempty M →
      ∀ s : ℕ → M, (∀ ψ ∈ T, @AlphaFormula.Realize L M inst ψ s) → @AlphaFormula.Realize L M inst φ s := by
  constructor
  · intro hp M inst _ s hs
    let := inst
    exact hp.sound s hs
  · intro h
    by_contra hn
    obtain ⟨M, inst, hne, hm, hf⟩ := exists_countermodel_of_not_proves hT hφ hn
    let s : ℕ → M := fun _ => Classical.choice hne
    exact hf s (h M inst hne s (hm s))

/-- An independent sentence has consistent opposite extensions and models disagreeing on it. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Only consistency is required, not soundness in the standard natural numbers or $\omega$-consistency.
    If $T$ is consistent, the two extensions $T\cup\{G\}$ and $T\cup\{\neg G\}$ are both consistent and hence have models
    by Gödel completeness. The models disagree on $G$, which explains why completeness of first-order logic and
    incompleteness of $T$ coexist. The second incompleteness theorem concerns the additional claim that $T$ cannot prove
    its own formalized consistency statement; that requires a separate analysis of the proof predicate inside $T$.
-/
theorem independent_sentence_has_disagreeing_models {T : Set (AlphaFormula L)}
    (hT : T ⊆ Sentences L) {φ : AlphaFormula L} (hφ : φ ∈ Sentences L)
    (hp : ¬ProvesFrom T φ) (hn : ¬ProvesFrom T (neg φ)) :
    Consistent (insert φ T) ∧ Consistent (insert (neg φ) T) ∧
      (∃ (M N : Type (max u v)) (A : L.Structure M) (B : L.Structure N),
        Nonempty M ∧ Nonempty N ∧
        (∀ (s : ℕ → M) ψ, ψ ∈ T → @AlphaFormula.Realize L M A ψ s) ∧
        (∀ (s : ℕ → N) ψ, ψ ∈ T → @AlphaFormula.Realize L N B ψ s) ∧
        (∀ s : ℕ → M, @AlphaFormula.Realize L M A φ s) ∧
        (∀ s : ℕ → N, ¬@AlphaFormula.Realize L N B φ s)) := by
  have hc : Consistent (insert φ T) := fun h => hn (ProvesFrom.deduction.mp h)
  have hd := Consistent.insert_neg_of_not_proves hp
  obtain ⟨M, A, hM, hm⟩ := hc.exists_model (Set.insert_subset hφ hT)
  have hneg : neg φ ∈ Sentences L := by simpa [Sentences] using hφ
  obtain ⟨N, B, hN, hmodel⟩ := hd.exists_model (Set.insert_subset hneg hT)
  refine ⟨hc, hd, M, N, A, B, hM, hN, ?_, ?_, ?_, ?_⟩
  · exact fun s ψ hψ => hm s ψ (Set.mem_insert_of_mem _ hψ)
  · exact fun s ψ hψ => hmodel s ψ (Set.mem_insert_of_mem _ hψ)
  · exact fun s => hm s φ (Set.mem_insert _ _)
  · intro s
    let := B
    exact (realize_neg φ s).mp (hmodel s (neg φ) (Set.mem_insert _ _))

end PolishSpaceBook.NamedFirstOrder
