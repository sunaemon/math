module

public import PolishSpaceBook.FirstOrderUniqueExistence

@[expose] public section

/-!
# Function definitions by uniquely satisfied graphs

Inputs occupy the first `n` variable positions, and the output occupies position
`n`. The hypotheses are actual proofs of universally closed unique-existence
formulas. Soundness supplies the unique value in each old model. Substitution
then proves the defining axiom. Constants are the nullary case throughout.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}

/-- A language consisting only of the fresh function symbols. -/
def functionSymbols (ι : ℕ → Type z) : Language where
  Functions := ι
  Relations _ := Empty

/-- A defining graph may use the inputs and one output variable. -/
structure FunctionDefinitions (L : Language.{u,v}) (ι : ℕ → Type z) where
  graph : ∀ {n}, ι n → AlphaFormula L
  freeVars : ∀ {n} (f : ι n), (graph f).fv ⊆ Finset.range (n + 1)

namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

abbrev inclusion : L →ᴸ L.sum (functionSymbols ι) := LHom.sumInl

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Function symbols.**
    Function notation requires uniqueness. Suppose $\theta(\vec{x},y)$ is an $L$-formula whose free variables are
    among the pairwise distinct variables in $\vec{x}$ and $y$, and suppose
    $$
    T \vdash \forall \vec{x}\,\exists! y\,\theta(\vec{x},y).
    $$
    Here unique existence abbreviates
    $$\exists!y\,\theta(\vec{x},y)
    \quad:\equiv\quad
    \exists y\,\bigl(\theta(\vec{x},y)\land
    \forall z\,(\theta(\vec{x},z)\to z=y)\bigr),$$
    where $z$ is fresh, and $\theta(\vec{x},z)$ is obtained by capture-avoiding substitution for $y$.
    The substitution lemma and assignment locality show that this formula says exactly that there is one and only one
    possible value of $y$. The comparison variable introduces no additional free parameter.
-/
def uniqueExistence {n : ℕ} (f : ι n) : AlphaFormula L := closeAll n (uniqueAt n (n + 1) (D.graph f))

def application {n : ℕ} (f : ι n) : (L.sum (functionSymbols ι)).Term ℕ :=
  .func (Sum.inr f) (fun i => .var i.val)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Add a fresh $n$-ary function symbol $f$ and the defining axiom
    $$
    \forall \vec{x}\,\theta(\vec{x},f(\vec{x})).
    $$
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Constants are the $0$-ary function case. If $T \vdash \exists! y\,\theta(y)$, a new constant $c$ may be added with axiom
    $\theta(c)$, and each occurrence of $c$ can be eliminated by replacing it with a fresh witness satisfying $\theta$.
-/
def definingAxiom {n : ℕ} (f : ι n) : AlphaFormula (L.sum (functionSymbols ι)) :=
  closeAll n (((D.graph f).mapLanguage inclusion).subst n (application f))

def theory (T : Set (AlphaFormula L)) : Set (AlphaFormula (L.sum (functionSymbols ι))) :=
  AlphaFormula.mapLanguage inclusion '' T ∪ {φ | ∃ n, ∃ f : ι n, φ = D.definingAxiom f}

theorem uniqueExistence_sentence {n : ℕ} (f : ι n) : D.uniqueExistence f ∈ Sentences L := by
  change (closeAll n (uniqueAt n (n + 1) (D.graph f))).fv = ∅
  rw [fv_closeAll, Finset.sdiff_eq_empty_iff_subset]
  intro x hx
  obtain ⟨hxn, hx⟩ := Finset.mem_erase.mp (fv_uniqueAt_subset _ _ _ hx)
  have := Finset.mem_range.mp (D.freeVars f hx)
  exact Finset.mem_range.mpr (by omega)

/-- The function term uses only its input variables. -/
theorem application_freeVars {n : ℕ} (f : ι n) : (application (L := L) f).varFinset ⊆ Finset.range n := by
  intro x hx
  change x ∈ Finset.univ.biUnion (fun i : Fin n => (Term.var i.val :
    (L.sum (functionSymbols ι)).Term ℕ).varFinset) at hx
  simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hx
  obtain ⟨i, rfl⟩ := hx
  exact Finset.mem_range.mpr i.isLt

/-- The substitution removes the output variable before the inputs are universally closed. -/
theorem definingAxiom_sentence {n : ℕ} (f : ι n) : D.definingAxiom f ∈ Sentences _ := by
  change (closeAll n (((D.graph f).mapLanguage inclusion).subst n (application f))).fv = ∅
  rw [fv_closeAll, Finset.sdiff_eq_empty_iff_subset, fv_subst, fv_mapLanguage]
  apply Finset.union_subset
  · intro x hx
    obtain ⟨hxn, hx⟩ := Finset.mem_erase.mp hx
    have := Finset.mem_range.mp (D.freeVars f hx)
    exact Finset.mem_range.mpr (by omega)
  · split_ifs
    · exact application_freeVars f
    · exact Finset.empty_subset _

/-- The proof hypothesis gives unique graph values in every model of the old theory. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Fix $\mathcal M\models T$. Soundness gives, for every input tuple $\vec{a}$, exactly one $b$ satisfying
    $\theta(\vec{a},b)$.
-/
theorem uniqueValues {T : Set (AlphaFormula L)} {M : Type w} (A : L.Structure M)
    (hT : TheoryRealize A T) (hp : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) :
    ∀ n (f : ι n) (s : ℕ → M), ∃! b, @AlphaFormula.Realize L M A (D.graph f) (Function.update s n b) := by
  let := A
  intro n f s
  have h : ∀ t : ℕ → M, (D.uniqueExistence f).Realize t := fun t => (hp n f).sound t (hT t)
  have hz : n + 1 ∉ (D.graph f).fv := by
    intro hx
    have := Finset.mem_range.mp (D.freeVars f hx)
    omega
  exact (realize_uniqueAt n (n + 1) (D.graph f) (by omega) hz s).mp
    ((forall_realize_closeAll n _).mp h s)

/-- Only input positions and the assigned output affect graph truth. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Assignment locality makes this assertion independent of values assigned outside the input
    and output variables.
-/
theorem realize_graph_assignment {M : Type w} [L.Structure M] (d : M) {n : ℕ} (f : ι n)
    (s : ℕ → M) (b : M) :
    (D.graph f).Realize (Function.update (RelationDefinitions.assignment d (fun i : Fin n => s i.val)) n b) ↔
      (D.graph f).Realize (Function.update s n b) := by
  apply AlphaFormula.realize_congr
  intro x hx
  have h := Finset.mem_range.mp (D.freeVars f hx)
  by_cases hxn : x = n
  · subst x; simp
  · have hlt : x < n := by omega
    simp [Function.update_of_ne hxn, RelationDefinitions.assignment, hlt]

/-- Choose the unique graph value for the given tuple. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Define $f^{\mathcal M'}(\vec{a})=b$, keeping the domain and all old interpretations.
-/
abbrev freshStructure {M : Type w} [L.Structure M] (d : M)
    (h : ∀ n (f : ι n) (s : ℕ → M), ∃! b, (D.graph f).Realize (Function.update s n b)) :
    (functionSymbols ι).Structure M where
  funMap := fun {n} f a => Classical.choose (h n f (RelationDefinitions.assignment d a)).exists
  RelMap := fun R => nomatch R

/-- Substitution interprets the defining axiom as membership of the function value in its graph. -/
theorem realize_axiom_iff {M : Type w} [L.Structure M] [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M] {n : ℕ} (f : ι n) :
    (∀ s : ℕ → M, (D.definingAxiom f).Realize s) ↔
      ∀ s : ℕ → M, (D.graph f).Realize
        (Function.update s n (Structure.funMap (L := L.sum (functionSymbols ι)) (Sum.inr f) (fun i => s i.val))) := by
  rw [definingAxiom, forall_realize_closeAll]
  apply forall_congr'
  intro s
  rw [realize_subst, mapLanguage_realize_expansion]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The substitution lemma shows that $\theta(\vec{x},f(\vec{x}))$ holds at every assignment, so its universal closure
    holds in the expansion.
-/
theorem freshStructure_satisfies {M : Type w} [L.Structure M] (d : M)
    (h : ∀ n (f : ι n) (s : ℕ → M), ∃! b, (D.graph f).Realize (Function.update s n b))
    {n : ℕ} (f : ι n) :
    letI := D.freshStructure d h
    ∀ s : ℕ → M, (D.definingAxiom f).Realize s := by
  let := D.freshStructure d h
  apply (D.realize_axiom_iff f).mpr
  intro s
  exact (D.realize_graph_assignment d f s _).mp
    (Classical.choose_spec (h n f (RelationDefinitions.assignment d (fun i : Fin n => s i.val))).exists)

/-- The chosen interpretations give an expansion satisfying the old theory and the graph axioms. -/
theorem exists_expansion {T : Set (AlphaFormula L)} {M : Type w} (A : L.Structure M)
    (hne : Nonempty M) (hT : TheoryRealize A T)
    (hp : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) :
    ∃ B : (L.sum (functionSymbols ι)).Structure M,
      @LHom.IsExpansionOn _ _ inclusion M A B ∧ TheoryRealize B (D.theory T) := by
  let := A
  let d : M := Classical.choice hne
  let h := D.uniqueValues A hT hp
  let := D.freshStructure d h
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro s φ hφ
  rcases hφ with ⟨ψ, hψ, rfl⟩ | ⟨n, f, rfl⟩
  · exact (ψ.mapLanguage_realize_expansion inclusion s).mpr (hT s ψ hψ)
  · exact D.freshStructure_satisfies d h f s

/-- Unique graph values force every fresh operation, including the nullary ones. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Conversely, any expansion satisfying this axiom must assign to each input the unique
    value in its defining graph. Thus all function values are forced. Apply the construction separately to each
    new symbol in a family. An empty input tuple gives the required unique interpretation of a constant.
-/
theorem expansion_unique {M : Type w} (A : L.Structure M) (hne : Nonempty M)
    (h : ∀ n (f : ι n) (s : ℕ → M), ∃! b, @AlphaFormula.Realize L M A (D.graph f) (Function.update s n b))
    (B C : (L.sum (functionSymbols ι)).Structure M)
    (hB : @LHom.IsExpansionOn _ _ inclusion M A B)
    (hC : @LHom.IsExpansionOn _ _ inclusion M A C)
    (hb : ∀ n (f : ι n) s, @AlphaFormula.Realize _ M B (D.definingAxiom f) s)
    (hc : ∀ n (f : ι n) s, @AlphaFormula.Realize _ M C (D.definingAxiom f) s) : B = C := by
  apply structure_ext
  · intro n F a
    rcases F with F | f
    · exact (hB.map_onFunction F a).trans (hC.map_onFunction F a).symm
    · let s := RelationDefinitions.assignment (Classical.choice hne) a
      let := A
      have left : (D.graph f).Realize (Function.update s n (@Structure.funMap _ M B n (Sum.inr f) a)) := by
        let := B
        let : (inclusion (L := L) (ι := ι)).IsExpansionOn M := hB
        simpa only [s, RelationDefinitions.assignment_apply] using (D.realize_axiom_iff f).mp (hb n f) s
      have right : (D.graph f).Realize (Function.update s n (@Structure.funMap _ M C n (Sum.inr f) a)) := by
        let := C
        let : (inclusion (L := L) (ι := ι)).IsExpansionOn M := hC
        simpa only [s, RelationDefinitions.assignment_apply] using (D.realize_axiom_iff f).mp (hc n f) s
      exact (h n f s).unique left right
  · intro n R a
    rcases R with R | R
    · exact (hB.map_onRelation R a).trans (hC.map_onRelation R a).symm
    · exact nomatch R

/-- A proved unique-existence assertion gives a unique expansion by function definitions. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Unique expansion by function definitions
-/
theorem existsUnique_expansion {T : Set (AlphaFormula L)} {M : Type w} (A : L.Structure M)
    (hne : Nonempty M) (hT : TheoryRealize A T)
    (hp : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) :
    ∃! B : (L.sum (functionSymbols ι)).Structure M,
      @LHom.IsExpansionOn _ _ inclusion M A B ∧ TheoryRealize B (D.theory T) := by
  obtain ⟨B, hB, hb⟩ := D.exists_expansion A hne hT hp
  refine ⟨B, ⟨hB, hb⟩, ?_⟩
  intro C hC
  exact D.expansion_unique A hne (D.uniqueValues A hT hp) C B hC.1 hB
    (fun n f s => hC.2 s _ (Or.inr ⟨n, f, rfl⟩))
    (fun n f s => hb s _ (Or.inr ⟨n, f, rfl⟩))

/-- Function and constant definitions create no new old-language theorems. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For function symbols and constants, use \termuse{unique expansion by function definitions}.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For relation definitions, \termuse{syntactic conservativity of relation definitions} gives a direct transformation
    of proofs. The model argument above also covers the function and constant definitions.
-/
theorem conservative {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hp : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {σ : AlphaFormula L} (hσ : σ ∈ Sentences L)
    (hσ' : ProvesFrom (D.theory T) (σ.mapLanguage inclusion)) : ProvesFrom T σ :=
  conservative_of_model_expansion inclusion hT (fun _ A hne h => D.exists_expansion A hne h hp) hσ hσ'

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
