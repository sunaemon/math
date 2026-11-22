module

public import PolishSpaceBook.FirstOrderExpansionConservativity

@[expose] public section

/-!
# Definitions of relation symbols

The new symbols have specified arities and old-language defining formulas.
Universal closure gives actual sentence axioms. Assignment locality makes the
interpretation independent of values outside the displayed argument list.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}}

namespace AlphaFormula

/-- Close the first `n` variable names; the outside quantifier is numbered `n - 1`. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{theory} in a language $L$ is a set $T$ of $L$-sentences, called its \termdefineas{axiom}{axioms}; the
    notation $T\vdash\varphi$ means that $\Gamma\vdash\varphi$ for some finite $\Gamma\IncludedIn T$. The
    consequences of $T$ are the sentences in its \termdefine{deductive closure} $\{\varphi : T \vdash \varphi\}$. When an
    axiom schema is written using an open formula, each instance is its universal closure: all free variables not explicitly
    bound in the displayed formula are universally quantified outside the displayed expression. In schemas with parameters,
    such as Replacement and Separation, the parameters are precisely those additional free variables before this universal
    closure is applied. \termdefine{ZFC} is the $L_\in$-theory whose axioms are listed in §{sec:zfc-axioms}.
-/
def closeAll : ℕ → AlphaFormula L → AlphaFormula L
  | 0, φ => φ
  | n + 1, φ => quant .all n (closeAll n φ)

@[simp] theorem fv_closeAll (n : ℕ) (φ : AlphaFormula L) :
    (closeAll n φ).fv = φ.fv \ Finset.range n := by
  induction n with
  | zero => simp [closeAll]
  | succ n ih =>
    rw [closeAll, fv_quant, ih]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_range]
    by_cases hx : x ∈ φ.fv
    · simp only [hx, true_and]
      omega
    · simp only [hx, and_false, false_and]

/-- Universal closure holds in a structure exactly when the body holds at every assignment. -/
theorem forall_realize_closeAll {M : Type w} [L.Structure M] (n : ℕ) (φ : AlphaFormula L) :
    (∀ s : ℕ → M, (closeAll n φ).Realize s) ↔ ∀ s : ℕ → M, φ.Realize s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    constructor
    · intro h s
      have hs := (realize_all n (closeAll n φ) s).mp (h s) (s n)
      simpa using hs
    · intro h s
      exact (realize_all n (closeAll n φ) s).mpr (fun a => h (Function.update s n a))

end AlphaFormula

/-- A language consisting only of the fresh relation symbols. -/
def relationSymbols (ι : ℕ → Type z) : Language where
  Functions _ := Empty
  Relations := ι

variable {ι : ℕ → Type z}

/-- A relation definition has no free variables beyond its argument positions. -/
structure RelationDefinitions (L : Language.{u,v}) (ι : ℕ → Type z) where
  formula : ∀ {n}, ι n → AlphaFormula L
  freeVars : ∀ {n} (r : ι n), (formula r).fv ⊆ Finset.range n

namespace RelationDefinitions
variable (D : RelationDefinitions L ι)

abbrev inclusion : L →ᴸ L.sum (relationSymbols ι) := LHom.sumInl

def atom {n : ℕ} (r : ι n) : AlphaFormula (L.sum (relationSymbols ι)) :=
  rel (Sum.inr r) (fun i => .var i.val)

def body {n : ℕ} (r : ι n) : AlphaFormula (L.sum (relationSymbols ι)) :=
  binary .conj (binary .imp (atom r) ((D.formula r).mapLanguage inclusion))
    (binary .imp ((D.formula r).mapLanguage inclusion) (atom r))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Relation symbols.**
    Suppose $\varphi(\vec{x})$ is an $L$-formula whose free variables are among the distinct variables in $\vec{x}$.
    Add a fresh $n$-ary relation symbol $R$ and the defining axiom
    $$
    \forall \vec{x}\,\bigl(R(\vec{x}) \leftrightarrow \varphi(\vec{x})\bigr).
    $$
-/
def definingAxiom {n : ℕ} (r : ι n) : AlphaFormula (L.sum (relationSymbols ι)) := closeAll n (D.body r)

def theory (T : Set (AlphaFormula L)) : Set (AlphaFormula (L.sum (relationSymbols ι))) :=
  AlphaFormula.mapLanguage inclusion '' T ∪ {φ | ∃ n, ∃ r : ι n, φ = D.definingAxiom r}

/-- An arbitrary default completes a finite tuple to a total assignment. -/
def assignment {M : Type w} (d : M) {n : ℕ} (a : Fin n → M) : ℕ → M :=
  fun x => if h : x < n then a ⟨x, h⟩ else d

@[simp] theorem assignment_apply {M : Type w} (d : M) {n : ℕ} (a : Fin n → M) (i : Fin n) :
    assignment d a i.val = a i := by simp [assignment, i.isLt]

theorem realize_assignment {M : Type w} [L.Structure M] (d : M) {n : ℕ} (r : ι n) (s : ℕ → M) :
    (D.formula r).Realize (assignment d (fun i : Fin n => s i.val)) ↔ (D.formula r).Realize s := by
  apply AlphaFormula.realize_congr
  intro x hx
  have h := Finset.mem_range.mp (D.freeVars r hx)
  simp [assignment, h]

/-- The interpretation prescribed by the defining formulas. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Keep the domain and the interpretations of all old symbols. For each tuple $\vec{a}$, choose an assignment $s$
    with $s(\vec{x})=\vec{a}$, and put
    $$\vec{a}\in R^{\mathcal M'}\quad\Longleftrightarrow\quad\mathcal M,s\models\varphi.$$
-/
abbrev freshStructure {M : Type w} [L.Structure M] (d : M) : (relationSymbols ι).Structure M where
  funMap := fun f => nomatch f
  RelMap := fun r a => (D.formula r).Realize (assignment d a)

/-- In any expansion, the axiom is exactly the required interpretation of the fresh symbol. -/
theorem realize_axiom_iff {M : Type w} [L.Structure M] [(L.sum (relationSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M] {n : ℕ} (r : ι n) :
    (∀ s : ℕ → M, (D.definingAxiom r).Realize s) ↔
      ∀ s : ℕ → M, Structure.RelMap (L := L.sum (relationSymbols ι)) (Sum.inr r) (fun i => s i.val) ↔
        (D.formula r).Realize s := by
  rw [definingAxiom, forall_realize_closeAll]
  apply forall_congr'
  intro s
  simp only [body, realize_conj, realize_imp, mapLanguage_realize_expansion]
  change ((Structure.RelMap (L := L.sum (relationSymbols ι)) (Sum.inr r) (fun i => s i.val) → (D.formula r).Realize s) ∧
    ((D.formula r).Realize s → Structure.RelMap (L := L.sum (relationSymbols ι)) (Sum.inr r) (fun i => s i.val))) ↔ _
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- The explicitly defined expansion satisfies every defining axiom. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Such an assignment exists because the domain is nonempty. Assignment locality shows that the right-hand side
    is independent of values outside $\vec{x}$. Old-language formulas have the same truth value in the expansion
    and its reduct, by induction on terms and formulas. Thus the displayed equivalence is exactly the defining axiom
    at an arbitrary tuple, so its universal closure holds.
-/
theorem freshStructure_satisfies {M : Type w} [L.Structure M] (d : M) {n : ℕ} (r : ι n) :
    letI := D.freshStructure d
    ∀ s : ℕ → M, (D.definingAxiom r).Realize s := by
  let := D.freshStructure d
  apply (D.realize_axiom_iff r).mpr
  intro s
  exact D.realize_assignment d r s


/-- The defining axiom is closed, including for nullary relation symbols. -/
theorem definingAxiom_sentence {n : ℕ} (r : ι n) : D.definingAxiom r ∈ Sentences _ := by
  change (closeAll n (D.body r)).fv = ∅
  rw [fv_closeAll, Finset.sdiff_eq_empty_iff_subset]
  have ha : (atom (L := L) r).fv ⊆ Finset.range n := by
    intro x hx
    change x ∈ Finset.univ.biUnion (fun i : Fin n => (Term.var i.val :
      (L.sum (relationSymbols ι)).Term ℕ).varFinset) at hx
    simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Finset.mem_range.mpr i.isLt
  simp only [body, fv_binary, fv_mapLanguage]
  exact Finset.union_subset (Finset.union_subset ha (D.freeVars r))
    (Finset.union_subset (D.freeVars r) ha)

/-- Keep the old interpretations and add the relations defined by the formulas. -/
theorem exists_expansion {T : Set (AlphaFormula L)} {M : Type w} (A : L.Structure M)
    (hne : Nonempty M) (hT : TheoryRealize A T) :
    ∃ B : (L.sum (relationSymbols ι)).Structure M,
      @LHom.IsExpansionOn _ _ inclusion M A B ∧ TheoryRealize B (D.theory T) := by
  let := A
  let d : M := Classical.choice hne
  let := D.freshStructure d
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro s φ hφ
  rcases hφ with ⟨ψ, hψ, rfl⟩ | ⟨n, r, rfl⟩
  · exact (ψ.mapLanguage_realize_expansion inclusion s).mpr (hT s ψ hψ)
  · exact D.freshStructure_satisfies d r s

/-- Every new relation is forced by its defining axiom, so the expansion is unique. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Conversely, that axiom forces the interpretation of $R$
    at every tuple. All old interpretations are fixed, hence the expansion is unique. For a family of definitions,
    apply this construction to each new symbol independently. The argument includes $0$-ary relations.
-/
theorem expansion_unique {M : Type w} (A : L.Structure M) (hne : Nonempty M)
    (B C : (L.sum (relationSymbols ι)).Structure M)
    (hB : @LHom.IsExpansionOn _ _ inclusion M A B)
    (hC : @LHom.IsExpansionOn _ _ inclusion M A C)
    (hb : ∀ n (r : ι n) s, @AlphaFormula.Realize _ M B (D.definingAxiom r) s)
    (hc : ∀ n (r : ι n) s, @AlphaFormula.Realize _ M C (D.definingAxiom r) s) : B = C := by
  apply structure_ext
  · intro n f a
    rcases f with f | f
    · exact (hB.map_onFunction f a).trans (hC.map_onFunction f a).symm
    · exact nomatch f
  · intro n R a
    rcases R with R | r
    · exact (hB.map_onRelation R a).trans (hC.map_onRelation R a).symm
    · let d : M := Classical.choice hne
      let s := assignment d a
      let := A
      have left : @Structure.RelMap _ M B n (Sum.inr r) a ↔ (D.formula r).Realize s := by
        let := B
        let : (inclusion (L := L) (ι := ι)).IsExpansionOn M := hB
        simpa only [s, assignment_apply] using (D.realize_axiom_iff r).mp (hb n r) s
      have right : @Structure.RelMap _ M C n (Sum.inr r) a ↔ (D.formula r).Realize s := by
        let := C
        let : (inclusion (L := L) (ι := ι)).IsExpansionOn M := hC
        simpa only [s, assignment_apply] using (D.realize_axiom_iff r).mp (hc n r) s
      exact propext (left.trans right.symm)

/-- Existence and uniqueness for all the defining axioms together with the old theory. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Unique expansion by relation definitions
-/
theorem existsUnique_expansion {T : Set (AlphaFormula L)} {M : Type w} (A : L.Structure M)
    (hne : Nonempty M) (hT : TheoryRealize A T) :
    ∃! B : (L.sum (relationSymbols ι)).Structure M,
      @LHom.IsExpansionOn _ _ inclusion M A B ∧ TheoryRealize B (D.theory T) := by
  obtain ⟨B, hB, hb⟩ := D.exists_expansion A hne hT
  refine ⟨B, ⟨hB, hb⟩, ?_⟩
  intro C hC
  exact D.expansion_unique A hne C B hC.1 hB
    (fun n r s => hC.2 s _ (Or.inr ⟨n, r, rfl⟩))
    (fun n r s => hb s _ (Or.inr ⟨n, r, rfl⟩))

/-- Universal closure keeps a theory of sentences closed after adding the definitions. -/
theorem theory_sentences {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L) :
    D.theory T ⊆ Sentences _ := by
  rintro φ (⟨ψ, hψ, rfl⟩ | ⟨n, r, rfl⟩)
  · simpa only [Sentences, Set.mem_ofPred_eq, fv_mapLanguage] using hT hψ
  · exact D.definingAxiom_sentence r

/-- Relation definitions create no new old-language theorems. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For relation symbols, use \termuse{unique expansion by relation definitions}.
-/
theorem conservative {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    {σ : AlphaFormula L} (hσ : σ ∈ Sentences L)
    (hp : ProvesFrom (D.theory T) (σ.mapLanguage inclusion)) : ProvesFrom T σ :=
  conservative_of_model_expansion inclusion hT (fun _ A hne h => D.exists_expansion A hne h) hσ hp

end RelationDefinitions
end PolishSpaceBook.NamedFirstOrder
