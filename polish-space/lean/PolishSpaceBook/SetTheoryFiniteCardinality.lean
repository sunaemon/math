module

public import PolishSpaceBook.SetTheoryPredicateComposition
public import PolishSpaceBook.SetTheoryFiniteSequences
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section


/-! # Absolute finite cardinalities from internal finite bijections -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-- Parameters domain, codomain, graph. Surjectivity and injectivity are bounded. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For a finite ordinal $k$, let
    $$\begin{aligned}
    \mathrm{Bij}(k,A,g):\equiv{}&g:k\to A\\
    &{}\land\forall y\in A\;\exists i\in k\;\langle i,y\rangle\in g\\
    &{}\land\forall i,j\in k\;\forall y\in A\;[\\
    &\quad(\langle i,y\rangle\in g\land\langle j,y\rangle\in g)
    \longrightarrow i=j].
    \end{aligned}$$
    This is a bounded predicate. Define $\mathrm{Count}(k,A):\equiv\exists g\;\mathrm{Bij}(k,A,g)$.
    The quantifier over $g$ is unrestricted, so absoluteness of $\mathrm{Count}$ requires a further argument.
-/
def bijectionPredicate : BoundedSetPredicate 3 :=
  .conj (.function 0 1 2)
    (.conj (.all 1 (.ex 0 (.pairMember 2 4 3)))
      (.all 0 (.all 0 (.all 1
        ((BoundedSetPredicate.conj (.pairMember 2 3 5) (.pairMember 2 4 5)).imply (.equal 3 4))))))

lemma eval_bijectionPredicate (A B g : ZFSet.{u}) :
    bijectionPredicate.eval ![A, B, g] ↔
      IsFunc A B g ∧ (∀ b ∈ B, ∃ a ∈ A, pair a b ∈ g) ∧
        ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, pair a b ∈ g → pair a' b ∈ g → a = a' := by
  simp [bijectionPredicate, eval, eval_imply, Fin.snoc, Fin.castPred, Fin.castLT, and_imp]

lemma pair_mem_functionGraph {A : ZFSet.{u}} (f : A → ZFSet.{u}) (a : A) (b : ZFSet.{u}) :
    pair a.val b ∈ functionGraph f ↔ f a = b := by
  rw [functionGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp hx
    exact (congrArg f (Subtype.ext ha)).symm.trans hb
  · intro h
    exact ⟨a, congrArg (pair a.val) h⟩

/-- The graph predicate recognizes ordinary bijections, represented by mathlib equivalences. -/
lemma bijectionPredicate_iff_equiv (A B g : ZFSet.{u}) :
    bijectionPredicate.eval ![A, B, g] ↔
      ∃ e : A ≃ B, functionGraph (fun a => (e a).val) = g := by
  rw [eval_bijectionPredicate]
  constructor
  · rintro ⟨hf, hs, hi⟩
    let f : A → B := fun a => ⟨Classical.choose (hf.2 a.val a.property),
      (ZFSet.pair_mem_prod.mp (hf.1 (Classical.choose_spec (hf.2 a.val a.property)).1)).2⟩
    have hfg (a : A) : pair a.val (f a).val ∈ g := (Classical.choose_spec (hf.2 a.val a.property)).1
    have hinj : Function.Injective f := by
      intro a a' he
      apply Subtype.ext
      exact hi _ a.property _ a'.property _ (f a).property (hfg a)
        (by simpa only [he] using hfg a')
    have hsurj : Function.Surjective f := by
      intro b
      obtain ⟨a, ha, hab⟩ := hs b.val b.property
      exact ⟨⟨a, ha⟩, Subtype.ext ((hf.2 a ha).unique (hfg ⟨a, ha⟩) hab)⟩
    refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
    ext p
    constructor
    · rintro hp
      obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hp
      exact hfg a
    · intro hp
      obtain ⟨a, ha, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
      exact ZFSet.mem_range.mpr ⟨⟨a, ha⟩, congrArg (pair a) ((hf.2 a ha).unique (hfg ⟨a, ha⟩) hp)⟩
  · rintro ⟨e, rfl⟩
    have hf := functionGraph_isFunc (fun a => (e a).val)
    refine ⟨⟨?_, hf.2⟩, ?_, ?_⟩
    · intro p hp
      obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hp
      exact ZFSet.pair_mem_prod.mpr ⟨a.property, (e a).property⟩
    · intro b hb
      exact ⟨(e.symm ⟨b, hb⟩).val, (e.symm ⟨b, hb⟩).property,
        (pair_mem_functionGraph _ _ _).mpr (congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩))⟩
    · intro a ha a' ha' b _ hab ha'b
      have h1 := (pair_mem_functionGraph _ ⟨a, ha⟩ b).mp hab
      have h2 := (pair_mem_functionGraph _ ⟨a', ha'⟩ b).mp ha'b
      exact congrArg Subtype.val (e.injective (Subtype.ext (h1.trans h2.symm)))

/-- Finite ordinals carry exactly their usual finite set of predecessors. -/
def finOrdinalEquiv (n : ℕ) : Fin n ≃ (natOrdinal n : ZFSet.{u}) :=
  Equiv.ofBijective (fun i => ⟨natOrdinal i.val, mem_natOrdinal.mpr ⟨i.val, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (natOrdinal_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨i, hi, he⟩ := mem_natOrdinal.mp x.property
      exact ⟨⟨i, by simpa using hi⟩, Subtype.ext he⟩⟩

/-- Existence of a bijection, with the graph quantified inside the model. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For a finite ordinal $k$, let
    $$\begin{aligned}
    \mathrm{Bij}(k,A,g):\equiv{}&g:k\to A\\
    &{}\land\forall y\in A\;\exists i\in k\;\langle i,y\rangle\in g\\
    &{}\land\forall i,j\in k\;\forall y\in A\;[\\
    &\quad(\langle i,y\rangle\in g\land\langle j,y\rangle\in g)
    \longrightarrow i=j].
    \end{aligned}$$
    This is a bounded predicate. Define $\mathrm{Count}(k,A):\equiv\exists g\;\mathrm{Bij}(k,A,g)$.
    The quantifier over $g$ is unrestricted, so absoluteness of $\mathrm{Count}$ requires a further argument.
-/
def finiteCardinalityFormula : ForcingFormulas.Formula 2 := bijectionPredicate.compile.ex

/-- The witness graph is finite, so its external existence already puts it in the model. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Absolute finite cardinalities
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    An internal witness $g$ satisfies the actual bijection conditions by the uniform interpretation principle.
    An actual bijection from $k$ to $A$ gives $k=|A|$.
    Conversely, such a bijection exists if $k=|A|$. Its graph belongs to $M$ by the finite-function lemma of
    §{sec:internal-borel-inputs}, since its domain is finite and all its values lie in $A\in M$.
    The same interpretation principle makes this graph an internal witness. The argument includes $k=0$ and
    $A=\emptyset$.
-/
theorem finiteCardinality_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (N A : M) (n k : ℕ) (hN : N.val = natOrdinal n) (e : Fin k ≃ A.val) :
    finiteCardinalityFormula.Realize Empty.elim ![N, A] ↔ n = k := by
  simp only [finiteCardinalityFormula, BoundedFormula.realize_ex]
  have habs (g : M) : bijectionPredicate.compile.Realize Empty.elim (Fin.snoc ![N, A] g) ↔
      ∃ f : (natOrdinal n : ZFSet.{u}) ≃ A.val, functionGraph (fun a => (f a).val) = g.val := by
    rw [bijectionPredicate.realize_compile hM]
    have he : Subtype.val ∘ Fin.snoc ![N, A] g = ![natOrdinal n, A.val, g.val] := by
      funext i; fin_cases i <;> simp [hN]
    rw [he, bijectionPredicate_iff_equiv]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨f, _⟩ := (habs g).mp hg
    exact Fintype.card_fin n ▸ Fintype.card_fin k ▸
      Fintype.card_congr ((finOrdinalEquiv n).trans (f.trans e.symm))
  · intro h
    subst k
    let f : (natOrdinal n : ZFSet.{u}) ≃ A.val := (finOrdinalEquiv n).symm.trans e
    have hb := (bijectionPredicate_iff_equiv _ _ _).mpr ⟨f, rfl⟩
    have hf := ((eval_bijectionPredicate _ _ _).mp hb).1
    let g : M := ⟨functionGraph (fun a => (f a).val), finite_function_mem hM hinf hpair hunion A.property hf⟩
    exact ⟨g, (habs g).mpr ⟨f, rfl⟩⟩

end PolishSpaceBook.SetTheoryModels
