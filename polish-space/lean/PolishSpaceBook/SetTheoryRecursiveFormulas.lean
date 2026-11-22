module

public import PolishSpaceBook.SetTheoryRestrictionFormulas
public import PolishSpaceBook.SetTheoryRecursiveSolutions
public import PolishSpaceBook.SetTheoryOrdinalFormulas

@[expose] public section

/-! # Internal formulas for partial solutions of membership recursion -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Insert the parameters and the three arguments of the step-defining formula. -/
def stepInstance {n k : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ρ : Fin n → Fin k)
    (a g b : Fin k) : ForcingFormulas.Formula k :=
  reindex ψ (Fin.snoc (Fin.snoc (Fin.snoc ρ a) g) b)

lemma realize_stepInstance (S : ZFSet.{u}) {n k : ℕ} (ψ : ForcingFormulas.Formula (n + 3))
    (ρ : Fin n → Fin k) (a g b : Fin k) (xs : Fin k → S) :
    (stepInstance ψ ρ a g b).Realize Empty.elim xs ↔
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc (xs ∘ ρ) (xs a)) (xs g)) (xs b)) := by
  rw [stepInstance, realize_reindex]
  simp only [Fin.comp_snoc]

/-- A transitive domain, a set-function graph, and the recursive equation at every input. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Fix a finite parameter tuple $\vec p\in M$ and a formula $\psi(a,g,b,\vec p)$ representing the step rule:
    $$M\models\psi(a,g,b,\vec p)\quad\Longleftrightarrow\quad b=H(a,g)
    \qquad(a,g,b\in M).$$
    Define the partial-solution formula
    $$\begin{aligned}
    \sigma(D,f,\vec p)\;:\equiv\;&\mathrm{Trans}(D)\land\exists Y\,(f:D\to Y)\\
    &{}\land\forall a\in D\,\exists g\,\exists b\,
     \bigl(\rho(f,a,g)\\
    &\qquad{}\land\langle a,b\rangle\in f\land\psi(a,g,b,\vec p)\bigr).
    \end{aligned}$$
    The transitivity, function, and ordered-pair clauses are the explicit formulas already given above and in
    §{sec:zfc-absoluteness}. All remaining quantifiers are displayed, so this is a single first-order formula
    with the indicated finite tuple of parameters. No boundedness claim is made for $\sigma$ or for $\psi$.
-/
def recursiveSolutionFormula {n k : ℕ} (ψ : ForcingFormulas.Formula (n + 3))
    (ρ : Fin n → Fin k) (D f : Fin k) : ForcingFormulas.Formula k :=
  transitiveFormula D ⊓
    ((functionFormula D.castSucc (Fin.last k) f.castSucc).ex ⊓
      boundedAll D
        ((restrictionFormula f.castSucc.castSucc.castSucc (Fin.last k).castSucc.castSucc
          (Fin.last (k + 1)).castSucc ⊓
          (pairMemberFormula f.castSucc.castSucc.castSucc (Fin.last k).castSucc.castSucc (Fin.last (k + 2)) ⊓
            stepInstance ψ (fun i => (ρ i).castSucc.castSucc.castSucc)
              (Fin.last k).castSucc.castSucc (Fin.last (k + 1)).castSucc (Fin.last (k + 2)))).ex.ex))

lemma realize_recursiveSolutionFormula (S : ZFSet.{u}) (hS : S.IsTransitive)
    {n k : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ρ : Fin n → Fin k)
    (D f : Fin k) (xs : Fin k → S) :
    (recursiveSolutionFormula ψ ρ D f).Realize Empty.elim xs ↔
      (xs D).val.IsTransitive ∧ (∃ Y : S, ZFSet.IsFunc (xs D).val Y.val (xs f).val) ∧
      ∀ a : S, a.val ∈ (xs D).val → ∃ g b : S,
        g.val = restrictGraph (xs f).val a.val ∧ ZFSet.pair a.val b.val ∈ (xs f).val ∧
        ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc (xs ∘ ρ) a) g) b) := by
  have ht {m : ℕ} (x : Fin m) (ys : Fin m → S) :
      (transitiveFormula x).Realize Empty.elim ys ↔ (ys x).val.IsTransitive :=
    realize_transitiveFormula (S : ZFClass) (fun _ ha _ hb => hS.mem_trans hb ha) x ys
  have hf {m : ℕ} (x y f : Fin m) (ys : Fin m → S) :
      (functionFormula x y f).Realize Empty.elim ys ↔ ZFSet.IsFunc (ys x).val (ys y).val (ys f).val :=
    realize_functionFormula (S : ZFClass) (fun _ ha _ hb => hS.mem_trans hb ha) x y f ys
  have hr {m : ℕ} (f x g : Fin m) (ys : Fin m → S) :
      (restrictionFormula f x g).Realize Empty.elim ys ↔ (ys g).val = restrictGraph (ys f).val (ys x).val :=
    realize_restrictionFormula (S : ZFClass) (fun _ ha _ hb => hS.mem_trans hb ha) f x g ys
  have hp {m : ℕ} (f a b : Fin m) (ys : Fin m → S) :
      (pairMemberFormula f a b).Realize Empty.elim ys ↔ ZFSet.pair (ys a).val (ys b).val ∈ (ys f).val :=
    realize_pairMemberFormula (S : ZFClass) (fun _ ha _ hb => hS.mem_trans hb ha) f a b ys
  have hall {m : ℕ} (i : Fin m) (φ : ForcingFormulas.Formula (m + 1)) (ys : Fin m → S) :
      (boundedAll i φ).Realize Empty.elim ys ↔
        ∀ a : S, a.val ∈ (ys i).val → φ.Realize Empty.elim (Fin.snoc ys a) :=
    realize_boundedAll (S : ZFClass) i φ ys
  simp only [recursiveSolutionFormula, BoundedFormula.realize_inf, BoundedFormula.realize_ex,
    ht, hf, hr, hp, hall, realize_stepInstance, Function.comp_def, Fin.snoc_last, Fin.snoc_castSucc]

/-- Internal satisfaction agrees with the actual partial solution when the step predicate represents H. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    From the internal formula, absoluteness of the transitivity and function predicates gives a transitive domain
    and an actual function graph. For each input, the witness $g$ is the actual restriction by the preceding
    calculation, and the witness $b$ is the graph's value. The defining equivalence for $\psi$ therefore gives the
    required recursive equation.

    Conversely, let $f$ be a partial solution on $D$ in the ambient universe. The set
    $Y=\bigcup\bigcup f$ belongs to $M$ and contains all its values, so it witnesses the function clause.
    For each $a\in D$, transitivity gives $a\in M$, and the restriction calculation puts
    $g=\restrict{f}{a}$ in $M$. The value $b=H(a,g)$ occurs in a pair of $f$, so $b\in Y$ and hence $b\in M$.
    These actual sets witness the two existential quantifiers, and the defining equivalence for $\psi$ gives
    its internal truth. Thus $\sigma(D,f,\vec p)$ holds internally.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal definition of partial solutions
-/
theorem recursiveSolutionFormula_iff {S : ZFSet.{u}} (hS : S.IsTransitive)
    (hunion : S ⊨ unionSentence) (hsep : S ⊨ separationSentence productSeparationFormula)
    {n k : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ρ : Fin n → Fin k)
    (D f : Fin k) (xs : Fin k → S) (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : S,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc (xs ∘ ρ) a) g) b) ↔ b.val = H a.val g.val) :
    (recursiveSolutionFormula ψ ρ D f).Realize Empty.elim xs ↔
      IsRecursiveSolution H (xs D).val (xs f).val := by
  rw [realize_recursiveSolutionFormula S hS]
  constructor
  · rintro ⟨hD, ⟨Y, hf⟩, heq⟩
    refine ⟨hD, isFunc_doubleUnion hf, ?_⟩
    intro a ha
    let aS : S := ⟨a, hS.mem_trans ha (xs D).property⟩
    obtain ⟨g, b, hg, hab, hψ⟩ := heq aS ha
    have hb := (hH aS g b).mp hψ
    simpa only [hb, hg] using hab
  · intro hsol
    let B := ZFSet.sUnion (ZFSet.sUnion (xs f).val)
    have hB : B ∈ S := union_mem hS hunion (union_mem hS hunion (xs f).property)
    refine ⟨hsol.domain_transitive, ⟨⟨B, hB⟩, hsol.function_graph⟩, ?_⟩
    intro a ha
    let g : S := ⟨restrictGraph (xs f).val a.val,
      restrictGraph_mem hS hunion hsep (xs f).property a.property⟩
    have hab := hsol.equation a.val ha
    have hb : H a.val g.val ∈ S := hS.mem_trans (second_mem_doubleUnion hab) hB
    let b : S := ⟨H a.val g.val, hb⟩
    exact ⟨g, b, rfl, hab, (hH a g b).mpr rfl⟩

/-- A value is witnessed by some internal partial solution containing the input. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Finally define the value predicate
    $$\begin{aligned}
    \nu(a,b,\vec p)\;:\equiv\;\exists D\,\exists f\,\bigl(
    \sigma(D,f,\vec p)\\
    {}\land a\in D\land\langle a,b\rangle\in f\bigr).
    \end{aligned}$$
    Internally, this says that some partial solution in the model assigns the proposed value to the input.
-/
def recursiveValueFormula {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) : ForcingFormulas.Formula (n + 2) :=
  ((recursiveSolutionFormula ψ (fun i => i.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (n + 2)).castSucc (Fin.last (n + 3)) ⊓
    (memberAt (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n + 2)).castSucc ⊓
      pairMemberFormula (Fin.last (n + 3)) (Fin.last n).castSucc.castSucc.castSucc
        (Fin.last (n + 1)).castSucc.castSucc)).ex.ex)

lemma realize_recursiveValueFormula {S : ZFSet.{u}} (hS : S.IsTransitive)
    (hunion : S ⊨ unionSentence) (hsep : S ⊨ separationSentence productSeparationFormula)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → S)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : S,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (a b : S) :
    (recursiveValueFormula ψ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) ↔
      ∃ D f : S, IsRecursiveSolution H D.val f.val ∧ a.val ∈ D.val ∧ ZFSet.pair a.val b.val ∈ f.val := by
  have hs (D f : S) :
      (recursiveSolutionFormula ψ (fun i => i.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 2)).castSucc (Fin.last (n + 3))).Realize Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps a) b) D) f) ↔ IsRecursiveSolution H D.val f.val := by
    simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
      (recursiveSolutionFormula_iff hS hunion hsep ψ
        (fun i => i.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 2)).castSucc (Fin.last (n + 3))
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps a) b) D) f) H
        (by simpa only [Function.comp_def, Fin.snoc_castSucc] using hH))
  have hp {m : ℕ} (f a b : Fin m) (ys : Fin m → S) :
      (pairMemberFormula f a b).Realize Empty.elim ys ↔ ZFSet.pair (ys a).val (ys b).val ∈ (ys f).val :=
    realize_pairMemberFormula (S : ZFClass) (fun _ ha _ hb => hS.mem_trans hb ha) f a b ys
  simp only [recursiveValueFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    hs, realize_memberAt, hp, Fin.snoc_castSucc, Fin.snoc_last]

/-- Different internal witnesses cannot assign different values to the same input. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    It is single-valued: two internal witnesses yield two actual partial solutions by the lemma, and the agreement
    lemma makes their values equal at the common input. Thus this fixed formula supplies the uniqueness premise
    needed for Replacement. Existence at each required input remains a separate step; the formula does not
    postulate a solution on the whole ground model.
-/
theorem recursive_value_unique {S : ZFSet.{u}} (hS : S.IsTransitive)
    (hunion : S ⊨ unionSentence) (hsep : S ⊨ separationSentence productSeparationFormula)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → S)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : S,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (a b c : S)
    (hb : (recursiveValueFormula ψ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b))
    (hc : (recursiveValueFormula ψ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) c)) : b = c := by
  obtain ⟨D, f, hf, haD, hab⟩ := (realize_recursiveValueFormula hS hunion hsep ψ ps H hH a b).mp hb
  obtain ⟨E, g, hg, haE, hac⟩ := (realize_recursiveValueFormula hS hunion hsep ψ ps H hH a c).mp hc
  exact Subtype.ext (recursive_solutions_agree hf hg a.val haD haE b.val c.val hab hac)

end PolishSpaceBook.SetTheoryModels
