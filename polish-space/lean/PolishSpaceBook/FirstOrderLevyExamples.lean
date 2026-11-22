module

public import PolishSpaceBook.FirstOrderBoundedUnfolding

@[expose] public section

/-! # Existential graph witnesses and Levy complexity -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas

private def shiftIndex {n : ℕ} (k m : ℕ) (i : Fin n) : Fin (n + k) :=
  if i.val < m then Fin.castAdd k i else Fin.addNat i k

private theorem liftAt_boundedAll {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1))
    (k m : ℕ) (hm : m ≤ n) :
    (boundedAll i φ).liftAt k m =
      boundedAll (shiftIndex k m i) ((φ.liftAt k m).castLE (by omega)) := by
  simp only [boundedAll, BoundedFormula.liftAt, BoundedFormula.mapTermRel,
    BoundedFormula.castLE, memberAt, variableAt, Term.liftAt]
  congr 2
  congr 1
  funext j
  fin_cases j <;> simp [Term.relabel, shiftIndex, Fin.ext_iff, Nat.not_lt_of_ge hm]
  split_ifs <;> rfl

private theorem deltaZero_castLE_of_eq {m n : ℕ} (φ : ForcingFormulas.Formula m)
    (he : m = n) (hφ : IsDeltaZero φ) : IsDeltaZero (φ.castLE he.le) := by
  subst n
  simpa using hφ

/-- Inserting variables preserves boundedness, including inside existing bounded quantifiers. -/
theorem IsDeltaZero.liftAt {n : ℕ} {φ : ForcingFormulas.Formula n} (hφ : IsDeltaZero φ) :
    ∀ k m, m ≤ n → IsDeltaZero (φ.liftAt k m) := by
  induction hφ with
  | falsum => intro k m hm; exact .falsum
  | equal s t => intro k m hm; exact .equal (s.liftAt k m) (t.liftAt k m)
  | member ts => intro k m hm; exact .member (fun i => (ts i).liftAt k m)
  | imp hφ hψ ihφ ihψ =>
    intro k m hm
    exact .imp (ihφ k m hm) (ihψ k m hm)
  | @all n i φ hφ ih =>
    intro k m hm
    rw [liftAt_boundedAll i φ k m hm]
    exact .all _ (deltaZero_castLE_of_eq (φ.liftAt k m) (by omega) (ih k m (by omega)))

/-- Expand the graph witness and move its existential witness in front of the bounded matrix. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Complexity bookkeeping.**
    Elimination is a proof-theoretic translation, not by itself a promise about the Lévy hierarchy. The complexity level
    must be measured after the expanded notation has been translated back into the old language. Thus $P(f(x),z)$ is atomic
    only in the expanded language $L\cup\{f\}$. In the old language $L$, the term $f(x)$ has to be replaced by a witness to
    its defining graph:
    $$
    P(f(x),z)
    \quad\leadsto\quad
    \exists u\,\bigl(\theta(x,u) \land P(u,z)\bigr).
    $$
    If $\theta(x,u)$ is $\Sigma_1$, say $\theta(x,u)$ has the form $\exists w\,\delta(x,u,w)$ with $\delta$ $\Delta_0$, then
    this becomes
    $$
    \exists u\,\exists w\,\bigl(\delta(x,u,w) \land P(u,z)\bigr),
    $$
    which is $\Sigma_1$. The apparent atomicity of $P(f(x),z)$ was therefore an artifact of the abbreviation. Definitional
    extension preserves truth and provability in the old language, but it does not automatically preserve the boundedness of
    quantifiers that the Lévy hierarchy tracks.
-/
def graphWitnessSigmaOne {n : ℕ} (δ : ForcingFormulas.Formula (n + 2))
    (P : ForcingFormulas.Formula (n + 1)) : ForcingFormulas.Formula n :=
  ((δ ⊓ P.liftAt 1 (n + 1)).ex).ex

/-- A bounded graph matrix and bounded surrounding atom give a Sigma-one expansion. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Complexity bookkeeping.**
    Elimination is a proof-theoretic translation, not by itself a promise about the Lévy hierarchy. The complexity level
    must be measured after the expanded notation has been translated back into the old language. Thus $P(f(x),z)$ is atomic
    only in the expanded language $L\cup\{f\}$. In the old language $L$, the term $f(x)$ has to be replaced by a witness to
    its defining graph:
    $$
    P(f(x),z)
    \quad\leadsto\quad
    \exists u\,\bigl(\theta(x,u) \land P(u,z)\bigr).
    $$
    If $\theta(x,u)$ is $\Sigma_1$, say $\theta(x,u)$ has the form $\exists w\,\delta(x,u,w)$ with $\delta$ $\Delta_0$, then
    this becomes
    $$
    \exists u\,\exists w\,\bigl(\delta(x,u,w) \land P(u,z)\bigr),
    $$
    which is $\Sigma_1$. The apparent atomicity of $P(f(x),z)$ was therefore an artifact of the abbreviation. Definitional
    extension preserves truth and provability in the old language, but it does not automatically preserve the boundedness of
    quantifiers that the Lévy hierarchy tracks.
-/
theorem graphWitnessSigmaOne_complexity {n : ℕ} {δ : ForcingFormulas.Formula (n + 2)}
    {P : ForcingFormulas.Formula (n + 1)} (hδ : IsDeltaZero δ) (hP : IsDeltaZero P) :
    IsSigmaOne (graphWitnessSigmaOne δ P) :=
  .ex (.ex (.delta (hδ.and (hP.liftAt 1 (n + 1) le_rfl))))

/-- Pulling the graph's existential quantifier outward preserves every parameter and truth value. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Complexity bookkeeping.**
    Elimination is a proof-theoretic translation, not by itself a promise about the Lévy hierarchy. The complexity level
    must be measured after the expanded notation has been translated back into the old language. Thus $P(f(x),z)$ is atomic
    only in the expanded language $L\cup\{f\}$. In the old language $L$, the term $f(x)$ has to be replaced by a witness to
    its defining graph:
    $$
    P(f(x),z)
    \quad\leadsto\quad
    \exists u\,\bigl(\theta(x,u) \land P(u,z)\bigr).
    $$
    If $\theta(x,u)$ is $\Sigma_1$, say $\theta(x,u)$ has the form $\exists w\,\delta(x,u,w)$ with $\delta$ $\Delta_0$, then
    this becomes
    $$
    \exists u\,\exists w\,\bigl(\delta(x,u,w) \land P(u,z)\bigr),
    $$
    which is $\Sigma_1$. The apparent atomicity of $P(f(x),z)$ was therefore an artifact of the abbreviation. Definitional
    extension preserves truth and provability in the old language, but it does not automatically preserve the boundedness of
    quantifiers that the Lévy hierarchy tracks.
-/
theorem realize_graphWitnessSigmaOne {M : Type*} [membershipLanguage.Structure M]
    {n : ℕ} (δ : ForcingFormulas.Formula (n + 2)) (P : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → M) :
    ((δ.ex ⊓ P).ex).Realize Empty.elim xs ↔
      (graphWitnessSigmaOne δ P).Realize Empty.elim xs := by
  simp only [graphWitnessSigmaOne, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_liftAt_one_self, Fin.snoc_comp_castSucc]
  constructor
  · rintro ⟨a, ⟨b, hδ⟩, hP⟩
    exact ⟨a, b, hδ, hP⟩
  · rintro ⟨a, b, hδ, hP⟩
    exact ⟨a, ⟨b, hδ⟩, hP⟩

end PolishSpaceBook.SetTheoryModels
