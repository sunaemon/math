module

public import PolishSpaceBook.SetTheoryBooleanEvaluationFormulas

@[expose] public section

/-! # Constructing Boolean evaluations inside a transitive model

Separation collects the nodes covered by some internal partial assignment and
the nodes made true by one. Agreement makes these unions a partial assignment.
Well-founded induction and one-node extension show that its domain is total.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.BooleanEvaluation
open FirstOrder Language ZFSet ForcingFormulas
open scoped Classical
universe u

/-- The domain or truth set covered by all partial assignments in M. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Use Separation inside $M$ to form
    $$\begin{aligned}
    D_*&:=\{s\in T:M\models\exists D\,\exists E\;(\sigma(D,E)\land s\in D)\},\\
    E_*&:=\{s\in T:M\models\exists D\,\exists E\;(\sigma(D,E)\land s\in E)\}.
    \end{aligned}$$
    These definitions quantify over partial evaluations belonging to $M$, not over all external subsets of $T$.
    They use the two displayed first-order formulas with parameters $T,R,U,C,L$.
    Transitivity and bounded absoluteness identify the witnesses with actual partial evaluations.
-/
def collected (M T R U C L : ZFSet.{u}) (truth : Bool) : ZFSet.{u} :=
  T.sep (fun s => ∃ D E : M, Partial T R U C L D.val E.val ∧
    s ∈ (if truth then E.val else D.val))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Use Separation inside $M$ to form
    $$\begin{aligned}
    D_*&:=\{s\in T:M\models\exists D\,\exists E\;(\sigma(D,E)\land s\in D)\},\\
    E_*&:=\{s\in T:M\models\exists D\,\exists E\;(\sigma(D,E)\land s\in E)\}.
    \end{aligned}$$
    These definitions quantify over partial evaluations belonging to $M$, not over all external subsets of $T$.
    They use the two displayed first-order formulas with parameters $T,R,U,C,L$.
    Transitivity and bounded absoluteness identify the witnesses with actual partial evaluations.
-/
lemma collected_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T R U C L : M) (truth : Bool) : collected M T.val R.val U.val C.val L.val truth ∈ M := by
  apply separation_mem_of_absolute hM (collectedFormula truth) (hsep _) ![T, R, U, C, L] T.property
  intro s _
  have he : Fin.snoc ![T, R, U, C, L] s = ![T, R, U, C, L, s] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact realize_collectedFormula hM truth T R U C L s

lemma mem_collected {M T R U C L s : ZFSet.{u}} (truth : Bool) :
    s ∈ collected M T R U C L truth ↔
      ∃ D E : M, Partial T R U C L D.val E.val ∧ s ∈ (if truth then E.val else D.val) := by
  rw [collected, ZFSet.mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨D, E, h, hs⟩ := h
  cases truth
  · exact h.1 hs
  · exact h.1 (h.2.1 hs)

lemma collected_agree {M T R U C L : ZFSet.{u}}
    (hw : WellFounded (fun t s : T => pair t.val s.val ∈ R))
    (D E : M) (h : Partial T R U C L D.val E.val) {s : ZFSet.{u}} (hs : s ∈ D.val) :
    s ∈ collected M T R U C L true ↔ s ∈ E.val := by
  rw [mem_collected]
  constructor
  · rintro ⟨D', E', h', hs'⟩
    exact (h'.agree hw h s (h'.2.1 hs') hs).mp hs'
  · intro hs'
    exact ⟨D, E, h, hs'⟩

/-- All internal partial evaluations glue without selecting an enumeration. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    We first show $\sigma(D_*,E_*)$. Certainly $E_*\IncludedIn D_*\IncludedIn T$.
    If $s\in D_*$, choose an internal partial evaluation $(D,E)$ whose domain contains $s$.
    Every child of $s$ belongs to $D$, hence to $D_*$.
    On $D$, membership in $E_*$ agrees with membership in $E$: one direction follows by using $(D,E)$ as a
    witness, and the other by comparing it with any internal partial evaluation witnessing membership in $E_*$.
    The same agreement holds at every child of $s$, so $\theta(E_*,s)$ agrees with $\theta(E,s)$.
    The equation for $(D,E)$ therefore proves the required equation at $s$.
-/
theorem collected_partial {M T R U C L : ZFSet.{u}}
    (hw : WellFounded (fun t s : T => pair t.val s.val ∈ R)) :
    Partial T R U C L (collected M T R U C L false) (collected M T R U C L true) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.mp h).1, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨D, E, h, hs⟩ := (mem_collected true).mp hs
    exact (mem_collected false).mpr ⟨D, E, h, h.2.1 hs⟩
  · intro s hs t ht hr
    obtain ⟨D, E, h, hs⟩ := (mem_collected false).mp hs
    exact (mem_collected false).mpr ⟨D, E, h, h.2.2.1 s hs t ht hr⟩
  · intro s hs
    obtain ⟨D, E, h, hs⟩ := (mem_collected false).mp hs
    rw [collected_agree hw D E h hs, h.2.2.2 s hs]
    exact (step_congr (fun t ht hr => collected_agree hw D E h (h.2.2.1 s hs t ht hr))).symm

/-- Pairing, Union, and Separation suffice for this bounded-value recursion. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal Boolean evaluation
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Now prove $D_*=T$ by well-founded induction. Suppose every child of $s\in T$ is in $D_*$.
    If $s\notin D_*$, extend the domain by $s$ and put
    $$D':=D_*\cup\{s\},\qquad
    E':=\begin{cases}E_*\cup\{s\},&\theta(E_*,s),\\E_*,&\neg\theta(E_*,s).\end{cases}$$
    Both sets belong to $M$ by Pairing and Union.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    This internal partial evaluation witnesses $s\in D_*$, a contradiction. Hence every node belongs to $D_*$.
-/
theorem internal_evaluation_existsUnique {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T R U C L : M)
    (hw : WellFounded (fun t s : T.val => pair t.val s.val ∈ R.val)) :
    ∃! E : M, Partial T.val R.val U.val C.val L.val T.val E.val := by
  let D := collected M T.val R.val U.val C.val L.val false
  let E := collected M T.val R.val U.val C.val L.val true
  have hD : D ∈ M := collected_mem hM hsep T R U C L false
  have hE : E ∈ M := collected_mem hM hsep T R U C L true
  have h : Partial T.val R.val U.val C.val L.val D E := collected_partial hw
  have hinsert {a B : ZFSet.{u}} (ha : a ∈ M) (hB : B ∈ M) : insert a B ∈ M := by
    rw [ZFSet.insert_eq]
    exact binaryUnion_mem hM hpair hunion (singleton_mem hM hpair ha) hB
  have htotal : ∀ s : T.val, s.val ∈ D := by
    intro s
    induction s using hw.induction with
    | h s ih =>
      by_cases hs : s.val ∈ D
      · exact hs
      · have hchildren : ∀ t ∈ T.val, pair t s.val ∈ R.val → t ∈ D :=
          fun t ht hr => ih ⟨t, ht⟩ hr
        let F := if Step T.val R.val U.val C.val L.val E s.val then insert s.val E else E
        have hsM : s.val ∈ M := hM.mem_trans s.property T.property
        have hF : F ∈ M := by
          dsimp [F]
          split_ifs
          · exact hinsert hsM hE
          · exact hE
        exact (mem_collected false).mpr
          ⟨⟨insert s.val D, hinsert hsM hD⟩, ⟨F, hF⟩,
            h.extend s.property hs hchildren, ZFSet.mem_insert _ _⟩
  have heq : D = T.val := ZFSet.ext fun s =>
    ⟨fun hs => h.1 hs, fun hs => htotal ⟨s, hs⟩⟩
  have hfull : Partial T.val R.val U.val C.val L.val T.val E := heq ▸ h
  exact ⟨⟨E, hE⟩, hfull, fun F hF => Subtype.ext (hF.unique hw hfull)⟩

/-- The internal set is the specified external evaluation, not just an unnamed solution. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal Boolean evaluation
-/
theorem external_evaluation_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T R U C L : M)
    (hw : WellFounded (fun t s : T.val => pair t.val s.val ∈ R.val))
    {E : ZFSet.{u}} (hE : Partial T.val R.val U.val C.val L.val T.val E) : E ∈ M := by
  obtain ⟨F, hF, _⟩ := internal_evaluation_existsUnique hM hpair hunion hsep T R U C L hw
  exact (hF.unique hw hE) ▸ F.property

/-- Truth at a node is asserted by an internal complete evaluation. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Define the first-order truth formula
    $$\tau(T,R,U,C,L,s)\;:\equiv\;\exists E\;(\sigma(T,E)\land s\in E).$$
-/
def truthFormula : ForcingFormulas.Formula 6 :=
  (partialFormula (0 : Fin 7) 1 2 3 4 0 6 ⊓ memberAt 5 6).ex

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For any external complete evaluation $E$ and any $s\in M$, the theorem and bounded absoluteness give
    $$M\models\tau(T,R,U,C,L,s)\quad\Longleftrightarrow\quad s\in E.$$
    Indeed, an internal witness must equal $E$ by uniqueness; conversely, the theorem puts $E$ in $M$, so it
    itself witnesses the formula. Thus models containing the same parameters compute the same truth value.
    This assertion concerns a fixed externally well-founded relation; it does not assert absoluteness of
    well-foundedness for arbitrary relations.
-/
theorem realize_truthFormula_external {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T R U C L s : M)
    (hw : WellFounded (fun t s : T.val => pair t.val s.val ∈ R.val))
    {E : ZFSet.{u}} (hE : Partial T.val R.val U.val C.val L.val T.val E) :
    truthFormula.Realize Empty.elim ![T, R, U, C, L, s] ↔ s.val ∈ E := by
  have hform : truthFormula.Realize Empty.elim ![T, R, U, C, L, s] ↔
      ∃ F : M, Partial T.val R.val U.val C.val L.val T.val F.val ∧ s.val ∈ F.val := by
    simp [truthFormula, realize_partialFormula hM]
  rw [hform]
  constructor
  · rintro ⟨F, hF, hs⟩
    exact (hF.unique hw hE) ▸ hs
  · intro hs
    exact ⟨⟨E, external_evaluation_mem hM hpair hunion hsep T R U C L hw hE⟩, hE, hs⟩

end PolishSpaceBook.SetTheoryModels.BooleanEvaluation
