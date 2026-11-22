module

public import Mathlib.ModelTheory.ElementarySubstructures
public import PolishSpaceBook.FirstOrderNamedSyntax

@[expose] public section

/-!
# Tarski--Vaught by induction on formulas

The public conclusion uses mathlib's canonical elementary-substructure predicate.
Finite parameter tuples are encoded by bounded formulas. Atomic formulas use the
restricted interpretations; implication uses induction, and universal quantification
uses the witness condition on a negated body to bring a counterexample inside.
The named formulas of the appendix inherit the resulting semantic equivalence.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

/-- The witness condition, with the quantified variable last in a finite tuple. -/
def WitnessClosed (S : L.Substructure M) : Prop :=
  ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (s : Fin n → S) (a : M),
    φ.Realize default (Fin.snoc (Subtype.val ∘ s) a) →
      ∃ b : S, φ.Realize default (Fin.snoc (Subtype.val ∘ s) (b : M))

/-- Term evaluation commutes with the inclusion, by induction on the term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Restrict the interpretations to $B$. Induction on terms shows that evaluation
    commutes with the inclusion into $A$: variables retain their assigned values, and the function step uses the
    restriction of the same function. Hence atomic formulas have the same truth value in the two structures.
    The Boolean steps follow from the induction hypotheses and their truth tables.
-/
theorem term_realize_inclusion (S : L.Substructure M) {α : Type*} (s : α → S) (t : L.Term α) :
    t.realize (Subtype.val ∘ s) = (↑(t.realize s) : M) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp only [Term.realize, ih]; rfl

/-- The formula induction underlying the test; no elementary-map test is invoked. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For an existential formula true in $\mathcal A$, the witness condition supplies a witness in $B$, and the induction
    hypothesis for the body makes it a witness in $\mathcal B$. Conversely, a witness in $\mathcal B$ is a witness in
    $\mathcal A$ by that same induction hypothesis. A universal formula true in $\mathcal A$ is true in $\mathcal B$
    by restriction and induction. For the converse, if it failed in $\mathcal A$, apply the witness condition to the
    negation of its body. This gives a counterexample in $B$, and induction contradicts its truth in $\mathcal B$.
    Thus every formula has the same truth value under parameter assignments from $B$, as required.
-/
theorem bounded_realize_of_witnessClosed (S : L.Substructure M) (hS : WitnessClosed S)
    {n : ℕ} (φ : L.BoundedFormula Empty n) (s : Fin n → S) :
    φ.Realize default (Subtype.val ∘ s) ↔ φ.Realize default s := by
  induction φ with
  | falsum => rfl
  | equal t r =>
    simp only [BoundedFormula.Realize]
    have ht := term_realize_inclusion S (Sum.elim default s) t
    have hr := term_realize_inclusion S (Sum.elim default s) r
    have he : Subtype.val ∘ Sum.elim (default : Empty → S) s =
        Sum.elim (default : Empty → M) (Subtype.val ∘ s) := by
      funext x
      cases x with
      | inl x => exact Empty.elim x
      | inr i => rfl
    rw [← he, ht, hr]
    exact Subtype.coe_injective.eq_iff
  | rel R ts =>
    simp only [BoundedFormula.Realize]
    have ht (i) := term_realize_inclusion S (Sum.elim default s) (ts i)
    have he : Subtype.val ∘ Sum.elim (default : Empty → S) s =
        Sum.elim (default : Empty → M) (Subtype.val ∘ s) := by
      funext x
      cases x with
      | inl x => exact Empty.elim x
      | inr i => rfl
    simp only [← he, ht]
    exact S.subtype.map_rel R (fun i => (ts i).realize (Sum.elim default s))
  | imp φ ψ ihφ ihψ => simp only [BoundedFormula.realize_imp, ihφ, ihψ]
  | @all n φ ih =>
    simp only [BoundedFormula.realize_all]
    constructor
    · intro h b
      apply (ih (Fin.snoc s b)).mp
      simpa only [Fin.comp_snoc] using h (b : M)
    · intro h a
      by_contra ha
      obtain ⟨b, hb⟩ := hS n φ.not s a (by simpa only [BoundedFormula.realize_not] using ha)
      have hbody := (ih (Fin.snoc s b)).mpr (h b)
      exact hb (by simpa only [Fin.comp_snoc] using hbody)

/-- The existential step explicitly transfers witnesses in both directions. -/
theorem ex_realize_of_witnessClosed (S : L.Substructure M) (hS : WitnessClosed S)
    {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) (s : Fin n → S) :
    φ.ex.Realize default (Subtype.val ∘ s) ↔ φ.ex.Realize default s := by
  rw [BoundedFormula.realize_ex, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hS n φ s a ha
    refine ⟨b, (bounded_realize_of_witnessClosed S hS φ (Fin.snoc s b)).mp ?_⟩
    simpa only [Fin.comp_snoc] using hb
  · rintro ⟨b, hb⟩
    refine ⟨(b : M), ?_⟩
    have h := (bounded_realize_of_witnessClosed S hS φ (Fin.snoc s b)).mpr hb
    simpa only [Fin.comp_snoc] using h

/-- Tarski--Vaught in terms of the standard elementary-substructure predicate. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: Tarski–Vaught test
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    If $\mathcal B\prec\mathcal A$, an existential formula true in $\mathcal A$ with parameters in $B$ is true in
    $\mathcal B$. Its witness in $B$ satisfies the body in both structures, giving the test.
-/
theorem isElementary_iff_witnessClosed (S : L.Substructure M) : S.IsElementary ↔ WitnessClosed S := by
  constructor
  · intro hS n φ s a ha
    let E : L.ElementarySubstructure M := ⟨S, hS⟩
    have hex : φ.ex.Realize default (Subtype.val ∘ s) := BoundedFormula.realize_ex.mpr ⟨a, ha⟩
    have hm := E.subtype.map_boundedFormula φ.ex (default : Empty → S) s
    rw [Unique.eq_default (E.subtype ∘ (default : Empty → S))] at hm
    have hinside := BoundedFormula.realize_ex.mp (hm.mp hex)
    obtain ⟨b, hb⟩ := hinside
    refine ⟨b, ?_⟩
    have hout := (E.subtype.map_boundedFormula φ (default : Empty → S) (Fin.snoc s b)).mpr hb
    rw [Unique.eq_default (E.subtype ∘ (default : Empty → S))] at hout
    convert hout using 1
    funext i
    cases i using Fin.lastCases <;> simp [E]
  · intro hS n φ s
    exact φ.realize_relabel_sumInr.symm.trans
      ((bounded_realize_of_witnessClosed S hS _ s).trans φ.realize_relabel_sumInr)

/-- The parameter-free witness condition also rules out an empty substructure. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Conversely, suppose the witness condition holds. Applied to the parameter-free formula $\existsbind{y}{y=y}$,
    it first shows that $B$ is nonempty.
-/
theorem WitnessClosed.nonempty [Nonempty M] {S : L.Substructure M} (hS : WitnessClosed S) : Nonempty S := by
  obtain ⟨b, _⟩ := hS 0 (⊤ : L.BoundedFormula Empty 1) Fin.elim0 (Classical.choice ‹Nonempty M›) (by simp)
  exact ⟨b⟩

/-- The same elementary inclusion preserves the named formulas used in the text. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Elementary substructure.** A structure $\mathcal B$ is an \termdefine{elementary substructure} of $\mathcal A$,
    written
    $\mathcal B \prec \mathcal A$, if $B \IncludedIn A$, the interpretations of relation and function symbols on $B$ are the
    restrictions of those on $A$, and for every formula $\varphi(\vec x)$ and every $\vec b \in B$,
    $$\mathcal B \models \varphi(\vec b) \iff \mathcal A \models \varphi(\vec b).$$
-/
theorem Formula.realize_elementarySubstructure (S : L.ElementarySubstructure M)
    (φ : Formula L) (s : ℕ → S) : φ.Realize (Subtype.val ∘ s) ↔ φ.Realize s :=
  (φ.realize_toStandard (Subtype.val ∘ s)).symm.trans
    ((S.subtype.map_formula φ.toStandard s).trans (φ.realize_toStandard s))

end PolishSpaceBook.NamedFirstOrder
