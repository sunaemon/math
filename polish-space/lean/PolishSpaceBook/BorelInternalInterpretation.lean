module

public import PolishSpaceBook.BorelInterpretationFormula

@[expose] public section

/-! # Internal sets interpreting Borel codes

The full external Borel set need not belong to the model. Separation constructs
exactly its graph-coded old points, and interpretations in two models agree on
their common points.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

/-- The fixed parameter tuple for the uniform Borel membership formula. -/
def interpretationValues (c : BorelExpression) (b : ℕ → List ℕ) (w : List ℕ) : Fin 8 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, finiteSequences, childRelation c.labelGraph,
    labelSlice c.labelGraph (natOrdinal 1), labelSlice c.labelGraph (natOrdinal 2),
    c.labelGraph, basisWordGraph b, wordGraph w]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    All fixed parameters belong to $M$ by the preceding constructions, including $e(s)\in M$.
-/
lemma interpretationValues_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (b : ℕ → List ℕ) (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M)
    (w : List ℕ) : ∀ i, interpretationValues c b w i ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hT := finiteSequences_mem hM hinf hpair hunion hpower hsep
  have hn (n : ℕ) := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  intro i; fin_cases i
  · exact hΩ
  · exact hT
  · exact childRelation_mem hM hinf hpair hunion hpower hsep hc
  · exact labelSlice_mem hM hsep hT hc (hn 1)
  · exact labelSlice_mem hM hsep hT hc (hn 2)
  · exact hc
  · exact hb
  · exact hM.mem_trans (mem_finiteSequences.mpr ⟨w, rfl⟩) hT

lemma realize_interpretationFormula_values {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ) (w : List ℕ)
    (ps : Fin 8 → M) (hp : Subtype.val ∘ ps = interpretationValues c b w)
    (x : ℕ → ℕ) (g : M) (hg : g.val = pointGraph x) :
    interpretationFormula.Realize Empty.elim (Fin.snoc ps g) ↔ x ∈ c.evaluate hw (fun n => cyl (b n)) w := by
  have he : Fin.snoc ps g = ![ps 0, ps 1, ps 2, ps 3, ps 4, ps 5, ps 6, ps 7, g] := by
    funext i; fin_cases i <;> rfl
  rw [he]
  exact realize_interpretationFormula_graphs hM hinf hpair hunion hpower hsep c hw b x
    (ps 0) (ps 1) (ps 2) (ps 3) (ps 4) (ps 5) (ps 6) (ps 7) g
    (congrFun hp 0) (congrFun hp 1) (congrFun hp 2) (congrFun hp 3) (congrFun hp 4)
    (congrFun hp 5) (congrFun hp 6) w (congrFun hp 7) hg

/-- The Borel interpretation at a node, restricted to the model's points. -/
def internalInterpretation (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (b : ℕ → List ℕ) (s : List ℕ) : ZFSet.{u} :=
  (internalBaire M).sep (fun g => ∃ x : ℕ → ℕ,
    pointGraph x = g ∧ x ∈ c.evaluate hw (fun n => cyl (b n)) s)

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal Borel interpretation
-/
lemma pointGraph_mem_internalInterpretation (M : ZFSet.{u}) (c : BorelExpression)
    (hw : WellFounded c.Child) (b : ℕ → List ℕ) (s : List ℕ) (x : ℕ → ℕ) :
    pointGraph x ∈ internalInterpretation M c hw b s ↔
      pointGraph x ∈ M ∧ x ∈ c.evaluate hw (fun n => cyl (b n)) s := by
  rw [internalInterpretation, ZFSet.mem_sep, pointGraph_mem_internalBaire]
  constructor
  · rintro ⟨hx, y, hy, hys⟩
    exact ⟨hx, pointGraph_injective hy ▸ hys⟩
  · rintro ⟨hx, hxs⟩
    exact ⟨hx, x, rfl, hxs⟩

/-- The external description equals the set defined by the internal membership formula. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal Borel interpretation
-/
theorem internalInterpretation_eq_formula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ) (w : List ℕ)
    (ps : Fin 8 → M) (hp : Subtype.val ∘ ps = interpretationValues c b w)
    : internalInterpretation M c hw b w =
      (internalBaire M).sep (fun g => ∃ hg : g ∈ M,
        interpretationFormula.Realize Empty.elim (Fin.snoc ps ⟨g, hg⟩)) := by
  apply ZFSet.ext
  intro g
  rw [ZFSet.mem_sep]
  constructor
  · intro hg
    have hgB : g ∈ internalBaire M := (ZFSet.mem_sep.mp hg).1
    obtain ⟨x, hx, hgM⟩ := mem_internalBaire.mp hgB
    refine ⟨hgB, hgM, ?_⟩
    apply (realize_interpretationFormula_values hM hinf hpair hunion hpower hsep
      c hw b w ps hp x ⟨g, hgM⟩ hx.symm).mpr
    rw [← hx, pointGraph_mem_internalInterpretation] at hg
    exact hg.2
  · rintro ⟨hgB, hgM, hφ⟩
    obtain ⟨x, hx, _⟩ := mem_internalBaire.mp hgB
    have he := (realize_interpretationFormula_values hM hinf hpair hunion hpower hsep
      c hw b w ps hp x ⟨g, hgM⟩ hx.symm).mp hφ
    rw [← hx, pointGraph_mem_internalInterpretation]
    exact ⟨hx.symm ▸ hgM, he⟩

/-- Construct the interpretation using a single Separation instance on the internal Baire space. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Internal Borel interpretation
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Separation on $X_M$ therefore constructs precisely the displayed set, with no requirement that all external
    points belong to $M$.
-/
theorem internalInterpretation_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ)
    (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M) (w : List ℕ) :
    internalInterpretation M c hw b w ∈ M := by
  let ps (i : Fin 8) : M := ⟨interpretationValues c b w i,
    interpretationValues_mem hM hinf hpair hunion hpower hsep c b hc hb w i⟩
  apply separation_mem_of_absolute hM interpretationFormula (hsep _) ps
    (internalBaire_mem hM hinf hpair hunion hpower hsep)
  intro g hg
  obtain ⟨x, hx, _⟩ := mem_internalBaire.mp hg
  rw [realize_interpretationFormula_values hM hinf hpair hunion hpower hsep c hw b w ps rfl x g hx.symm]
  constructor
  · intro h
    exact ⟨x, hx, h⟩
  · rintro ⟨y, hy, h⟩
    exact pointGraph_injective (hy.trans hx.symm) ▸ h

/-- Interpreting in a larger model adds only the newly available points. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Restriction of Borel interpretations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Every $g\in X_M$ has the form $g_x$ and also belongs to $X_N$. Apply the theorem in both models:
    membership is equivalent to the same external condition $x\in A_s$. This proves both inclusions in the
    set equality.
-/
theorem internalInterpretation_restrict {M N : ZFSet.{u}} (hMN : M ⊆ N)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ) (s : List ℕ) :
    internalInterpretation N c hw b s ∩ internalBaire M = internalInterpretation M c hw b s := by
  apply ZFSet.ext
  intro g
  simp only [internalInterpretation, ZFSet.mem_inter, ZFSet.mem_sep]
  constructor
  · rintro ⟨⟨_, h⟩, hg⟩
    exact ⟨hg, h⟩
  · rintro ⟨hg, h⟩
    obtain ⟨x, hx, hxM⟩ := mem_internalBaire.mp hg
    exact ⟨⟨mem_internalBaire.mpr ⟨x, hx, hMN hxM⟩, h⟩, hg⟩

/-- Membership is absolute on points whose graphs belong to both models. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For cylinder codes on Baire space, the basic membership comparison is supplied by the explicit construction
    in §{sec:internal-borel-sets}. Given the label and basis graphs in a transitive model $M$, one fixed formula
    selects the point graphs satisfying the code from the model's internal function space.
    This constructs $\BorelInterpretation{c}{M}\in M$ rather than merely deciding membership separately for each point.
    For a second transitive model $N$ containing $M$ and the same inputs, external well-foundedness of the code gives
    $$\BorelInterpretation{c}{N}\cap(\BaireSpace\cap M)=\BorelInterpretation{c}{M}.$$
    Both models test each common point against the same external evaluation. This argument does not require
    the models to have the same ordinals. Transfer of the measure of a coded set is a further assertion.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Restriction of Borel interpretations
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The same equivalence proves agreement for a point shared by two arbitrary models.
    The argument uses the common input graphs and external well-foundedness; it does not require the models to
    have the same ordinals.
-/
lemma internalInterpretation_agree {M N : ZFSet.{u}} (c : BorelExpression)
    (hw : WellFounded c.Child) (b : ℕ → List ℕ) (s : List ℕ) (x : ℕ → ℕ)
    (hxM : pointGraph x ∈ M) (hxN : pointGraph x ∈ N) :
    pointGraph x ∈ internalInterpretation M c hw b s ↔
      pointGraph x ∈ internalInterpretation N c hw b s := by
  simp only [pointGraph_mem_internalInterpretation, hxM, hxN, true_and]

end PolishSpaceBook.BorelExpression
