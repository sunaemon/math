module

public import PolishSpaceBook.BorelInternalInterpretation
public import PolishSpaceBook.SetTheoryDefinableChoice
public import PolishSpaceBook.SetTheoryFiniteCardinality

@[expose] public section

/-! # The whole family of internal interpretations of a Borel expression -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

/-- Every finite node is assigned its internal interpretation, including absent nodes. -/
def internalInterpretationFamily (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (b : ℕ → List ℕ) : ZFSet.{u} :=
  functionGraph (fun s : (finiteSequences : ZFSet.{u}) =>
    internalInterpretation M c hw b (wordEquiv.symm s))

lemma pair_mem_internalInterpretationFamily (M : ZFSet.{u}) (c : BorelExpression)
    (hw : WellFounded c.Child) (b : ℕ → List ℕ) (s : List ℕ) (A : ZFSet.{u}) :
    pair (wordGraph s) A ∈ internalInterpretationFamily M c hw b ↔
      A = internalInterpretation M c hw b s := by
  change pair (wordEquiv s).val A ∈ functionGraph _ ↔ _
  rw [pair_mem_functionGraph, Equiv.symm_apply_apply, eq_comm]

/-- The same defining formula recognizes each set-valued fiber, not just each point in it. -/
lemma realize_interpretationFiber {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ) (w : List ℕ)
    (Ω T R U C l B X s A : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (hT : T.val = finiteSequences)
    (hR : R.val = childRelation c.labelGraph)
    (hU : U.val = labelSlice c.labelGraph (natOrdinal 1))
    (hC : C.val = labelSlice c.labelGraph (natOrdinal 2))
    (hl : l.val = c.labelGraph) (hB : B.val = basisWordGraph b)
    (hX : X.val = internalBaire M) (hs : s.val = wordGraph w) :
    (choiceFiberFormula interpretationFormula).Realize Empty.elim
      (Fin.snoc (Fin.snoc (Fin.snoc ![Ω, T, R, U, C, l, B] X) s) A) ↔
      A.val = internalInterpretation M c hw b w := by
  rw [realize_choiceFiberFormula]
  have hg (g : M) (hgX : g.val ∈ X.val) :
      interpretationFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ![Ω, T, R, U, C, l, B] s) g) ↔
        g.val ∈ internalInterpretation M c hw b w := by
    obtain ⟨x, hx, hxM⟩ := mem_internalBaire.mp (hX ▸ hgX)
    have he : Fin.snoc (Fin.snoc ![Ω, T, R, U, C, l, B] s) g = ![Ω, T, R, U, C, l, B, s, g] := by
      funext i; fin_cases i <;> rfl
    rw [he, realize_interpretationFormula_graphs hM hinf hpair hunion hpower hsep c hw b x
      Ω T R U C l B s g hΩ hT hR hU hC hl hB w hs hx.symm, ← hx,
      pointGraph_mem_internalInterpretation, and_iff_right (hx.symm ▸ hxM)]
  have hbound {g : ZFSet.{u}} (h : g ∈ internalInterpretation M c hw b w) : g ∈ X.val :=
    hX.symm ▸ (ZFSet.mem_sep.mp h).1
  have hI : internalInterpretation M c hw b w ∈ M :=
    internalInterpretation_mem hM hinf hpair hunion hpower hsep c hw b (hl ▸ l.property) (hB ▸ B.property) w
  constructor
  · intro h
    ext g
    constructor
    · intro hga
      let G : M := ⟨g, hM.mem_trans hga A.property⟩
      obtain ⟨hgX, hφ⟩ := (h G).mp hga
      exact (hg G hgX).mp hφ
    · intro hgi
      let G : M := ⟨g, hM.mem_trans hgi hI⟩
      exact (h G).mpr ⟨hbound hgi, (hg G (hbound hgi)).mpr hgi⟩
  · intro he g
    rw [he]
    exact ⟨fun hi => ⟨hbound hi, (hg g (hbound hi)).mpr hi⟩,
      fun ⟨hgX, hφ⟩ => (hg g hgX).mp hφ⟩

/-- Replacement collects every set-valued interpretation into one internal input graph. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal family of node interpretations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Use the membership formula $\Phi$ of §{sec:internal-borel-sets}. With its label, basis, and other fixed
    parameters suppressed, the set-valued fiber at $s$ is defined by
    $$\forall g\;[g\in D\longleftrightarrow g\in X_M\land\Phi(e(s),g)].$$
    Inside $M$, this formula holds exactly when $D=B_s$. Indeed, for a graph in $X_M$, the interpretation theorem
    identifies $\Phi$ with membership in $B_s$; outside $X_M$, both descriptions exclude the graph.
    Each $B_s$ belongs to $M$ by that theorem, and Extensionality gives uniqueness. The graph-collection lemma
    of §{sec:internal-model-closure}, applied on the internal finite-word set $F$, now puts $\mathcal I_c$ in $M$.
    This uses Replacement for the set-valued definition, not just pointwise membership of its values in $M$.
-/
theorem internalInterpretationFamily_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (b : ℕ → List ℕ)
    (hc : c.labelGraph ∈ M) (hb : basisWordGraph b ∈ M) : internalInterpretationFamily M c hw b ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let T : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let R : M := ⟨_, childRelation_mem hM hinf hpair hunion hpower hsep hc⟩
  let U : M := ⟨_, labelSlice_mem hM hsep T.property hc (hn 1)⟩
  let C : M := ⟨_, labelSlice_mem hM hsep T.property hc (hn 2)⟩
  let l : M := ⟨_, hc⟩
  let B : M := ⟨_, hb⟩
  let X : M := ⟨_, internalBaire_mem hM hinf hpair hunion hpower hsep⟩
  let values (s : (finiteSequences : ZFSet.{u})) : M := ⟨internalInterpretation M c hw b (wordEquiv.symm s),
    internalInterpretation_mem hM hinf hpair hunion hpower hsep c hw b hc hb _⟩
  apply replacement_graph_mem hM hpair (choiceFiberFormula interpretationFormula) (hrep _)
    (Fin.snoc ![Ω, T, R, U, C, l, B] X) T.property values
  intro s A
  have he : wordGraph (wordEquiv.symm s) = s.val := congrArg Subtype.val (wordEquiv.apply_symm_apply s)
  rw [realize_interpretationFiber hM hinf hpair hunion hpower hsep c hw b (wordEquiv.symm s)
    Ω T R U C l B X ⟨s.val, hM.mem_trans s.property T.property⟩ A
    rfl rfl rfl rfl rfl rfl rfl rfl he.symm]
  constructor
  · intro he
    apply Subtype.ext
    exact he
  · intro he
    exact congrArg Subtype.val he

end PolishSpaceBook.BorelExpression
