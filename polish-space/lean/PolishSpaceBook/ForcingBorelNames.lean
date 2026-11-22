module

public import PolishSpaceBook.ForcingFunctionSpaceNames
public import PolishSpaceBook.ForcingOrdinalPreservation
public import PolishSpaceBook.ForcingPairing
public import PolishSpaceBook.ForcingUnionClosure
public import PolishSpaceBook.CantorInternalMeasureBorelValues

@[expose] public section

/-! # A uniform ground-model name for the interpretation of a Borel code in the extension -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames BorelExpression CantorTreeMeasure
universe u

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)

/-- The name for all binary point graphs belonging to the extension. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, put
    $$\CantorSpaceName:=\ForcingFunctionSpaceName{\omega}{2}.$$
    Its value is $Y_{M[G]}$, the set of binary point graphs in the extension.
    For a well-founded Borel code $c$ with its entire label graph in $M$, let $\vec a_c$ be the eight
    parameters of the membership formula $\Phi$ in §{sec:internal-borel-sets}, using the standard cylinder
    enumeration and the root node. The internal finite-word, label-slice, and canonical-basis constructions
    put every parameter in $M$. Use their componentwise check names and define
    $$\BorelCodeName{c}:=\ForcingSeparationName{\CantorSpaceName}{\Phi}{\check{\vec a_c}}.$$
    The interpretation of the code in a model is the set denoted by $\BorelInterpretation{c}{M}$ in
    §{sec:borel-codes-why}.
-/
def cantorSpaceName : Name P.val M :=
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let two : M := ⟨natOrdinal 2, hM.mem_trans (mem_omegaOrdinal.mpr ⟨2, rfl⟩) Ω.property⟩
  functionSpaceName hM hinf hpair hunion hpower hsep hrep P R hR Ω two

include hM hinf hpair hunion hpower hsep hrep hR in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, put
    $$\CantorSpaceName:=\ForcingFunctionSpaceName{\omega}{2}.$$
    Its value is $Y_{M[G]}$, the set of binary point graphs in the extension.
    For a well-founded Borel code $c$ with its entire label graph in $M$, let $\vec a_c$ be the eight
    parameters of the membership formula $\Phi$ in §{sec:internal-borel-sets}, using the standard cylinder
    enumeration and the root node. The internal finite-word, label-slice, and canonical-basis constructions
    put every parameter in $M$. Use their componentwise check names and define
    $$\BorelCodeName{c}:=\ForcingSeparationName{\CantorSpaceName}{\Phi}{\check{\vec a_c}}.$$
    The interpretation of the code in a model is the set denoted by $\BorelInterpretation{c}{M}$ in
    §{sec:borel-codes-why}.
-/
lemma value_cantorSpaceName (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    value P.val G (cantorSpaceName hM hinf hpair hunion hpower hsep hrep P R hR).val =
      internalCantor (Extension P.val M G) :=
  value_functionSpaceName hM hinf hpair hunion hpower hsep hrep P R hR _ _ G hG

/-- Only the entire label graph is an input; the canonical basis and node parameters are constructed. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, put
    $$\CantorSpaceName:=\ForcingFunctionSpaceName{\omega}{2}.$$
    Its value is $Y_{M[G]}$, the set of binary point graphs in the extension.
    For a well-founded Borel code $c$ with its entire label graph in $M$, let $\vec a_c$ be the eight
    parameters of the membership formula $\Phi$ in §{sec:internal-borel-sets}, using the standard cylinder
    enumeration and the root node. The internal finite-word, label-slice, and canonical-basis constructions
    put every parameter in $M$. Use their componentwise check names and define
    $$\BorelCodeName{c}:=\ForcingSeparationName{\CantorSpaceName}{\Phi}{\check{\vec a_c}}.$$
    The interpretation of the code in a model is the set denoted by $\BorelInterpretation{c}{M}$ in
    §{sec:borel-codes-why}.
-/
def borelNameParameters (c : BorelExpression) (hc : c.labelGraph ∈ M) : Fin 8 → M := fun i =>
  ⟨interpretationValues c NamedLambda.NatListCode.decode [] i,
    interpretationValues_mem hM hinf hpair hunion hpower hsep c _ hc
      (canonicalBasisWordGraph_mem hM hinf hpair hunion hpower hsep) [] i⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, put
    $$\CantorSpaceName:=\ForcingFunctionSpaceName{\omega}{2}.$$
    Its value is $Y_{M[G]}$, the set of binary point graphs in the extension.
    For a well-founded Borel code $c$ with its entire label graph in $M$, let $\vec a_c$ be the eight
    parameters of the membership formula $\Phi$ in §{sec:internal-borel-sets}, using the standard cylinder
    enumeration and the root node. The internal finite-word, label-slice, and canonical-basis constructions
    put every parameter in $M$. Use their componentwise check names and define
    $$\BorelCodeName{c}:=\ForcingSeparationName{\CantorSpaceName}{\Phi}{\check{\vec a_c}}.$$
    The interpretation of the code in a model is the set denoted by $\BorelInterpretation{c}{M}$ in
    §{sec:borel-codes-why}.
-/
def borelInterpretationName (c : BorelExpression) (hc : c.labelGraph ∈ M) : Name P.val M :=
  separatedName hM hinf hpair hunion hpower hsep hrep P R hR
    (cantorSpaceName hM hinf hpair hunion hpower hsep hrep P R hR) interpretationFormula
    (fun i => internalCheckName hM hinf hpair hunion hpower hsep hrep P
      (borelNameParameters hM hinf hpair hunion hpower hsep c hc i))

include hM hinf hpair hunion hpower hsep hrep hR in
lemma realize_borelNameParameters (c : BorelExpression) (hw : WellFounded c.Child) (hc : c.labelGraph ∈ M)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    (x : ℕ → Bool) (hx : cantorPointGraph x ∈ Extension P.val M G) :
    interpretationFormula.Realize Empty.elim
      (Fin.snoc (fun i => evalName P.val M G (internalCheckName hM hinf hpair hunion hpower hsep hrep P
        (borelNameParameters hM hinf hpair hunion hpower hsep c hc i))) ⟨cantorPointGraph x, hx⟩) ↔
      x ∈ cantorSet c hw := by
  have hE := extension_isTransitive P.val M (chosen P.val G) hM
  have hiE := extension_models_infinity hM hinf hpair hunion hpower hsep hrep P.property
    (chosen P.val G) (chosen_meets_condition P.val G)
  have hpE := ForcingNames.extension_models_pairing hM hinf hpair hunion hpower (hrep _) P.property
    (chosen P.val G) (chosen_meets_condition P.val G)
  have huE := extension_models_union hM hinf hpair hunion hpower (hrep _) (hrep _)
    P.property R.property hR G
  have hpowE := extension_models_power hM hinf hpair hunion hpower hsep hrep P R hR G hG
  have hsepE := fun {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)) =>
    extension_models_separation hM hinf hpair hunion hpower hsep hrep P R hR G hG φ
  let ps (i : Fin 8) := evalName P.val M G (internalCheckName hM hinf hpair hunion hpower hsep hrep P
    (borelNameParameters hM hinf hpair hunion hpower hsep c hc i))
  have hps : Subtype.val ∘ ps = interpretationValues c NamedLambda.NatListCode.decode [] := by
    funext i
    exact value_internalCheckName hM hinf hpair hunion hpower hsep hrep P _ G
  exact realize_interpretationFormula_values hE hiE hpE huE hpowE hsepE c hw NamedLambda.NatListCode.decode []
    ps hps (cantorInclusion x) ⟨cantorPointGraph x, hx⟩ rfl

include hM hinf hpair hunion hpower hsep hrep hR in
lemma mem_value_borelInterpretationName (c : BorelExpression) (hw : WellFounded c.Child) (hc : c.labelGraph ∈ M)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    (x : ℕ → Bool) (hx : cantorPointGraph x ∈ Extension P.val M G) :
    cantorPointGraph x ∈ value P.val G (borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hc).val ↔
      x ∈ cantorSet c hw := by
  change (⟨cantorPointGraph x, hx⟩ : Extension P.val M G).val ∈ _ ↔ _
  rw [borelInterpretationName, separatedName, mem_value_separationName P.val M hM _ _ _ G
    (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG),
    value_cantorSpaceName hM hinf hpair hunion hpower hsep hrep P R hR G hG,
    cantorPointGraph_mem_internalCantor,
    realize_borelNameParameters hM hinf hpair hunion hpower hsep hrep P R hR c hw hc G hG x hx]
  exact and_iff_right hx

include hM hinf hpair hunion hpower hsep hrep hR in
lemma value_borelInterpretationName_subset (c : BorelExpression) (hc : c.labelGraph ∈ M)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    value P.val G (borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hc).val ⊆
      internalCantor (Extension P.val M G) := by
  intro g hg
  have hgE := (extension_isTransitive P.val M (chosen P.val G) hM).mem_trans hg
    (evalName P.val M G (borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hc)).property
  have hmem := (mem_value_separationName P.val M hM _ _ _ G
    (modelGeneric_meets_tests hM hinf hpair hunion hpower hsep hrep P R hR G hG) ⟨g, hgE⟩).mp hg
  rw [value_cantorSpaceName hM hinf hpair hunion hpower hsep hrep P R hR G hG] at hmem
  exact hmem.1

include hM hinf hpair hunion hpower hsep hrep hR in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Names for interpreted Borel sets
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Check-name closure and the internal Separation construction give the displayed name in $M^P$.
    The preceding theorem supplies its ambient set of binary graphs. The extension is transitive and
    satisfies the elementary axioms and Separation needed in §{sec:internal-borel-sets}.
    Each checked parameter evaluates to the same ground-model set. Apply the uniform interpretation
    formula there to the extension and to any binary point graph it contains. External well-foundedness
    of the code identifies the truth set at all nodes, so $\Phi$ holds at the root exactly when the
    binary point belongs to $A_c$. The Separation valuation identity therefore gives precisely the
    internal interpretation in $M[G]$, proving equality of the whole sets.
    For the final assertion, the value of any ground-model name belongs to the extension; apply this
    membership characterization to the specified value of $\tau$.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Let $c\in M$ be a Borel code, and write $\BorelInterpretation{c}{K}$ for its interpretation in a transitive model $K$
    containing $c$. The construction in §{sec:internal-random-union-tests} gives a ground-model name
    $\BorelCodeName{c}$ with
    $$\bigl(\BorelCodeName{c}\bigr)^G=\BorelInterpretation{c}{M[G]}$$
    for every $M$-generic filter $G$.
    It first constructs a name for all binary point graphs in the extension, then applies the uniform
    Borel membership formula by Separation. This is the convention of §{sec:borel-codes-why};
    unlike $\check{\BorelInterpretation{c}{M}}$, the valuation of $\BorelCodeName{c}$ may contain new reals.
-/
theorem value_borelInterpretationName (c : BorelExpression) (hw : WellFounded c.Child) (hc : c.labelGraph ∈ M)
    (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G) :
    value P.val G (borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hc).val =
      internalBorelCantorSet (Extension P.val M G) c hw := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, rfl, hxE⟩ := mem_internalCantor.mp
      (value_borelInterpretationName_subset hM hinf hpair hunion hpower hsep hrep P R hR c hc G hG hg)
    exact (cantorPointGraph_mem_internalBorelCantorSet _ c hw x).mpr
      ⟨hxE, (mem_value_borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hw hc G hG x hxE).mp hg⟩
  · intro hg
    obtain ⟨x, rfl, hxE⟩ := mem_internalCantor.mp (ZFSet.mem_inter.mp hg).2
    exact (mem_value_borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hw hc G hG x hxE).mpr
      ((cantorPointGraph_mem_internalBorelCantorSet _ c hw x).mp hg).2

include hM hinf hpair hunion hpower hsep hrep hR in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Names for interpreted Borel sets
-/
theorem named_point_mem_borelInterpretationName (c : BorelExpression) (hw : WellFounded c.Child)
    (hc : c.labelGraph ∈ M) (G : Order.PFilter (Condition P.val)) (hG : ModelGeneric P.val M G)
    (σ : Name P.val M) (x : ℕ → Bool) (hσ : value P.val G σ.val = cantorPointGraph x) :
    value P.val G σ.val ∈
        value P.val G (borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hc).val ↔
      x ∈ cantorSet c hw := by
  have hx : cantorPointGraph x ∈ Extension P.val M G := hσ ▸ (evalName P.val M G σ).property
  rw [hσ]
  exact mem_value_borelInterpretationName hM hinf hpair hunion hpower hsep hrep P R hR c hw hc G hG x hx

end PolishSpaceBook.SetTheoryModels
