module

public import PolishSpaceBook.InternalDenseConullCodes
public import PolishSpaceBook.InternalRandomPointFilter

@[expose] public section

/-! # Null avoidance implies genericity for the internal random order -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas BorelExpression MeasureTheory
universe u

variable {M D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)
  (hcode : ∀ c : Code, c.val.labelGraph ∈ M → internalBorelCantorSet M c.val c.property.2.2.2.2.2 ∈ D)
  (himage : ∀ (c : Code) (hc : c.val.labelGraph ∈ M),
    η (nullClassOf (F := F) ⟨_, hcode c hc⟩) = c.measureClass)

include h hpos himage in
lemma code_null_of_internal_zero (c : Code) (hc : c.val.labelGraph ∈ M)
    (hz : h.value (internalBorelCantorSet M c.val c.property.2.2.2.2.2) = 0) :
    fairCoinProduct c.cantor = 0 := by
  apply (Code.measureClass_eq_bot_iff c).mp
  rw [← himage c hc]
  by_contra hn
  have hp := (class_mem_positiveNullQuotient_iff h
    ⟨internalBorelCantorSet M c.val c.property.2.2.2.2.2, hcode c hc⟩).mp ((hpos _).mp hn)
  rw [hz] at hp
  exact (lt_irrefl (0 : ℝ)) hp

variable (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hchoice : M ⊨ choiceSentence) (hca : h.CountablyAdditiveOn M)
  (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M) (hY : internalCantor M ∈ D)
  (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔
    h.value (A.val \ B.val) = 0)
  (hcodes : HasInternalBorelRepresentatives M D)

include h hpos himage hM hinf hpair hunion hpower hsep hrep hchoice hca hD hR hF hY hdom hle hcodes in
/-- An internally coded conull cover makes the point filter meet an arbitrary ground-model dense set. -/
theorem internalPointFilter_meets_dense {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    {Δ : ZFSet.{u}} (hΔ : Δ ∈ M)
    (hdense : IsCoinitial {p : InternalRandomCondition D F η | p.val ∈ Δ}) :
    ∃ p ∈ internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx,
      p.val ∈ Δ := by
  obtain ⟨c,hc,hcD,hU,_,hz⟩ := internal_dense_conull_codes hM hinf hpair hunion hpower hsep hrep
    hchoice h hca hD hR hF hY hdom hΔ η hle hdense hcodes
  let U := Code.iUnion c
  have hcomp := Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep U hU
  have hzcomp : h.value (internalBorelCantorSet M U.compl.val U.compl.property.2.2.2.2.2) = 0 := by
    rw [internalBorelCantorSet_compl]
    exact hz
  have hxU : x ∈ U.cantor := by
    by_contra hn
    exact hx U.compl hcomp (code_null_of_internal_zero h η hpos hcode himage U.compl hcomp hzcomp)
      (by rw [Code.cantor_compl]; exact hn)
  rw [show U = Code.iUnion c from rfl, Code.cantor_iUnion, Set.mem_iUnion] at hxU
  obtain ⟨n,hxn⟩ := hxU
  have hcn : (c n).val.labelGraph ∈ M := hM.mem_trans
    (mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph _ n _).mpr rfl⟩)
    (graphRange_mem hM hunion (hsep _) hc)
  let p := pointCodeCondition η hpos hcode himage hx (c n) hcn hxn
  have hpG : p ∈ internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx :=
    (mem_internalPointFilter_iff η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx p
      (c n) hcn (image_pointCodeCondition η hpos hcode himage hx (c n) hcn hxn)).mpr hxn
  refine ⟨p,hpG,?_⟩
  rcases (hcD n).2 with he | he
  · have hp := (class_mem_positiveNullQuotient_iff h
      ⟨internalBorelCantorSet M (c n).val (c n).property.2.2.2.2.2, hcode (c n) hcn⟩).mp p.property
    change 0 < h.value (internalBorelCantorSet M (c n).val (c n).property.2.2.2.2.2) at hp
    rw [he,h.value_zero] at hp
    exact False.elim ((lt_irrefl (0 : ℝ)) hp)
  · exact he

include h hpos himage hM hinf hpair hunion hpower hsep hrep hchoice hca hD hR hF hY hdom hle hcodes in
/-- Genericity follows from null avoidance; the whole-table hypothesis has already been constructed. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Genericity of the null-avoiding point filter
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The selection theorem in §{sec:internal-borel-code-recognition} expresses the relation
    $\BorelInterpretation{c}{M}=V_j$ by one formula on the internal set of valid label graphs.
    Internal choice gives a selector on the range of the sequence $V_j$; reading that same selector along the
    sequence gives the entire table of chosen label graphs in $M$. The internal union constructor therefore
    produces a Borel code in $M$ for the cover.
    Its complement is internally null, so measure absoluteness makes its full external interpretation null as well.
    Thus $r$ belongs to a representative of a positive condition in $\Delta$, and $G_r$ meets $\Delta$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Let $\Delta\in M$ be dense in the internal positive order. The preceding corollary supplies codes $c_j$ and
    a union code $u$ in $M$, with internally conull union, such that each internal interpretation $V_j$ is empty
    or represents a condition in $\Delta$. Measure comparison makes the full external interpretation of the
    complement of $u$ null. Since $r$ avoids it, $r\in A_{c_j}$ for some $j$.
    The point-filter lemma makes $q(V_j)$ a positive condition in $G_r$.
    Consequently $V_j\ne\emptyset$, so $q(V_j)\in\Delta$. This proves genericity.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    For a finite binary word $s$, take its one-leaf cylinder code. Its root label is the basis index plus $3$,
    and all other labels are $0$. Bounded graph collection puts this entire label graph in $M$.
    Its external interpretation is exactly $\cyl{s}$, so the point-filter membership criterion proves the displayed
    cylinder equivalence. The random-real valuation theorem now gives a point $y$ with these same cylinder decisions.
    For each $n$, both points belong to $\cyl{\restrict{r}{n+1}}$, hence $y(n)=r(n)$.
    Thus $y=r$, proving the valuation identity.
-/
theorem internalPointFilter_modelGeneric {x : ℕ → Bool} (hx : AvoidsNullCodes M x) :
    @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η)
      (codedRandomFilter η (internalPointFilter η hpos hcode himage
        hM hinf hpair hunion hpower hsep hrep hx)) := by
  let := internalConditionCodedOrder η
  intro Δ hΔ _ hd
  have hd' : IsCoinitial {p : InternalRandomCondition D F η | p.val ∈ Δ} := by
    intro p
    obtain ⟨q,hq,hqp⟩ := hd (internalConditionCoding η p)
    exact ⟨(internalConditionCoding η).symm q,hq,hqp⟩
  obtain ⟨p,hp,hpΔ⟩ := internalPointFilter_meets_dense h η hpos hcode himage
    hM hinf hpair hunion hpower hsep hrep hchoice hca hD hR hF hY hdom hle hcodes hx hΔ hd'
  refine ⟨internalConditionCoding η p,?_,hpΔ⟩
  exact (image_mem_transportPFilter (internalConditionCoding η).toOrderEmbedding _ p).mpr hp

end PolishSpaceBook.CantorTreeMeasure
