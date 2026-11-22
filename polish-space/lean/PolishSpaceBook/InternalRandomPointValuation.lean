module

public import PolishSpaceBook.InternalRandomPointGenericity
public import PolishSpaceBook.BorelInternalCylinderCodes
public import PolishSpaceBook.InternalRandomLengthTests

@[expose] public section

/-! # The generic filter of a null-avoiding point recovers that point -/

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
  (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hη : Function.Injective η)
  (hrepSet : ∀ (X : D) (A : Set (ℕ → Bool)) (hm : MeasurableSet A), InternallyApproximable M A →
    RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hm)
  (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
    pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)

include h himage hM hinf hpair hunion hpower hsep hrep hrepSet hcyl in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Genericity of the null-avoiding point filter
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
lemma internalPointFilter_cylinder_decisions {x : ℕ → Bool} (hx : AvoidsNullCodes M x) (s : List Bool) :
    x ∈ cyl s ↔ randomCoinCylinder s ∈ transportPFilter (internalConditionEmbedding η hη hpos)
      (internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx) := by
  let c := Code.binaryCylinder s
  have hc : c.val.labelGraph ∈ M := Code.binaryCylinder_labelGraph_mem hM hinf hpair hunion hpower hsep hrep s
  have he := image_internalCylinderCondition η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet s
  have hec : η (internalConditionClass η (internalCylinderCondition η h hcyl s)) = c.measureClass := by
    have hv := congrArg Subtype.val he
    change η (internalConditionClass η (internalCylinderCondition η h hcyl s)) =
      randomCylinder fairCoinProduct s at hv
    change η (internalConditionClass η (internalCylinderCondition η h hcyl s)) =
      MeasureAlgebra.mk (Code.binaryCylinder s).cantor _
    apply hv.trans
    apply (MeasureAlgebra.mk_eq_mk _ _).mpr
    rw [Code.cantor_binaryCylinder]
  rw [← he, image_mem_transportPFilter]
  rw [mem_internalPointFilter_iff η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx
    (internalCylinderCondition η h hcyl s) c hc hec]
  rw [Code.cantor_binaryCylinder]

variable (hchoice : M ⊨ choiceSentence) (hca : h.CountablyAdditiveOn M)
  (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M) (hY : internalCantor M ∈ D)
  (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔
    h.value (A.val \ B.val) = 0)
  (hcodes : HasInternalBorelRepresentatives M D)

include h himage hM hinf hpair hunion hpower hsep hrep hrepSet hcyl
  hη hchoice hca hD hR hF hY hdom hle hcodes in
/-- Evaluating the random-real name at the point's generic filter returns its actual graph. -/
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
    For each finite binary word $s$, its one-leaf cylinder code belongs to $M$. Hence
    $$q(\InternalCylinder{M}{s})\in G_r\quad\Longleftrightarrow\quad r\in\cyl{s}.$$
    §{sec:internal-borel-code-recognition} uses these decisions to identify the valuation of the
    random-real name with $r$. Together with null-set avoidance, this proves the random-genericity characterization.
    The internally selected table supplies the conull code; the collection of all defects considered externally
    need not itself have a code in $M$.
-/
theorem internalPointFilter_valuation {x : ℕ → Bool} (hx : AvoidsNullCodes M x) :
    ForcingNames.valuation (internalFilterSet η
      (internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx))
      (randomRealName M D F) = cantorPointGraph x := by
  let G := internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep hx
  have hG := internalPointFilter_modelGeneric h η hpos hcode himage hM hinf hpair hunion hpower hsep hrep
    hchoice hca hD hR hF hY hdom hle hcodes hx
  obtain ⟨y, hy, hv, _⟩ := modelGeneric_randomReal hM hinf hpair hunion hpower hsep hrep h η hle hcyl
    hD hF hdom hη hpos hrepSet G hG
  have he : y = x := by
    funext i
    have hx' := (internalPointFilter_cylinder_decisions h η hpos hcode himage hM hinf hpair hunion hpower
      hsep hrep hη hrepSet hcyl hx (seqPrefix x (i+1))).mp (mem_cyl_seqPrefix x (i+1))
    have hy' := (hy (seqPrefix x (i+1))).mpr hx'
    exact (hy' i (by simp)).trans (seqPrefix_get x _)
  exact hv.trans (congrArg cantorPointGraph he)

end PolishSpaceBook.CantorTreeMeasure
