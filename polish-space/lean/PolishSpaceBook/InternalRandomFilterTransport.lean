module

public import PolishSpaceBook.InternalMeasureAlgebraComparison
public import PolishSpaceBook.InternalRandomRealNames
public import PolishSpaceBook.PFilterTransport

@[expose] public section

/-! # Internal random conditions, transported filters, and evaluation of the random-real name -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory ForcingNames
universe u

/-- Positive set-coded classes, ordered using the faithful comparison map. -/
structure InternalRandomCondition (D F : ZFSet.{u})
    (_η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct) where
  val : ZFSet.{u}
  property : val ∈ positiveNullQuotient D F

variable {D F : ZFSet.{u}} (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)

lemma internalRandomCondition_ext {p q : InternalRandomCondition D F η} (he : p.val = q.val) : p = q := by
  cases p; cases q; cases he; rfl

def internalConditionClass (p : InternalRandomCondition D F η) : relationQuotient D (nullRelation D F) :=
  ⟨p.val, (ZFSet.mem_sep.mp p.property).1⟩

instance : Preorder (InternalRandomCondition D F η) :=
  Preorder.lift (fun p => η (internalConditionClass η p))

lemma internalCondition_antisymm (hη : Function.Injective η) {p q : InternalRandomCondition D F η}
    (hpq : p ≤ q) (hqp : q ≤ p) : p = q :=
  internalRandomCondition_ext η (congrArg Subtype.val (hη (le_antisymm hpq hqp)))

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Order the internal positive classes by $q(X)\le q(Y)$ if $\nu(\SetDifference{X}{Y})=0$.
    The comparison theorem makes this well-defined and turns the restriction of $\eta$ to $P$ into an
    order embedding into the external positive measure classes $Q_+$.
-/
def internalConditionEmbedding (hη : Function.Injective η)
    (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F) :
    InternalRandomCondition D F η ↪o MeasureAlgebra.Positive fairCoinProduct where
  toFun p := ⟨η (internalConditionClass η p), (hpos _).mpr p.property⟩
  inj' := by
    intro p q he
    exact internalRandomCondition_ext η (congrArg Subtype.val (hη (congrArg Subtype.val he)))
  map_rel_iff' := Iff.rfl

/-- The set of set-coded conditions used by valuation. -/
def internalFilterSet (G : Order.PFilter (InternalRandomCondition D F η)) : Set ZFSet.{u} :=
  {p | ∃ q ∈ G, q.val = p}

lemma condition_mem_internalFilterSet (G : Order.PFilter (InternalRandomCondition D F η))
    (p : InternalRandomCondition D F η) : p.val ∈ internalFilterSet η G ↔ p ∈ G := by
  constructor
  · rintro ⟨q, hq, he⟩; exact internalRandomCondition_ext η he ▸ hq
  · intro hp; exact ⟨p, hp, rfl⟩

lemma internalFilterSet_meets (G : Order.PFilter (InternalRandomCondition D F η)) :
    ∃ p ∈ internalFilterSet η G, p ∈ positiveNullQuotient D F := by
  obtain ⟨p, hp⟩ := G.nonempty
  exact ⟨p.val, ⟨p, hp, rfl⟩, p.property⟩

lemma measurable_bitCell (n : ℕ) (i : Bool) : MeasurableSet {x : ℕ → Bool | x n = i} :=
  (measurableSet_singleton i).preimage (measurable_pi_apply n)

def randomCoinBit (n : ℕ) (i : Bool) : MeasureAlgebra.Positive fairCoinProduct :=
  ⟨MeasureAlgebra.mk {x | x n = i} (measurable_bitCell n i), by
    rw [ne_eq, MeasureAlgebra.mk_eq_bot, measure_bitCell]
    norm_num⟩

lemma randomFilterReal_bit_iff (H : Order.PFilter (MeasureAlgebra.Positive fairCoinProduct))
    (hlen : ∀ n, ∃ p ∈ H, p ∈ randomLengthRequirement fairCoinProduct n) (n : ℕ) (i : Bool) :
    randomFilterReal H hlen n = i ↔ randomCoinBit n i ∈ H := by
  let x := randomFilterReal H hlen
  let s := seqPrefix x (n + 1)
  have hs : randomCoinCylinder s ∈ H := (randomCoinFilterReal_mem_cyl H hlen s).mp (mem_cyl_seqPrefix x _)
  have hcoord {y : ℕ → Bool} (hy : y ∈ cyl s) : y n = x n := by
    have he := hy n (by simp [s, seqPrefix_length])
    simpa only [s, seqPrefix, List.get_eq_getElem, List.getElem_ofFn] using he
  constructor
  · intro hx
    apply H.mem_of_le (x := randomCoinCylinder s) _ hs
    change (MeasureAlgebra.mk (cyl s) _ : MeasureAlgebra fairCoinProduct) ≤ MeasureAlgebra.mk {y | y n = i} _
    exact Filter.Eventually.of_forall (fun y hy => (hcoord hy).trans hx)
  · intro hi
    obtain ⟨p, _, hps, hpi⟩ := H.directed _ hs _ hi
    by_contra hx
    have hempty : cyl s ∩ {y : ℕ → Bool | y n = i} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hx ((hcoord hy.1).symm.trans hy.2)
    have hbot : (randomCoinCylinder s).val ⊓ (randomCoinBit n i).val = ⊥ := by
      change MeasureAlgebra.mk (cyl s) _ ⊓ MeasureAlgebra.mk {y | y n = i} _ = _
      rw [MeasureAlgebra.mk_inf, MeasureAlgebra.mk_eq_bot, hempty]
      exact measure_empty
    exact p.property (le_bot_iff.mp ((le_inf hps hpi).trans_eq hbot))

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

include hM hinf hpair hunion hpower hsep in
lemma internallyApproximable_binaryCylinder (s : List Bool) : InternallyApproximable M (cyl s) := by
  rw [← BorelExpression.cantorInclusion_preimage_cyl]
  exact internallyApproximable_cylinder hM hinf hpair hunion hpower hsep (s.map Bool.toNat)

include hM hinf hpair hunion hpower hsep in
lemma internallyApproximable_bitCell (n : ℕ) (i : Bool) : InternallyApproximable M {x | x n = i} := by
  rw [← levelSet_bitWords]
  exact internallyApproximable_finset_union hM hinf hpair hunion hpower hsep _ _
    (fun s _ => internallyApproximable_binaryCylinder hM hinf hpair hunion hpower hsep (List.ofFn s))

variable {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
    pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)

def internalCylinderCondition (s : List Bool) : InternalRandomCondition D F η :=
  ⟨relationClass D (nullRelation D F) (internalWordCylinder M s),
    (class_mem_positiveNullQuotient_iff h ⟨_, (hcyl s).1⟩).mpr (by
      rw [h.value_of_code (hcyl s).1 (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ s.length) (hcyl s).2]
      positivity)⟩

def internalBitCondition (n : ℕ) (i : Bool) : InternalRandomCondition D F η :=
  ⟨relationClass D (nullRelation D F) (membershipFiber (internalCantor M) (bitLabel n i)),
    (class_mem_positiveNullQuotient_iff h ⟨_, (bitFiber_domain_positive h M hcyl n i).1⟩).mpr
      (bitFiber_domain_positive h M hcyl n i).2⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For each $n\in\omega$, define the internal length requirement by
    $$\InternalRandomLength{M}{n}:=
    \{p\in P:\exists s\in\funcspace{n}{2}\ (p\le q(\InternalCylinder{M}{s}))\}.$$
    We now construct these sets inside the model and prove their density.
-/
def internalRandomLengthRequirement (n : ℕ) : Set (InternalRandomCondition D F η) :=
  {p | ∃ s : List Bool, s.length = n ∧ p ≤ internalCylinderCondition η h hcyl s}

variable (hη : Function.Injective η) (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)
  (hrepSet : ∀ (X : D) (A : Set (ℕ → Bool)) (hm : MeasurableSet A), InternallyApproximable M A →
    RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hm)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Cylinder and bit conditions under comparison
-/
include hM hinf hpair hunion hpower hsep hrepSet in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The internal sets contain exactly the old point graphs satisfying the indicated cylinder or bit test.
    Basic cylinders have internal approximations by §{sec:internal-finite-measure-bounds}.
    The bit set is the finite union of the cylinders of length $n+1$ whose last bit is $i$.
    The finite-union lemma in §{sec:internal-null-quotients} therefore supplies its internal
    approximations as well. Both external sets are measurable, so the representative identity for the
    comparison map applies. Their measures are $2^{-|s|}$ and $1/2$, respectively, so both identities
    also hold in the positive condition orders.
-/
lemma image_internalCylinderCondition (s : List Bool) :
    internalConditionEmbedding η hη hpos (internalCylinderCondition η h hcyl s) = randomCoinCylinder s := by
  apply Subtype.ext
  apply hrepSet ⟨_, (hcyl s).1⟩ (cyl s) (isOpen_cyl s).measurableSet
    (internallyApproximable_binaryCylinder hM hinf hpair hunion hpower hsep s)
  exact ⟨fun _ hx => mem_internalWordCylinder_ambient hx, cantorPointGraph_mem_internalWordCylinder M s⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Cylinder and bit conditions under comparison
-/
include hM hinf hpair hunion hpower hsep hrepSet in
lemma image_internalBitCondition (n : ℕ) (i : Bool) :
    internalConditionEmbedding η hη hpos (internalBitCondition η h hcyl n i) = randomCoinBit n i := by
  apply Subtype.ext
  apply hrepSet ⟨_, (bitFiber_domain_positive h M hcyl n i).1⟩ {x | x n = i} (measurable_bitCell n i)
    (internallyApproximable_bitCell hM hinf hpair hunion hpower hsep n i)
  refine ⟨?_, cantorPointGraph_mem_bitFiber M n i⟩
  intro g hg
  change g ∈ membershipFiber (internalCantor M) (bitLabel n i) at hg
  unfold membershipFiber at hg
  exact (ZFSet.mem_sep.mp hg).1

include hM hinf hpair hunion hpower hsep hrepSet in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    A condition of $G$ below an internal cylinder of length $n$ maps to a condition of $H$ below the
    corresponding external cylinder. Hence $H$ meets $C_n$, and the filter-union construction gives $r_H$.
    For each coordinate, its bit is characterized by
    $$r_H(n)=i\quad\longleftrightarrow\quad\MeasureClass{\mu}{\{x:x(n)=i\}}\in H.$$
    Indeed, the cylinder determined by the first $n+1$ bits of $r_H$ belongs to $H$.
    If its last bit is $i$, its class lies below the displayed bit class, which therefore belongs to $H$.
    If its last bit differs from $i$, the cylinder and bit set are disjoint, so their classes cannot both
    belong to a filter of positive conditions.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Let $G$ be a filter on $P$ meeting every internal length requirement $\InternalRandomLength{M}{n}$, and put
    $H:=\FilterTransport{\eta}{G}$. Then $H$ meets the external length tests, so it determines a binary sequence $r_H$.
-/
lemma transportedRandomFilter_length (G : Order.PFilter (InternalRandomCondition D F η))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ internalRandomLengthRequirement η h hcyl n) :
    ∀ n, ∃ p ∈ transportPFilter (internalConditionEmbedding η hη hpos) G,
      p ∈ randomLengthRequirement fairCoinProduct n := by
  intro n
  obtain ⟨p, hp, s, hs, hps⟩ := hlen n
  refine ⟨internalConditionEmbedding η hη hpos p,
    (image_mem_transportPFilter _ G p).mpr hp, s, hs, ?_⟩
  have he := (internalConditionEmbedding η hη hpos).monotone hps
  rw [image_internalCylinderCondition η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet s] at he
  exact he

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Evaluation of the internal random-real name
-/
include hM hinf hpair hunion hpower hsep hrepSet in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The image-membership equivalence and the preceding comparison lemma now give
    $$\begin{aligned}
    q(\InternalBitCell{M}{n}{i})\in G
    &\quad\longleftrightarrow\quad\MeasureClass{\mu}{\{x:x(n)=i\}}\in H\\
    &\quad\longleftrightarrow\quad r_H(n)=i.
    \end{aligned}$$
    Apply the graph-recovery corollary of §{sec:internal-null-quotients}.
-/
theorem valuation_randomRealName_eq_filterReal (G : Order.PFilter (InternalRandomCondition D F η))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ internalRandomLengthRequirement η h hcyl n) :
    valuation (internalFilterSet η G) (randomRealName M D F) =
      cantorPointGraph (randomFilterReal (transportPFilter (internalConditionEmbedding η hη hpos) G)
        (transportedRandomFilter_length η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet G hlen)) := by
  apply value_randomRealName_eq h M hcyl (internalFilterSet η G) (internalFilterSet_meets η G)
  intro n i
  change (internalBitCondition η h hcyl n i).val ∈ internalFilterSet η G ↔ _
  rw [condition_mem_internalFilterSet, ← image_mem_transportPFilter (internalConditionEmbedding η hη hpos) G,
    image_internalBitCondition η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet n i]
  exact (randomFilterReal_bit_iff _ _ n i).symm


/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: The filter real belongs to the valuation extension
-/
include hM hinf hpair hunion hpower hsep hrepSet in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The decision-table construction gives a $P$-name $\dot r\in M$.
    Its valuation belongs to $M[G]$ by the definition of that extension, and the theorem identifies
    this valuation with the graph of the filter real.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    By §{sec:internal-random-filter-valuation}, valuation gives the graph of $r_H$, which therefore belongs to $M[G]$.
    Identifying a binary sequence with its graph, we write $r_G:=r_H$ and $\dot r^G=r_G$.
-/
theorem filterReal_graph_mem_extension
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hD : D ∈ M) (hF : F ∈ M) (G : Order.PFilter (InternalRandomCondition D F η))
    (hlen : ∀ n, ∃ p ∈ G, p ∈ internalRandomLengthRequirement η h hcyl n) :
    cantorPointGraph (randomFilterReal (transportPFilter (internalConditionEmbedding η hη hpos) G)
      (transportedRandomFilter_length η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet G hlen)) ∈
        extension (positiveNullQuotient D F) M (internalFilterSet η G) := by
  apply (mem_extension _ _ _ _).mpr
  exact ⟨randomRealName M D F,
    randomRealName_mem hM hinf hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h hcyl,
    randomRealName_isName M D F,
    valuation_randomRealName_eq_filterReal η hM hinf hpair hunion hpower hsep h hcyl hη hpos hrepSet G hlen⟩

end PolishSpaceBook.CantorTreeMeasure
