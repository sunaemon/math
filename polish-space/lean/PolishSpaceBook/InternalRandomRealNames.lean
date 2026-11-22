module

public import PolishSpaceBook.InternalNullQuotients
public import PolishSpaceBook.CantorInternalMeasureFiniteValues
public import PolishSpaceBook.ForcingDecisionClosure

@[expose] public section

/-! # Entire bit-decision tables and random-real names in the ground model -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas BoundedSetPredicate BorelExpression ForcingNames
universe u

/-- A membership fiber of a family of sets, used here for graphs of binary sequences. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a family of sets and an input label, define its membership fiber by
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\MembershipFiber{Y}{a}:=\{g\in Y:a\in g\}.$$
    For binary point graphs, this gives the coordinate cells
    $$\begin{gathered}
    \InternalBitCell{M}{n}{i}:=\MembershipFiber{Y_M}{\langle n,i\rangle}
    =\{g\in Y_M:g(n)=i\},\\
    n\in\omega,\quad i\in2.
    \end{gathered}$$
    The integers in these graph pairs are represented by finite ordinals.
-/
def membershipFiber (Y a : ZFSet.{u}) : ZFSet.{u} := Y.sep (fun g => a ∈ g)

def membershipFiberPredicate : BoundedSetPredicate 3 := setComprehension 0 2 (.member 1 3)

lemma eval_membershipFiberPredicate (Y a C : ZFSet.{u}) :
    membershipFiberPredicate.eval ![Y, a, C] ↔ C = membershipFiber Y a := by
  apply eval_setComprehension_iff_eq (0 : Fin 3) 2 _ ![Y, a, C]
  · exact fun _ hx => (ZFSet.mem_sep.mp hx).1
  · intro g hg
    change g ∈ Y at hg
    change (a ∈ g) ↔ g ∈ membershipFiber Y a
    simp only [membershipFiber, ZFSet.mem_sep, hg, true_and]

def quotientFiberTable (I Y D E : ZFSet.{u}) : ZFSet.{u} :=
  functionGraph (fun a : I => relationClass D E (membershipFiber Y a.val))

lemma pair_mem_quotientFiberTable (I Y D E : ZFSet.{u}) (a : I) (p : ZFSet.{u}) :
    pair a.val p ∈ quotientFiberTable I Y D E ↔ relationClass D E (membershipFiber Y a.val) = p :=
  pair_mem_functionGraph _ a p

/-- Parameters domain of measure, ambient points, class map, input, output. -/
def quotientFiberPredicate : BoundedSetPredicate 5 :=
  .ex 0 (.conj (membershipFiberPredicate.rename ![1, 3, 5]) (.pairMember 2 5 4))

lemma eval_quotientFiberPredicate (I Y D E : ZFSet.{u})
    (hdom : ∀ a ∈ I, membershipFiber Y a ∈ D) (a : I) (p : ZFSet.{u}) :
    quotientFiberPredicate.eval ![D, Y, relationClassMap D E, a.val, p] ↔
      p = relationClass D E (membershipFiber Y a.val) := by
  simp only [quotientFiberPredicate, eval, eval_rename, Fin.snoc]
  change (∃ C ∈ D, membershipFiberPredicate.eval ![Y, a.val, C] ∧ pair C p ∈ relationClassMap D E) ↔ _
  simp only [eval_membershipFiberPredicate]
  constructor
  · rintro ⟨C, hC, rfl, hp⟩
    exact ((pair_mem_relationClassMap D E ⟨_, hC⟩ p).mp hp).symm
  · intro hp
    exact ⟨_, hdom a.val a.property, rfl,
      (pair_mem_relationClassMap D E ⟨_, hdom a.val a.property⟩ p).mpr hp.symm⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hsep in
lemma membershipFiber_mem (Y a : M) : membershipFiber Y.val a.val ∈ M :=
  (BoundedSetPredicate.member (0 : Fin 2) 1).separation_mem hM (hsep _) ![a] Y.property

include hM hpair hsep hrep in
lemma quotientFiberTable_mem (I Y D E : M) (hdom : ∀ a ∈ I.val, membershipFiber Y.val a ∈ D.val) :
    quotientFiberTable I.val Y.val D.val E.val ∈ M := by
  let q : M := ⟨_, relationClassMap_mem hM hpair hsep hrep D E⟩
  let f (a : I.val) : M := ⟨_, relationClass_mem hM hsep D E
    ⟨_, membershipFiber_mem hM hsep Y ⟨a.val, hM.mem_trans a.property I.property⟩⟩⟩
  apply replacement_graph_mem hM hpair quotientFiberPredicate.compile (hrep _) ![D, Y, q] I.property f
  intro a p
  rw [quotientFiberPredicate.realize_compile hM]
  have he : Subtype.val ∘ Fin.snoc (Fin.snoc ![D, Y, q] ⟨a.val, hM.mem_trans a.property I.property⟩) p =
      ![D.val, Y.val, relationClassMap D.val E.val, a.val, p.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_quotientFiberPredicate I.val Y.val D.val E.val hdom]
  change p.val = (f a).val ↔ p = f a
  exact Subtype.ext_iff.symm

def bitLabels : ZFSet.{u} := prod Ordinal.omega0.toZFSet (natOrdinal 2)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\MembershipFiber{Y}{a}:=\{g\in Y:a\in g\}.$$
    For binary point graphs, this gives the coordinate cells
    $$\begin{gathered}
    \InternalBitCell{M}{n}{i}:=\MembershipFiber{Y_M}{\langle n,i\rangle}
    =\{g\in Y_M:g(n)=i\},\\
    n\in\omega,\quad i\in2.
    \end{gathered}$$
    The integers in these graph pairs are represented by finite ordinals.
-/
def bitLabel (n : ℕ) (i : Bool) : ZFSet.{u} := pair (natOrdinal n) (natOrdinal i.toNat)

lemma bitLabel_mem (n : ℕ) (i : Bool) : bitLabel n i ∈ (bitLabels : ZFSet.{u}) :=
  ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨n, rfl⟩,
    mem_natOrdinal.mpr ⟨i.toNat, by cases i <;> decide, rfl⟩⟩

lemma mem_bitLabels (a : ZFSet.{u}) : a ∈ bitLabels ↔ ∃ n i, bitLabel n i = a := by
  constructor
  · intro ha
    obtain ⟨n, hn, i, hi, rfl⟩ := ZFSet.mem_prod.mp ha
    obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp hn
    obtain ⟨j, hj, rfl⟩ := mem_natOrdinal.mp hi
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact ⟨k, false, rfl⟩
    · exact ⟨k, true, rfl⟩
  · rintro ⟨n, i, rfl⟩; exact bitLabel_mem n i

include hM hinf hpair hunion hpower hsep in
lemma bitLabels_mem : (bitLabels : ZFSet.{u}) ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  exact prod_mem_of_separation hM hpair hunion hpower (hsep _) hΩ
    (hM.mem_trans (mem_omegaOrdinal.mpr ⟨2, rfl⟩) hΩ)

lemma bitLabel_mem_cantorPointGraph (n : ℕ) (i : Bool) (x : ℕ → Bool) :
    bitLabel n i ∈ (cantorPointGraph x : ZFSet.{u}) ↔ x n = i := by
  change pair (natOrdinal n) (natOrdinal i.toNat) ∈ pointGraph (cantorInclusion x) ↔ _
  rw [pair_mem_pointGraph]
  change (x n).toNat = i.toNat ↔ x n = i
  cases i <;> cases x n <;> decide

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $$\MembershipFiber{Y}{a}:=\{g\in Y:a\in g\}.$$
    For binary point graphs, this gives the coordinate cells
    $$\begin{gathered}
    \InternalBitCell{M}{n}{i}:=\MembershipFiber{Y_M}{\langle n,i\rangle}
    =\{g\in Y_M:g(n)=i\},\\
    n\in\omega,\quad i\in2.
    \end{gathered}$$
    The integers in these graph pairs are represented by finite ordinals.
-/
lemma cantorPointGraph_mem_bitFiber (M : ZFSet.{u}) (n : ℕ) (i : Bool) (x : ℕ → Bool) :
    cantorPointGraph x ∈ membershipFiber (internalCantor M) (bitLabel n i) ↔
      cantorPointGraph x ∈ M ∧ x n = i := by
  simp only [membershipFiber, ZFSet.mem_sep, cantorPointGraph_mem_internalCantor, bitLabel_mem_cantorPointGraph]

/-- Words whose nth coordinate has the prescribed bit; only level n+1 is used. -/
def bitWords (n : ℕ) (i : Bool) : Set (List Bool) := {s | s[n]?.getD false = i}

lemma bitFiber_eq_level (M : ZFSet.{u}) (n : ℕ) (i : Bool) :
    membershipFiber (internalCantor M) (bitLabel n i) = internalLevelSet M (bitWords n i) (n + 1) := by
  ext g
  have left : g ∈ membershipFiber (internalCantor M) (bitLabel n i) → g ∈ internalCantor M :=
    fun hg => (ZFSet.mem_sep.mp hg).1
  have right : g ∈ internalLevelSet M (bitWords n i) (n + 1) → g ∈ internalCantor M :=
    by
      intro hg
      unfold internalLevelSet internalCylinderUnion at hg
      exact (ZFSet.mem_sep.mp hg).1
  by_cases hg : g ∈ internalCantor M
  · obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp hg
    rw [cantorPointGraph_mem_bitFiber, cantorPointGraph_mem_internalLevelSet, mem_levelSet]
    simp only [bitWords, Set.mem_ofPred_eq, seqPrefix, List.getElem?_ofFn,
      dite_eq_left (Nat.lt_succ_self n), Option.getD_some]
  · exact ⟨fun h => (hg (left h)).elim, fun h => (hg (right h)).elim⟩

lemma levelSet_bitWords (n : ℕ) (i : Bool) : levelSet (bitWords n i) (n + 1) = {x | x n = i} := by
  ext x
  rw [mem_levelSet]
  simp only [bitWords, Set.mem_ofPred_eq, seqPrefix, List.getElem?_ofFn,
    dite_eq_left (Nat.lt_succ_self n), Option.getD_some]

lemma measure_bitCell (n : ℕ) (i : Bool) : fairCoinProduct {x | x n = i} = (1 / 2 : ENNReal) := by
  have he : {x : ℕ → Bool | x n = i} = Set.pi (↑({n} : Finset ℕ)) (fun _ => {i}) := by
    ext x; simp
  rw [he, fairCoinProduct, MeasureTheory.Measure.infinitePi_pi _ (by measurability)]
  simp [fairCoin_singleton]

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal coordinate cells
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The coordinate cell is the disjoint union of the internal cylinders of length $n+1$ whose last bit
    is $i$. Thus finite-union closure puts it in the measure domain. The finite-level value theorem
    identifies its value with the ordinary fair-coin measure of $\{x:x(n)=i\}$: both are the same finite
    sum of normalized cylinder values. The one-coordinate product calculation gives $1/2$.
    The positivity criterion in §{sec:internal-null-quotients} then puts the class in the condition set.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Each condition has internal measure $\tfrac12$.
-/
lemma bitFiber_domain_value {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (M : ZFSet.{u})
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (n : ℕ) (i : Bool) : membershipFiber (internalCantor M) (bitLabel n i) ∈ D ∧
      h.value (membershipFiber (internalCantor M) (bitLabel n i)) = 1 / 2 := by
  rw [bitFiber_eq_level]
  have hdom := h.listUnion_mem (levelCylinderList M (bitWords n i) (n + 1))
    ((forall_levelCylinderList _ _ _ _).mpr (fun s _ => (hcyl (List.ofFn s)).1))
  rw [listUnion_levelCylinderList] at hdom
  refine ⟨hdom, ?_⟩
  rw [finiteMeasure_value_level h M (bitWords n i) (n + 1)
    (fun s _ => by simpa only [List.length_ofFn] using hcyl (List.ofFn s)),
    levelWeight_eq_measureReal, levelSet_bitWords, MeasureTheory.Measure.real, measure_bitCell]
  norm_num

lemma bitFiber_domain_positive {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (M : ZFSet.{u})
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (n : ℕ) (i : Bool) : membershipFiber (internalCantor M) (bitLabel n i) ∈ D ∧
      0 < h.value (membershipFiber (internalCantor M) (bitLabel n i)) := by
  obtain ⟨hdom, hv⟩ := bitFiber_domain_value h M hcyl n i
  exact ⟨hdom, by rw [hv]; norm_num⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Set $I:=\omega\times2$ and form the entire decision table and its name:
    $$\begin{gathered}
    T:=\{\langle a,q(\MembershipFiber{Y_M}{a})\rangle:a\in I\},\\
    \dot r:=\ForcingDecisionName{P}{I}{T}.
    \end{gathered}$$
-/
def bitDecisionTable (M D F : ZFSet.{u}) : ZFSet.{u} :=
  quotientFiberTable bitLabels (internalCantor M) D (nullRelation D F)

lemma bitDecisionTable_subset {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (M : ZFSet.{u})
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F) :
    bitDecisionTable M D F ⊆ prod bitLabels (positiveNullQuotient D F) := by
  intro z hz
  obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
  obtain ⟨n, i, he⟩ := (mem_bitLabels a.val).mp a.property
  have hp := bitFiber_domain_positive h M hcyl n i
  apply ZFSet.pair_mem_prod.mpr
  refine ⟨a.property, ?_⟩
  change relationClass D (nullRelation D F) (membershipFiber (internalCantor M) a.val) ∈ _
  rw [← he]
  exact (class_mem_positiveNullQuotient_iff h ⟨_, hp.1⟩).mpr hp.2

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Set $I:=\omega\times2$ and form the entire decision table and its name:
    $$\begin{gathered}
    T:=\{\langle a,q(\MembershipFiber{Y_M}{a})\rangle:a\in I\},\\
    \dot r:=\ForcingDecisionName{P}{I}{T}.
    \end{gathered}$$
-/
def randomRealName (M D F : ZFSet.{u}) : ZFSet.{u} :=
  relationDecisionName (positiveNullQuotient D F) bitLabels (bitDecisionTable M D F)

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal random-real decision tables
-/
include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The label set and internal Cantor space belong to the model. For each label, bounded Separation
    constructs its membership fiber. A candidate output class is specified by a bounded existential
    quantifier over the measure domain: the intermediate set must be that membership fiber, and its
    pair with the output must belong to the already constructed quotient map. The shared subset
    predicate and graph lookup express these tests. The coordinate-cell lemma supplies every intermediate
    set in the measure domain, and the quotient construction supplies the unique output in the model.
    Bounded-predicate interpretation and the shared definable-graph construction collect the whole table
    by Replacement. This proves internality of the table, rather than only internality of each entry.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The coordinate-cell lemma also puts every table value in the positive condition set. Apply
    §{sec:forcing-names-valuation} to the entire internal relation to obtain the name and its internality.
    Its explicit form follows by writing each label as a coordinate-bit pair. The general evaluation
    formula for decision names gives the displayed bit test, since the table has exactly one value at
    each label. No genericity assumption is needed for this evaluation formula.
-/
theorem bitDecisionTable_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D.val ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F.val) :
    bitDecisionTable M D.val F.val ∈ M := by
  apply quotientFiberTable_mem hM hpair hsep hrep
    ⟨_, bitLabels_mem hM hinf hpair hunion hpower hsep⟩
    ⟨_, internalCantor_mem hM hinf hpair hunion hpower hsep⟩ D
    ⟨_, nullRelation_mem hM hpair hunion hpower hsep D F h⟩
  intro a ha
  obtain ⟨n, i, rfl⟩ := (mem_bitLabels a).mp ha
  exact (bitFiber_domain_positive h M hcyl n i).1

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal random-real decision tables
-/
include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The construction in §{sec:internal-null-quotients} places the entire decision table and its name in $M$.
-/
theorem randomRealName_mem (D F : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D.val ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F.val) :
    randomRealName M D.val F.val ∈ M :=
  relationDecisionName_mem hM hinf hpair hunion hpower hsep hrep
    ⟨_, positiveNullQuotient_mem hM hpair hunion hpower hsep hrep D F h⟩
    ⟨_, bitLabels_mem hM hinf hpair hunion hpower hsep⟩
    ⟨_, bitDecisionTable_mem hM hinf hpair hunion hpower hsep hrep D F h hcyl⟩

lemma randomRealName_isName (M D F : ZFSet.{u}) : IsName (positiveNullQuotient D F) (randomRealName M D F) :=
  relationDecisionName_isName _ _ _

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal random-real decision tables
-/
theorem bit_mem_value_randomRealName {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (M : ZFSet.{u})
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ positiveNullQuotient D F) (n : ℕ) (i : Bool) :
    bitLabel n i ∈ valuation G (randomRealName M D F) ↔
      relationClass D (nullRelation D F) (membershipFiber (internalCantor M) (bitLabel n i)) ∈ G := by
  have hp := bitFiber_domain_positive h M hcyl n i
  have hpos := (class_mem_positiveNullQuotient_iff h ⟨_, hp.1⟩).mpr hp.2
  rw [randomRealName, mem_value_relationDecisionName _ _ _ G hG]
  simp only [bitLabel_mem, true_and]
  constructor
  · rintro ⟨p, _, hpG, htable⟩
    exact ((pair_mem_quotientFiberTable _ _ _ _ ⟨_, bitLabel_mem n i⟩ p).mp htable).symm ▸ hpG
  · intro hc
    exact ⟨_, hpos, hc, (pair_mem_quotientFiberTable _ _ _ _ ⟨_, bitLabel_mem n i⟩ _).mpr rfl⟩


/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal random-real decision tables
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The canonical name records the internal bit decisions:
    $$\dot r := \{\langle \check{\langle n,i\rangle},q(\InternalBitCell{M}{n}{i})\rangle :
     n\in\omega,\;i\in\{0,1\}\}.$$
-/
theorem mem_randomRealName {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (M : ZFSet.{u})
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F) (z : ZFSet.{u}) :
    z ∈ randomRealName M D F ↔ ∃ n i, z = pair (check (positiveNullQuotient D F) (bitLabel n i))
      (relationClass D (nullRelation D F) (membershipFiber (internalCantor M) (bitLabel n i))) := by
  rw [randomRealName, mem_relationDecisionName]
  constructor
  · rintro ⟨a, ha, p, _, ht, hz⟩
    obtain ⟨n, i, rfl⟩ := (mem_bitLabels a).mp ha
    have he := (pair_mem_quotientFiberTable _ _ _ _ ⟨_, bitLabel_mem n i⟩ p).mp ht
    exact ⟨n, i, he.symm ▸ hz⟩
  · rintro ⟨n, i, rfl⟩
    have hp := bitFiber_domain_positive h M hcyl n i
    exact ⟨_, bitLabel_mem n i, _, (class_mem_positiveNullQuotient_iff h ⟨_, hp.1⟩).mpr hp.2,
      (pair_mem_quotientFiberTable _ _ _ _ ⟨_, bitLabel_mem n i⟩ _).mpr rfl, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Recovering the binary graph from its decisions
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Every element of the valuation is a coordinate-bit label. For such a label, the theorem and the
    assumed bit test identify membership in the valuation with membership in the binary graph.
    Extensionality gives equality of the whole sets.
-/
theorem value_randomRealName_eq {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F) (M : ZFSet.{u})
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ positiveNullQuotient D F) (x : ℕ → Bool)
    (hbits : ∀ n i, relationClass D (nullRelation D F)
      (membershipFiber (internalCantor M) (bitLabel n i)) ∈ G ↔ x n = i) :
    valuation G (randomRealName M D F) = cantorPointGraph x := by
  ext a
  constructor
  · intro ha
    have hl := ((mem_value_relationDecisionName _ _ _ G hG a).mp ha).1
    obtain ⟨n, i, rfl⟩ := (mem_bitLabels a).mp hl
    exact (bitLabel_mem_cantorPointGraph n i x).mpr
      ((hbits n i).mp ((bit_mem_value_randomRealName h M hcyl G hG n i).mp ha))
  · intro ha
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp ha
    exact (bit_mem_value_randomRealName h M hcyl G hG n (x n)).mpr ((hbits n (x n)).mpr rfl)

end PolishSpaceBook.CantorTreeMeasure
