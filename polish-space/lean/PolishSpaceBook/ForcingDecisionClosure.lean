module

public import PolishSpaceBook.ForcingCheckClosure
public import PolishSpaceBook.SetTheoryFiniteCardinality

@[expose] public section

/-! # Ground-model closure for names assembled from entire decision relations -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames BoundedSetPredicate
universe u

/-- The whole graph, rather than just the individual check names. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Write
    $$\CheckNameGraph{P}{A}:=\{\langle a,\check a\rangle:a\in A\}.$$
    The parameter $P$ specifies the all-conditions convention for every check name.
-/
def checkGraph (P A : ZFSet.{u}) : ZFSet.{u} := functionGraph (fun a : A => check P a.val)

lemma pair_mem_checkGraph (P A : ZFSet.{u}) (a : A) (σ : ZFSet.{u}) :
    pair a.val σ ∈ checkGraph P A ↔ check P a.val = σ := pair_mem_functionGraph _ a σ

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
include hM hinf hpair hunion hpower hsep hrep

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Internal check-name graphs
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Apply the internal recursive-value formula from §{sec:internal-model-closure} to the check-name
    step rule. For $a,\sigma\in M$, it holds precisely when $\sigma=\check a$. The check-name closure lemma
    supplies this unique value in $M$. The shared definable-graph construction now applies Replacement on
    $A$ and collects the pairs $\langle a,\check a\rangle$ into one graph in $M$.
-/
theorem checkGraph_mem (P A : M) : checkGraph P.val A.val ∈ M := by
  let f (a : A.val) : M := ⟨check P.val a.val,
    check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep P ⟨a.val, hM.mem_trans a.property A.property⟩⟩
  apply replacement_graph_mem hM hpair (recursiveValueFormula checkStepFormula) (hrep _) ![P] A.property f
  intro a b
  rw [realize_recursiveValueFormula_external hM hinf hpair hunion hpower hsep hrep checkStepFormula ![P]
    (checkStep P.val) (fun a g b => realize_checkStepFormula hM hpair hunion (hsep _) P a g b)
    (fun a g => checkStep_mem hM hpair hunion hpower hsep P a g)
    (check P.val) (check_step_equation P.val)]
  change b.val = (f a).val ↔ b = f a
  exact Subtype.ext_iff.symm

omit hM hinf hpair hunion hpower hsep hrep in
/-- A relation can attach several conditions to the same label. -/
def relationDecisionName (P A E : ZFSet.{u}) : ZFSet.{u} :=
  decisionName P (fun ap : {ap : A × P // pair ap.1.val ap.2.val ∈ E} => ap.val.1.val)
    (fun ap => ap.val.2.val)

omit hM hinf hpair hunion hpower hsep hrep in
lemma mem_relationDecisionName (P A E z : ZFSet.{u}) :
    z ∈ relationDecisionName P A E ↔ ∃ a ∈ A, ∃ p ∈ P, pair a p ∈ E ∧ z = pair (check P a) p := by
  rw [relationDecisionName, decisionName, ZFSet.mem_range]
  constructor
  · rintro ⟨ap, rfl⟩
    exact ⟨ap.val.1.val, ap.val.1.property, ap.val.2.val, ap.val.2.property, ap.property, rfl⟩
  · rintro ⟨a, ha, p, hp, he, rfl⟩
    exact ⟨⟨⟨⟨a, ha⟩, ⟨p, hp⟩⟩, he⟩, rfl⟩

omit hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Every first coordinate is a check name and every second
    coordinate belongs to $P$, which proves the name condition.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Decision names from internal relations
-/
lemma relationDecisionName_isName (P A E : ZFSet.{u}) : IsName P (relationDecisionName P A E) :=
  decisionName_isName P _ _ (fun ap => ap.val.2.property)

omit hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Substituting $\check a^G=a$ into the
    valuation equation gives the stated value.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Decision names from internal relations
-/
lemma mem_value_relationDecisionName (P A E : ZFSet.{u}) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) (x : ZFSet.{u}) :
    x ∈ valuation G (relationDecisionName P A E) ↔ x ∈ A ∧ ∃ p ∈ P, p ∈ G ∧ pair x p ∈ E := by
  rw [relationDecisionName, mem_valuation_decisionName P G hG]
  constructor
  · rintro ⟨ap, hg, rfl⟩
    exact ⟨ap.val.1.property, ap.val.2.val, ap.val.2.property, hg, ap.property⟩
  · rintro ⟨hx, p, hp, hg, he⟩
    exact ⟨⟨⟨⟨x, hx⟩, ⟨p, hp⟩⟩, he⟩, hg, rfl⟩

/-- Parameters A, P, decision relation, check graph, check range, candidate output pair. -/
def decisionPairPredicate : BoundedSetPredicate 6 :=
  .ex 0 (.ex 1 (.ex 4 (.conj (.pairMember 3 6 8)
    (.conj (.pairMember 2 6 7) (.orderedPair 5 8 7)))))

omit hM hinf hpair hunion hpower hsep hrep in
lemma eval_decisionPairPredicate (P A E z : ZFSet.{u}) :
    decisionPairPredicate.eval ![A, P, E, checkGraph P A, graphRange (checkGraph P A), z] ↔
      z ∈ relationDecisionName P A E := by
  change (∃ a ∈ A, ∃ p ∈ P, ∃ σ ∈ graphRange (checkGraph P A),
    pair a σ ∈ checkGraph P A ∧ pair a p ∈ E ∧ z = pair σ p) ↔ _
  rw [mem_relationDecisionName]
  constructor
  · rintro ⟨a, ha, p, hp, σ, _, hc, he, hz⟩
    rw [← (pair_mem_checkGraph P A ⟨a, ha⟩ σ).mp hc] at hz
    exact ⟨a, ha, p, hp, he, hz⟩
  · rintro ⟨a, ha, p, hp, he, hz⟩
    have hc := (pair_mem_checkGraph P A ⟨a, ha⟩ (check P a)).mpr rfl
    exact ⟨a, ha, p, hp, check P a, mem_graphRange.mpr ⟨a, hc⟩, hc, he, hz⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: theorem
  title: Decision names from internal relations
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Put $H=\CheckNameGraph{P}{A}$ and $R=\GraphRange{H}$. Both sets belong to $M$, as does $R\times P$.
    For a candidate pair $z$, use the bounded condition
    $$\begin{aligned}
    &\exists a\in A\;\exists p\in P\;\exists\sigma\in R\\
    &\qquad(\langle a,\sigma\rangle\in H\land\langle a,p\rangle\in E
    \land z=\langle\sigma,p\rangle).
    \end{aligned}$$
    The common bounded interpretation theorem applies directly. Separation on $R\times P$ therefore
    constructs exactly the displayed name in $M$.
-/
theorem relationDecisionName_mem (P A E : M) : relationDecisionName P.val A.val E.val ∈ M := by
  let H : M := ⟨_, checkGraph_mem hM hinf hpair hunion hpower hsep hrep P A⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) H.property⟩
  apply decisionPairPredicate.subset_mem hM (hsep _) ![A, P, E, H, R]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) R.property P.property)
  · intro z hz
    obtain ⟨a, ha, p, hp, _, rfl⟩ := (mem_relationDecisionName _ _ _ _).mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨mem_graphRange.mpr ⟨a, (pair_mem_checkGraph _ _ ⟨a, ha⟩ _).mpr rfl⟩, hp⟩
  · intro z _
    have he : Fin.snoc (Subtype.val ∘ ![A, P, E, H, R]) z =
        ![A.val, P.val, E.val, checkGraph P.val A.val, graphRange (checkGraph P.val A.val), z] := by
      funext i; fin_cases i <;> rfl
    rw [he, eval_decisionPairPredicate]

/-- Diagonal decision relation for the generic filter. -/
def diagonalDecisions (P : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod P P).sep (fun z => ∃ p ∈ P, z = pair p p)

omit hM hinf hpair hunion hpower hsep hrep in
lemma pair_mem_diagonalDecisions (P a p : ZFSet.{u}) :
    pair a p ∈ diagonalDecisions P ↔ a = p ∧ p ∈ P := by
  simp only [diagonalDecisions, ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.pair_inj]
  constructor
  · rintro ⟨_, q, hq, rfl, rfl⟩; exact ⟨rfl, hq⟩
  · rintro ⟨rfl, hp⟩; exact ⟨⟨hp, hp⟩, a, hp, rfl, rfl⟩

omit hinf hrep in
lemma diagonalDecisions_mem (P : M) : diagonalDecisions P.val ∈ M := by
  let p : BoundedSetPredicate 2 := .ex 0 (.orderedPair 1 2 2)
  exact p.separation_mem hM (hsep _) ![P]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) P.property P.property)

omit hM hinf hpair hunion hpower hsep hrep in
lemma relationDecisionName_diagonal (P : ZFSet.{u}) :
    relationDecisionName P P (diagonalDecisions P) = genericName P := by
  ext z
  simp only [mem_relationDecisionName, pair_mem_diagonalDecisions, genericName, decisionName, ZFSet.mem_range]
  constructor
  · rintro ⟨a, ha, p, _, ⟨rfl, _⟩, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.property, p.val, p.property, ⟨rfl, p.property⟩, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Generic-filter and union names in the ground model
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For $\dot G$, take $A=P$ and the diagonal relation
    $$E_0=\{\langle p,p\rangle:p\in P\}.$$
    It belongs to $M$ by bounded Separation on $P\times P$.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For Cohen conditions represented by finite function graphs, $\dot u$ is exactly $\dot c$.
-/
theorem genericName_mem_ground (P : M) : genericName P.val ∈ M := by
  rw [← relationDecisionName_diagonal]
  exact relationDecisionName_mem hM hinf hpair hunion hpower hsep hrep P P
    ⟨_, diagonalDecisions_mem hM hpair hunion hpower hsep P⟩

/-- A label is an element of its attached condition. -/
def membershipDecisions (P : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod (sUnion P) P).sep (fun z => ∃ a ∈ sUnion P, ∃ p ∈ P, a ∈ p ∧ z = pair a p)

omit hM hinf hpair hunion hpower hsep hrep in
lemma pair_mem_membershipDecisions (P a p : ZFSet.{u}) :
    pair a p ∈ membershipDecisions P ↔ p ∈ P ∧ a ∈ p := by
  simp only [membershipDecisions, ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.pair_inj]
  constructor
  · rintro ⟨_, a', _, p', hp, ha, rfl, rfl⟩; exact ⟨hp, ha⟩
  · rintro ⟨hp, ha⟩
    have hu := ZFSet.mem_sUnion.mpr ⟨p, hp, ha⟩
    exact ⟨⟨hu, hp⟩, a, hu, p, hp, ha, rfl, rfl⟩

omit hinf hrep in
lemma membershipDecisions_mem (P : M) : membershipDecisions P.val ∈ M := by
  let A : M := ⟨_, union_mem hM hunion P.property⟩
  let p : BoundedSetPredicate 3 := .ex 0 (.ex 1 (.conj (.member 3 4) (.orderedPair 2 3 4)))
  exact p.separation_mem hM (hsep _) ![A, P]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) A.property P.property)

omit hM hinf hpair hunion hpower hsep hrep in
lemma relationDecisionName_membership (P : ZFSet.{u}) :
    relationDecisionName P (sUnion P) (membershipDecisions P) = unionName P := by
  ext z
  simp only [mem_relationDecisionName, pair_mem_membershipDecisions, unionName, decisionName, ZFSet.mem_range]
  constructor
  · rintro ⟨a, _, p, hp, ⟨_, ha⟩, rfl⟩
    exact ⟨⟨⟨p, hp⟩, ⟨a, ha⟩⟩, rfl⟩
  · rintro ⟨⟨p, a⟩, rfl⟩
    exact ⟨a.val, ZFSet.mem_sUnion.mpr ⟨p.val, p.property, a.property⟩,
      p.val, p.property, ⟨p.property, a.property⟩, rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Generic-filter and union names in the ground model
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    For $\dot u$, take $A=\bigcup P\in M$ and the relation
    $$E_1=\{\langle a,p\rangle\in A\times P:a\in p\}.$$
    This relation also belongs to $M$ by bounded Separation.
-/
theorem unionName_mem_ground (P : M) : unionName P.val ∈ M := by
  rw [← relationDecisionName_membership]
  exact relationDecisionName_mem hM hinf hpair hunion hpower hsep hrep P
    ⟨_, union_mem hM hunion P.property⟩
    ⟨_, membershipDecisions_mem hM hpair hunion hpower hsep P⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Generic-filter and union names in the ground model
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Apply the theorem to each relation, and use
    the previously proved valuation formulas. Membership in $M[G]$ follows from the definition of the
    extension as the values of names in $M$. No genericity assumption is needed for these two membership
    claims.
-/
theorem genericFilter_mem_extension (P : M) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P.val) :
    P.val.sep (fun p => p ∈ G) ∈ extension P.val M G :=
  (mem_extension _ _ _ _).mpr ⟨genericName P.val,
    genericName_mem_ground hM hinf hpair hunion hpower hsep hrep P,
    genericName_isName P.val, valuation_genericName P.val G hG⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: corollary
  title: Generic-filter and union names in the ground model
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Apply the theorem to each relation, and use
    the previously proved valuation formulas. Membership in $M[G]$ follows from the definition of the
    extension as the values of names in $M$. No genericity assumption is needed for these two membership
    claims.
-/
theorem unionFilter_mem_extension (P : M) (G : Set ZFSet.{u}) (hG : ∃ p ∈ G, p ∈ P.val) :
    sUnion (P.val.sep (fun p => p ∈ G)) ∈ extension P.val M G :=
  (mem_extension _ _ _ _).mpr ⟨unionName P.val,
    unionName_mem_ground hM hinf hpair hunion hpower hsep hrep P,
    unionName_isName P.val, valuation_unionName P.val G hG⟩

end PolishSpaceBook.SetTheoryModels
