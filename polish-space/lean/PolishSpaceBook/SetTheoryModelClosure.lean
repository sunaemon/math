module

public import PolishSpaceBook.SetTheoryModelAxioms

@[expose] public section

/-! # Elementary closure and inherited axioms of transitive models -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames
universe u
variable {M : ZFSet.{u}}

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The internal Infinity axiom supplies an element $e\in M$ with no member in $M$.
    Every actual member of $e$ would lie in $M$ by transitivity, so $e=\emptyset$.
-/
lemma empty_mem (hM : M.IsTransitive) (h : M ⊨ emptySentence) : (∅ : ZFSet.{u}) ∈ M := by
  obtain ⟨e, he⟩ := (models_empty_iff M).mp h
  have heq : e.val = ∅ := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact False.elim (he ⟨z, hM.mem_trans hz e.property⟩ hz)
    · simp
  exact heq ▸ e.property

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Elementary closure of a transitive model
-/
lemma empty_mem_of_infinity (hM : M.IsTransitive) (h : M ⊨ infinitySentence) :
    (∅ : ZFSet.{u}) ∈ M := empty_mem hM (models_empty_of_infinity h)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For Pairing, the internal witness $p\in M$ satisfies
    $$z\in p\quad\Longleftrightarrow\quad z=a\lor z=b\qquad(z\in M).$$
    Every element of $p$ lies in $M$, and both $a$ and $b$ lie in $M$.
    Thus this equivalence also holds for arbitrary $z$, and external Extensionality gives $p=\{a,b\}$.
    Taking $b=a$ gives the singleton, and repeating Pairing gives the Kuratowski pair
    $\langle a,b\rangle=\{\{a\},\{a,b\}\}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Elementary closure of a transitive model
-/
lemma unorderedPair_mem (hM : M.IsTransitive) (h : M ⊨ pairingSentence)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ({a, b} : ZFSet.{u}) ∈ M := by
  obtain ⟨p, hp⟩ := (models_pairing_iff M).mp h ⟨a, ha⟩ ⟨b, hb⟩
  have heq : p.val = {a, b} := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_pair]
    constructor
    · intro hz
      rcases (hp ⟨z, hM.mem_trans hz p.property⟩).mp hz with he | he
      · exact Or.inl (congrArg Subtype.val he)
      · exact Or.inr (congrArg Subtype.val he)
    · rintro (hza | hzb)
      · subst z
        exact (hp ⟨a, ha⟩).mpr (Or.inl rfl)
      · subst z
        exact (hp ⟨b, hb⟩).mpr (Or.inr rfl)
  exact heq ▸ p.property

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Elementary closure of a transitive model
-/
lemma singleton_mem (hM : M.IsTransitive) (h : M ⊨ pairingSentence)
    {a : ZFSet.{u}} (ha : a ∈ M) : ({a} : ZFSet.{u}) ∈ M := by
  simpa only [ZFSet.pair_eq_singleton] using unorderedPair_mem hM h ha ha

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Elementary closure of a transitive model
-/
lemma orderedPair_mem (hM : M.IsTransitive) (h : M ⊨ pairingSentence)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ZFSet.pair a b ∈ M :=
  unorderedPair_mem hM h (singleton_mem hM h ha) (unorderedPair_mem hM h ha hb)

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For Union, let $u\in M$ be the internal union of $x\in M$.
    If $z\in u$, transitivity puts $z$ in $M$, so the internal axiom supplies $y\in M$ with $z\in y\in x$.
    Conversely, if $z\in y\in x$, transitivity applied twice puts $y$ and $z$ in $M$,
    and the internal axiom gives $z\in u$. Hence $u=\bigcup x$.
    Apply this to $\{a,b\}$ to obtain $a\cup b$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Elementary closure of a transitive model
-/
lemma union_mem (hM : M.IsTransitive) (h : M ⊨ unionSentence)
    {x : ZFSet.{u}} (hx : x ∈ M) : ZFSet.sUnion x ∈ M := by
  obtain ⟨v, hv⟩ := (models_union_iff M).mp h ⟨x, hx⟩
  have heq : v.val = ZFSet.sUnion x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · intro hz
      obtain ⟨y, hzy, hyx⟩ := (hv ⟨z, hM.mem_trans hz v.property⟩).mp hz
      exact ⟨y.val, hyx, hzy⟩
    · rintro ⟨y, hyx, hzy⟩
      have hyM := hM.mem_trans hyx hx
      exact (hv ⟨z, hM.mem_trans hzy hyM⟩).mpr ⟨⟨y, hyM⟩, hzy, hyx⟩
  exact heq ▸ v.property

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Elementary closure of a transitive model
-/
lemma binaryUnion_mem (hM : M.IsTransitive) (hp : M ⊨ pairingSentence) (hu : M ⊨ unionSentence)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : a ∪ b ∈ M := by
  have h := union_mem hM hu (unorderedPair_mem hM hp ha hb)
  have heq : ZFSet.sUnion ({a, b} : ZFSet.{u}) = a ∪ b := by
    ext z
    simp only [ZFSet.mem_sUnion, ZFSet.mem_pair, ZFSet.mem_union]
    aesop
  exact heq ▸ h

/-- Internal Power Set collects just the subsets that belong to the model. -/
def internalPowerSet (M x : ZFSet.{u}) : ZFSet.{u} := M.sep (fun z => z ⊆ x)

lemma subset_iff_internal (hM : M.IsTransitive) {z x : ZFSet.{u}} (hz : z ∈ M) :
    z ⊆ x ↔ ∀ w : M, w.val ∈ z → w.val ∈ x := by
  constructor
  · intro h w hw
    exact h hw
  · intro h w hw
    exact h ⟨w, hM.mem_trans hw hz⟩ hw

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Elementary closure of a transitive model
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Finally, let $p\in M$ be the internal power set of $x\in M$.
    For $z\in M$, every member of $z$ belongs to $M$, so
    $$M\models z\IncludedIn x\quad\Longleftrightarrow\quad z\IncludedIn x.$$
    The internal Power Set axiom therefore says that $z\in p$ exactly when $z\IncludedIn x$, for $z\in M$.
    Since every member of $p$ lies in $M$, this identifies $p$ with $\PowerSet{x}\cap M$.
    It makes no assertion that an arbitrary external subset of $x$ belongs to $M$.
-/
lemma internalPowerSet_mem (hM : M.IsTransitive) (h : M ⊨ powerSentence)
    {x : ZFSet.{u}} (hx : x ∈ M) : internalPowerSet M x ∈ M := by
  obtain ⟨p, hp⟩ := (models_power_iff M).mp h ⟨x, hx⟩
  have heq : p.val = internalPowerSet M x := by
    apply ZFSet.ext
    intro z
    rw [internalPowerSet, ZFSet.mem_sep]
    constructor
    · intro hz
      have hzM := hM.mem_trans hz p.property
      exact ⟨hzM, (subset_iff_internal hM hzM).mpr ((hp ⟨z, hzM⟩).mp hz)⟩
    · rintro ⟨hzM, hzx⟩
      exact (hp ⟨z, hzM⟩).mpr ((subset_iff_internal hM hzM).mp hzx)
  exact heq ▸ p.property

/-- Extensionality is inherited because every element of either set stays in M. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Let $N$ be transitive. If $x,y\in N$ have the same members in $N$, all their actual members lie in $N$,
    so they have the same members externally. External Extensionality gives $x=y$.
-/
theorem models_extensionality (hM : M.IsTransitive) : M ⊨ extensionalitySentence := by
  apply (models_extensionality_iff M).mpr
  intro x y h
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (h ⟨z, hM.mem_trans hz x.property⟩).mp hz
  · intro hz
    exact (h ⟨z, hM.mem_trans hz y.property⟩).mpr hz

/-- Foundation is inherited from the ambient membership relation. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For Foundation, let $x\in N$ have a member in $N$. It is externally nonempty, so external Foundation gives
    $y\in x$ with $x\cap y=\emptyset$. Transitivity gives $y\in N$.
    There is no $z\in N$ belonging to both $x$ and $y$, so this $y$ also witnesses the internal Foundation axiom.
-/
theorem models_foundation (hM : M.IsTransitive) : M ⊨ foundationSentence := by
  apply (models_foundation_iff M).mpr
  intro x hx
  obtain ⟨z, hz⟩ := hx
  have hne : x.val ≠ ∅ := by
    intro he
    rw [he] at hz
    exact ZFSet.notMem_empty _ hz
  obtain ⟨y, hy, hxy⟩ := ZFSet.regularity x.val hne
  refine ⟨⟨y, hM.mem_trans hy x.property⟩, hy, ?_⟩
  intro w hwy hwx
  have h : w.val ∈ x.val ∩ y := ZFSet.mem_inter.mpr ⟨hwx, hwy⟩
  rw [hxy] at h
  exact ZFSet.notMem_empty _ h

/-- These two axioms already hold in every evaluated extension of a transitive set. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    The transitivity of $M[G]$ proved in §{sec:forcing-names-valuation} now gives the last assertion.
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Extensionality and Foundation in a transitive domain
-/
theorem extension_inherits_extensionality_foundation (P : ZFSet.{u}) (G : Set ZFSet.{u})
    (hM : M.IsTransitive) :
    (extension P M G ⊨ extensionalitySentence) ∧ (extension P M G ⊨ foundationSentence) :=
  ⟨models_extensionality (extension_isTransitive P M G hM),
    models_foundation (extension_isTransitive P M G hM)⟩

end PolishSpaceBook.SetTheoryModels
