module

public import PolishSpaceBook.PermutationTopology
public import PolishSpaceBook.AnalyticBorelMaps
public import Mathlib.ModelTheory.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Logic actions on countable structures

The model space is the product of discrete relation and function coordinates.
Relabeling pulls back every input tuple and also pushes function outputs forward.
All statements include arity zero, so constants and nullary relations are covered.
-/

namespace PolishSpaceBook.LogicActions

open Set Topology MeasureTheory
open scoped PointwisePerm

variable (L : FirstOrder.Language)

abbrev RelIndex := Σ r : (Σ n, L.Relations n), Fin r.1 → ℕ
abbrev FunIndex := Σ f : (Σ n, L.Functions n), Fin f.1 → ℕ

instance : TopologicalSpace (RelIndex L) := ⊥
instance : DiscreteTopology (RelIndex L) := ⟨rfl⟩
instance : TopologicalSpace (FunIndex L) := ⊥
instance : DiscreteTopology (FunIndex L) := ⟨rfl⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    Equip this space with the product topology on the individual table entries, indexed by a symbol and a tuple of
    natural numbers of its arity. There are countably many such entries, each taking values in the discrete space $2$
    or $\NN$, so $\mathrm{Mod}_L$ is Polish.
    For positive arities, the displayed factors are Cantor or Baire spaces; zero-ary symbols instead give finite
    or countable discrete factors. A point $M \in \mathrm{Mod}_L$ specifies the truth table of each relation symbol
    and the value table of each function symbol. Conversely, any choice of these tables defines a unique $L$-structure
    on $\NN$; there are no additional compatibility conditions.
-/
/-- The countable product used to present all structures on the natural numbers. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    A basic example of a Polish-group action in classification theory is the action of $\InfiniteSymmetricGroup$ on the space of
    countable structures. Fix a countable first-order language $L$ consisting of relation symbols $R_i$ of arities $n_i$ and
    function symbols $f_j$ of arities $m_j$; constants are zero-ary functions. The space of $L$-structures with universe
    $\NN$ is
    $$\mathrm{Mod}_L \;:=\; \prod_i 2^{\funcspace{n_i}{\NN}} \;\times\; \prod_j \funcspace{\funcspace{m_j}{\NN}}{\NN}.$$
-/
abbrev ModelCode := (RelIndex L → Bool) × (FunIndex L → ℕ)

instance [Countable (Σ n, L.Relations n)] [Countable (Σ n, L.Functions n)] :
    PolishSpace (ModelCode L) where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := inferInstance

/-- Read the code using mathlib's canonical first-order structure. -/
@[implicit_reducible]
def toStructure (M : ModelCode L) : L.Structure ℕ where
  funMap f a := M.2 ⟨⟨_, f⟩, a⟩
  RelMap r a := M.1 ⟨⟨_, r⟩, a⟩ = true

/-- A copy of the natural numbers carrying the selected interpretation. -/
def ModelCarrier (_M : ModelCode L) := ℕ

instance (M : ModelCode L) : L.Structure (ModelCarrier L M) := toStructure L M

/-- The usual structure isomorphisms, with the two interpretations explicit. -/
abbrev ModelIso (M N : ModelCode L) :=
  FirstOrder.Language.Equiv L (ModelCarrier L M) (ModelCarrier L N)

/-- Pull back all inputs and push forward the output of every function. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The \termdefine{logic action} of $\InfiniteSymmetricGroup$ on $\mathrm{Mod}_L$ is the action by permutation of the
    universe: for $\sigma \in \InfiniteSymmetricGroup$ and $M \in \mathrm{Mod}_L$,
    $$(\sigma \cdot M)(R_i)(a_1, \ldots, a_{n_i}) := M(R_i)(\sigma^{-1}(a_1), \ldots, \sigma^{-1}(a_{n_i})).$$
    For function symbols one must also relabel the output:
    $$(\sigma\cdot M)(f_j)(a_1,\ldots,a_{m_j})
    :=\sigma\bigl(M(f_j)(\sigma^{-1}(a_1),\ldots,\sigma^{-1}(a_{m_j}))\bigr).$$
-/
def relabel (p : Equiv.Perm ℕ) (M : ModelCode L) : ModelCode L :=
  (fun i => M.1 ⟨i.1, p.symm ∘ i.2⟩,
   fun i => p (M.2 ⟨i.1, p.symm ∘ i.2⟩))

instance : MulAction (Equiv.Perm ℕ) (ModelCode L) where
  smul := relabel L
  one_smul M := by
    change relabel L 1 M = M
    apply Prod.ext <;> funext i <;> simp [relabel, Equiv.Perm.one_def]
  mul_smul p q M := by
    change relabel L (p * q) M = relabel L p (relabel L q M)
    apply Prod.ext <;> funext i <;> simp [relabel, Function.comp_def, Equiv.Perm.mul_def]

@[simp] lemma smul_rel (p : Equiv.Perm ℕ) (M : ModelCode L) (i : RelIndex L) :
    (p • M).1 i = M.1 ⟨i.1, p.symm ∘ i.2⟩ := rfl

@[simp] lemma smul_fun (p : Equiv.Perm ℕ) (M : ModelCode L) (i : FunIndex L) :
    (p • M).2 i = p (M.2 ⟨i.1, p.symm ∘ i.2⟩) := rfl

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    The identity and composition laws follow by substitution into the two definitions above.
    For continuity, fix $(\sigma,M)$ and an output coordinate with input tuple $\bar a$.
    Put $\bar b:=\sigma^{-1}\bar a$, applying the permutation coordinatewise. In a neighborhood of $\sigma$,
    require the inverse permutation to agree with $\sigma^{-1}$ on the finitely many entries of $\bar a$.
    For a relation symbol, also fix its truth value in $M$ at $\bar b$. These open conditions fix the output bit.
    For a function symbol $f_j$, put $c:=M(f_j)(\bar b)$, fix this value in the structure coordinate,
    and require the permutation to agree with $\sigma$ at $c$. These open conditions fix the output value $\sigma(c)$.
    Thus every output coordinate is continuous, and the action is continuous in the product topology.
    For a zero-ary symbol the tuple is empty: a nullary relation needs only its truth value fixed, while a constant
    also requires the permutation value at its interpretation to be fixed.
-/
/-- A finite tuple of inverse-permutation values depends continuously on the permutation. -/
lemma continuous_inverse_tuple {n : ℕ} (a : Fin n → ℕ) :
    Continuous (fun p : Equiv.Perm ℕ => p.symm ∘ a) :=
  continuous_pi fun i => (PointwisePerm.continuous_apply (a i)).comp
    PointwisePerm.continuous_inverse

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    The logic action is continuous, and its orbit equivalence relation is
-/
instance : ContinuousSMul (Equiv.Perm ℕ) (ModelCode L) where
  continuous_smul := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      have ht : Continuous (fun p : Equiv.Perm ℕ =>
          (⟨i.1, p.symm ∘ i.2⟩ : RelIndex L)) :=
        continuous_of_discreteTopology.comp (continuous_inverse_tuple i.2)
      have hv : Continuous (fun z : (RelIndex L → Bool) × RelIndex L => z.1 z.2) :=
        continuous_prod_of_discrete_right.mpr (fun i => continuous_apply i)
      exact hv.comp ((continuous_fst.comp continuous_snd).prodMk (ht.comp continuous_fst))
    · apply continuous_pi
      intro i
      have ht : Continuous (fun p : Equiv.Perm ℕ =>
          (⟨i.1, p.symm ∘ i.2⟩ : FunIndex L)) :=
        continuous_of_discreteTopology.comp (continuous_inverse_tuple i.2)
      have hv : Continuous (fun z : (FunIndex L → ℕ) × FunIndex L => z.1 z.2) :=
        continuous_prod_of_discrete_right.mpr (fun i => continuous_apply i)
      have he : Continuous (fun z : Equiv.Perm ℕ × ℕ => z.1 z.2) :=
        continuous_prod_of_discrete_right.mpr PointwisePerm.continuous_apply
      exact he.comp (continuous_fst.prodMk
        (hv.comp ((continuous_snd.comp continuous_snd).prodMk (ht.comp continuous_fst))))

/-- Encode every ordinary first-order structure by its relation and function tables. -/
noncomputable def fromStructure (M : L.Structure ℕ) : ModelCode L :=
  (fun i => @decide (M.RelMap i.1.2 i.2) (Classical.propDecidable _),
   fun i => M.funMap i.1.2 i.2)

lemma toStructure_injective : Function.Injective (toStructure L) := by
  intro M N h
  apply Prod.ext
  · funext i
    apply Bool.eq_iff_iff.mpr
    exact Iff.of_eq (congrArg (fun S : L.Structure ℕ => S.RelMap i.1.2 i.2) h)
  · funext i
    exact congrArg (fun S : L.Structure ℕ => S.funMap i.1.2 i.2) h

@[simp] lemma toStructure_fromStructure (M : L.Structure ℕ) :
    toStructure L (fromStructure L M) = M := by
  apply FirstOrder.Language.Structure.ext
  · rfl
  · funext n r a
    change (@decide (M.RelMap r a) (Classical.propDecidable _) = true) = M.RelMap r a
    simp

/-- The coding has no extra conditions and omits no structures. -/
noncomputable def structureEquiv : ModelCode L ≃ L.Structure ℕ where
  toFun := toStructure L
  invFun := fromStructure L
  left_inv M := toStructure_injective L (toStructure_fromStructure L (toStructure L M))
  right_inv := toStructure_fromStructure L

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    The permutation $\sigma$ is an isomorphism from $M$ to $\sigma\cdot M$, since it preserves the relations and
    functions by the defining equations. Conversely, if $\sigma:M\to N$ is an isomorphism, apply its preservation
    conditions to $\sigma^{-1}\bar a$. They give the defining equations for $N=\sigma\cdot M$ at every table entry.
    Hence the orbits are exactly the isomorphism classes.
-/
/-- The relabeling permutation is an isomorphism to the transported structure. -/
def relabelIso (p : Equiv.Perm ℕ) (M : ModelCode L) : ModelIso L M (p • M) where
  toEquiv := p
  map_fun' := by
    intro n f a
    change p (M.2 ⟨⟨n, f⟩, a⟩) = p (M.2 ⟨⟨n, f⟩, p.symm ∘ (p ∘ a)⟩)
    simp [Function.comp_def]
  map_rel' := by
    intro n r a
    change (M.1 ⟨⟨n, r⟩, p.symm ∘ (p ∘ a)⟩ = true) ↔ M.1 ⟨⟨n, r⟩, a⟩ = true
    simp [Function.comp_def]

/-- Forget the two structure tags and retain the underlying permutation. -/
def isoPerm {M N : ModelCode L} (e : ModelIso L M N) : Equiv.Perm ℕ := e.toEquiv

/-- Conversely, preserving all functions and relations determines the transported code. -/
lemma eq_smul_of_iso {M N : ModelCode L} (e : ModelIso L M N) : N = isoPerm L e • M := by
  apply Prod.ext
  · funext i
    apply Bool.eq_iff_iff.mpr
    have h := e.map_rel' i.1.2 ((isoPerm L e).symm ∘ i.2)
    change (N.1 ⟨i.1, isoPerm L e ∘ ((isoPerm L e).symm ∘ i.2)⟩ = true) ↔
      M.1 ⟨i.1, (isoPerm L e).symm ∘ i.2⟩ = true at h
    simpa [Function.comp_def] using h
  · funext i
    have h := e.map_fun' i.1.2 ((isoPerm L e).symm ∘ i.2)
    change isoPerm L e (M.2 ⟨i.1, (isoPerm L e).symm ∘ i.2⟩) =
      N.2 ⟨i.1, isoPerm L e ∘ ((isoPerm L e).symm ∘ i.2)⟩ at h
    simpa [Function.comp_def] using h.symm

/-- The logic action has precisely the usual isomorphism classes as orbits. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    The logic action is continuous, and its orbit equivalence relation is
-/
theorem orbit_iff_modelIso (M N : ModelCode L) :
    (∃ p : Equiv.Perm ℕ, N = p • M) ↔ Nonempty (ModelIso L M N) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨relabelIso L p M⟩
  · rintro ⟨e⟩
    exact ⟨isoPerm L e, eq_smul_of_iso L e⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    For the empty language any bijection witnesses isomorphism, so the relation is trivial.
-/
/-- With no symbols, the identity bijection is already a structure isomorphism. -/
def emptyLanguageIso [∀ n, IsEmpty (L.Functions n)] [∀ n, IsEmpty (L.Relations n)]
    (M N : ModelCode L) : ModelIso L M N where
  toEquiv := Equiv.refl ℕ
  map_fun' := by intro n f; exact isEmptyElim f
  map_rel' := by intro n r; exact isEmptyElim r

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    In $(\mathrm{Mod}_L\times\mathrm{Mod}_L)\times\InfiniteSymmetricGroup$, put
    $$C:=\{((M,N),\sigma):N=\sigma\cdot M\}.$$
    The two maps $((M,N),\sigma)\mapsto N$ and $((M,N),\sigma)\mapsto\sigma\cdot M$ are continuous into the
    Hausdorff space $\mathrm{Mod}_L$, so their equality set $C$ is closed. It is therefore Polish, and its continuous
    projection onto $(M,N)$ has image exactly the isomorphism relation. This image is analytic by §{sec:analytic-sets}.
-/
/-- The isomorphism witness relation is closed in the two codes and the permutation. -/
def witnessSet : Set ((ModelCode L × ModelCode L) × Equiv.Perm ℕ) :=
  {z | z.1.2 = z.2 • z.1.1}

theorem isClosed_witnessSet : IsClosed (witnessSet L) :=
  isClosed_eq (continuous_snd.comp continuous_fst)
    (continuous_snd.smul (continuous_fst.comp continuous_fst))

/-- Isomorphism of structures in a countable language is analytic. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    The logic action is continuous, and its orbit equivalence relation is
-/
theorem analyticSet_modelIso [Countable (Σ n, L.Relations n)]
    [Countable (Σ n, L.Functions n)] :
    AnalyticSet {z : ModelCode L × ModelCode L | Nonempty (ModelIso L z.1 z.2)} := by
  have : PolishSpace (witnessSet L) := (isClosed_witnessSet L).polishSpace
  have ha := analyticSet_range_via_baire_surjection (Z := witnessSet L)
    (continuous_fst.comp continuous_subtype_val)
  convert ha using 1
  ext z
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (orbit_iff_modelIso L z.1 z.2).mpr h
    exact ⟨⟨(z, p), hp⟩, rfl⟩
  · rintro ⟨⟨⟨⟨M, N⟩, p⟩, hp⟩, he⟩
    change (M, N) = z at he
    subst z
    exact (orbit_iff_modelIso L M N).mp ⟨p, hp⟩

end PolishSpaceBook.LogicActions
