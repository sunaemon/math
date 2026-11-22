module

public import PolishSpaceBook.NonarchimedeanRepresentation
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.ModelTheory.Basic
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

/-! # Automorphism groups and orbit relations

We use mathlib's first-order structures and structure equivalences. Their
underlying permutations form a closed subgroup. Conversely, the relations
naming the orbits of a closed permutation group recover precisely that group.
-/

namespace PolishSpaceBook.AutomorphismGroups

open Set Topology FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open scoped PolishSpaceBook.PointwisePerm

variable (L : Language) (M : Type*) [L.Structure M]

/-- The underlying permutations of the canonical structure automorphisms. -/
def automorphismSubgroup : Subgroup (Equiv.Perm M) where
  carrier := Set.range (fun e : M ≃[L] M => e.toEquiv)
  one_mem' := ⟨FirstOrder.Language.Equiv.refl L M, rfl⟩
  mul_mem' := by
    rintro p q ⟨e, rfl⟩ ⟨f, rfl⟩
    exact ⟨e.comp f, rfl⟩
  inv_mem' := by
    rintro p ⟨e, rfl⟩
    exact ⟨e.symm, rfl⟩

/-- Preserving each function and relation is exactly being an automorphism. -/
theorem mem_automorphismSubgroup_iff (p : Equiv.Perm M) :
    p ∈ automorphismSubgroup L M ↔
      (∀ n (f : L.Functions n) (a : Fin n → M),
        p (funMap f a) = funMap f (p ∘ a)) ∧
      (∀ n (r : L.Relations n) (a : Fin n → M),
        RelMap r (p ∘ a) ↔ RelMap r a) := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨fun _ => e.map_fun, fun _ => e.map_rel⟩
  · rintro ⟨hf, hr⟩
    exact ⟨⟨p, fun {n} => hf n, fun {n} => hr n⟩, rfl⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    For a countably infinite structure, identify its universe with $\NN$. Its automorphism group is a closed
    subgroup of $\InfiniteSymmetricGroup$. To see this, fix a finite tuple $\bar a$.
    For an interpreted function $f$, the condition $\sigma(f(\bar a))=f(\sigma\bar a)$ depends only on the values of
    $\sigma$ at the entries of $\bar a$ and at $f(\bar a)$. For an interpreted relation $R$, the condition
    $R(\sigma\bar a)\iff R(\bar a)$ depends only on the values at the entries of $\bar a$.
    Failure of either condition therefore defines an open set of permutations, so the complement of
    $\mathrm{Aut}(M)$ is open. This also covers constants, viewed as functions of arity zero.
-/
/-- Each violation is detected on finitely many coordinates, so the
permutations preserving the structure form a closed set. -/
theorem isClosed_automorphismSubgroup [TopologicalSpace M] [DiscreteTopology M] :
    IsClosed (automorphismSubgroup L M : Set (Equiv.Perm M)) := by
  have ht (n : ℕ) (a : Fin n → M) :
      Continuous (fun p : Equiv.Perm M => p ∘ a) :=
    continuous_pi fun i => PointwisePerm.continuous_apply (a i)
  have he : (automorphismSubgroup L M : Set (Equiv.Perm M)) =
      (⋂ n, ⋂ f : L.Functions n, ⋂ a : Fin n → M,
        {p : Equiv.Perm M | p (funMap f a) = funMap f (p ∘ a)}) ∩
      (⋂ n, ⋂ r : L.Relations n, ⋂ a : Fin n → M,
        {p : Equiv.Perm M | RelMap r (p ∘ a) ↔ RelMap r a}) := by
    ext p
    simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
    exact mem_automorphismSubgroup_iff L M p
  rw [he]
  apply IsClosed.inter
  · exact isClosed_iInter fun n => isClosed_iInter fun f => isClosed_iInter fun a =>
      isClosed_eq (PointwisePerm.continuous_apply _) ((continuous_of_discreteTopology).comp (ht n a))
  · exact isClosed_iInter fun n => isClosed_iInter fun r => isClosed_iInter fun a =>
      (isClosed_discrete {b : Fin n → M | RelMap r b ↔ RelMap r a}).preimage (ht n a)

/-- A countable structure's automorphism group is Polish in its pointwise topology. -/
instance automorphism_polishSpace [TopologicalSpace M] [DiscreteTopology M] [Countable M] :
    PolishSpace (automorphismSubgroup L M) :=
  (isClosed_automorphismSubgroup L M).isClosedEmbedding_subtypeVal.polishSpace

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    A finite structure has a finite discrete automorphism group, which embeds as a closed subgroup by permuting a
    finite subset of $\NN$ and fixing all remaining points.
-/
/-- Relabel an infinite countable universe; on a finite universe, extend each
permutation by the identity outside a finite subset of the natural numbers. -/
theorem exists_closedEmbedding_automorphisms [TopologicalSpace M] [DiscreteTopology M]
    [Countable M] :
    ∃ f : automorphismSubgroup L M →* Equiv.Perm ℕ, IsClosedEmbedding f := by
  classical
  cases finite_or_infinite M with
  | inl hM =>
    let := hM
    let ι : M ↪ ℕ := ⟨_, Countable.exists_injective_nat M |>.choose_spec⟩
    let f := (Equiv.Perm.viaEmbeddingHom ι).comp (automorphismSubgroup L M).subtype
    have hf : Function.Injective f :=
      (Equiv.Perm.viaEmbeddingHom_injective ι).comp Subtype.val_injective
    have hc : Continuous f := continuous_of_discreteTopology
    exact ⟨f, hc.isClosedEmbedding hf⟩
  | inr hM =>
    let := hM
    let e : M ≃ ℕ := Classical.choice inferInstance
    refine ⟨e.permCongrHom.toMonoidHom.comp (automorphismSubgroup L M).subtype, ?_⟩
    exact (PointwisePerm.relabelHomeomorph e).isClosedEmbedding.comp
      (isClosed_automorphismSubgroup L M).isClosedEmbedding_subtypeVal

variable (H : Subgroup (Equiv.Perm ℕ))

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Conversely, let $H\leq\InfiniteSymmetricGroup$ be closed. Build a countable relational language with one $n$-ary
    relation symbol $R_O$ for each $H$-orbit $O\IncludedIn \NN^n$, over all $n\geq 1$.
    For each arity, the set of orbits is a quotient of the countable set $\NN^n$, so there are only countably many
    symbols in total. Let $M_H$ be the structure on universe $\NN$ in which $R_O(\bar a)$ holds exactly when $\bar a\in O$.
    Every element of $H$ preserves all these orbit relations, so $H\leq\mathrm{Aut}(M_H)$.
-/
/-- One relation for each orbit of each positive arity, and no functions. -/
def orbitLanguage : Language where
  Functions := fun _ => Empty
  Relations
    | 0 => Empty
    | n + 1 => MulAction.orbitRel.Quotient H (Fin (n + 1) → ℕ)

instance : (orbitLanguage H).IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Countable (orbitLanguage H).Symbols := by
  have : ∀ n, Countable ((orbitLanguage H).Relations n) := by
    intro n
    cases n <;> dsimp [orbitLanguage] <;> infer_instance
  unfold Language.Symbols
  infer_instance

/-- A tuple satisfies its own orbit relation. -/
instance orbitStructure : (orbitLanguage H).Structure ℕ where
  funMap := isEmptyElim
  RelMap := fun {n} => match n with
    | 0 => fun r => Empty.elim r
    | _ + 1 => fun O a => Quotient.mk'' a = O

/-- Acting by a member of the group does not change a tuple's orbit. -/
theorem orbit_mk_apply (h : H) {n : ℕ} (a : Fin n → ℕ) :
    (Quotient.mk'' (h.val ∘ a) : MulAction.orbitRel.Quotient H (Fin n → ℕ)) =
      Quotient.mk'' a := by
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨h, rfl⟩

/-- The group acts by automorphisms of its orbit structure. -/
def toOrbitAut (h : H) : ℕ ≃[orbitLanguage H] ℕ where
  toEquiv := h.val
  map_fun' := isEmptyElim
  map_rel' := by
    intro n
    cases n with
    | zero => exact fun r => Empty.elim r
    | succ n =>
      intro O a
      change Quotient.mk'' (h.val ∘ a) = O ↔ Quotient.mk'' a = O
      rw [orbit_mk_apply]

/-- Every member of the original group preserves all orbit relations. -/
theorem le_orbit_automorphismSubgroup : H ≤ automorphismSubgroup (orbitLanguage H) ℕ := by
  intro h hh
  exact ⟨toOrbitAut H ⟨h, hh⟩, rfl⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    If $\sigma\in\mathrm{Aut}(M_H)$ and $F=\{a_1,\ldots,a_n\}$ is finite and nonempty, then
    $\sigma(a_1,\ldots,a_n)$ lies in the same $H$-orbit as $(a_1,\ldots,a_n)$.
    Hence some $h\in H$ agrees with $\sigma$ on $F$. For the empty set, the identity already gives such agreement.
    Every basic neighborhood of $\sigma$ therefore meets $H$, so $\sigma$ belongs to the closure of $H$ in
    $\InfiniteSymmetricGroup$. Since $H$ is closed, $\sigma\in H$. Thus $H=\mathrm{Aut}(M_H)$.
-/
/-- Preserving the orbit of a positive tuple gives one group member agreeing
with the automorphism at every coordinate of that tuple. -/
theorem exists_agreement_tuple (e : ℕ ≃[orbitLanguage H] ℕ) {n : ℕ}
    (a : Fin (n + 1) → ℕ) : ∃ h : H, ∀ i, h.val (a i) = e (a i) := by
  have he := (e.map_rel (n := n + 1) (Quotient.mk'' a) a).2 rfl
  change Quotient.mk'' (e ∘ a) = Quotient.mk'' a at he
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
  exact ⟨h, fun i => congrFun hh i⟩

/-- Automorphisms can be matched on any finite set; the empty set needs no
positive-arity relation. -/
theorem exists_agreement_finset (e : ℕ ≃[orbitLanguage H] ℕ) (F : Finset ℕ) :
    ∃ h : H, ∀ x ∈ F, h.val x = e x := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hF)
    let a : Fin (n + 1) → ℕ := fun i => (F.equivFin.symm (Fin.cast hn.symm i)).val
    obtain ⟨h, hh⟩ := exists_agreement_tuple H e a
    refine ⟨h, fun x hx => ?_⟩
    have hi := hh (Fin.cast hn (F.equivFin ⟨x, hx⟩))
    simpa [a] using hi
  · exact ⟨1, by simp [Finset.not_nonempty_iff_eq_empty.mp hF]⟩

/-- Finite agreement places every orbit-structure automorphism in the closure. -/
theorem orbit_automorphism_mem_closure (e : ℕ ≃[orbitLanguage H] ℕ) :
    e.toEquiv ∈ closure (H : Set (Equiv.Perm ℕ)) := by
  apply mem_closure_iff.mpr
  intro U hU heU
  obtain ⟨F, hF⟩ := PointwisePerm.mem_nhds_iff.mp (hU.mem_nhds heU)
  obtain ⟨h, hh⟩ := exists_agreement_finset H e F
  exact ⟨h.val, hF hh, h.property⟩

/-- A closed permutation group is exactly the automorphism group of its
countable relational orbit structure. -/
theorem orbit_automorphismSubgroup_eq (hH : IsClosed (H : Set (Equiv.Perm ℕ))) :
    automorphismSubgroup (orbitLanguage H) ℕ = H := by
  apply le_antisymm
  · rintro p ⟨e, rfl⟩
    have he := orbit_automorphism_mem_closure H e
    rw [hH.closure_eq] at he
    exact he
  · exact le_orbit_automorphismSubgroup H

/-- The non-Archimedean representation can be chosen to have exactly the
canonical automorphism subgroup of a countable relational structure as range. -/
theorem nonarchimedean_iff_automorphism_range {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] :
    NonarchimedeanGroup G ↔ ∃ (L : Language.{0, 0}) (_ : Countable L.Symbols)
      (_ : L.IsRelational) (_ : L.Structure ℕ) (f : G →* Equiv.Perm ℕ),
      IsClosedEmbedding f ∧ f.range = automorphismSubgroup L ℕ := by
  constructor
  · intro hG
    let := hG
    obtain ⟨f, hf⟩ := NonarchimedeanRepresentation.exists_closedEmbedding_perm_nat (G := G)
    exact ⟨orbitLanguage f.range, inferInstance, inferInstance, orbitStructure f.range,
      f, hf, (orbit_automorphismSubgroup_eq f.range hf.isClosed_range).symm⟩
  · rintro ⟨L, _, _, _, f, hf, _⟩
    exact PointwisePerm.nonarchimedean_of_embedding f hf.isEmbedding

/-- The third condition implies the first, for any discrete universe. -/
theorem nonarchimedean_of_automorphism_equiv [TopologicalSpace M] [DiscreteTopology M]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G ≃* automorphismSubgroup L M) (he : IsHomeomorph e) :
    NonarchimedeanGroup G :=
  PointwisePerm.nonarchimedean_of_embedding
    ((automorphismSubgroup L M).subtype.comp e.toMonoidHom)
    (IsEmbedding.subtypeVal.comp he.isEmbedding)

/-- Every non-Archimedean Polish group is topologically isomorphic to the
canonical automorphism subgroup of a countable relational structure on ℕ. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{theorem*} For a Polish group $G$, the following are equivalent.
-/
theorem nonarchimedean_iff_automorphism_group {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] :
    NonarchimedeanGroup G ↔ ∃ (L : Language.{0, 0}) (_ : Countable L.Symbols)
      (_ : L.IsRelational) (_ : L.Structure ℕ) (e : G ≃* automorphismSubgroup L ℕ),
      IsHomeomorph e := by
  constructor
  · intro hG
    obtain ⟨L, hL, hr, hM, f, hf, hfr⟩ := nonarchimedean_iff_automorphism_range.mp hG
    have he : ∃ e : G ≃* f.range, IsHomeomorph e :=
      ⟨MonoidHom.ofInjective hf.injective, hf.isEmbedding.toHomeomorph.isHomeomorph⟩
    rw [hfr] at he
    obtain ⟨e, he⟩ := he
    exact ⟨L, hL, hr, hM, e, he⟩
  · rintro ⟨L, _, _, _, e, he⟩
    exact nonarchimedean_of_automorphism_equiv L ℕ e he

end PolishSpaceBook.AutomorphismGroups
