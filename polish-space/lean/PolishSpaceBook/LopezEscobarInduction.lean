module

public import PolishSpaceBook.LopezEscobarOpen

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Localized formula construction and the Borel induction for Lopez--Escobar -/

namespace PolishSpaceBook.LopezEscobar

open Set Topology TopologicalSpace LogicActions InfinitaryLogic
open scoped PointwisePerm

/-- Regard a fixed tuple of natural-number names as indices in a sufficiently large context. -/
def nameIndices {n m} (s : Fin n → ℕ) (hm : ∀ i, s i < m) : Fin n → Fin m :=
  fun i => ⟨s i, hm i⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    We next express localization using the same finite-variable construction. Write $n$ for the length of $\bar s$.
    For each $m\in\omega$ with $s_i<m$ for all $i<n$, put
    $$\bar t_m:=\Sequence{j}{j<m},\qquad e_m(i):=s_i.$$
    If $\bar b$ is injective and $b_{e_m(i)}=a_i$ for all $i<n$, then
    $$\TupleAgreementCoset{\bar b}{\bar t_m}\IncludedIn\TupleAgreementCoset{\bar a}{\bar s}.$$
    These subcosets suffice to refine every nonempty open subset $V$ of the original coset. Indeed, choose
    $\sigma\in V$ and finitely many inputs $u_j$ such that agreement with $\sigma$ on those inputs implies membership
    in $V$. Choose $m$ larger than all entries of $\bar s$ and all values $\sigma(u_j)$, and put
    $b_r:=\sigma^{-1}(r)$ for $r<m$. Then $b_{e_m(i)}=a_i$, and a permutation sending every $b_r$ to $r$ agrees
    with $\sigma$ on the specified inputs. Hence its coset is contained in $V$.
-/
/-- Inverse images of an initial segment refine any open neighborhood inside a moving coset. -/
theorem exists_initial_refinement {n} (a s : Fin n → ℕ) {V : Set (Equiv.Perm ℕ)}
    (hV : IsOpen V) {p : Equiv.Perm ℕ} (hpV : p ∈ V) (hp : p ∈ tupleCoset a s) :
    ∃ m, ∃ hm : ∀ i, s i < m, ∃ b : Fin m → ℕ,
      Function.Injective b ∧ b ∘ nameIndices s hm = a ∧ tupleCoset b Fin.val ⊆ V := by
  classical
  obtain ⟨F, hF⟩ := PointwisePerm.mem_nhds_iff.mp (hV.mem_nhds hpV)
  obtain ⟨r, hr⟩ := (F.finite_toSet.image (fun x => p x)).bddAbove
  obtain ⟨q, hq⟩ := (Set.finite_range s).bddAbove
  let m := max r q + 1
  have hm : ∀ i, s i < m := fun i =>
    Nat.lt_succ_of_le ((hq (mem_range_self i)).trans (Nat.le_max_right r q))
  let b : Fin m → ℕ := p.symm ∘ Fin.val
  refine ⟨m, hm, b, p.symm.injective.comp Fin.val_injective, ?_, ?_⟩
  · funext i
    change p.symm (s i) = a i
    exact p.symm_apply_eq.mpr (hp i).symm
  · intro u hu
    apply hF
    intro x hx
    have hx' : p x < m := Nat.lt_succ_of_le
      ((hr (mem_image_of_mem _ hx)).trans (Nat.le_max_left r q))
    simpa only [b, Function.comp_apply, Equiv.symm_apply_apply] using hu ⟨p x, hx'⟩

/-- A compatible inverse tuple defines a subcoset of the original moving coset. -/
theorem initial_coset_subset {n m} (a s : Fin n → ℕ) (hm : ∀ i, s i < m)
    (b : Fin m → ℕ) (hab : b ∘ nameIndices s hm = a) :
    tupleCoset b Fin.val ⊆ tupleCoset a s := by
  intro p hp i
  rw [← congrFun hab i]
  exact hp (nameIndices s hm i)

variable {L : FirstOrder.Language}

/-- Nonmeagerness in a smaller open parameter set implies nonmeagerness in a larger one. -/
theorem vaughtStar_mono_parameter {U V : Set (Equiv.Perm ℕ)} (hUV : U ⊆ V)
    (B : Set (ModelCode L)) : vaughtStar U B ⊆ vaughtStar V B := by
  intro M h hm
  exact h (hm.mono (inter_subset_inter_right _ hUV))

/-- Initial-segment inverse tuples suffice for the localization of the comeager transform. -/
theorem mem_triangle_iff_initial_refinements
    [MeasurableSpace (ModelCode L)] [BorelSpace (ModelCode L)]
    {B : Set (ModelCode L)} (hB : MeasurableSet B) {n} (a s : Fin n → ℕ) (M : ModelCode L) :
    M ∈ vaughtTriangle (tupleCoset a s) B ↔
      ∀ m (hm : ∀ i, s i < m) (b : Fin m → ℕ), Function.Injective b →
        b ∘ nameIndices s hm = a → M ∈ vaughtStar (tupleCoset b Fin.val) B := by
  change M ∈ categoryTriangle (tupleCoset a s) (actionRelation B) ↔ _
  rw [mem_categoryTriangle_local isTopologicalBasis_tupleCosets (isClopen_tupleCoset a s).isOpen
    _ M (baireMeasurable_actionSection hB M)]
  constructor
  · intro h m hm b hb hab
    exact h (tupleCoset b Fin.val) ⟨m, b, Fin.val, hb, Fin.val_injective, rfl⟩
      (tupleCoset_nonempty hb Fin.val_injective) (initial_coset_subset a s hm b hab)
  · intro h V hV ⟨p, hpV⟩ hVU
    obtain ⟨m, hm, b, hb, hab, hbV⟩ :=
      exists_initial_refinement a s (isTopologicalBasis_tupleCosets.isOpen hV) hpV (hVU hpV)
    exact vaughtStar_mono_parameter hbV B (h m hm b hb hab)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Suppose the formulas $\varphi^{\bar t}_{B,*}$ are available for every finite tuple $\bar t$, and write
    $\theta_m:=\varphi^{\bar t_m}_{B,*}$. The localization rule in Vaught's lemma says that the section of the Borel
    set $B$ is comeager in $\TupleAgreementCoset{\bar a}{\bar s}$ exactly when it is non-meager in every nonempty
    basic refinement. It suffices to check the subcosets just constructed: non-meagerness in a smaller open set
    implies non-meagerness in a larger one. Thus the comeager transform is expressed by
    $$
    \varphi^{\bar s}_{B,\triangle}(\bar x)
    :=\neg\bigvee_{\substack{m\in\omega\\\forall i<n\;s_i<m}}
    \InverseTupleFormula{e_m}{\neg\theta_m}(\bar x).
    $$
    Indeed, the disjunction asserts that for some admissible $m$ there is an injective tuple $\bar b$ with
    $b_{e_m(i)}=a_i$ for all $i<n$ and $M\not\models\theta_m(\bar b)$, exactly a failure of the localized condition.
    The disjunction is countable, and each disjunct binds only finitely many extra variables. The original finite
    context remains the full set of free variables.
-/
/-- A formula for every nonmeager transform gives a formula for every comeager transform. -/
theorem exists_triangleFormula_of_star
    [MeasurableSpace (ModelCode L)] [BorelSpace (ModelCode L)]
    {B : Set (ModelCode L)} (hB : MeasurableSet B)
    (hstar : ∀ m (t : Fin m → ℕ), ∃ φ : Formula L m,
      ∀ M b, φ.Satisfies M b ↔ M ∈ vaughtStar (tupleCoset b t) B)
    {n} (s : Fin n → ℕ) :
    ∃ φ : Formula L n, ∀ M a, φ.Satisfies M a ↔ M ∈ vaughtTriangle (tupleCoset a s) B := by
  classical
  choose φ hφ using fun m => hstar m Fin.val
  let I := {m : ℕ // ∀ i, s i < m}
  let ψ : I → Formula L n := fun m => extensionFormula (nameIndices s m.property) (φ m.val).neg
  refine ⟨(countableDisj ψ).neg, ?_⟩
  intro M a
  change ¬ (countableDisj ψ).Realize (M := ModelCarrier L M) a ↔ _
  rw [realize_countableDisj, mem_triangle_iff_initial_refinements hB]
  constructor
  · intro h m hm b hb hab
    by_contra hn
    apply h
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [show ψ ⟨m, hm⟩ = extensionFormula (nameIndices s hm) (φ m).neg from rfl,
      realize_extensionFormula]
    exact ⟨b, hb, hab, fun hf => hn ((hφ m M b).mp hf)⟩
  · intro h ⟨m, hm⟩
    rw [show ψ m = extensionFormula (nameIndices s m.property) (φ m.val).neg from rfl,
      realize_extensionFormula] at hm
    obtain ⟨b, hb, hab, hn⟩ := hm
    exact hn ((hφ m.val M b).mpr (h m.val m.property b hb hab))


local instance : MeasurableSpace (ModelCode L) := borel _
local instance : BorelSpace (ModelCode L) := ⟨rfl⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    We can now complete the simultaneous Borel induction. For open sets, the preceding construction gives the
    non-meager formula, and localization gives the comeager formula. For complements, duality gives
    $$
    \varphi^{\bar s}_{\complement B,*}:=\neg\varphi^{\bar s}_{B,\triangle},
    \qquad
    \varphi^{\bar s}_{\complement B,\triangle}:=\neg\varphi^{\bar s}_{B,*}.
    $$
    For $B=\bigcup_k B_k$, the non-meager union identity gives
    $$\varphi^{\bar s}_{B,*}:=\bigvee_k\varphi^{\bar s}_{B_k,*}.$$
    Apply localization to these newly constructed non-meager formulas to obtain the comeager formulas for $B$.
    Every step uses only the constructors of $\LCountableInfinitaryLogic$ and preserves the finite free-variable context.
    This completes the induction for every Borel set.
-/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    For every Borel $B\IncludedIn\mathrm{Mod}_L$ and every finite $\bar s$, the induction simultaneously constructs formulas
    $\varphi^{\bar s}_{B,*}(\bar x)$ and $\varphi^{\bar s}_{B,\triangle}(\bar x)$ such that
    $$
    \begin{aligned}
    M\models\varphi^{\bar s}_{B,*}(\bar a)
    &\quad\Longleftrightarrow\quad
    \{\sigma\in \TupleAgreementCoset{\bar a}{\bar s}:\sigma\cdot M\in B\}
       \text{ is non-meager in }\TupleAgreementCoset{\bar a}{\bar s},\\
    M\models\varphi^{\bar s}_{B,\triangle}(\bar a)
    &\quad\Longleftrightarrow\quad
    \{\sigma\in \TupleAgreementCoset{\bar a}{\bar s}:\sigma\cdot M\in B\}
       \text{ is comeager in }\TupleAgreementCoset{\bar a}{\bar s}.
    \end{aligned}
    $$
    The same construction allows repeated entries: an empty coset gives a false non-meager condition and a true
    comeager condition. The crucial point is that the coset varies with $\bar a$. Consequently these conditions are
    invariant under the diagonal action on $\mathrm{Mod}_L\times\NN^{|\bar s|}$; a fixed basic group neighborhood would
    not have this invariance.
-/
/-- Simultaneous construction of the two formulas, for every finite target tuple. -/
theorem exists_vaughtFormulas
    [Countable (Σ n, L.Relations n)] [Countable (Σ n, L.Functions n)]
    {A : Set (ModelCode L)} (hA : MeasurableSet A) :
    ∀ n (s : Fin n → ℕ),
      (∃ φ : Formula L n, ∀ M a, φ.Satisfies M a ↔ M ∈ vaughtStar (tupleCoset a s) A) ∧
      (∃ φ : Formula L n, ∀ M a, φ.Satisfies M a ↔ M ∈ vaughtTriangle (tupleCoset a s) A) := by
  induction A, hA using MeasurableSet.induction_on_open with
  | isOpen A hA =>
    intro n s
    exact ⟨exists_open_starFormula hA s,
      exists_triangleFormula_of_star hA.measurableSet (fun _ t => exists_open_starFormula hA t) s⟩
  | compl A hA ih =>
    intro n s
    obtain ⟨⟨φ, hφ⟩, ⟨ψ, hψ⟩⟩ := ih n s
    constructor
    · refine ⟨ψ.neg, fun M a => ?_⟩
      have hd : vaughtStar (tupleCoset a s) Aᶜ = (vaughtTriangle (tupleCoset a s) A)ᶜ := by
        simpa only [compl_compl] using congrArg compl (vaughtStar_compl (tupleCoset a s) Aᶜ)
      rw [hd]
      exact not_congr (hψ M a)
    · refine ⟨φ.neg, fun M a => ?_⟩
      rw [← vaughtStar_compl]
      exact not_congr (hφ M a)
  | iUnion A _ hA ih =>
    have hstar : ∀ n (s : Fin n → ℕ), ∃ φ : Formula L n,
        ∀ M a, φ.Satisfies M a ↔ M ∈ vaughtStar (tupleCoset a s) (⋃ k, A k) := by
      intro n s
      choose φ hφ using fun k => (ih k n s).1
      refine ⟨Formula.disj φ, fun M a => ?_⟩
      change (Formula.disj φ).Realize (M := ModelCarrier L M) a ↔ _
      rw [Formula.realize_disj, vaughtStar_iUnion]
      simp only [mem_iUnion]
      exact exists_congr fun k => hφ k M a
    intro n s
    exact ⟨hstar n s, exists_triangleFormula_of_star (MeasurableSet.iUnion hA) hstar s⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Finally take $\bar s$ empty. Then $\TupleAgreementCoset{\emptyset}{\emptyset}=\InfiniteSymmetricGroup$.
    If $A$ is invariant, the section
    $\{\sigma:\sigma\cdot M\in A\}$ is the whole group when $M\in A$ and empty otherwise. Hence the sentence
    $\varphi^{\emptyset}_{A,\triangle}$ defines precisely $A$.
-/
/-- An invariant section is either the whole permutation group or empty. -/
theorem mem_triangle_univ_iff_of_invariant (A : Set (ModelCode L))
    (hA : ∀ (p : Equiv.Perm ℕ) M, p • M ∈ A ↔ M ∈ A) (M : ModelCode L) :
    M ∈ vaughtTriangle (univ : Set (Equiv.Perm ℕ)) A ↔ M ∈ A := by
  classical
  have hs : relationSection (actionRelation (G := Equiv.Perm ℕ) A) M =
      if M ∈ A then univ else ∅ := by
    ext p
    change (p • M ∈ A) ↔ _
    by_cases h : M ∈ A <;> simp [h, hA p M]
  change IsMeagre ((univ : Set (Equiv.Perm ℕ)) \ relationSection (actionRelation A) M) ↔ _
  rw [hs]
  by_cases h : M ∈ A
  · simpa [h] using (IsMeagre.empty : IsMeagre (∅ : Set (Equiv.Perm ℕ)))
  · simp only [h, ↓reduceIte, sdiff_empty, iff_false]
    exact not_isMeagre_of_isOpen isOpen_univ ⟨1, mem_univ _⟩

/-- Lopez--Escobar: every invariant Borel class is defined by an infinitary sentence. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{Lopez--Escobar theorem}{Lopez--Escobar}] If
-/
theorem exists_sentence_of_borel_invariant
    [Countable (Σ n, L.Relations n)] [Countable (Σ n, L.Functions n)]
    {A : Set (ModelCode L)} (hA : MeasurableSet A)
    (hinv : ∀ (p : Equiv.Perm ℕ) M, p • M ∈ A ↔ M ∈ A) :
    ∃ φ : Sentence L, A = models φ := by
  obtain ⟨φ, hφ⟩ := (exists_vaughtFormulas hA 0 Fin.elim0).2
  refine ⟨φ, ?_⟩
  ext M
  change M ∈ A ↔ φ.Satisfies M Fin.elim0
  rw [hφ]
  have he : tupleCoset Fin.elim0 Fin.elim0 = (univ : Set (Equiv.Perm ℕ)) := by
    ext p
    simp [tupleCoset]
  rw [he]
  exact (mem_triangle_univ_iff_of_invariant A hinv M).symm

end PolishSpaceBook.LopezEscobar
