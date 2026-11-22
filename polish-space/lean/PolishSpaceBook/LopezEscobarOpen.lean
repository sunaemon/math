module

public import PolishSpaceBook.LopezEscobarBasic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # From finite coordinate diagrams to arbitrary open sets

Enlarge finite variable contexts, intersect finite diagrams, and use the
finite-coordinate neighborhood basis of the logic space. Second countability
then gives the countable union needed for open nonmeager transforms.
-/

namespace PolishSpaceBook.LopezEscobar

open Set Topology TopologicalSpace Filter LogicActions InfinitaryLogic
open scoped PointwisePerm

variable {L : FirstOrder.Language}

/-- Reindex the variables of a coordinate condition. -/
def CoordinateAtom.rename {m n} (f : Fin m → Fin n) : CoordinateAtom L m → CoordinateAtom L n
  | .rel r args value => .rel r (f ∘ args) value
  | .func g args out => .func g (f ∘ args) (f out)

theorem CoordinateAtom.holds_rename {m n} (c : CoordinateAtom L m) (f : Fin m → Fin n)
    (M : ModelCode L) (t : Fin n → ℕ) :
    (c.rename f).Holds M t ↔ c.Holds M (t ∘ f) := by cases c <;> rfl

/-- Reindex all variables in a finite diagram. -/
def Diagram.rename {m n} (d : Diagram L m) (f : Fin m → Fin n) : Diagram L n :=
  d.map (CoordinateAtom.rename f)

theorem Diagram.mem_set_iff {m} (d : Diagram L m) (M : ModelCode L) (t : Fin m → ℕ) :
    M ∈ d.set t ↔ ∀ c ∈ d, c.Holds M t := by
  simp only [Diagram.set, mem_ofPred_eq]
  constructor
  · intro h c hc
    obtain ⟨i, hi⟩ := List.get_of_mem hc
    exact hi ▸ h i
  · intro h i
    exact h _ (List.get_mem d i)

theorem Diagram.set_rename {m n} (d : Diagram L m) (f : Fin m → Fin n) (t : Fin n → ℕ) :
    (d.rename f).set t = d.set (t ∘ f) := by
  ext M
  simp [Diagram.mem_set_iff, Diagram.rename, CoordinateAtom.holds_rename]

theorem Diagram.set_append {m} (d e : Diagram L m) (t : Fin m → ℕ) :
    (d ++ e).set t = d.set t ∩ e.set t := by
  ext M
  simp [Diagram.mem_set_iff, or_imp, forall_and]

/-- A cylinder represented by a finite diagram with the distinct names `0,...,m-1`. -/
def DiagramCylinder (B : Set (ModelCode L)) : Prop :=
  ∃ m, ∃ d : Diagram L m, B = d.set Fin.val

theorem DiagramCylinder.univ : DiagramCylinder (univ : Set (ModelCode L)) := by
  refine ⟨0, [], ?_⟩
  ext M
  simp [Diagram.mem_set_iff]

theorem DiagramCylinder.inter {B C : Set (ModelCode L)}
    (hB : DiagramCylinder B) (hC : DiagramCylinder C) : DiagramCylinder (B ∩ C) := by
  obtain ⟨m, d, rfl⟩ := hB
  obtain ⟨n, e, rfl⟩ := hC
  refine ⟨max m n, d.rename (Fin.castLE (Nat.le_max_left m n)) ++
    e.rename (Fin.castLE (Nat.le_max_right m n)), ?_⟩
  simp only [Diagram.set_append, Diagram.set_rename]
  rfl

theorem DiagramCylinder.biInter {ι : Type*} (F : Finset ι) (B : ι → Set (ModelCode L))
    (hB : ∀ i ∈ F, DiagramCylinder (B i)) : DiagramCylinder (⋂ i ∈ F, B i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (DiagramCylinder.univ (L := L))
  | @insert i F hi ih =>
    simp only [Finset.mem_insert, iInter_iInter_eq_or_left]
    exact (hB i (Finset.mem_insert_self i F)).inter
      (ih fun j hj => hB j (Finset.mem_insert_of_mem hj))

/-- Every relation-table coordinate condition has a finite-diagram representation. -/
theorem DiagramCylinder.rel (r : RelIndex L) (value : Bool) :
    DiagramCylinder {M : ModelCode L | M.1 r = value} := by
  obtain ⟨b, hb⟩ := (Set.finite_range r.2).bddAbove
  let args : Fin r.1.1 → Fin (b + 1) := fun i => ⟨r.2 i, Nat.lt_succ_of_le (hb (mem_range_self i))⟩
  refine ⟨b + 1, [.rel r.1.2 args value], ?_⟩
  ext M
  simp only [Diagram.mem_set_iff, List.mem_singleton, forall_eq]
  rfl

/-- Function outputs must be included among the finitely many named values. -/
theorem DiagramCylinder.func (f : FunIndex L) (value : ℕ) :
    DiagramCylinder {M : ModelCode L | M.2 f = value} := by
  obtain ⟨b, hb⟩ := (Set.finite_range f.2).bddAbove
  let m := max b value + 1
  let args : Fin f.1.1 → Fin m := fun i =>
    ⟨f.2 i, Nat.lt_succ_of_le ((hb (mem_range_self i)).trans (Nat.le_max_left b value))⟩
  let out : Fin m := ⟨value, Nat.lt_succ_of_le (Nat.le_max_right b value)⟩
  refine ⟨m, [.func f.1.2 args out], ?_⟩
  ext M
  simp only [Diagram.mem_set_iff, List.mem_singleton, forall_eq]
  rfl

/-- A neighborhood in a product of discrete spaces contains a finite agreement cylinder. -/
theorem exists_finite_agreement {ι A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (x : ι → A) {U : Set (ι → A)} (hU : U ∈ 𝓝 x) :
    ∃ F : Finset ι, {y | ∀ i ∈ F, y i = x i} ⊆ U := by
  classical
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨F, V, hV, hFU⟩ := hU
  refine ⟨F, fun y hy => hFU ?_⟩
  intro i hi
  change y i ∈ V i
  rw [hy i hi]
  exact mem_of_mem_nhds (hV i)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Finite coordinate diagrams form a basis for the logic space. To see this, take a neighborhood of a structure.
    It contains a neighborhood fixing finitely many relation-table and function-table entries. Choose a natural number
    $m$ larger than every value in their argument tuples and every specified function output. All these conditions
    then use names below $m$ and form a finite diagram. Enlarging the range of names merely renames its variables;
    after placing two diagrams in a common range, their intersection is represented by concatenating their lists of
    conditions. Each diagram defines a clopen set.
-/
/-- Finite diagrams are a basis for the full relation/function-table topology. -/
theorem isTopologicalBasis_diagrams : IsTopologicalBasis {B : Set (ModelCode L) | DiagramCylinder B} := by
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro B ⟨m, d, rfl⟩
    exact (d.isClopen_set Fin.val).isOpen
  · intro M U hM hU
    have hn := hU.mem_nhds hM
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hn
    obtain ⟨V, hV, W, hW, hVW⟩ := hn
    obtain ⟨F, hF⟩ := exists_finite_agreement M.1 hV
    obtain ⟨H, hH⟩ := exists_finite_agreement M.2 hW
    let B : Set (ModelCode L) :=
      (⋂ i ∈ F, {N | N.1 i = M.1 i}) ∩ (⋂ j ∈ H, {N | N.2 j = M.2 j})
    refine ⟨B, ?_, ?_, ?_⟩
    · exact (DiagramCylinder.biInter F _ (fun i _ => DiagramCylinder.rel i (M.1 i))).inter
        (DiagramCylinder.biInter H _ (fun j _ => DiagramCylinder.func j (M.2 j)))
    · simp [B]
    · intro N hN
      have hN' : (∀ i ∈ F, N.1 i = M.1 i) ∧ (∀ j ∈ H, N.2 j = M.2 j) := by
        simpa only [B, mem_inter_iff, mem_iInter, mem_ofPred_eq] using hN
      exact hVW ⟨hF hN'.1, hH hN'.2⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Since $\mathrm{Mod}_L$ is second countable, every open set $U$ is a countable union of such cylinders:
    $$U=\bigcup_{j\in J}D_j,$$
    where $J$ is countable and may be empty. For a fixed target tuple $\bar s$, enlarge the name range of each diagram
    to include all entries of $\bar s$. Thus $D_j$ is defined by a formula $\psi_j$ at the tuple
    $\bar t_j=\Sequence{r}{r<m_j}$, and we may regard $e_j(i)=s_i$ as an index below $m_j$.
    The formula for the open non-meager transform is
    $$
    \varphi^{\bar s}_{U,*}(\bar x)
    :=\bigvee_{j\in J}\InverseTupleFormula{e_j}{\psi_j}(\bar x).
    $$
    The empty disjunction is false. A disjunction over any countable $J$ can be written as one indexed by $\omega$,
    putting $\bot$ at unused indices. Although the finite blocks of bound variables may have different lengths,
    each disjunct has the same original finite context of free variables.
-/
/-- Every open set is a countable union of finite-diagram cylinders, including the empty union. -/
theorem open_eq_countable_union_diagrams
    [Countable (Σ n, L.Relations n)] [Countable (Σ n, L.Functions n)]
    {U : Set (ModelCode L)} (hU : IsOpen U) :
    ∃ S : Set (Set (ModelCode L)), S.Countable ∧ (∀ B ∈ S, DiagramCylinder B) ∧ U = ⋃ B ∈ S, B := by
  obtain ⟨S, hS, hc, he⟩ := isTopologicalBasis_diagrams.exists_countable_biUnion_of_isOpen hU
  exact ⟨S, hc, hS, he⟩

/-- A cylinder can use a name range containing any prescribed finite target tuple. -/
theorem DiagramCylinder.exists_starFormula {B : Set (ModelCode L)} (hB : DiagramCylinder B)
    {n} (s : Fin n → ℕ) :
    ∃ φ : Formula L n, ∀ M a, φ.Satisfies M a ↔ M ∈ vaughtStar (tupleCoset a s) B := by
  obtain ⟨m, d, rfl⟩ := hB
  obtain ⟨b, hb⟩ := (Set.finite_range s).bddAbove
  let k := max m (b + 1)
  let d' := d.rename (Fin.castLE (Nat.le_max_left m (b + 1)))
  let e : Fin n → Fin k := fun i =>
    ⟨s i, (Nat.lt_succ_of_le (hb (mem_range_self i))).trans_le (Nat.le_max_right m (b + 1))⟩
  refine ⟨extensionFormula e d'.formula, ?_⟩
  intro M a
  have hd : d'.set Fin.val = d.set Fin.val := by
    simp only [d', Diagram.set_rename]
    rfl
  have h := d'.extensionFormula_iff_star e Fin.val Fin.val_injective M a
  rw [hd] at h
  exact h

/-- Disjunction over an arbitrary countable index type, with false at unused natural-number indices. -/
noncomputable def countableDisj {ι : Type*} [Countable ι] {n}
    (φ : ι → Formula L n) : Formula L n :=
  letI := Encodable.ofCountable ι
  Formula.disj fun k => match Encodable.decode (α := ι) k with
    | none => .falsum
    | some i => φ i

theorem realize_countableDisj {ι : Type*} [Countable ι] {M : Type*} [L.Structure M] {n}
    (φ : ι → Formula L n) (a : Fin n → M) :
    (countableDisj φ).Realize a ↔ ∃ i, (φ i).Realize a := by
  classical
  let := Encodable.ofCountable ι
  change (Formula.disj fun k => match Encodable.decode (α := ι) k with
    | none => Formula.falsum | some i => φ i).Realize a ↔ _
  rw [Formula.realize_disj]
  constructor
  · rintro ⟨k, hk⟩
    cases h : Encodable.decode (α := ι) k with
    | none => simp [h, Formula.Realize] at hk
    | some i => exact ⟨i, by simpa only [h] using hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨Encodable.encode i, by simpa using hi⟩

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Indeed, the section of $U$ inside $\TupleAgreementCoset{\bar a}{\bar s}$ is open, so it is non-meager exactly when
    some permutation in this coset sends $M$ into $U$. Such a permutation sends $M$ into some $D_j$, and the preceding
    finite-diagram construction expresses precisely this condition by $\InverseTupleFormula{e_j}{\psi_j}(\bar a)$.
    Conversely, any disjunct supplies a permutation sending $M$ into $D_j\IncludedIn U$.
    This proves the asserted interpretation of $\varphi^{\bar s}_{U,*}$.
    For a closed set $C$, duality gives
    $$\varphi^{\bar s}_{C,\triangle}(\bar x):=\neg\varphi^{\bar s}_{\complement C,*}(\bar x).$$
-/
/-- The nonmeager transform of any open set is given by a formula in the original finite context. -/
theorem exists_open_starFormula
    [Countable (Σ n, L.Relations n)] [Countable (Σ n, L.Functions n)]
    {U : Set (ModelCode L)} (hU : IsOpen U) {n} (s : Fin n → ℕ) :
    ∃ φ : Formula L n, ∀ M a, φ.Satisfies M a ↔ M ∈ vaughtStar (tupleCoset a s) U := by
  classical
  obtain ⟨S, hc, hS, hUnion⟩ := open_eq_countable_union_diagrams hU
  let : Countable S := hc.to_subtype
  choose φ hφ using fun B : S => (hS B.val B.property).exists_starFormula s
  refine ⟨countableDisj φ, ?_⟩
  intro M a
  change (countableDisj φ).Realize (M := ModelCarrier L M) a ↔ _
  rw [realize_countableDisj, vaughtStar_open_eq (isClopen_tupleCoset a s).isOpen hU]
  constructor
  · rintro ⟨B, hB⟩
    have hMB := (hφ B M a).mp hB
    obtain ⟨m, d, hd⟩ := hS B.val B.property
    have ho : IsOpen B.val := hd ▸ (d.isClopen_set Fin.val).isOpen
    rw [vaughtStar_open_eq (isClopen_tupleCoset a s).isOpen ho] at hMB
    obtain ⟨p, hp, hPB⟩ := hMB
    refine ⟨p, hp, ?_⟩
    rw [hUnion]
    exact mem_iUnion.mpr ⟨B.val, mem_iUnion.mpr ⟨B.property, hPB⟩⟩
  · rintro ⟨p, hp, hPU⟩
    rw [hUnion] at hPU
    obtain ⟨B, hB'⟩ := mem_iUnion.mp hPU
    obtain ⟨hB, hPB⟩ := mem_iUnion.mp hB'
    obtain ⟨m, d, hd⟩ := hS B hB
    have ho : IsOpen B := hd ▸ (d.isClopen_set Fin.val).isOpen
    refine ⟨⟨B, hB⟩, (hφ ⟨B, hB⟩ M a).mpr ?_⟩
    rw [vaughtStar_open_eq (isClopen_tupleCoset a s).isOpen ho]
    exact ⟨p, hp, hPB⟩

/-- Complement duality gives a formula for the comeager transform of every closed set. -/
theorem exists_closed_triangleFormula
    [Countable (Σ n, L.Relations n)] [Countable (Σ n, L.Functions n)]
    {C : Set (ModelCode L)} (hC : IsClosed C) {n} (s : Fin n → ℕ) :
    ∃ φ : Formula L n, ∀ M a, φ.Satisfies M a ↔ M ∈ vaughtTriangle (tupleCoset a s) C := by
  obtain ⟨φ, hφ⟩ := exists_open_starFormula hC.isOpen_compl s
  refine ⟨φ.neg, fun M a => ?_⟩
  have hd := vaughtStar_compl (tupleCoset a s) Cᶜ
  rw [compl_compl] at hd
  rw [← hd]
  exact not_congr (hφ M a)

end PolishSpaceBook.LopezEscobar
