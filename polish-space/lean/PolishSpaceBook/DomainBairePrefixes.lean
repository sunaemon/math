module

public import PolishSpaceBook.DomainScottTopology
public import PolishSpaceBook.CantorBaireSpace
public import Mathlib.Data.Seq.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-! # The Baire prefix domain

The canonical possibly infinite sequence type represents finite words and Baire
points uniformly. Its information order preserves every already defined entry.
Directed suprema are the compatible unions of those entries.
-/
namespace PolishSpaceBook
open Set Topology Stream'

abbrev BairePrefixDomain := Stream'.Seq ℕ

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Baire prefix domain
-/
instance bairePrefixOrder : PartialOrder BairePrefixDomain where
  le x y := ∀ n a, x.get? n = some a → y.get? n = some a
  le_refl _ _ _ h := h
  le_trans _ _ _ hxy hyz n a h := hyz n a (hxy n a h)
  le_antisymm x y hxy hyx := by
    apply Seq.ext
    intro n
    cases hx : x.get? n with
    | none =>
      cases hy : y.get? n with
      | none => rfl
      | some a => have h := hyx n a hy; simp [hx] at h
    | some a => exact (hxy n a hx).symm

instance bairePrefixOrderBot : OrderBot BairePrefixDomain where
  bot := Seq.nil
  bot_le _ _ _ h := by cases h

theorem baire_compatible_entries {S : Set BairePrefixDomain} (hd : DirectedOn (· ≤ ·) S)
    {x y : BairePrefixDomain} (hx : x ∈ S) (hy : y ∈ S) {n a b : ℕ}
    (ha : x.get? n = some a) (hb : y.get? n = some b) : a = b := by
  obtain ⟨z,_,hxz,hyz⟩ := hd x hx y hy
  exact Option.some.inj ((hxz n a ha).symm.trans (hyz n b hb))

noncomputable def baireUnionEntry (S : Set BairePrefixDomain) (n : ℕ) : Option ℕ := by
  classical
  exact if h : ∃ a, ∃ x ∈ S, x.get? n = some a then some h.choose else none

theorem baireUnionEntry_some_iff {S : Set BairePrefixDomain} (hd : DirectedOn (· ≤ ·) S) (n a : ℕ) :
    baireUnionEntry S n = some a ↔ ∃ x ∈ S, x.get? n = some a := by
  classical
  unfold baireUnionEntry
  split_ifs with h
  · obtain ⟨x,hx,hxa⟩ := h.choose_spec
    constructor
    · intro he
      exact ⟨x,hx,Option.some.inj he ▸ hxa⟩
    · rintro ⟨y,hy,hya⟩
      exact congrArg some (baire_compatible_entries hd hx hy hxa hya)
  · constructor
    · intro he; cases he
    · intro he; exact False.elim (h ⟨a,he⟩)

noncomputable def baireDirectedUnion (S : Set BairePrefixDomain) (hd : DirectedOn (· ≤ ·) S) : BairePrefixDomain :=
  ⟨baireUnionEntry S,by
    intro n hn
    cases he : baireUnionEntry S (n+1) with
    | none => rfl
    | some a =>
      obtain ⟨x,hx,hxa⟩ := (baireUnionEntry_some_iff hd (n+1) a).mp he
      obtain ⟨b,hxb⟩ := x.ge_stable (Nat.le_succ n) hxa
      have h := (baireUnionEntry_some_iff hd n b).mpr ⟨x,hx,hxb⟩
      rw [hn] at h
      cases h⟩

theorem baireDirectedUnion_get {S : Set BairePrefixDomain} (hd : DirectedOn (· ≤ ·) S) (n a : ℕ) :
    (baireDirectedUnion S hd).get? n = some a ↔ ∃ x ∈ S, x.get? n = some a :=
  baireUnionEntry_some_iff hd n a

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Baire prefix domain
-/
theorem baireDirectedUnion_isLUB (S : Set BairePrefixDomain) (hd : DirectedOn (· ≤ ·) S) :
    IsLUB S (baireDirectedUnion S hd) := by
  constructor
  · intro x hx n a ha
    exact (baireDirectedUnion_get hd n a).mpr ⟨x,hx,ha⟩
  · intro y hy n a ha
    obtain ⟨x,hx,hxa⟩ := (baireDirectedUnion_get hd n a).mp ha
    exact hy hx n a hxa

noncomputable instance bairePrefixSupSet : SupSet BairePrefixDomain where
  sSup S := by
    classical
    exact if hd : DirectedOn (· ≤ ·) S then baireDirectedUnion S hd else ⊥

noncomputable instance bairePrefixCompletePartialOrder : CompletePartialOrder BairePrefixDomain where
  lubOfDirected S hd := by
    classical
    change IsLUB S (if h : DirectedOn (· ≤ ·) S then baireDirectedUnion S h else ⊥)
    simpa only [dite_eq_left hd] using baireDirectedUnion_isLUB S hd

/-- Every element is either a finite word or an infinite branch. -/
theorem bairePrefix_cases (x : BairePrefixDomain) :
    (∃ s : List ℕ, x = Seq.ofList s) ∨ ∃ y : ℕ → ℕ, x = Seq.ofStream y := by
  classical
  by_cases h : x.Terminates
  · exact Or.inl ⟨x.toList h,(Seq.ofList_toList x h).symm⟩
  · refine Or.inr ⟨x.toStream h,?_⟩
    apply Seq.ext
    intro n
    change x.get? n = some ((x.get? n).get _)
    exact (Option.some_get _).symm

/-- Any finite amount of a directed union's information is already present in one member. -/
theorem baire_union_finite_stage {S : Set BairePrefixDomain} (hne : S.Nonempty)
    (hd : DirectedOn (· ≤ ·) S) (n : ℕ) :
    ∃ x ∈ S, ∀ k < n, ∀ a, (baireDirectedUnion S hd).get? k = some a → x.get? k = some a := by
  induction n with
  | zero => obtain ⟨x,hx⟩ := hne; exact ⟨x,hx,by omega⟩
  | succ n ih =>
    obtain ⟨x,hx,hxp⟩ := ih
    cases he : (baireDirectedUnion S hd).get? n with
    | none =>
      refine ⟨x,hx,?_⟩
      intro k hk a ha
      by_cases hkn : k < n
      · exact hxp k hkn a ha
      · have : k = n := by omega
        subst k
        simp [he] at ha
    | some b =>
      obtain ⟨y,hy,hyb⟩ := (baireDirectedUnion_get hd n b).mp he
      obtain ⟨z,hz,hxz,hyz⟩ := hd x hx y hy
      refine ⟨z,hz,?_⟩
      intro k hk a ha
      by_cases hkn : k < n
      · exact hxz k a (hxp k hkn a ha)
      · have : k = n := by omega
        subst k
        have hab : b = a := Option.some.inj (he.symm.trans ha)
        exact hab ▸ hyz n b hyb

def baireTruncation (x : BairePrefixDomain) (n : ℕ) : BairePrefixDomain := Seq.ofList (x.take n)

theorem baireTruncation_le (x : BairePrefixDomain) (n : ℕ) : baireTruncation x n ≤ x := by
  intro k a ha
  simp only [baireTruncation,Seq.ofList_get?,Seq.getElem?_take] at ha
  split_ifs at ha with hk
  exact ha


theorem baireTruncation_mono (x : BairePrefixDomain) : Monotone (baireTruncation x) := by
  intro m n hmn k a ha
  simp only [baireTruncation,Seq.ofList_get?,Seq.getElem?_take] at ha ⊢
  split_ifs at ha with hm
  rw [ite_eq_left (hm.trans_le hmn)]
  exact ha


theorem baireTruncations_isLUB (x : BairePrefixDomain) : IsLUB (range (baireTruncation x)) x := by
  constructor
  · rintro _ ⟨n,rfl⟩
    exact baireTruncation_le x n
  · intro y hy n a ha
    apply hy ⟨n+1,rfl⟩ n a
    simpa only [baireTruncation,Seq.ofList_get?,Seq.getElem?_take,ite_eq_left (Nat.lt_succ_self n)] using ha

theorem baireTruncations_directed (x : BairePrefixDomain) : DirectedOn (· ≤ ·) (range (baireTruncation x)) := by
  rintro _ ⟨m,rfl⟩ _ ⟨n,rfl⟩
  exact ⟨_,⟨max m n,rfl⟩,baireTruncation_mono x (le_max_left _ _),baireTruncation_mono x (le_max_right _ _)⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Baire prefix domain
-/
theorem baire_finite_wayBelow_iff (s : List ℕ) (x : BairePrefixDomain) :
    DomainWayBelow (Seq.ofList s) x ↔ Seq.ofList s ≤ x := by
  refine ⟨domainWayBelow_le,?_⟩
  intro hs S L hne hd hL hxL
  have hsL := hs.trans hxL
  rw [hL.unique (baireDirectedUnion_isLUB S hd)] at hsL
  obtain ⟨y,hy,hyp⟩ := baire_union_finite_stage hne hd s.length
  refine ⟨y,hy,?_⟩
  intro n a ha
  by_cases hn : n < s.length
  · exact hyp n hn a (hsL n a ha)
  · have hh : (Seq.ofList s).get? n = none := by simpa using List.getElem?_eq_none (Nat.le_of_not_gt hn)
    simp [hh] at ha

theorem baire_finite_le_iff (s : List ℕ) (x : BairePrefixDomain) :
    Seq.ofList s ≤ x ↔ ∀ n (hn : n < s.length), x.get? n = some s[n] := by
  constructor
  · intro h n hn
    exact h n s[n] (List.getElem?_eq_getElem hn)
  · intro h n a ha
    by_cases hn : n < s.length
    · have he := List.getElem?_eq_getElem hn
      have heq : s[n] = a := Option.some.inj (he.symm.trans ha)
      exact heq ▸ h n hn
    · have hh := List.getElem?_eq_none (l := s) (Nat.le_of_not_gt hn)
      change s[n]? = some a at ha
      rw [hh] at ha
      cases ha

theorem baire_finite_le_finite_iff (s t : List ℕ) :
    Seq.ofList s ≤ Seq.ofList t ↔ s <+: t := by
  rw [baire_finite_le_iff,List.prefix_iff_getElem?]
  rfl

@[simp] theorem baire_branch_get (x : ℕ → ℕ) (n : ℕ) : (Seq.ofStream x).get? n = some (x n) := rfl

theorem baire_finite_le_branch_iff (s : List ℕ) (x : ℕ → ℕ) :
    Seq.ofList s ≤ Seq.ofStream x ↔ x ∈ cyl s := by
  rw [baire_finite_le_iff]
  constructor
  · intro h n hn
    exact Option.some.inj (h n hn)
  · intro h n hn
    exact congrArg some (h n hn)

theorem baire_finite_eq_take {s : List ℕ} {x : BairePrefixDomain} (h : Seq.ofList s ≤ x) :
    s = x.take s.length := by
  apply List.ext_getElem?
  intro n
  rw [Seq.getElem?_take]
  by_cases hn : n < s.length
  · rw [ite_eq_left hn,List.getElem?_eq_getElem hn]
    exact ((baire_finite_le_iff s x).mp h n hn).symm
  · rw [ite_eq_right hn]
    exact List.getElem?_eq_none (Nat.le_of_not_gt hn)

theorem baire_le_finite_is_finite {x : BairePrefixDomain} {s : List ℕ} (h : x ≤ Seq.ofList s) :
    ∃ t : List ℕ, x = Seq.ofList t := by
  have hn : x.get? s.length = none := by
    cases he : x.get? s.length with
    | none => rfl
    | some a =>
      have hh := h s.length a he
      simp only [Seq.ofList_get?,List.getElem?_length] at hh
      cases hh
  have ht : x.Terminates := ⟨s.length,hn⟩
  exact ⟨x.toList ht,(Seq.ofList_toList x ht).symm⟩

theorem baire_wayBelow_iff (x y : BairePrefixDomain) :
    DomainWayBelow x y ↔ ∃ s : List ℕ, x = Seq.ofList s ∧ Seq.ofList s ≤ y := by
  constructor
  · intro h
    obtain ⟨z,⟨n,rfl⟩,hxz⟩ := h _ _ (range_nonempty _) (baireTruncations_directed y)
      (baireTruncations_isLUB y) le_rfl
    obtain ⟨s,rfl⟩ := baire_le_finite_is_finite hxz
    exact ⟨s,rfl,domainWayBelow_le h⟩
  · rintro ⟨s,rfl,hs⟩
    exact (baire_finite_wayBelow_iff s y).mpr hs

def baireFiniteBasis : Set BairePrefixDomain := range Seq.ofList

theorem baireFiniteBasis_approximants (x : BairePrefixDomain) :
    baireFiniteBasis ∩ {a | DomainWayBelow a x} = range (baireTruncation x) := by
  ext a
  constructor
  · rintro ⟨⟨s,rfl⟩,hs⟩
    refine ⟨s.length,?_⟩
    exact congrArg Seq.ofList (baire_finite_eq_take (domainWayBelow_le hs)).symm
  · rintro ⟨n,rfl⟩
    exact ⟨⟨x.take n,rfl⟩,(baire_finite_wayBelow_iff _ _).mpr (baireTruncation_le x n)⟩

theorem baireFiniteBasis_isBasis : IsDomainBasis baireFiniteBasis := by
  intro x
  rw [baireFiniteBasis_approximants]
  exact ⟨range_nonempty _,baireTruncations_directed x,baireTruncations_isLUB x⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Baire prefix domain
-/
theorem baire_countable_basis : baireFiniteBasis.Countable ∧ IsDomainBasis baireFiniteBasis :=
  ⟨countable_range _,baireFiniteBasis_isBasis⟩

theorem baire_branch_isMax (x : ℕ → ℕ) : IsMax (Seq.ofStream x : BairePrefixDomain) := by
  intro y hy n a ha
  have hn : y.get? n = some (x n) := hy n (x n) rfl
  exact hn.symm.trans ha

theorem baire_finite_not_isMax (s : List ℕ) : ¬ IsMax (Seq.ofList s : BairePrefixDomain) := by
  intro h
  have hle : Seq.ofList s ≤ Seq.ofList (s ++ [0]) :=
    (baire_finite_le_finite_iff _ _).mpr (List.prefix_append _ _)
  have hget : (Seq.ofList (s ++ [0])).get? s.length = some 0 := by
    change (s ++ [0])[s.length]? = some 0
    simp
  have hh := h hle s.length 0 hget
  simp only [Seq.ofList_get?,List.getElem?_length] at hh
  cases hh

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Baire prefix domain
-/
theorem baire_isMax_iff (x : BairePrefixDomain) : IsMax x ↔ ∃ y : ℕ → ℕ, x = Seq.ofStream y := by
  constructor
  · intro h
    rcases bairePrefix_cases x with ⟨s,rfl⟩ | hinf
    · exact False.elim (baire_finite_not_isMax s h)
    · exact hinf
  · rintro ⟨y,rfl⟩
    exact baire_branch_isMax y

theorem baire_directed_branch_isGreatest {S : Set BairePrefixDomain} (hd : DirectedOn (· ≤ ·) S)
    {x : ℕ → ℕ} (hx : Seq.ofStream x ∈ S) : IsGreatest S (Seq.ofStream x) := by
  refine ⟨hx,?_⟩
  intro y hy
  obtain ⟨z,_,hxz,hyz⟩ := hd _ hx y hy
  exact hyz.trans (baire_branch_isMax x hxz)

theorem baire_directed_union_bounded {S : Set BairePrefixDomain} (hd : DirectedOn (· ≤ ·) S) (N : ℕ)
    (hb : ∀ x ∈ S, ∃ s : List ℕ, s.length ≤ N ∧ x = Seq.ofList s) :
    ∃ s : List ℕ, s.length ≤ N ∧ baireDirectedUnion S hd = Seq.ofList s := by
  have hn : (baireDirectedUnion S hd).get? N = none := by
    cases he : (baireDirectedUnion S hd).get? N with
    | none => rfl
    | some a =>
      obtain ⟨x,hx,hxa⟩ := (baireDirectedUnion_get hd N a).mp he
      obtain ⟨s,hs,rfl⟩ := hb x hx
      change s[N]? = some a at hxa
      rw [List.getElem?_eq_none hs] at hxa
      cases hxa
  refine ⟨(baireDirectedUnion S hd).take N,Seq.length_take_le,?_⟩
  apply Seq.ext
  intro n
  rw [Seq.ofList_get?,Seq.getElem?_take]
  by_cases h : n < N
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact (baireDirectedUnion S hd).le_stable (Nat.le_of_not_gt h) hn

theorem baire_directed_union_unbounded {S : Set BairePrefixDomain} (hd : DirectedOn (· ≤ ·) S)
    (hu : ∀ N, ∃ s : List ℕ, Seq.ofList s ∈ S ∧ N < s.length) :
    ∃ x : ℕ → ℕ, baireDirectedUnion S hd = Seq.ofStream x := by
  rcases bairePrefix_cases (baireDirectedUnion S hd) with ⟨s,hs⟩ | hinf
  · obtain ⟨t,ht,hst⟩ := hu s.length
    have h := (baireDirectedUnion_get hd s.length t[s.length]).mpr
      ⟨Seq.ofList t,ht,List.getElem?_eq_getElem hst⟩
    rw [hs,Seq.ofList_get?,List.getElem?_length] at h
    cases h
  · exact hinf

/-- Include a Baire point as a total element of the prefix domain. -/
def baireBranch (x : ℕ → ℕ) : BairePrefixDomain := Seq.ofStream x

section Scott
local instance bairePrefixScottTopology : TopologicalSpace BairePrefixDomain :=
  Topology.scott BairePrefixDomain univ
local instance bairePrefixIsScott : Topology.IsScott BairePrefixDomain univ := ⟨rfl⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Baire prefix domain
-/
theorem baire_scott_open_iff (U : Set BairePrefixDomain) :
    IsOpen U ↔ ∀ x ∈ U, ∃ s : List ℕ, Seq.ofList s ≤ x ∧ Ici (Seq.ofList s) ⊆ U := by
  constructor
  · intro hU x hx
    obtain ⟨hu,hi⟩ := (domain_scott_open_iff U).mp hU
    obtain ⟨y,⟨n,rfl⟩,hy⟩ := hi (range_nonempty _) (baireTruncations_directed x) (baireTruncations_isLUB x) hx
    exact ⟨x.take n,baireTruncation_le x n,fun z hz => hu hz hy⟩
  · intro h
    apply (domain_scott_open_iff U).mpr
    constructor
    · intro x y hxy hx
      obtain ⟨s,hs,hsU⟩ := h x hx
      exact hsU (hs.trans hxy)
    · intro S hne hd x hx hxU
      obtain ⟨s,hs,hsU⟩ := h x hxU
      obtain ⟨y,hy,hsy⟩ := (baire_finite_wayBelow_iff s x).mpr hs S x hne hd hx le_rfl
      exact ⟨y,hy,hsU hsy⟩

theorem baire_finite_upper_isOpen (s : List ℕ) : IsOpen (Ici (Seq.ofList s) : Set BairePrefixDomain) := by
  apply (baire_scott_open_iff _).mpr
  intro x hx
  exact ⟨s,hx,subset_rfl⟩

theorem baire_branch_preimage_upper (s : List ℕ) :
    baireBranch ⁻¹' Ici (Seq.ofList s) = cyl s := by
  ext x
  exact baire_finite_le_branch_iff s x

theorem baire_branch_continuous : Continuous baireBranch := by
  apply continuous_def.mpr
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨s,hs,hsU⟩ := (baire_scott_open_iff U).mp hU _ hx
  have hxS := (baire_finite_le_branch_iff s x).mp hs
  apply Filter.mem_of_superset ((isOpen_cyl s).mem_nhds hxS)
  intro y hy
  exact hsU ((baire_finite_le_branch_iff s y).mpr hy)

def baireScottLift (U : Set (ℕ → ℕ)) : Set BairePrefixDomain :=
  {x | ∃ s : List ℕ, Seq.ofList s ≤ x ∧ cyl s ⊆ U}

theorem baireScottLift_isOpen (U : Set (ℕ → ℕ)) : IsOpen (baireScottLift U) := by
  apply (baire_scott_open_iff _).mpr
  rintro x ⟨s,hs,hsU⟩
  exact ⟨s,hs,fun y hy => ⟨s,hy,hsU⟩⟩

theorem baireScottLift_preimage {U : Set (ℕ → ℕ)} (hU : IsOpen U) :
    baireBranch ⁻¹' baireScottLift U = U := by
  ext x
  constructor
  · rintro ⟨s,hs,hsU⟩
    exact hsU ((baire_finite_le_branch_iff s x).mp hs)
  · intro hx
    obtain ⟨s,hxs,hsU⟩ := exists_cyl_subset_of_mem_open hx hU
    exact ⟨s,(baire_finite_le_branch_iff s x).mpr hxs,hsU⟩

theorem baire_branch_isEmbedding : Topology.IsEmbedding baireBranch := by
  constructor
  · constructor
    apply TopologicalSpace.ext
    funext U
    apply propext
    rw [isOpen_induced_iff]
    constructor
    · intro hU
      exact ⟨baireScottLift U,baireScottLift_isOpen U,baireScottLift_preimage hU⟩
    · rintro ⟨V,hV,rfl⟩
      exact hV.preimage baire_branch_continuous
  · intro x y h
    funext n
    exact Option.some.inj (congrArg (fun z : BairePrefixDomain => z.get? n) h)

theorem range_baire_branch : range baireBranch = {x | IsMax x} := by
  ext x
  simp only [mem_range,mem_ofPred_eq,baire_isMax_iff]
  exact exists_congr (fun y => eq_comm)

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Baire prefix domain
-/
noncomputable def baireMaximalHomeomorph : (ℕ → ℕ) ≃ₜ {x : BairePrefixDomain // IsMax x} :=
  baire_branch_isEmbedding.toHomeomorph.trans (Homeomorph.setCongr range_baire_branch)

@[simp] theorem baireMaximalHomeomorph_apply (x : ℕ → ℕ) :
    (baireMaximalHomeomorph x).val = Seq.ofStream x := rfl

end Scott

end PolishSpaceBook
