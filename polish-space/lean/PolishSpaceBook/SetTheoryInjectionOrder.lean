module

public import PolishSpaceBook.SetTheoryOrdinalIsoFormulas

@[expose] public section

/-! # Transporting membership through an internal injection -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

private lemma pair_coordinates_mem {M f a b : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (hf : f ∈ M) (hp : pair a b ∈ f) : a ∈ M ∧ b ∈ M := by
  have hB := union_mem hM hunion (union_mem hM hunion hf)
  exact ⟨hM.mem_trans (first_mem_doubleUnion hp) hB, hM.mem_trans (second_mem_doubleUnion hp) hB⟩

private lemma realize_pair_model {M : ZFSet.{u}} (hM : M.IsTransitive) {n : ℕ}
    (q a b : Fin n) (xs : Fin n → M) :
    (orderedPairFormula q a b).Realize Empty.elim xs ↔ (xs q).val = pair (xs a).val (xs b).val :=
  realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) q a b xs

/-- Parameters f,q; q is a reversed pair from f. -/
def reversePairFormula : ForcingFormulas.Formula 2 :=
  (orderedPairFormula (1 : Fin 4) 2 3 ⊓ pairMemberFormula 0 3 2).ex.ex

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    For complete first-order formulas, replace each displayed ordered pair by a variable $q$ and existentially
    quantify its two coordinates, using the predicate $q=\langle x,y\rangle$ or $q=\langle x,a\rangle$.
    Every coordinate of a pair in $j$ belongs to $\bigcup\bigcup j\in M$.
    Transitivity therefore puts all witnesses in $M$, and the internal formulas define exactly these sets.
-/
lemma realize_reversePairFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (f q : M) :
    reversePairFormula.Realize Empty.elim ![f, q] ↔
      ∃ x y, q.val = pair x y ∧ pair y x ∈ f.val := by
  simp only [reversePairFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_pair_model hM, realize_pairMemberFormula_model hM, Fin.snoc]
  constructor
  · rintro ⟨x, y, hq, hp⟩
    exact ⟨x.val, y.val, hq, hp⟩
  · rintro ⟨x, y, hq, hp⟩
    obtain ⟨hy, hx⟩ := pair_coordinates_mem hM hunion f.property hp
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hq, hp⟩

def inverseGraph (f A D : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod D A).sep (fun q => ∃ x y, q = pair x y ∧ pair y x ∈ f)

lemma pair_mem_inverseGraph {f A D x y : ZFSet.{u}} :
    pair x y ∈ inverseGraph f A D ↔ x ∈ D ∧ y ∈ A ∧ pair y x ∈ f := by
  rw [inverseGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, a, b, he, hp⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx, hy, hp⟩
  · rintro ⟨hx, hy, hp⟩
    exact ⟨⟨hx, hy⟩, x, y, rfl, hp⟩

lemma inverseGraph_mem {M f A D : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hf : f ∈ M) (hA : A ∈ M) (hD : D ∈ M) : inverseGraph f A D ∈ M := by
  apply separation_mem_of_absolute hM reversePairFormula (hsep _) ![⟨f, hf⟩]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) hD hA)
    (fun q => ∃ x y, q = pair x y ∧ pair y x ∈ f)
  intro q _
  have hs : Fin.snoc ![⟨f, hf⟩] q = ![⟨f, hf⟩, q] := by
    funext i
    fin_cases i <;> rfl
  rw [hs]
  exact realize_reversePairFormula hM hunion ⟨f, hf⟩ q

/-- Parameters f,q; q relates outputs whose inputs are related by membership. -/
def transportedMembershipFormula : ForcingFormulas.Formula 2 :=
  (orderedPairFormula (1 : Fin 6) 2 3 ⊓ pairMemberFormula 0 4 2 ⊓
    pairMemberFormula 0 5 3 ⊓ memberAt 4 5).ex.ex.ex.ex

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    For complete first-order formulas, replace each displayed ordered pair by a variable $q$ and existentially
    quantify its two coordinates, using the predicate $q=\langle x,y\rangle$ or $q=\langle x,a\rangle$.
    Every coordinate of a pair in $j$ belongs to $\bigcup\bigcup j\in M$.
    Transitivity therefore puts all witnesses in $M$, and the internal formulas define exactly these sets.
-/
lemma realize_transportedMembershipFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence) (f q : M) :
    transportedMembershipFormula.Realize Empty.elim ![f, q] ↔
      ∃ x y a b, ((q.val = pair x y ∧ pair a x ∈ f.val) ∧ pair b y ∈ f.val) ∧ a ∈ b := by
  simp only [transportedMembershipFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_pair_model hM, realize_pairMemberFormula_model hM, realize_memberAt_model, Fin.snoc]
  constructor
  · rintro ⟨x, y, a, b, h⟩
    exact ⟨x.val, y.val, a.val, b.val, h⟩
  · rintro ⟨x, y, a, b, ⟨⟨hq, ha⟩, hb⟩, hab⟩
    obtain ⟨haM, hxM⟩ := pair_coordinates_mem hM hunion f.property ha
    obtain ⟨hbM, hyM⟩ := pair_coordinates_mem hM hunion f.property hb
    exact ⟨⟨x, hxM⟩, ⟨y, hyM⟩, ⟨a, haM⟩, ⟨b, hbM⟩, ⟨⟨hq, ha⟩, hb⟩, hab⟩

def transportedMembership (f D : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod D D).sep (fun q => ∃ x y a b, ((q = pair x y ∧ pair a x ∈ f) ∧ pair b y ∈ f) ∧ a ∈ b)

lemma pair_mem_transportedMembership {f D x y : ZFSet.{u}} :
    pair x y ∈ transportedMembership f D ↔
      x ∈ D ∧ y ∈ D ∧ ∃ a b, pair a x ∈ f ∧ pair b y ∈ f ∧ a ∈ b := by
  rw [transportedMembership, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, z, w, a, b, ⟨⟨he, ha⟩, hb⟩, hab⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx, hy, a, b, ha, hb, hab⟩
  · rintro ⟨hx, hy, a, b, ha, hb, hab⟩
    exact ⟨⟨hx, hy⟩, x, y, a, b, ⟨⟨rfl, ha⟩, hb⟩, hab⟩

lemma transportedMembership_mem {M f D : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hf : f ∈ M) (hD : D ∈ M) : transportedMembership f D ∈ M := by
  apply separation_mem_of_absolute hM transportedMembershipFormula (hsep _) ![⟨f, hf⟩]
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) hD hD)
    (fun q => ∃ x y a b, ((q = pair x y ∧ pair a x ∈ f) ∧ pair b y ∈ f) ∧ a ∈ b)
  intro q _
  have hs : Fin.snoc ![⟨f, hf⟩] q = ![⟨f, hf⟩, q] := by
    funext i
    fin_cases i <;> rfl
  rw [hs]
  exact realize_transportedMembershipFormula hM hunion ⟨f, hf⟩ q

lemma inverseGraph_isFunc_of_injective {A W f : ZFSet.{u}}
    (hf : ZFSet.IsFunc A W f)
    (hinj : ∀ a b x, pair a x ∈ f → pair b x ∈ f → a = b) :
    ZFSet.IsFunc (graphRange f) A (inverseGraph f A (graphRange f)) := by
  constructor
  · intro p hp
    exact (ZFSet.mem_sep.mp hp).1
  · intro x hx
    obtain ⟨a, ha⟩ := mem_graphRange.mp hx
    have haA := (ZFSet.pair_mem_prod.mp (hf.1 ha)).1
    refine ⟨a, pair_mem_inverseGraph.mpr ⟨hx, haA, ha⟩, ?_⟩
    intro b hb
    exact hinj b a x (pair_mem_inverseGraph.mp hb).2.2 ha

lemma injection_ordinalIso {A W f : ZFSet.{u}}
    (hf : ZFSet.IsFunc A W f)
    (hinj : ∀ a b x, pair a x ∈ f → pair b x ∈ f → a = b) :
    ∃ e : (fun x y : graphRange f => pair x.val y.val ∈ transportedMembership f (graphRange f)) ≃r
        (fun a b : A => a.val ∈ b.val),
      functionGraph (fun x => (e x).val) = inverseGraph f A (graphRange f) := by
  apply ordinalIso_of_graph (inverseGraph_isFunc_of_injective hf hinj)
  · intro a ha
    obtain ⟨x, hx, _⟩ := hf.2 a ha
    have hxD : x ∈ graphRange f := mem_graphRange.mpr ⟨a, hx⟩
    exact ⟨x, hxD, pair_mem_inverseGraph.mpr ⟨hxD, ha, hx⟩⟩
  · intro x hx y hy a ha b _ hxa hyb
    have hax := (pair_mem_inverseGraph.mp hxa).2.2
    have hby := (pair_mem_inverseGraph.mp hyb).2.2
    constructor
    · constructor
      · intro hxy
        exact hinj a b y (hxy ▸ hax) hby
      · intro hab
        subst b
        exact (hf.2 a ha).unique hax hby
    · rw [pair_mem_transportedMembership]
      constructor
      · rintro ⟨_, _, c, d, hcx, hdy, hcd⟩
        have hca := hinj c a x hcx hax
        have hdb := hinj d b y hdy hby
        exact hca ▸ hdb ▸ hcd
      · intro hab
        exact ⟨hx, hy, a, b, hax, hby, hab⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: proof
  excerpt: |
    Suppose, toward a contradiction, that $j\in M$ is the graph of an injection $j:H\to W$.
    Range closure gives $D:=\GraphRange{j}\in M$ and $D\IncludedIn W$.
    Construct the transported relation and the inverse graph by
    $$\begin{aligned}
    R:=\{\langle x,y\rangle\in D\times D:\exists a\,\exists b\,
      (&\langle a,x\rangle\in j\land\langle b,y\rangle\in j\\
       &{}\land a\in b)\},\\
    g:=\{\langle x,a\rangle\in D\times H:&\ \langle a,x\rangle\in j\}.
    \end{aligned}$$
    These sets belong to $M$ by product closure and Separation.
-/
theorem internal_injection_ordinalIso {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (A W f : M) (hA : A.val.IsOrdinal) (hf : ZFSet.IsFunc A.val W.val f.val)
    (hinj : ∀ a b x, pair a x ∈ f.val → pair b x ∈ f.val → a = b) :
    ∃ D R g : M, D.val ⊆ W.val ∧ R.val ⊆ ZFSet.prod W.val W.val ∧
      ordinalIsoFormula.Realize Empty.elim ![D, R, A, g] := by
  let D : M := ⟨graphRange f.val, graphRange_mem hM hunion (hsep _) f.property⟩
  let R : M := ⟨transportedMembership f.val D.val,
    transportedMembership_mem hM hpair hunion hpower hsep f.property D.property⟩
  let g : M := ⟨inverseGraph f.val A.val D.val,
    inverseGraph_mem hM hpair hunion hpower hsep f.property A.property D.property⟩
  have hDW : D.val ⊆ W.val := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_graphRange.mp hx
    exact (ZFSet.pair_mem_prod.mp (hf.1 ha)).2
  refine ⟨D, R, g, hDW, ?_, ?_⟩
  · intro p hp
    dsimp only [R, transportedMembership] at hp
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hp).1
    exact ZFSet.pair_mem_prod.mpr ⟨hDW hx, hDW hy⟩
  · exact (realize_ordinalIsoFormula hM D R A g).mpr ⟨hA, injection_ordinalIso hf hinj⟩

end PolishSpaceBook.SetTheoryModels
