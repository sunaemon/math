module

public import PolishSpaceBook.SetTheoryChoice
public import PolishSpaceBook.SetTheoryOrdinalFormulas

@[expose] public section

/-! # A first-order selector using the least ordinal preimage under two graphs -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def ThroughGraphs (e F a x : ZFSet.{u}) : Prop := ∃ d, pair a d ∈ e ∧ pair d x ∈ F

def throughGraphsFormula {n : ℕ} (e F a x : Fin n) : ForcingFormulas.Formula n :=
  (pairMemberFormula e.castSucc a.castSucc (Fin.last n) ⊓
    pairMemberFormula F.castSucc (Fin.last n) x.castSucc).ex

lemma realize_throughGraphsFormula {N : ZFSet.{u}} (hN : N.IsTransitive)
    (hunion : N ⊨ unionSentence) {n : ℕ} (e F a x : Fin n) (xs : Fin n → N) :
    (throughGraphsFormula e F a x).Realize Empty.elim xs ↔
      ThroughGraphs (xs e).val (xs F).val (xs a).val (xs x).val := by
  simp only [throughGraphsFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_pairMemberFormula_model hN, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨d, he, hF⟩
    exact ⟨d.val, he, hF⟩
  · rintro ⟨d, he, hF⟩
    have hB := union_mem hN hunion (union_mem hN hunion (xs e).property)
    exact ⟨⟨d, hN.mem_trans (second_mem_doubleUnion he) hB⟩, he, hF⟩

def choiceCandidateFormula {n : ℕ} (e F y a : Fin n) : ForcingFormulas.Formula n :=
  boundedExists y (throughGraphsFormula e.castSucc F.castSucc a.castSucc (Fin.last n))

lemma realize_choiceCandidateFormula {N : ZFSet.{u}} (hN : N.IsTransitive)
    (hunion : N ⊨ unionSentence) {n : ℕ} (e F y a : Fin n) (xs : Fin n → N) :
    (choiceCandidateFormula e F y a).Realize Empty.elim xs ↔
      ∃ x ∈ (xs y).val, ThroughGraphs (xs e).val (xs F).val (xs a).val x := by
  simp only [choiceCandidateFormula, realize_boundedExists_model, realize_throughGraphsFormula hN hunion,
    Fin.snoc_castSucc, Fin.snoc_last]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x.val, hx, h⟩,
    fun ⟨x, hx, h⟩ => ⟨⟨x, hN.mem_trans hx (xs y).property⟩, hx, h⟩⟩

def LeastOrdinalChoice (γ e F y x : ZFSet.{u}) : Prop :=
  ∃ a ∈ γ, (x ∈ y ∧ ThroughGraphs e F a x) ∧
    ∀ b ∈ a, ¬ ∃ z ∈ y, ThroughGraphs e F b z

/-- Parameters γ,e,F; input y and output x. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    For the fixed parameters $\gamma,e,F$, define the first-order formulas
    $$\begin{aligned}
    \theta(\alpha,x)&:\equiv\exists d\,
     (\langle\alpha,d\rangle\in e\land\langle d,x\rangle\in F),\\
    C(y,\alpha)&:\equiv\exists x\in y\;\theta(\alpha,x),\\
    \psi(y,x)&:\equiv\exists\alpha\in\gamma\,\bigl[
     x\in y\land\theta(\alpha,x)\\
     &\hspace{5em}{}\land\forall\beta\in\alpha\;\neg C(y,\beta)\bigr].
    \end{aligned}$$
    Thus $\psi(y,x)$ selects an output in $y$ at the least possible ordinal input.
    All ordered-pair membership clauses use the previously verified first-order expansions.
-/
def leastOrdinalChoiceFormula : ForcingFormulas.Formula 5 :=
  boundedExists (0 : Fin 5)
    (memberAt 4 3 ⊓ throughGraphsFormula 1 2 5 4 ⊓
      boundedAll 5 (choiceCandidateFormula (1 : Fin 7) 2 3 6).not)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    These formulas have the intended meaning internally. If $\theta(\alpha,x)$ holds, its witness $d$ is a
    coordinate of a pair in $e$, hence belongs to $\bigcup\bigcup e\in N$. Transitivity then puts it in $N$.
    Conversely, an internal witness is an actual witness. The quantifiers bounded by $y$, $\gamma$, or
    $\alpha\in\gamma$ range over their actual members, which also lie in $N$.
    Thus, for parameters and arguments in $N$, internal satisfaction of $\theta$, $C$, and $\psi$ agrees with
    the displayed set-theoretic conditions.
-/
lemma realize_leastOrdinalChoiceFormula {N : ZFSet.{u}} (hN : N.IsTransitive)
    (hunion : N ⊨ unionSentence) (γ e F y x : N) :
    leastOrdinalChoiceFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ![γ, e, F] y) x) ↔
      LeastOrdinalChoice γ.val e.val F.val y.val x.val := by
  have hall {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → N) :
      (boundedAll i φ).Realize Empty.elim xs ↔
        ∀ b : N, b.val ∈ (xs i).val → φ.Realize Empty.elim (Fin.snoc xs b) :=
    realize_boundedAll (N : ZFClass) i φ xs
  simp only [leastOrdinalChoiceFormula, realize_boundedExists_model, BoundedFormula.realize_inf,
    realize_memberAt_model, realize_throughGraphsFormula hN hunion, hall, BoundedFormula.realize_not,
    realize_choiceCandidateFormula hN hunion, Fin.snoc]
  constructor
  · rintro ⟨a, ha, hax, hmin⟩
    exact ⟨a.val, ha, hax, fun b hb => hmin ⟨b, hN.mem_trans hb a.property⟩ hb⟩
  · rintro ⟨a, ha, hax, hmin⟩
    exact ⟨⟨a, hN.mem_trans ha γ.property⟩, ha, hax, fun b hb => hmin b.val hb⟩

lemma throughGraphs_unique {γ D U X e F a x y : ZFSet.{u}}
    (he : ZFSet.IsFunc γ D e) (hF : ZFSet.IsFunc U X F)
    (hx : ThroughGraphs e F a x) (hy : ThroughGraphs e F a y) : x = y := by
  obtain ⟨d, hd, hx⟩ := hx
  obtain ⟨d', hd', hy⟩ := hy
  have haγ := (ZFSet.pair_mem_prod.mp (he.1 hd)).1
  have hdd : d' = d := (he.2 a haγ).unique hd' hd
  subst d'
  exact (hF.2 d (ZFSet.pair_mem_prod.mp (hF.1 hx)).1).unique hx hy

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The values $e(\alpha_y)$ and $F(e(\alpha_y))$ are unique, so there is a unique $x\in y$ satisfying $\psi(y,x)$.
    More explicitly, two distinct candidate minima would be comparable by membership; the smaller would
    contradict minimality of the larger. At the same ordinal input, functionality of $e$ and then of $F$ forces
    both outputs to be equal.
-/
lemma leastOrdinalChoice_unique {γ D U X e F y x z : ZFSet.{u}} (hγ : γ.IsOrdinal)
    (he : ZFSet.IsFunc γ D e) (hF : ZFSet.IsFunc U X F)
    (hx : LeastOrdinalChoice γ e F y x) (hz : LeastOrdinalChoice γ e F y z) : x = z := by
  obtain ⟨a, ha, ⟨hxy, hax⟩, hmina⟩ := hx
  obtain ⟨b, hb, ⟨hzy, hbz⟩, hminb⟩ := hz
  rcases (hγ.mem ha).mem_trichotomous (hγ.mem hb) with hab | hab | hba
  · exact False.elim (hminb a hab ⟨x, hxy, hax⟩)
  · subst b
    exact throughGraphs_unique he hF hax hbz
  · exact False.elim (hmina b hba ⟨z, hzy, hbz⟩)

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The nonempty set of candidate ordinals has a least member $\alpha_y$.
-/
lemma leastOrdinalChoice_exists {γ e F y : ZFSet.{u}}
    (hγ : γ.IsOrdinal)
    (hex : ∃ a ∈ γ, ∃ x ∈ y, ThroughGraphs e F a x) :
    ∃ x, LeastOrdinalChoice γ e F y x := by
  let S : Set ZFSet.{u} := {a | a ∈ γ ∧ ∃ x ∈ y, ThroughGraphs e F a x}
  obtain ⟨a, ⟨ha, x, hxy, hax⟩, hmin⟩ := ZFSet.mem_wf.has_min S hex
  refine ⟨x, a, ha, ⟨hxy, hax⟩, ?_⟩
  intro b hba hb
  exact hmin b ⟨hγ.mem_trans hba ha, hb⟩ hba

end PolishSpaceBook.SetTheoryModels
