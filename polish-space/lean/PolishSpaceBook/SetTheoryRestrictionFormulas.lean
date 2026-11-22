module

public import PolishSpaceBook.SetTheoryGraphRestrictions

@[expose] public section

/-! # Bounded formulas recognizing restrictions of set-coded graphs -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- A pair with first coordinate in x; its second coordinate is bounded by a member of the pair. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    The restriction predicate can be written without an extra parameter bounding its values. Set
    $$\chi(x,q)\;:\equiv\;\exists a\in x\,\exists u\in q\,\exists b\in u\,(q=\langle a,b\rangle).$$
    The extra bound $u\in q$ loses no pair: for $q=\langle a,b\rangle$, use $u=\{a,b\}$.
    Conversely, any witnesses to this formula exhibit a pair whose first coordinate lies in $x$.
    Thus define
    $$\begin{aligned}
    \rho(f,x,g)\;:\equiv\;&\forall q\in g\,(q\in f\land\chi(x,q))\\
    &{}\land\forall q\in f\,(\chi(x,q)\to q\in g).
    \end{aligned}$$
    Both formulas are $\Delta_0$ after expanding ordered-pair equality as in §{sec:zfc-absoluteness}.
    In any transitive domain containing the parameters, the two clauses of $\rho$ give precisely the two inclusions
    in $g=\restrict{f}{x}$. This recognition statement needs no closure axioms; the existence of the restriction
    inside the model uses the closure argument above.
-/
def firstCoordinateFormula {n : ℕ} (x p : Fin n) : ForcingFormulas.Formula n :=
  boundedExists x (boundedExists p.castSucc (boundedExists (Fin.last (n + 1))
    (orderedPairFormula p.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc (Fin.last (n + 2)))))

lemma firstCoordinateFormula_deltaZero {n : ℕ} (x p : Fin n) : IsDeltaZero (firstCoordinateFormula x p) :=
  .exists x (.exists p.castSucc (.exists (Fin.last (n + 1)) (orderedPairFormula_deltaZero _ _ _)))

/-- Both inclusions in the restricted graph are checked with bounded quantifiers. -/
def restrictionFormula {n : ℕ} (f x g : Fin n) : ForcingFormulas.Formula n :=
  boundedAll g (memberAt (Fin.last n) f.castSucc ⊓ firstCoordinateFormula x.castSucc (Fin.last n)) ⊓
    boundedAll f ((firstCoordinateFormula x.castSucc (Fin.last n)).imp (memberAt (Fin.last n) g.castSucc))

lemma restrictionFormula_deltaZero {n : ℕ} (f x g : Fin n) : IsDeltaZero (restrictionFormula f x g) :=
  (IsDeltaZero.all g ((memberAt_deltaZero _ _).and (firstCoordinateFormula_deltaZero _ _))).and
    (.all f ((firstCoordinateFormula_deltaZero _ _).imp (memberAt_deltaZero _ _)))

lemma realize_firstCoordinateFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x p : Fin n) (xs : Fin n → ClassDomain C) :
    (firstCoordinateFormula x p).Realize Empty.elim xs ↔
      ∃ a ∈ (xs x).val, ∃ b, (xs p).val = ZFSet.pair a b := by
  simp only [firstCoordinateFormula, realize_boundedExists, realize_orderedPairFormula C hC,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨a, ha, _, _, b, _, he⟩
    exact ⟨a.val, ha, b.val, he⟩
  · rintro ⟨a, ha, b, he⟩
    have hu : ({a, b} : ZFSet.{u}) ∈ (xs p).val := by simp [he, ZFSet.pair]
    have hb : b ∈ ({a, b} : ZFSet.{u}) := by simp
    have huC := hC _ (xs p).property _ hu
    exact ⟨⟨a, hC _ (xs x).property _ ha⟩, ha, ⟨{a, b}, huC⟩, hu,
      ⟨b, hC _ huC _ hb⟩, hb, he⟩

/-- In any transitive domain this bounded formula identifies the actual restriction. -/
lemma realize_restrictionFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (f x g : Fin n) (xs : Fin n → ClassDomain C) :
    (restrictionFormula f x g).Realize Empty.elim xs ↔
      (xs g).val = restrictGraph (xs f).val (xs x).val := by
  simp only [restrictionFormula, BoundedFormula.realize_inf, realize_boundedAll,
    BoundedFormula.realize_imp, realize_memberAt_class, realize_firstCoordinateFormula C hC,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨hsub, hsuper⟩
    apply ZFSet.ext
    intro p
    constructor
    · intro hp
      obtain ⟨hpf, a, ha, b, he⟩ := hsub ⟨p, hC _ (xs g).property _ hp⟩ hp
      exact mem_restrictGraph.mpr ⟨a, ha, b, he, he ▸ hpf⟩
    · intro hp
      obtain ⟨a, ha, b, he, hab⟩ := mem_restrictGraph.mp hp
      have hpf : p ∈ (xs f).val := he ▸ hab
      exact hsuper ⟨p, hC _ (xs f).property _ hpf⟩ hpf ⟨a, ha, b, he⟩
  · intro heq
    constructor
    · intro p hp
      rw [heq] at hp
      obtain ⟨a, ha, b, he, hab⟩ := mem_restrictGraph.mp hp
      exact ⟨he ▸ hab, a, ha, b, he⟩
    · intro p hpf hp
      obtain ⟨a, ha, b, he⟩ := hp
      rw [heq]
      exact mem_restrictGraph.mpr ⟨a, ha, b, he, he ▸ hpf⟩

end PolishSpaceBook.SetTheoryModels
