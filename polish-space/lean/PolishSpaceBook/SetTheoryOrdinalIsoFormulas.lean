module

public import PolishSpaceBook.SetTheoryOrdinalRepresentation
public import PolishSpaceBook.SetTheoryGraphOperations

@[expose] public section

/-! # Bounded definitions of set-coded ordinal representations

The formula recognizes an actual order isomorphism when its graph and target
ordinal are already in the transitive domain. It does not assume or assert that
the model contains the ordinal representation of every externally given order.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

private lemma realize_model_boundedAll (M : ZFSet.{u}) {n : ℕ} (i : Fin n)
    (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) :
    (boundedAll i φ).Realize Empty.elim xs ↔
      ∀ y : M, y.val ∈ (xs i).val → φ.Realize Empty.elim (Fin.snoc xs y) :=
  realize_boundedAll (M : ZFClass) i φ xs

/-- Every element of the target has a preimage in the source. -/
def ontoFormula {n : ℕ} (A B f : Fin n) : ForcingFormulas.Formula n :=
  boundedAll B (boundedExists A.castSucc
    (pairMemberFormula f.castSucc.castSucc (Fin.last (n + 1)) (Fin.last n).castSucc))

lemma ontoFormula_deltaZero {n : ℕ} (A B f : Fin n) : IsDeltaZero (ontoFormula A B f) :=
  .all B (.exists A.castSucc (pairMemberFormula_deltaZero _ _ _))

lemma realize_ontoFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (A B f : Fin n) (xs : Fin n → M) :
    (ontoFormula A B f).Realize Empty.elim xs ↔
      ∀ b ∈ (xs B).val, ∃ a ∈ (xs A).val, pair a b ∈ (xs f).val := by
  simp only [ontoFormula, realize_model_boundedAll, realize_boundedExists_model,
    realize_pairMemberFormula_model hM, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro h b hb
    obtain ⟨a, ha, hab⟩ := h ⟨b, hM.mem_trans hb (xs B).property⟩ hb
    exact ⟨a.val, ha, hab⟩
  · intro h b hb
    obtain ⟨a, ha, hab⟩ := h b.val hb
    exact ⟨⟨a, hM.mem_trans ha (xs A).property⟩, ha, hab⟩

/-- Parameters A,R,α,f; inputs x,y and outputs b,c are all bounded. -/
def ordinalIsoComparisonFormula : ForcingFormulas.Formula 4 :=
  boundedAll 0 (boundedAll 0 (boundedAll 2 (boundedAll 2
    (((pairMemberFormula (3 : Fin 8) 4 6) ⊓ (pairMemberFormula (3 : Fin 8) 5 7)).imp
      (((equalAt (4 : Fin 8) 5).iff (equalAt 6 7)) ⊓
        ((pairMemberFormula (1 : Fin 8) 4 5).iff (memberAt 6 7)))))))

private lemma deltaZero_iff {n : ℕ} {φ ψ : ForcingFormulas.Formula n}
    (hφ : IsDeltaZero φ) (hψ : IsDeltaZero ψ) : IsDeltaZero (φ.iff ψ) :=
  (hφ.imp hψ).and (hψ.imp hφ)

lemma ordinalIsoComparisonFormula_deltaZero : IsDeltaZero ordinalIsoComparisonFormula := by
  apply IsDeltaZero.all
  apply IsDeltaZero.all
  apply IsDeltaZero.all
  apply IsDeltaZero.all
  exact ((pairMemberFormula_deltaZero _ _ _).and (pairMemberFormula_deltaZero _ _ _)).imp
    ((deltaZero_iff (equalAt_deltaZero _ _) (equalAt_deltaZero _ _)).and
      (deltaZero_iff (pairMemberFormula_deltaZero _ _ _) (.member _)))

/-- An ordinal target and a bijective graph that preserves and reflects the source relation. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For use inside a transitive model, we need a formula that recognizes both the representing ordinal and
    the entire isomorphism graph. Let $R$ code the relation on $W$, and define
    $$\begin{aligned}
    \iota(W,R,\alpha,f)\;:\equiv\;&\mathrm{Ord}(\alpha)\land(f:W\to\alpha)\\
     &{}\land\forall b\in\alpha\,\exists x\in W\,
       \langle x,b\rangle\in f\\
     &{}\land\forall x,y\in W\,\forall b,c\in\alpha\\
     &\quad\bigl[(\langle x,b\rangle\in f\land\langle y,c\rangle\in f)\\
     &\qquad\longrightarrow\bigl((x=y\leftrightarrow b=c)\\
     &\hspace{7em}{}\land(\langle x,y\rangle\in R\leftrightarrow b\in c)\bigr)\bigr].
    \end{aligned}$$
    The ordinal, function, and pair predicates are the bounded formulas spelled out in §{sec:zfc-absoluteness}.
    Thus $\iota$ is a $\Delta_0$ formula; it does not quantify over arbitrary subsets to test well-ordering.
-/
def ordinalIsoFormula : ForcingFormulas.Formula 4 :=
  ordinalFormula 2 ⊓ functionFormula 0 2 3 ⊓ ontoFormula 0 2 3 ⊓ ordinalIsoComparisonFormula

lemma ordinalIsoFormula_deltaZero : IsDeltaZero ordinalIsoFormula :=
  (((ordinalFormula_deltaZero _).and (functionFormula_deltaZero _ _ _)).and
    (ontoFormula_deltaZero _ _ _)).and ordinalIsoComparisonFormula_deltaZero

lemma realize_ordinalIsoComparisonFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (A R α f : M) :
    ordinalIsoComparisonFormula.Realize Empty.elim ![A, R, α, f] ↔
      ∀ x ∈ A.val, ∀ y ∈ A.val, ∀ b ∈ α.val, ∀ c ∈ α.val,
        pair x b ∈ f.val → pair y c ∈ f.val →
          (x = y ↔ b = c) ∧ (pair x y ∈ R.val ↔ b ∈ c) := by
  simp only [ordinalIsoComparisonFormula, realize_model_boundedAll, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_iff, realize_equalAt,
    realize_pairMemberFormula_model hM, realize_memberAt,
    Fin.isValue, Matrix.cons_val_zero]
  constructor
  · intro h x hx y hy b hb c hc hxb hyc
    let xM : M := ⟨x, hM.mem_trans hx A.property⟩
    let yM : M := ⟨y, hM.mem_trans hy A.property⟩
    let bM : M := ⟨b, hM.mem_trans hb α.property⟩
    let cM : M := ⟨c, hM.mem_trans hc α.property⟩
    obtain ⟨he, hr⟩ := h xM hx yM hy bM hb cM hc ⟨hxb, hyc⟩
    exact ⟨⟨fun hxy => congrArg Subtype.val (he.mp (Subtype.ext hxy)),
      fun hbc => congrArg Subtype.val (he.mpr (Subtype.ext hbc))⟩, hr⟩
  · intro h x hx y hy b hb c hc hp
    obtain ⟨he, hr⟩ := h x.val hx y.val hy b.val hb c.val hc hp.1 hp.2
    exact ⟨⟨fun hxy => Subtype.ext (he.mp (congrArg Subtype.val hxy)),
      fun hbc => Subtype.ext (he.mpr (congrArg Subtype.val hbc))⟩, hr⟩

/-- Convert graph conditions to mathlib's canonical relation isomorphism. -/
lemma ordinalIso_of_graph {A R α f : ZFSet.{u}} (hf : ZFSet.IsFunc A α f)
    (honto : ∀ b ∈ α, ∃ a ∈ A, pair a b ∈ f)
    (hcomp : ∀ x ∈ A, ∀ y ∈ A, ∀ b ∈ α, ∀ c ∈ α,
      pair x b ∈ f → pair y c ∈ f → (x = y ↔ b = c) ∧ (pair x y ∈ R ↔ b ∈ c)) :
    ∃ e : (fun x y : A => pair x.val y.val ∈ R) ≃r (fun b c : α => b.val ∈ c.val),
      functionGraph (fun x => (e x).val) = f := by
  let g : A → α := fun x =>
    ⟨Classical.choose (hf.2 x.val x.property),
      (ZFSet.pair_mem_prod.mp (hf.1 (Classical.choose_spec (hf.2 x.val x.property)).1)).2⟩
  have hg (x : A) : pair x.val (g x).val ∈ f := (Classical.choose_spec (hf.2 x.val x.property)).1
  have hgi : Function.Injective g := by
    intro x y he
    exact Subtype.ext ((hcomp x.val x.property y.val y.property (g x).val (g x).property
      (g y).val (g y).property (hg x) (hg y)).1.mpr (congrArg Subtype.val he))
  have hgs : Function.Surjective g := by
    intro b
    obtain ⟨x, hx, hxb⟩ := honto b.val b.property
    exact ⟨⟨x, hx⟩, Subtype.ext ((hf.2 x hx).unique (hg ⟨x, hx⟩) hxb)⟩
  let e : (fun x y : A => pair x.val y.val ∈ R) ≃r (fun b c : α => b.val ∈ c.val) :=
    { Equiv.ofBijective g ⟨hgi, hgs⟩ with
      map_rel_iff' := fun {x y} => (hcomp x.val x.property y.val y.property
        (g x).val (g x).property (g y).val (g y).property (hg x) (hg y)).2.symm }
  refine ⟨e, ZFSet.ext (fun p => ?_)⟩
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hp
    exact hg x
  · intro hp
    obtain ⟨x, hx, b, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    have he : (g ⟨x, hx⟩).val = b := (hf.2 x hx).unique (hg ⟨x, hx⟩) hp
    exact ZFSet.mem_range.mpr ⟨⟨x, hx⟩, congrArg (pair x) he⟩

/-- The bounded definition recognizes exactly a graph of an actual ordinal representation. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Transitivity makes every bounded quantifier range over the actual members of its bounding set.
    The first clauses therefore say that $\alpha$ is an ordinal and $f$ is a function from $W$ onto $\alpha$.
    The equality clause makes it injective, and the relation clause preserves and reflects the order.
    Conversely, an actual order-isomorphism satisfies each clause with witnesses already in $M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal recognition of ordinal representations
-/
theorem realize_ordinalIsoFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (A R α f : M) :
    ordinalIsoFormula.Realize Empty.elim ![A, R, α, f] ↔ α.val.IsOrdinal ∧
      ∃ e : (fun x y : A.val => pair x.val y.val ∈ R.val) ≃r (fun b c : α.val => b.val ∈ c.val),
        functionGraph (fun x => (e x).val) = f.val := by
  have ho : (ordinalFormula (2 : Fin 4)).Realize Empty.elim ![A, R, α, f] ↔ α.val.IsOrdinal :=
    realize_ordinalFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) 2 ![A, R, α, f]
  have hf : (functionFormula (0 : Fin 4) 2 3).Realize Empty.elim ![A, R, α, f] ↔
      ZFSet.IsFunc A.val α.val f.val :=
    realize_functionFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) 0 2 3 ![A, R, α, f]
  simp only [ordinalIsoFormula, BoundedFormula.realize_inf, ho, hf,
    realize_ontoFormula hM, realize_ordinalIsoComparisonFormula hM]
  change ((α.val.IsOrdinal ∧ ZFSet.IsFunc A.val α.val f.val) ∧
    (∀ b ∈ α.val, ∃ a ∈ A.val, pair a b ∈ f.val)) ∧ _ ↔ _
  constructor
  · rintro ⟨⟨⟨hα, hf⟩, hs⟩, hc⟩
    exact ⟨hα, ordinalIso_of_graph hf hs hc⟩
  · rintro ⟨hα, ⟨e, he⟩⟩
    have hp (x : A.val) : pair x.val (e x).val ∈ f.val := by
      rw [← he]
      exact ZFSet.mem_range.mpr ⟨x, rfl⟩
    have hfunc : ZFSet.IsFunc A.val α.val f.val := by
      rw [← he]
      have h := functionGraph_isFunc (fun x => (e x).val)
      have hrange : ZFSet.range (fun x => (e x).val) = α.val := by
        apply ZFSet.ext
        intro b
        constructor
        · rintro hb
          obtain ⟨x, rfl⟩ := ZFSet.mem_range.mp hb
          exact (e x).property
        · intro hb
          exact ZFSet.mem_range.mpr ⟨e.symm ⟨b, hb⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
      rw [hrange] at h
      exact h
    refine ⟨⟨⟨hα, hfunc⟩, ?_⟩, ?_⟩
    · intro b hb
      let x := e.symm ⟨b, hb⟩
      refine ⟨x.val, x.property, ?_⟩
      simpa only [x, RelIso.apply_symm_apply] using hp x
    · intro x hx y hy b _ c _ hxb hyc
      have hxv : (e ⟨x, hx⟩).val = b := (hfunc.2 x hx).unique (hp ⟨x, hx⟩) hxb
      have hyv : (e ⟨y, hy⟩).val = c := (hfunc.2 y hy).unique (hp ⟨y, hy⟩) hyc
      rw [← hxv, ← hyv]
      constructor
      · exact ⟨fun hxy => congrArg (fun z : A.val => (e z).val) (Subtype.ext hxy),
          fun heq => congrArg Subtype.val (e.injective (Subtype.ext heq))⟩
      · exact (e.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).symm

/-- Fixed source and relation admit at most one ordinal target and one isomorphism graph. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    For uniqueness, two such representations have equal ordinal targets by the theorem, and their graphs agree
    because an ordinal has no nonidentity order-automorphism.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Gluing internal ordinal representations
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal recognition of ordinal representations
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal restriction of ordinal representations
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: theorem
  title: Internal ordinal representation theorem
-/
theorem internal_ordinalIso_unique {M : ZFSet.{u}} (hM : M.IsTransitive) (A R α β f g : M)
    (hf : ordinalIsoFormula.Realize Empty.elim ![A, R, α, f])
    (hg : ordinalIsoFormula.Realize Empty.elim ![A, R, β, g]) : α = β ∧ f = g := by
  obtain ⟨hα, e, he⟩ := (realize_ordinalIsoFormula hM A R α f).mp hf
  obtain ⟨hβ, e', he'⟩ := (realize_ordinalIsoFormula hM A R β g).mp hg
  obtain ⟨hab, hval⟩ := ordinal_representations_agree hα hβ e e'
  refine ⟨Subtype.ext hab, Subtype.ext ?_⟩
  rw [← he, ← he']
  exact congrArg functionGraph (funext hval)

end PolishSpaceBook.SetTheoryModels
