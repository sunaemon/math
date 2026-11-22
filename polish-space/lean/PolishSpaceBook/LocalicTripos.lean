module

public import PolishSpaceBook.SetTriposCore
public import Mathlib.Order.CompleteBooleanAlgebra

@[expose] public section

namespace PolishSpaceBook
open CategoryTheory Limits Opposite
universe u
variable (Ω : Type u) [Order.Frame Ω]

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
def localicReindex {I J : Type u} (f : I → J) : HeytingHom (J → Ω) (I → Ω) where
  toFun φ := φ ∘ f
  map_inf' _ _ := rfl
  map_sup' _ _ := rfl
  map_bot' := rfl
  map_himp' _ _ := rfl

def localicIndexedHeyting : (Type u)ᵒᵖ ⥤ HeytAlg.{u} where
  obj I := HeytAlg.of (I.unop → Ω)
  map f := HeytAlg.ofHom (localicReindex Ω f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
noncomputable def localicExists {I J : Type u} (f : I → J) : (I → Ω) →o (J → Ω) where
  toFun φ j := ⨆ i, ⨆ (_ : f i = j), φ i
  monotone' _ _ h _ := iSup_mono fun i => iSup_mono fun _ => h i

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
noncomputable def localicForall {I J : Type u} (f : I → J) : (I → Ω) →o (J → Ω) where
  toFun φ j := ⨅ i, ⨅ (_ : f i = j), φ i
  monotone' _ _ h _ := iInf_mono fun i => iInf_mono fun _ => h i

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
theorem localic_exists_adjunction {I J : Type u} (f : I → J) :
    GaloisConnection (localicExists Ω f) (localicReindex Ω f) := by
  intro φ ψ
  change (∀ j, (⨆ i, ⨆ (_ : f i = j), φ i) ≤ ψ j) ↔ ∀ i, φ i ≤ ψ (f i)
  constructor
  · intro h i
    exact (le_iSup_of_le i (le_iSup_of_le (show f i = f i from rfl) (le_refl (φ i)))).trans (h (f i))
  · intro h j
    exact iSup_le fun i => iSup_le fun hi => by simpa only [← hi] using h i

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
theorem localic_forall_adjunction {I J : Type u} (f : I → J) :
    GaloisConnection (localicReindex Ω f) (localicForall Ω f) := by
  intro ψ φ
  change (∀ i, ψ (f i) ≤ φ i) ↔ ∀ j, ψ j ≤ ⨅ i, ⨅ (_ : f i = j), φ i
  constructor
  · intro h j
    exact le_iInf fun i => le_iInf fun hi => by simpa only [← hi] using h i
  · intro h i
    exact (h (f i)).trans (iInf_le_of_le i (iInf_le_of_le rfl le_rfl))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
theorem localic_exists_beckChevalley {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (φ : I → Ω) :
    localicReindex Ω g (localicExists Ω f φ) =
      localicExists Ω f' (localicReindex Ω g' φ) := by
  funext j
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    obtain ⟨i', hg', hf'⟩ := Types.exists_of_isPullback h i j hi
    exact le_iSup_of_le i' (le_iSup_of_le hf' (by change φ i ≤ φ (g' i'); rw [hg']))
  · apply iSup_le
    intro i'
    apply iSup_le
    intro hi
    have he := (ConcreteCategory.congr_hom h.w i').trans (congrArg g hi)
    exact le_iSup_of_le (g' i') (le_iSup_of_le he le_rfl)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
theorem localic_forall_beckChevalley {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (φ : I → Ω) :
    localicReindex Ω g (localicForall Ω f φ) =
      localicForall Ω f' (localicReindex Ω g' φ) := by
  funext j
  apply le_antisymm
  · apply le_iInf
    intro i'
    apply le_iInf
    intro hi
    have he := (ConcreteCategory.congr_hom h.w i').trans (congrArg g hi)
    exact iInf_le_of_le (g' i') (iInf_le_of_le he le_rfl)
  · apply le_iInf
    intro i
    apply le_iInf
    intro hi
    obtain ⟨i', hg', hf'⟩ := Types.exists_of_isPullback h i j hi
    exact iInf_le_of_le i' (iInf_le_of_le hf' (by change φ (g' i') ≤ φ i; rw [hg']))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The forcing side of the story begins with a complete Heyting algebra $\Omega$, equivalently a locale of truth values.
    Define a predicate on a set $I$ to be a function
    $$\varphi:I\to\Omega,$$
    ordered pointwise. For $f:I\to J$, reindexing is pullback:
    $$f^\ast(\psi)(i)=\psi(f(i)).$$
    The logical operations are pointwise:
    $$
    (\varphi\land\psi)(i)=\varphi(i)\land\psi(i),
    \qquad
    (\varphi\to\psi)(i)=\varphi(i)\to\psi(i),
    $$
    and similarly for $\top,\bot,\lor$. Quantifiers along $f:I\to J$ are computed by joins and meets over fibers:
    $$
    (\exists_f\varphi)(j)=\bigvee_{f(i)=j}\varphi(i),
    \qquad
    (\forall_f\varphi)(j)=\bigwedge_{f(i)=j}\varphi(i).
    $$
    The complete-Heyting-algebra adjunction laws make these joins and meets the left and right adjoints to reindexing, and
    Beck--Chevalley follows because pullback squares identify the relevant fibers. The generic predicate is the identity map
    $\Omega\to\Omega$. Thus $I\mapsto\Omega^I$ is a \termdefine{localic tripos} over $\SetCat$.
-/
noncomputable def localicTripos : SetTripos.{u} where
  predicates := localicIndexedHeyting Ω
  existsAlong := localicExists Ω
  forallAlong := localicForall Ω
  exists_adjunction := localic_exists_adjunction Ω
  forall_adjunction := localic_forall_adjunction Ω
  exists_beckChevalley := localic_exists_beckChevalley Ω
  forall_beckChevalley := localic_forall_beckChevalley Ω
  genericObject := Ω
  genericPredicate := id
  generic φ := ⟨φ, rfl⟩

end PolishSpaceBook
