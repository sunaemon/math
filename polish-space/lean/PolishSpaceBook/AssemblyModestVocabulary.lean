module

public import PolishSpaceBook.ModestAssemblies

@[expose] public section

/-! # Disjoint realization sets and injectivity -/
namespace PolishSpaceBook.Assembly
universe u v
variable {A : Type u} {K : PartialCombinatoryAlgebra A} {X : Assembly.{u,v} K}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Modest sets.** A \termdefine{modest set} is an assembly $X$ in which distinct elements have disjoint realizer sets:
    $$x \ne x' \;\Longrightarrow\; \Vdash_X x \cap \Vdash_X x' = \emptyset.$$
    Equivalently, each realizer realizes at most one element. This implies that the map
    $|X| \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$ is injective, but injectivity alone does not imply disjointness.
    \begin{mathmeta}
      \define{ModCat}
    \end{mathmeta}
    Write $\ModCat{A} \IncludedIn \AsmCat{A}$ for the full subcategory on modest sets.
-/
theorem Modest.realization_injective (hX : Modest X) :
    Function.Injective (fun x => {a | X.realizes a x}) := by
  intro x y h
  obtain ⟨a, ha⟩ := X.inhabited x
  exact hX a ha ((Set.ext_iff.mp h a).mp ha)

/-- The two nonempty realization sets overlap, although they are different. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Modest sets.** A \termdefine{modest set} is an assembly $X$ in which distinct elements have disjoint realizer sets:
    $$x \ne x' \;\Longrightarrow\; \Vdash_X x \cap \Vdash_X x' = \emptyset.$$
    Equivalently, each realizer realizes at most one element. This implies that the map
    $|X| \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$ is injective, but injectivity alone does not imply disjointness.
    \begin{mathmeta}
      \define{ModCat}
    \end{mathmeta}
    Write $\ModCat{A} \IncludedIn \AsmCat{A}$ for the full subcategory on modest sets.
-/
def overlapping (K : PartialCombinatoryAlgebra ℕ) : Assembly.{0,0} K where
  Carrier := Bool
  realizes a b := if b then a = 1 ∨ a = 2 else a = 0 ∨ a = 1
  inhabited b := ⟨1, by cases b <;> simp⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Modest sets.** A \termdefine{modest set} is an assembly $X$ in which distinct elements have disjoint realizer sets:
    $$x \ne x' \;\Longrightarrow\; \Vdash_X x \cap \Vdash_X x' = \emptyset.$$
    Equivalently, each realizer realizes at most one element. This implies that the map
    $|X| \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$ is injective, but injectivity alone does not imply disjointness.
    \begin{mathmeta}
      \define{ModCat}
    \end{mathmeta}
    Write $\ModCat{A} \IncludedIn \AsmCat{A}$ for the full subcategory on modest sets.
-/
theorem overlapping_realization_injective (K : PartialCombinatoryAlgebra ℕ) :
    Function.Injective (fun x => {a | (overlapping K).realizes a x}) := by
  intro x y h
  cases x <;> cases y <;> try rfl
  all_goals
    have h0 := congrArg (fun s : Set ℕ => 0 ∈ s) h
    simp [overlapping] at h0

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Modest sets.** A \termdefine{modest set} is an assembly $X$ in which distinct elements have disjoint realizer sets:
    $$x \ne x' \;\Longrightarrow\; \Vdash_X x \cap \Vdash_X x' = \emptyset.$$
    Equivalently, each realizer realizes at most one element. This implies that the map
    $|X| \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$ is injective, but injectivity alone does not imply disjointness.
    \begin{mathmeta}
      \define{ModCat}
    \end{mathmeta}
    Write $\ModCat{A} \IncludedIn \AsmCat{A}$ for the full subcategory on modest sets.
-/
theorem overlapping_not_modest (K : PartialCombinatoryAlgebra ℕ) :
    ¬ Modest (overlapping K) := by
  intro h
  have he : false = true := h 1 (by simp [overlapping]) (by simp [overlapping])
  cases he

end PolishSpaceBook.Assembly
