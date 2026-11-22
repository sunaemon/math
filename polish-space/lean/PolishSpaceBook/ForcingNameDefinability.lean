module

public import PolishSpaceBook.ForcingAtomicGlobalDefinability
public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # A first-order definition of the class of forcing names -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames
universe u

lemma isName_iff_pairs (P τ : ZFSet.{u}) : IsName P τ ↔
    ∀ z ∈ τ, ∃ σ p, z = pair σ p ∧ p ∈ P ∧ IsName P σ := by
  rw [isName_iff]
  constructor
  · rintro ⟨hpairs, hnames⟩ z hz
    obtain ⟨σ, p, he⟩ := hpairs z hz
    exact ⟨σ, p, he, hnames σ p (he ▸ hz)⟩
  · intro h
    refine ⟨fun z hz => by obtain ⟨σ, p, he, _, _⟩ := h z hz; exact ⟨σ, p, he⟩, ?_⟩
    intro σ p hp
    obtain ⟨σ', p', he, hp', hσ'⟩ := h (pair σ p) hp
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp', hσ'⟩

/-- A positive operation on candidate collections of names in W. -/
def nameStep (P W T τ : ZFSet.{u}) : Prop :=
  ∀ z ∈ τ, ∃ σ ∈ W, ∃ p ∈ P, z = pair σ p ∧ σ ∈ T

lemma nameStep_mono {P W S T τ : ZFSet.{u}} (hST : S ⊆ T) (h : nameStep P W S τ) :
    nameStep P W T τ := by
  intro z hz
  obtain ⟨σ, hσ, p, hp, he, hσS⟩ := h z hz
  exact ⟨σ, hσ, p, hp, he, hST hσS⟩

/-- A fixed candidate contains exactly the actual names in its transitive bound. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    We prove by induction on $\mathrm{rank}(\tau)$, for $\tau\in W$, that
    $$\tau\in C\quad\Longleftrightarrow\quad\tau\in M^P.$$
    The fixed-point equation says that every element of $\tau$ must be a pair $\langle\sigma,p\rangle$ with
    $p\in P$ and $\sigma\in C$. Every such child has smaller rank.
    By induction, membership of the child in $C$ is equivalent to its being a name, giving the forward implication.
    Conversely, if $\tau$ is a name, every element has this pair form with a child name.
    Transitivity of $W$ puts each child in $W$, so induction puts it in $C$ and the fixed-point equation gives
    $\tau\in C$. The empty name satisfies the condition vacuously; a set containing an element that is not a
    suitable pair fails it.
-/
theorem fixed_names_iff {P W C : ZFSet.{u}} (hW : W.IsTransitive)
    (hfix : W.sep (nameStep P W C) = C) (τ : ZFSet.{u}) (hτ : τ ∈ W) : τ ∈ C ↔ IsName P τ := by
  have heq : τ ∈ C ↔ nameStep P W C τ := by
    conv_lhs => rw [← hfix, ZFSet.mem_sep]
    exact and_iff_right hτ
  rw [heq, isName_iff_pairs]
  constructor
  · intro h z hz
    obtain ⟨σ, hσ, p, hp, he, hσC⟩ := h z hz
    have hchild : pair σ p ∈ τ := he ▸ hz
    exact ⟨σ, p, he, hp, (fixed_names_iff hW hfix σ hσ).mp hσC⟩
  · intro h z hz
    obtain ⟨σ, p, he, hp, hσn⟩ := h z hz
    have hchild : pair σ p ∈ τ := he ▸ hz
    have hσW : σ ∈ W := child_mem_ground hW hτ hchild
    exact ⟨σ, hσW, p, hp, he, (fixed_names_iff hW hfix σ hσW).mpr hσn⟩
termination_by τ.rank
 decreasing_by all_goals exact child_rank_lt hchild

/-- Variables P,W,T,τ; the shared bounded compiler handles the internal quantifiers. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Choose a transitive $W\in M$. For each candidate $T$, define the positive step
    $$\begin{aligned}
    \psi(P,W,T,\tau)\;:\equiv\;&\forall z\in\tau\;\exists\sigma\in W\;\exists p\in P\\
    &\bigl(z=\langle\sigma,p\rangle\land\sigma\in T\bigr),\\
    \Psi(T)&:=\{\tau\in W:\psi(P,W,T,\tau)\}.
    \end{aligned}$$
-/
def nameStepPredicate : BoundedSetPredicate 4 :=
  .all 3 (.ex 1 (.ex 0 (.conj (.orderedPair 4 5 6) (.member 5 2))))

def nameStepFormula : ForcingFormulas.Formula 4 := nameStepPredicate.compile

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    After expanding ordered-pair equality, $\psi$ is a bounded first-order formula with the displayed parameters.
    Bounded absoluteness from §{sec:zfc-absoluteness} therefore identifies its internal interpretation with the
    external condition.
-/
lemma realize_nameStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive) (xs : Fin 4 → M) :
    nameStepFormula.Realize Empty.elim xs ↔ nameStep (xs 0).val (xs 1).val (xs 2).val (xs 3).val := by
  simpa [nameStepFormula, nameStepPredicate, BoundedSetPredicate.eval,
    Function.comp_def, Fin.snoc, Fin.castPred, Fin.castLT, nameStep] using
    nameStepPredicate.realize_compile hM xs

/-- The rank induction identifies the entire fixed set, including non-name inputs. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Thus $C=\{\tau\in W:\tau\in M^P\}$.
-/
theorem fixed_names_eq {P W C : ZFSet.{u}} (hW : W.IsTransitive)
    (hfix : W.sep (nameStep P W C) = C) : C = W.sep (IsName P) := by
  ext τ
  rw [ZFSet.mem_sep]
  constructor
  · intro hτ
    have hτW : τ ∈ W := by rw [← hfix] at hτ; exact (ZFSet.mem_sep.mp hτ).1
    exact ⟨hτW, (fixed_names_iff hW hfix τ hτW).mp hτ⟩
  · rintro ⟨hτW, hτ⟩
    exact (fixed_names_iff hW hfix τ hτW).mpr hτ

/-- Two transitive bounds recognize the same names on their intersection. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    If $V\in M$ is another transitive bound, the two fixed sets
    agree on $W\cap V$, since both recognize precisely the names there. The choice of a transitive bound
    therefore does not affect the name predicate.
-/
theorem fixed_names_agree {P W V C D : ZFSet.{u}} (hW : W.IsTransitive) (hV : V.IsTransitive)
    (hC : W.sep (nameStep P W C) = C) (hD : V.sep (nameStep P V D) = D)
    {τ : ZFSet.{u}} (hτW : τ ∈ W) (hτV : τ ∈ V) : τ ∈ C ↔ τ ∈ D :=
  (fixed_names_iff hW hC τ hτW).trans (fixed_names_iff hV hD τ hτV).symm

def boundedNameFormula : ForcingFormulas.Formula 3 :=
  memberAt 2 1 ⊓ reindex (leastClosedMemberFormula nameStepFormula) ![0, 1, 1, 2]

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    The only occurrence of $T$ is positive, so $\Psi$ is monotone.
    The internal least-fixed-point construction gives
    $$C\in M,\qquad C\IncludedIn W,\qquad \Psi(C)=C.$$
    Its defining formula is
    $$\begin{aligned}
    \chi_{P,W}(T)&\;:\equiv\;\forall\rho\in W\,
     (\psi(P,W,T,\rho)\longrightarrow\rho\in T),\\
    \lambda_{P,W}(\tau)&\;:\equiv\;\tau\in W\land
     \forall T\,(\chi_{P,W}(T)\longrightarrow\tau\in T).
    \end{aligned}$$
-/
lemma internal_names_fixed {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) (P W : M) :
    let C := internalLeastClosed M W.val (nameStep P.val W.val)
    C ∈ M ∧ W.val.sep (nameStep P.val W.val C) = C := by
  apply internal_definable_fixed_point hM hsep nameStepFormula ![P, W] W (nameStep P.val W.val)
  · intro T x _
    simpa [Fin.snoc, Fin.castPred, Fin.castLT] using realize_nameStepFormula hM (Fin.snoc (Fin.snoc ![P, W] T) x)
  · intro S T hST τ _ hτ
    exact nameStep_mono hST hτ

lemma realize_boundedNameFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P W τ : M) (hW : W.val.IsTransitive) (hτ : τ.val ∈ W.val) :
    boundedNameFormula.Realize Empty.elim ![P, W, τ] ↔ IsName P.val τ.val := by
  have hφ (T y : M) (_hy : y.val ∈ W.val) :
      nameStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ![P, W] T) y) ↔
        nameStep P.val W.val T.val y.val := by
    simpa [Fin.snoc, Fin.castPred, Fin.castLT] using realize_nameStepFormula hM (Fin.snoc (Fin.snoc ![P, W] T) y)
  have hv := realize_leastClosedMember_step hM nameStepFormula ![P, W] W τ (nameStep P.val W.val) hφ
  have hxs : (![P, W, τ] ∘ ![0, 1, 1, 2]) = Fin.snoc (Fin.snoc ![P, W] W) τ := by
    funext i
    fin_cases i <;> rfl
  rw [boundedNameFormula, BoundedFormula.realize_inf, realize_memberAt_model, realize_reindex, hxs, hv]
  change (τ.val ∈ W.val ∧ _) ↔ _
  simpa only [internalLeastClosed, ZFSet.mem_sep] using
    fixed_names_iff hW (internal_names_fixed hM hsep P W).2 τ.val hτ

/-- A uniform formula with just P and τ free. -/
def nameFormula : ForcingFormulas.Formula 2 :=
  (transitiveFormula 2 ⊓ memberAt 1 2 ⊓ reindex boundedNameFormula ![0, 2, 1]).ex

lemma realize_nameFormula_witnesses {M : ZFSet.{u}} (hM : M.IsTransitive) (P τ : M) :
    nameFormula.Realize Empty.elim ![P, τ] ↔
      ∃ W : M, W.val.IsTransitive ∧ τ.val ∈ W.val ∧ boundedNameFormula.Realize Empty.elim ![P, W, τ] := by
  simp only [nameFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_transitive_model hM, realize_memberAt_model, realize_reindex, and_assoc]
  dsimp [Fin.snoc, Function.comp_def]
  apply exists_congr
  intro W
  repeat' (apply and_congr_right; intro _)
  apply Iff.of_eq
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Actual names, including the empty name and arbitrary ranks, are recognized internally. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Now define the formula with just $P$ and $\tau$ free by
    $$\eta(P,\tau)\;:\equiv\;\exists W\,
     (\mathrm{Trans}(W)\land\tau\in W\land\lambda_{P,W}(\tau)).$$
    For $P,\tau\in M$, any witnesses give a name by the rank induction.
    Conversely, the internal transitive-bound construction supplies a suitable $W\in M$ containing $\tau$,
    so every name satisfies this formula. Hence
    $$M\models\eta(P,\tau)\quad\Longleftrightarrow\quad\tau\in M^P.$$
    In particular, quantifying internally over this predicate ranges over exactly the actual names in the model.
-/
theorem name_definable {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (P τ : M) : nameFormula.Realize Empty.elim ![P, τ] ↔ IsName P.val τ.val := by
  rw [realize_nameFormula_witnesses hM]
  constructor
  · rintro ⟨W, hW, hτ, hφ⟩
    exact (realize_boundedNameFormula hM hsep P W τ hW hτ).mp hφ
  · intro hτ
    obtain ⟨W, hWM, hτW, hWt⟩ := internal_transitive_bound hM hinf hpair hunion hpower hsep hrep τ
    exact ⟨⟨W, hWM⟩, hWt, hτW, (realize_boundedNameFormula hM hsep P ⟨W, hWM⟩ τ hWt hτW).mpr hτ⟩

end PolishSpaceBook.SetTheoryModels
