module

public import PolishSpaceBook.FirstOrderGraphElimination

@[expose] public section

/-!
# Simultaneous substitution through fresh temporary names

A sequential substitution has an explicit assignment transformer. Two passes,
first through fresh names and then to the replacement terms, implement genuine
simultaneous substitution without rewriting one replacement inside another.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}}

namespace AlphaFormula

def substSequence (φ : AlphaFormula L) : List (ℕ × L.Term ℕ) → AlphaFormula L
  | [] => φ
  | (x, t) :: rest => substSequence (φ.subst x t) rest

def sequenceKeys : List (ℕ × L.Term ℕ) → Finset ℕ
  | [] => ∅
  | (x, _) :: rest => insert x (sequenceKeys rest)

def sequenceVars : List (ℕ × L.Term ℕ) → Finset ℕ
  | [] => ∅
  | (_, t) :: rest => t.varFinset ∪ sequenceVars rest

@[simp] theorem mem_sequenceKeys (xs : List (ℕ × L.Term ℕ)) (x : ℕ) :
    x ∈ sequenceKeys xs ↔ ∃ p ∈ xs, x = p.1 := by
  induction xs with
  | nil => simp [sequenceKeys]
  | cons p ps ih => rcases p with ⟨y,t⟩; simp [sequenceKeys, ih]

@[simp] theorem mem_sequenceVars (xs : List (ℕ × L.Term ℕ)) (x : ℕ) :
    x ∈ sequenceVars xs ↔ ∃ p ∈ xs, x ∈ p.2.varFinset := by
  induction xs with
  | nil => simp [sequenceVars]
  | cons p ps ih => rcases p with ⟨y,t⟩; simp [sequenceVars, ih]

/-- Sequential substitutions remove their keys and introduce only replacement variables. -/
theorem fv_substSequence_subset (φ : AlphaFormula L) (xs : List (ℕ × L.Term ℕ)) :
    (φ.substSequence xs).fv ⊆ (φ.fv \ sequenceKeys xs) ∪ sequenceVars xs := by
  induction xs generalizing φ with
  | nil => simp [substSequence, sequenceKeys, sequenceVars]
  | cons p ps ih =>
    rcases p with ⟨x,t⟩
    intro y hy
    have h := ih (φ.subst x t) hy
    simp only [Finset.mem_union, Finset.mem_sdiff] at h
    change y ∈ (φ.fv \ insert x (sequenceKeys ps)) ∪ (t.varFinset ∪ sequenceVars ps)
    rcases h with ⟨h, hrest⟩ | h
    · rw [fv_subst] at h
      rcases Finset.mem_union.mp h with h | h
      · have ho := Finset.mem_erase.mp h
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ho.2, by simp [ho.1, hrest]⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        split_ifs at h with hx
        · exact h
        · exact (Finset.notMem_empty _ h).elim
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)

section Semantics
variable {M : Type w} [L.Structure M]

/-- Later substitutions act on the terms inserted by earlier substitutions. -/
def sequenceAssignment : List (ℕ × L.Term ℕ) → (ℕ → M) → ℕ → M
  | [], s => s
  | (x,t) :: rest, s => Function.update (sequenceAssignment rest s) x (t.realize (sequenceAssignment rest s))

theorem realize_substSequence (φ : AlphaFormula L) (xs : List (ℕ × L.Term ℕ)) (s : ℕ → M) :
    (φ.substSequence xs).Realize s ↔ φ.Realize (sequenceAssignment xs s) := by
  induction xs generalizing φ with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨x,t⟩
    rw [substSequence, ih, realize_subst]
    rfl

theorem sequenceAssignment_not_key (xs : List (ℕ × L.Term ℕ)) (s : ℕ → M) (x : ℕ)
    (hx : x ∉ sequenceKeys xs) : sequenceAssignment xs s x = s x := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨y,t⟩
    have h : x ≠ y ∧ x ∉ sequenceKeys ps := by simpa only [sequenceKeys, Finset.mem_insert, not_or] using hx
    simp only [sequenceAssignment, Function.update_of_ne h.1, ih h.2]

theorem term_realize_sequenceAssignment (t : L.Term ℕ) (xs : List (ℕ × L.Term ℕ)) (s : ℕ → M)
    (h : Disjoint t.varFinset (sequenceKeys xs)) : t.realize (sequenceAssignment xs s) = t.realize s := by
  apply term_realize_congr
  intro x hx
  exact sequenceAssignment_not_key xs s x (fun hk => Finset.disjoint_left.mp h hx hk)

/-- If keys do not occur in replacement terms, each replacement is evaluated in the original assignment. -/
theorem sequenceAssignment_mem (xs : List (ℕ × L.Term ℕ)) (s : ℕ → M)
    (hkeys : (xs.map Prod.fst).Nodup)
    (hvars : Disjoint (sequenceVars xs) (sequenceKeys xs))
    (p : ℕ × L.Term ℕ) (hp : p ∈ xs) : sequenceAssignment xs s p.1 = p.2.realize s := by
  induction xs with
  | nil => simp at hp
  | cons q qs ih =>
    rcases q with ⟨x,t⟩
    have hk : x ∉ qs.map Prod.fst ∧ (qs.map Prod.fst).Nodup := by simpa using hkeys
    have hv : Disjoint t.varFinset (insert x (sequenceKeys qs)) ∧
        Disjoint (sequenceVars qs) (insert x (sequenceKeys qs)) := by
      simpa only [sequenceVars, sequenceKeys, Finset.disjoint_union_left] using hvars
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [sequenceAssignment, Function.update_self]
      apply term_realize_sequenceAssignment
      exact hv.1.mono_right (Finset.subset_insert _ _)
    · have hpx : p.1 ≠ x := by
        intro he
        exact hk.1 (he ▸ List.mem_map_of_mem hp)
      rw [sequenceAssignment, Function.update_of_ne hpx]
      exact ih hk.2 (hv.2.mono_right (Finset.subset_insert _ _)) hp

end Semantics

/-- Original input names are moved into a disjoint block. -/
def renameInputs (n B : ℕ) : List (ℕ × L.Term ℕ) :=
  List.ofFn (fun i : Fin n => (i.val, .var (B + i.val)))

/-- The temporary names are replaced by the actual arguments. -/
def fillInputs {n : ℕ} (ts : Fin n → L.Term ℕ) (B : ℕ) : List (ℕ × L.Term ℕ) :=
  List.ofFn (fun i : Fin n => (B + i.val, ts i))

def argumentVars {n : ℕ} (ts : Fin n → L.Term ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => (ts i).varFinset)

def temporaryNames (n B : ℕ) : Finset ℕ := (Finset.range n).image (fun x => B + x)

@[simp] theorem keys_renameInputs (n B : ℕ) : sequenceKeys (renameInputs (L := L) n B) = Finset.range n := by
  ext x
  simp [renameInputs, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact i.isLt
  · intro hx; exact ⟨⟨x,hx⟩, rfl⟩

@[simp] theorem vars_renameInputs (n B : ℕ) :
    sequenceVars (renameInputs (L := L) n B) = temporaryNames n B := by
  ext x
  simp [renameInputs, temporaryNames, List.mem_ofFn, Term.varFinset]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i.val, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i,hi⟩, rfl⟩

@[simp] theorem keys_fillInputs {n : ℕ} (ts : Fin n → L.Term ℕ) (B : ℕ) :
    sequenceKeys (fillInputs ts B) = temporaryNames n B := by
  ext x
  simp [fillInputs, temporaryNames, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i.val, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i,hi⟩, rfl⟩

@[simp] theorem vars_fillInputs {n : ℕ} (ts : Fin n → L.Term ℕ) (B : ℕ) :
    sequenceVars (fillInputs ts B) = argumentVars ts := by
  ext x
  simp [fillInputs, argumentVars, List.mem_ofFn]

/-- Two substitution passes, parametrized by the fresh block's starting point. -/
def simultaneousAt {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ) (B : ℕ) : AlphaFormula L :=
  (φ.substSequence (renameInputs n B)).substSequence (fillInputs ts B)

theorem fv_simultaneousAt_subset {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ) (B : ℕ) :
    (φ.simultaneousAt ts B).fv ⊆ (φ.fv \ Finset.range n) ∪ argumentVars ts := by
  intro x hx
  have h := fv_substSequence_subset (φ.substSequence (renameInputs n B)) (fillInputs ts B) hx
  rw [keys_fillInputs, vars_fillInputs] at h
  rcases Finset.mem_union.mp h with h | h
  · have hr := fv_substSequence_subset φ (renameInputs n B) (Finset.mem_sdiff.mp h).1
    rw [keys_renameInputs, vars_renameInputs] at hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact Finset.mem_union_left _ hr
    · exact ((Finset.mem_sdiff.mp h).2 hr).elim
  · exact Finset.mem_union_right _ h

section SimultaneousSemantics
variable {M : Type w} [L.Structure M]

/-- The two passes act on each original name by the simultaneous input assignment. -/
theorem sequenceInputs_apply {n : ℕ} (ts : Fin n → L.Term ℕ) (B : ℕ)
    (hn : n ≤ B) (ht : ∀ i x, x ∈ (ts i).varFinset → x < B)
    (s : ℕ → M) (x : ℕ) (hx : x ∉ temporaryNames n B) :
    sequenceAssignment (renameInputs (L := L) n B) (sequenceAssignment (fillInputs ts B) s) x =
      if h : x < n then (ts ⟨x,h⟩).realize s else s x := by
  have hkr : ((renameInputs (L := L) n B).map Prod.fst).Nodup := by
    simp only [renameInputs, List.map_ofFn, Function.comp_def]
    exact List.nodup_ofFn.mpr (fun i j h => Fin.ext h)
  have hkf : ((fillInputs ts B).map Prod.fst).Nodup := by
    simp only [fillInputs, List.map_ofFn, Function.comp_def]
    exact List.nodup_ofFn.mpr (fun i j h => Fin.ext (Nat.add_left_cancel h))
  have hvr : Disjoint (sequenceVars (renameInputs (L := L) n B)) (sequenceKeys (renameInputs (L := L) n B)) := by
    rw [vars_renameInputs, keys_renameInputs]
    apply Finset.disjoint_left.mpr
    intro x hx hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have := Finset.mem_range.mp hk
    omega
  have hvf : Disjoint (sequenceVars (fillInputs ts B)) (sequenceKeys (fillInputs ts B)) := by
    rw [vars_fillInputs, keys_fillInputs]
    apply Finset.disjoint_left.mpr
    intro x hx hk
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    have hlt := ht i x hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    omega
  by_cases hxn : x < n
  · let i : Fin n := ⟨x,hxn⟩
    have hr := sequenceAssignment_mem (renameInputs (L := L) n B)
      (sequenceAssignment (fillInputs ts B) s) hkr hvr (x, .var (B+x))
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have hf := sequenceAssignment_mem (fillInputs ts B) s hkf hvf (B+x,ts i)
      (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [Term.realize_var, dite_eq_left hxn] using hr.trans hf
  · rw [sequenceAssignment_not_key _ _ x (by simpa using hxn)]
    rw [sequenceAssignment_not_key _ _ x]
    · simp [hxn]
    · simpa only [keys_fillInputs] using hx


theorem realize_simultaneousAt {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ) (B : ℕ)
    (hn : n ≤ B) (hφ : ∀ x ∈ φ.fv, x < B) (ht : ∀ i x, x ∈ (ts i).varFinset → x < B)
    (s : ℕ → M) :
    (φ.simultaneousAt ts B).Realize s ↔
      φ.Realize (fun x => if h : x < n then (ts ⟨x,h⟩).realize s else s x) := by
  rw [simultaneousAt, realize_substSequence, realize_substSequence]
  apply φ.realize_congr
  intro x hx
  apply sequenceInputs_apply ts B hn ht s x
  intro hk
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hk
  have := hφ x hx
  omega

end SimultaneousSemantics

/-- One bound avoids all original free variables, all inputs, and all replacement variables. -/
def substitutionBound {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ) : ℕ :=
  (φ.fv ∪ Finset.range n ∪ argumentVars ts).sup id + 1

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Carry out two passes of the already defined capture-avoiding single-variable substitution:
    $$\begin{aligned}
    \varphi_0&:=\varphi,&
    \varphi_i&:=\varphi_{i-1}\subst{x_i}{z_i},\\
    \psi_0&:=\varphi_n,&
    \psi_i&:=\psi_{i-1}\subst{z_i}{t_i}
    \qquad(1\le i\le n).
    \end{aligned}$$
    Set $\varphi\subst{\vec{x}}{\vec{t}}:=\psi_n$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    When several variables are replaced, the substitution is simultaneous: a later replacement must not alter a term
    inserted by an earlier one. Number the pairwise distinct formal input variables as $x_1,\ldots,x_n$.
-/
def simultaneous {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ) : AlphaFormula L :=
  φ.simultaneousAt ts (φ.substitutionBound ts)

/-- The selected block avoids the input names and every relevant free variable. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Choose pairwise distinct temporary variables $z_1,\ldots,z_n$ outside the input variables and the free variables
    of the original formula and all replacement terms. Such names exist by taking their indices above all indices
    in these finite sets.
-/
theorem substitutionBound_spec {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ) :
    n ≤ φ.substitutionBound ts ∧ (∀ x ∈ φ.fv, x < φ.substitutionBound ts) ∧
      ∀ i x, x ∈ (ts i).varFinset → x < φ.substitutionBound ts := by
  have bound (x : ℕ) (hx : x ∈ φ.fv ∪ Finset.range n ∪ argumentVars ts) : x < φ.substitutionBound ts :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    have hlt : φ.substitutionBound ts < n := Nat.lt_of_not_ge hn
    exact (lt_irrefl _ (bound _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_range.mpr hlt)))))
  · intro x hx
    exact bound x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  · intro i x hx
    exact bound x (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Simultaneous substitution
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Apply the single-variable substitution lemma successively, starting from the last substitution.
    In the second pass, later substitutions change only temporary variables, which occur in none of the replacement
    terms. Hence every replacement term is evaluated in the original assignment $s$.
    In the first pass, later substitutions change only input variables, so they leave the temporary names unchanged.
    Thus each original input variable receives its corresponding term value. Other original free variables keep
    their values, because they are not temporary names. Assignment locality gives the asserted equivalence.
-/
theorem realize_simultaneous {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ)
    {M : Type w} [L.Structure M] (s : ℕ → M) :
    (φ.simultaneous ts).Realize s ↔
      φ.Realize (fun x => if h : x < n then (ts ⟨x,h⟩).realize s else s x) := by
  have h := substitutionBound_spec φ ts
  exact realize_simultaneousAt φ ts _ h.1 h.2.1 h.2.2 s

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For free variables, each single substitution removes its target variable and introduces only variables of its
    replacement term. After the first pass, the only possible extra free variables are the temporary names; the
    second pass removes all of them and introduces only free variables of the replacement terms.
-/
theorem fv_simultaneous_subset {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ) :
    (φ.simultaneous ts).fv ⊆ (φ.fv \ Finset.range n) ∪ argumentVars ts :=
  fv_simultaneousAt_subset φ ts _

/-- Substituting closed parameters leaves only the distinguished input name free. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This covers closed parameters as well. If $\theta(x,\vec y)$ is an $L_H$-formula and $\vec r$ is a tuple of closed
    $L_H$-terms, then $\theta(x,\vec r)$ has free variables only among $x$ and belongs to a finite stage.
    Its Henkin axiom supplies a constant witnessing $\exists x\,\theta(x,\vec r)$.
-/
theorem fv_closed_parameter_instance {n : ℕ} (φ : AlphaFormula L)
    (hφ : φ.fv ⊆ Finset.range (n + 1)) (x : ℕ) (rs : Fin n → L.Term Empty) :
    (φ.simultaneous (Fin.cons (.var x) (fun i => namedClosedTerm (rs i)))).fv ⊆ {x} := by
  intro y hy
  have h := fv_simultaneous_subset φ (Fin.cons (.var x) (fun i => namedClosedTerm (rs i))) hy
  rcases Finset.mem_union.mp h with h | h
  · exact False.elim ((Finset.mem_sdiff.mp h).2 (hφ (Finset.mem_sdiff.mp h).1))
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    cases i using Fin.cases with
    | zero => simpa using hi
    | succ i => simp at hi

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
