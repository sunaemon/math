module

public import PolishSpaceBook.FirstOrderLambdaContexts

@[expose] public section

/-! # Finite synthesis of equality-elimination templates

Binding trees make the selected occurrences explicit: only free leaves bearing
the left-hand variable can be replaced. Bound leaves never participate. The
central completeness theorem uses the existing capture-avoiding substitution
identity for binding trees; it does not assume a template-size bound or an
annotated witness on the input tree.
-/
namespace PolishSpaceBook.NamedLambda.BindingTree

/-- All ways of replacing a subset of free `t` leaves by one distinguished name. -/
def templates (t z : ℕ) : BindingTree → List BindingTree
  | .free v => if v = t then [.free v, .free z] else [.free v]
  | .bound i => [.bound i]
  | .app A B => (templates t z A).flatMap (fun C => (templates t z B).map (.app C))
  | .lam A => (templates t z A).map .lam

/-- The empty subset is always included, even if `t` has no free occurrence. -/
theorem self_mem_templates (A : BindingTree) (t z : ℕ) : A ∈ templates t z A := by
  induction A with
  | free v => by_cases h : v = t <;> simp [templates, h]
  | bound i => simp [templates]
  | app A B ihA ihB =>
    exact List.mem_flatMap.mpr ⟨A, ihA, List.mem_map.mpr ⟨B, ihB, rfl⟩⟩
  | lam A ih => exact List.mem_map.mpr ⟨A, ih, rfl⟩

/-- Substitution preserves every other free name. This is the local freshness
fact needed to choose the distinguished name from the observed source alone. -/
theorem erase_fv_subset_subst (A : BindingTree) (x t : ℕ) :
    A.fv.erase x ⊆ (A.subst x (.free t)).fv := by
  induction A with
  | free v =>
    by_cases h : v = x
    · subst v; simp [fv]
    · simp only [subst, ite_eq_right h, fv]
      exact Finset.erase_subset _ _
  | bound i => simp [fv, subst]
  | app A B ihA ihB =>
    simp only [fv, subst, Finset.erase_union_distrib]
    exact Finset.union_subset_union ihA ihB
  | lam A ih => exact ih

/-- Renaming the distinguished free variable and then instantiating it recovers
any variable instance. Freshness is only needed away from the distinguished variable. -/
theorem subst_fresh_variable (A : BindingTree) (x z t : ℕ) (hz : z ∉ A.fv.erase x) :
    (A.subst x (.free z)).subst z (.free t) = A.subst x (.free t) := by
  induction A with
  | free v =>
    by_cases hx : v = x
    · simp [subst, hx]
    · have hv : v ≠ z := by
        intro h; subst v
        exact hz (by simp [fv, hx])
      simp [subst, hx, hv]
  | bound i => rfl
  | app A B ihA ihB =>
    simp only [fv, Finset.erase_union_distrib, Finset.mem_union, not_or] at hz
    simp only [subst, ihA hz.1, ihB hz.2]
  | lam A ih => exact congrArg lam (ih hz)

/-- No free occurrence means that there is only the empty subset to choose. -/
theorem templates_of_not_mem (A : BindingTree) (t z : ℕ) (ht : t ∉ A.fv) :
    templates t z A = [A] := by
  induction A with
  | free v => simp only [fv, Finset.mem_singleton] at ht; simp [templates, Ne.symm ht]
  | bound i => rfl
  | app A B ihA ihB =>
    simp only [fv, Finset.mem_union, not_or] at ht
    simp [templates, ihA ht.1, ihB ht.2]
  | lam A ih => simp [templates, ih ht]

/-- Closing another name commutes with choosing the free occurrences. -/
theorem templates_close (A : BindingTree) (t z x k : ℕ) (hxt : x ≠ t) (hxz : x ≠ z) :
    templates t z (close x k A) = (templates t z A).map (close x k) := by
  induction A generalizing k with
  | free v =>
    by_cases hvx : v = x
    · subst v; simp [close, templates, hxt]
    · by_cases hvt : v = t
      · subst v; simp [close, templates, hvx, Ne.symm hxz]
      · simp [close, templates, hvx, hvt]
  | bound i => rfl
  | app A B ihA ihB =>
    simp only [close, templates, ihA, ihB, List.flatMap_map, List.map_flatMap, List.map_map]
    rfl
  | lam A ih => simp only [close, templates, ih, List.map_map]; rfl

/-- The original distinguished-variable occurrences select one of the finitely
many subsets of free `t` leaves in the instantiated source. -/
theorem renamed_mem_templates_instance (A : BindingTree) (x t z : ℕ) :
    A.subst x (.free z) ∈ templates t z (A.subst x (.free t)) := by
  induction A with
  | free v =>
    by_cases hx : v = x
    · simp [subst, hx, templates]
    · simp only [subst, ite_eq_right hx]
      exact self_mem_templates _ _ _
  | bound i => simp [subst, templates]
  | app A B ihA ihB =>
    exact List.mem_flatMap.mpr ⟨_, ihA, List.mem_map.mpr ⟨_, ihB, rfl⟩⟩
  | lam A ih => exact List.mem_map.mpr ⟨_, ih, rfl⟩

/-- Every enumerated candidate instantiates back to the given source. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    For every candidate, substituting $t$ back for $z$ recovers $A$, since $z$ was absent from the
    chosen representative and no bound occurrence was replaced. Thus a successful candidate gives
    the required template by taking $\theta=\psi$ and $x=z$.
-/
theorem template_subst_back {A C : BindingTree} {t z : ℕ}
    (hC : C ∈ templates t z A) (hz : z ∉ A.fv) : C.subst z (.free t) = A := by
  induction A generalizing C with
  | free v =>
    have hv : v ≠ z := by simpa only [fv, Finset.mem_singleton, ne_eq, eq_comm] using hz
    by_cases ht : v = t
    · simp only [templates, ite_eq_left ht, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl <;> simp [subst, ht]
    · simp only [templates, ite_eq_right ht, List.mem_singleton] at hC
      subst C; simp [subst, hv]
  | bound i => simp only [templates, List.mem_singleton] at hC; subst C; rfl
  | app A B ihA ihB =>
    obtain ⟨D, hD, hC⟩ := List.mem_flatMap.mp hC
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hC
    simp only [fv, Finset.mem_union, not_or] at hz
    simp only [subst, ihA hD hz.1, ihB hE hz.2]
  | lam A ih =>
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact congrArg lam (ih hD hz)

/-- Finite template synthesis is complete for every pair of variable instances.
The distinguished name is fresh for the observed source; it need not be chosen
from the unknown original witness. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    Conversely, suppose a template $\theta$ and a variable $x$ give the two displayed instances.
    Compare formulas by the positions of their binders, so changes of bound names are ignored.
    Each free occurrence of $x$ in the template becomes a free occurrence of $t$ in $A$.
    Select exactly those occurrences in the candidate construction. Every other free name of the
    template survives in $A$, so the fresh name $z$ cannot be one of these other names.
    The selected candidate therefore represents the template with its distinguished free name replaced by $z$.
    Substituting $r$ for $z$ gives $B$, by compatibility of capture-avoiding substitution with
    $\alpha$-equivalence. The empty subset is included, so the argument also covers vacuous templates
    and the case $t=r$.
-/
theorem exists_template_of_instances (A B D : BindingTree) (x t r z : ℕ)
    (hA : D.subst x (.free t) = A) (hB : D.subst x (.free r) = B)
    (hz : z ∉ A.fv) :
    ∃ C ∈ templates t z A, C.subst z (.free t) = A ∧ C.subst z (.free r) = B := by
  have hf : z ∉ D.fv.erase x := fun h => hz (hA ▸ erase_fv_subset_subst D x t h)
  refine ⟨D.subst x (.free z), ?_, ?_, ?_⟩
  · rw [← hA]; exact renamed_mem_templates_instance D x t z
  · exact (subst_fresh_variable D x z t hf).trans hA
  · exact (subst_fresh_variable D x z r hf).trans hB

/-- The finite construction never creates a dangling bound index. -/
theorem template_scoped {A C : BindingTree} {t z d : ℕ}
    (hC : C ∈ templates t z A) (hA : A.Scoped d) : C.Scoped d := by
  induction A generalizing C d with
  | free v =>
    by_cases ht : v = t
    · simp only [templates, ite_eq_left ht, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl <;> trivial
    · simp only [templates, ite_eq_right ht, List.mem_singleton] at hC
      subst C; trivial
  | bound i => simp only [templates, List.mem_singleton] at hC; subst C; exact hA
  | app A B ihA ihB =>
    obtain ⟨D, hD, hC⟩ := List.mem_flatMap.mp hC
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hC
    exact ⟨ihA hD hA.1, ihB hE hA.2⟩
  | lam A ih =>
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact ih (C := D) (d := d + 1) hD hA


/-- The full subset realizes literal free-leaf substitution. -/
theorem subst_mem_templates (A : BindingTree) (t z : ℕ) :
    A.subst t (.free z) ∈ templates t z A := by
  induction A with
  | free v => by_cases h : v = t <;> simp [subst, templates, h]
  | bound i => simp [subst, templates]
  | app A B ihA ihB => exact List.mem_flatMap.mpr ⟨_, ihA, List.mem_map.mpr ⟨_, ihB, rfl⟩⟩
  | lam A ih => exact List.mem_map.mpr ⟨_, ih, rfl⟩

/-- If no source leaf remains, a subset replacement must have replaced every
source occurrence. This permits a second finite enumeration instead of another
binding-tree substitution interpreter. -/
theorem template_eq_subst_of_not_mem {A B : BindingTree} {t z : ℕ}
    (hB : B ∈ templates t z A) (ht : t ∉ B.fv) : B = A.subst t (.free z) := by
  induction A generalizing B with
  | free v =>
    by_cases hv : v = t
    · subst v
      simp only [templates, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl
      · exact (ht (by simp [fv])).elim
      · simp [subst]
    · simp only [templates, ite_eq_right hv, List.mem_singleton] at hB
      subst B; simp [subst, hv]
  | bound i => simp only [templates, List.mem_singleton] at hB; subst B; rfl
  | app A C ihA ihC =>
    obtain ⟨D, hD, hB⟩ := List.mem_flatMap.mp hB
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hB
    simp only [fv, Finset.mem_union, not_or] at ht
    simp only [subst, ihA hD ht.1, ihC hE ht.2]
  | lam A ih =>
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hB
    exact congrArg lam (ih hD ht)

end PolishSpaceBook.NamedLambda.BindingTree

namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedFirstOrder FirstOrder Language
open ForcingFormulas (membershipLanguage MembershipSymbol)

/-- All names, including bound names; a fresh name for this finite set cannot
be captured by any binder of any enumerated template. -/
def names : FOL → Finset ℕ
  | .falsum => ∅
  | .equal s t => {termName s, termName t}
  | .rel .mem ts => {termName (ts 0), termName (ts 1)}
  | .binary _ φ ψ => names φ ∪ names ψ
  | .quant _ x φ => insert x (names φ)

theorem fv_subset_names (φ : FOL) : φ.fv ⊆ names φ := by
  induction φ with
  | falsum => simp [Formula.fv, names]
  | equal s t => simp [Formula.fv, names, term_varFinset]
  | rel r ts =>
    cases r
    simp [Formula.fv, names, term_varFinset, Fin.forall_fin_two]
  | binary c φ ψ ihφ ihψ => exact Finset.union_subset_union ihφ ihψ
  | quant q x φ ih => exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans ih (Finset.subset_insert _ _))

private theorem tag_templates (k t z : ℕ) :
    BindingTree.templates t z (tag k).bindingTree = [(tag k).bindingTree] :=
  BindingTree.templates_of_not_mem _ _ _ (by simp)

private theorem node_templates (k t z : ℕ) (T : BindingTree) :
    BindingTree.templates t z (.app (tag k).bindingTree T) =
      (BindingTree.templates t z T).map (.app (tag k).bindingTree) := by
  simp [BindingTree.templates, tag_templates]

private theorem free_template {C : BindingTree} {v t z : ℕ}
    (h : C ∈ BindingTree.templates t z (.free v)) : ∃ w, C = .free w := by
  by_cases hv : v = t
  · simp only [BindingTree.templates, ite_eq_left hv, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [BindingTree.templates, ite_eq_right hv, List.mem_singleton] at h
    exact ⟨v, h⟩

/-- Every enumerated binding-tree candidate remains the encoding of an actual
membership formula. Freshness refers only to the given source's finite names. -/
theorem template_is_formula (φ : FOL) (t z : ℕ) (hz : z ∉ names φ)
    {C : BindingTree} (hC : C ∈ BindingTree.templates t z (encode φ).bindingTree) :
    ∃ ψ : FOL, (encode ψ).bindingTree = C := by
  induction φ generalizing C with
  | falsum =>
    simp only [encode, node, Term.bindingTree, node_templates, tag_templates,
      List.map_singleton, List.mem_singleton] at hC
    exact ⟨.falsum, hC.symm⟩
  | equal s r =>
    simp only [encode, node, Term.bindingTree, node_templates, List.mem_map] at hC
    obtain ⟨D, hD, rfl⟩ := hC
    obtain ⟨A, hA, hD⟩ := List.mem_flatMap.mp hD
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hD
    obtain ⟨a, rfl⟩ := free_template hA
    obtain ⟨b, rfl⟩ := free_template hB
    exact ⟨.equal (.var a) (.var b), rfl⟩
  | rel r ts =>
    cases r
    simp only [encode, node, Term.bindingTree, node_templates, List.mem_map] at hC
    obtain ⟨D, hD, rfl⟩ := hC
    obtain ⟨A, hA, hD⟩ := List.mem_flatMap.mp hD
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hD
    obtain ⟨a, rfl⟩ := free_template hA
    obtain ⟨b, rfl⟩ := free_template hB
    exact ⟨.rel .mem ![.var a, .var b], rfl⟩
  | binary c φ ψ ihφ ihψ =>
    simp only [names, Finset.mem_union, not_or] at hz
    simp only [encode, node, Term.bindingTree, node_templates, List.mem_map] at hC
    obtain ⟨D, hD, rfl⟩ := hC
    obtain ⟨A, hA, hD⟩ := List.mem_flatMap.mp hD
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hD
    obtain ⟨α, rfl⟩ := ihφ hz.1 hA
    obtain ⟨β, rfl⟩ := ihψ hz.2 hB
    exact ⟨.binary c α β, rfl⟩
  | quant q x φ ih =>
    simp only [names, Finset.mem_insert, not_or] at hz
    simp only [encode, node, Term.bindingTree, node_templates, List.mem_map] at hC
    obtain ⟨D, hD, rfl⟩ := hC
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hD
    by_cases hxt : x = t
    · subst t
      rw [BindingTree.templates_of_not_mem _ x z (by simp)] at hA
      simp only [List.mem_singleton] at hA
      subst A
      exact ⟨.quant q x φ, rfl⟩
    · rw [BindingTree.templates_close _ t z x 0 hxt (Ne.symm hz.1)] at hA
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      obtain ⟨ψ, rfl⟩ := ih hz.2 hB
      exact ⟨.quant q x ψ, rfl⟩

/-- Binding trees transport the already proved capture-avoiding formula substitution. -/
theorem encode_instance_tree (φ : FOL) (x t : ℕ) :
    (encode (φ.subst x (.var t))).bindingTree =
      (encode φ).bindingTree.subst x (.free t) := by
  have h := (Term.alpha_iff_bindingTree _ _).mp (encode_subst_alpha φ x t)
  exact h.symm.trans (Term.bindingTree_subst _ _ _)

/-- The finite list decides the full, unannotated equality-template relation,
including vacuous templates and equal replacement variables. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: statement
  kind: lemma
  title: Finite equality-template search
-/
theorem equality_templates_iff (A B : FOL) (t r z : ℕ) (hz : z ∉ names A) :
    (∃ C ∈ BindingTree.templates t z (encode A).bindingTree,
      C.subst z (.free r) = (encode B).bindingTree) ↔
    ∃ (φ : FOL) (x : ℕ), (φ.subst x (.var t)).Alpha A ∧ (φ.subst x (.var r)).Alpha B := by
  have hz' : z ∉ (encode A).bindingTree.fv := by
    simpa only [Term.bindingTree_fv, encode_fv] using fun h => hz (fv_subset_names A h)
  constructor
  · rintro ⟨C, hC, hB⟩
    obtain ⟨φ, hφ⟩ := template_is_formula A t z hz hC
    refine ⟨φ, z, ?_, ?_⟩
    · apply (encode_alpha_iff _ _).mp
      apply (Term.alpha_iff_bindingTree _ _).mpr
      rw [encode_instance_tree, hφ]
      exact BindingTree.template_subst_back hC hz'
    · apply (encode_alpha_iff _ _).mp
      apply (Term.alpha_iff_bindingTree _ _).mpr
      rw [encode_instance_tree, hφ]
      exact hB
  · rintro ⟨φ, x, hA, hB⟩
    have hAt := (Term.alpha_iff_bindingTree _ _).mp ((encode_alpha_iff _ _).mpr hA)
    have hBt := (Term.alpha_iff_bindingTree _ _).mp ((encode_alpha_iff _ _).mpr hB)
    rw [encode_instance_tree] at hAt hBt
    obtain ⟨C, hC, _, hB⟩ := BindingTree.exists_template_of_instances _ _ _ x t r z hAt hBt hz'
    exact ⟨C, hC, hB⟩

end PolishSpaceBook.FirstOrderLambdaEncoding
