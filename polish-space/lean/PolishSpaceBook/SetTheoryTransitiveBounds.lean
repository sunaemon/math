module

public import PolishSpaceBook.SetTheoryGraphOperations

@[expose] public section

/-! # Internal transitive bounds from recursion on the actual natural numbers -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def transitiveStep (x _a g : ZFSet.{u}) : ZFSet.{u} :=
  insert x (ZFSet.sUnion (ZFSet.sUnion (graphRange g)))

/-- Parameters x, input a, preceding graph g, and output b, in that order. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Fix $x\in M$ and use the step rule
    $$H_x(a,g):=\{x\}\cup\bigcup\bigcup\GraphRange{g}.$$
    The preceding range construction, two unions, and insertion show that this rule has values in the model.
    An internal defining formula is
    $$\begin{aligned}
    \psi_x(a,g,b)\;:\equiv\;\exists r\,\exists u\,\exists v\,\bigl(
     r=\GraphRange{g}\land u=\bigcup r\\
    {}\land v=\bigcup u\land b=\{x\}\cup v\bigr).
    \end{aligned}$$
    Expand the range equality as above, the union equalities by their membership clauses, and the last equality
    as $\forall z\,(z\in b\leftrightarrow z=x\lor z\in v)$.
    All three intermediate sets belong to the model, so this formula defines exactly $H_x(a,g)$ internally.
-/
def transitiveStepFormula : ForcingFormulas.Formula 4 :=
  (rangeFormula (2 : Fin 7) 4 ⊓ unionFormula 4 5 ⊓ unionFormula 5 6 ⊓ insertFormula 0 6 3).ex.ex.ex

lemma transitiveStep_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1))
    (x a g : M) : transitiveStep x.val a.val g.val ∈ M :=
  insert_mem hM hpair hunion x.property
    (union_mem hM hunion (union_mem hM hunion (graphRange_mem hM hunion hsep g.property)))

lemma realize_transitiveStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : M ⊨ separationSentence (rangeMemberFormula (0 : Fin 2) 1)) (x a g b : M) :
    transitiveStepFormula.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ![x] a) g) b) ↔
      b.val = transitiveStep x.val a.val g.val := by
  simp only [transitiveStepFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_rangeFormula hM hunion, realize_unionFormula hM, realize_insertFormula hM]
  simp only [Fin.snoc]
  constructor
  · rintro ⟨r, u, v, ⟨⟨hr, hu⟩, hv⟩, hb⟩
    exact hb.trans (by rw [hv, hu, hr]; rfl)
  · intro hb
    let r : M := ⟨graphRange g.val, graphRange_mem hM hunion hsep g.property⟩
    let u : M := ⟨ZFSet.sUnion r.val, union_mem hM hunion r.property⟩
    let v : M := ⟨ZFSet.sUnion u.val, union_mem hM hunion u.property⟩
    exact ⟨r, u, v, ⟨⟨rfl, rfl⟩, rfl⟩, hb⟩

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    By the preceding lemma, $\omega\in M$ is an actual transitive set.
    Internal membership recursion therefore gives $F\in M$ with domain $\omega$ and
    $$F(n)=\{x\}\cup\bigcup\bigcup\GraphRange{\restrict{F}{n}}\qquad(n\in\omega).$$
    Set $T:=\bigcup\GraphRange{F}\in M$. Since $x\in F(0)$, we have $x\in T$.
    To prove transitivity, suppose $z\in y\in T$. Choose $n\in\omega$ with $y\in F(n)$.
    The pair $\langle n,F(n)\rangle$ belongs to $\restrict{F}{n+1}$, so
    $$\begin{aligned}
    F(n)&\in\GraphRange{\restrict{F}{n+1}},\\
    z&\in\bigcup\bigcup\GraphRange{\restrict{F}{n+1}}\IncludedIn F(n+1).
    \end{aligned}$$
    Thus $z\in T$, as required. The construction collects the entire graph by the previously proved recursion
    theorem; it does not infer that an externally chosen infinite sequence belongs to the model.
    \end{proof}
-/
lemma transitive_bound_of_solution {x f : ZFSet.{u}}
    (hf : IsRecursiveSolution (transitiveStep x) Ordinal.omega0.toZFSet f) :
    x ∈ ZFSet.sUnion (graphRange f) ∧ (ZFSet.sUnion (graphRange f)).IsTransitive := by
  have hn (n : ℕ) : natOrdinal n ∈ Ordinal.omega0.toZFSet := mem_omegaOrdinal.mpr ⟨n, rfl⟩
  constructor
  · have hpair := hf.equation (natOrdinal 0) (hn 0)
    exact ZFSet.mem_sUnion.mpr ⟨_, mem_graphRange.mpr ⟨_, hpair⟩, ZFSet.mem_insert _ _⟩
  · intro y hy z hz
    obtain ⟨v, hv, hyv⟩ := ZFSet.mem_sUnion.mp hy
    obtain ⟨a, hav⟩ := mem_graphRange.mp hv
    have ha := (ZFSet.pair_mem_prod.mp (hf.function_graph.1 hav)).1
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp ha
    have hprev : ZFSet.pair (natOrdinal n) v ∈ restrictGraph f (natOrdinal (n + 1)) :=
      pair_mem_restrictGraph.mpr ⟨hav, mem_natOrdinal.mpr ⟨n, Nat.lt_succ_self n, rfl⟩⟩
    have hvprev := mem_graphRange.mpr ⟨natOrdinal n, hprev⟩
    have hzprev : z ∈ ZFSet.sUnion (ZFSet.sUnion (graphRange (restrictGraph f (natOrdinal (n + 1))))) :=
      ZFSet.mem_sUnion.mpr ⟨y, ZFSet.mem_sUnion.mpr ⟨v, hvprev, hyv⟩, hz⟩
    have hnext := hf.equation (natOrdinal (n + 1)) (hn (n + 1))
    exact ZFSet.mem_sUnion.mpr ⟨_, mem_graphRange.mpr ⟨_, hnext⟩,
      ZFSet.mem_insert_iff.mpr (Or.inr hzprev)⟩

/-- Infinity, internal recursion, and graph operations provide a transitive bound for every input. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Internal transitive bounds
-/
theorem internal_transitive_bound {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (x : M) : ∃ T ∈ M, x.val ∈ T ∧ T.IsTransitive := by
  let ωM : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  obtain ⟨F, hF, _⟩ := internal_membership_recursion hM hpair hunion hpower hsep hrep
    transitiveStepFormula ![x] (transitiveStep x.val)
    (fun a g b => realize_transitiveStepFormula hM hunion (hsep _) x a g b)
    (fun a g => transitiveStep_mem hM hpair hunion (hsep _) x a g) ωM
    (ZFSet.isOrdinal_toZFSet _).isTransitive
  exact ⟨ZFSet.sUnion (graphRange F.val), union_mem hM hunion (graphRange_mem hM hunion (hsep _) F.property),
    transitive_bound_of_solution hF⟩

/-- With internal transitive bounds, the recursive-value formula is total on the model. -/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    For $a\in M$, choose a transitive $T\in M$ containing $a$, and apply internal membership recursion on $T$.
    It gives a graph $F\in M$ assigning a value $b$ at $a$. Because $\langle a,b\rangle\in F$,
    transitivity gives $b\in M$. The domain and graph witness $\nu(a,b,\vec p)$ internally.
    Agreement of partial solutions gives uniqueness, independently of the chosen transitive bound.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: corollary
  title: Existence of internal recursive values
-/
theorem internal_recursive_value_existsUnique {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    {n : ℕ} (ψ : ForcingFormulas.Formula (n + 3)) (ps : Fin n → M)
    (H : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (hH : ∀ a g b : M,
      ψ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) ↔ b.val = H a.val g.val)
    (hclosed : ∀ a g : M, H a.val g.val ∈ M) (a : M) :
    ∃! b : M, (recursiveValueFormula ψ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  obtain ⟨T, hT, haT, hTt⟩ := internal_transitive_bound hM hinf hpair hunion hpower hsep hrep a
  obtain ⟨F, hF, _⟩ := internal_membership_recursion hM hpair hunion hpower hsep hrep ψ ps H hH hclosed
    ⟨T, hT⟩ hTt
  obtain ⟨b, hab, _⟩ := hF.function_graph.2 a.val haT
  have hbM : b ∈ M := hM.mem_trans (second_mem_doubleUnion hab)
    (union_mem hM hunion (union_mem hM hunion F.property))
  have hb := (realize_recursiveValueFormula hM hunion (hsep _) ψ ps H hH a ⟨b, hbM⟩).mpr
    ⟨⟨T, hT⟩, F, hF, haT, hab⟩
  exact ⟨⟨b, hbM⟩, hb, fun c hc => recursive_value_unique hM hunion (hsep _) ψ ps H hH a c ⟨b, hbM⟩ hc hb⟩

end PolishSpaceBook.SetTheoryModels
