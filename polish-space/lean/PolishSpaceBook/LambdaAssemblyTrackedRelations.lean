module

public import PolishSpaceBook.LambdaAssemblies

@[expose] public section

/-! # Functional relations retaining the input realizer of a tracked assembly map -/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
namespace Assembly
universe u

/-- The input index itself realizes the relation; its transformed index realizes the output. -/
def trackedRelationValue {A B : Assembly.{u}} (f : Hom A B) (t : ℕ → ℕ)
    (x : A.Carrier) (y : B.Carrier) : Set ℕ :=
  {e | e ∈ A.realizes x ∧ t e ∈ B.realizes y ∧ y = f.toFun x}

/-- All four trackers are numerical lambda programs; no underlying point is computed. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    We verify all four conditions for $D$. Strictness is tracked by
    $$e\longmapsto\NatPair{e}{t(e)}.$$
    The two components realize the input and output extents. For extensionality, the equality realizers imply that the
    input representatives are equal and the output representatives are equal. Retain the middle relation realizer:
    $$\NatPair{\NatPair{r}{e}}{s}\longmapsto e.$$
    For single-valuedness, if $e\in D(x,y)$ and $e'\in D(x,y')$, then $y=y'=2x$, and $t(e)$ realizes $y\sim_A y'$.
    Thus its tracker is
    $$\NatPair{e}{e'}\longmapsto t(e).$$
    For totality, keep the input realizer $e$. The element $2x$ supplies the semantic witness, and $e\in D(x,2x)$
    because $t(e)$ realizes $2x$. These are fixed numerical programs made from projections, pairing, the program for $t$,
    and the identity; none takes an underlying real number as an extra input.
-/
def trackedRelation {A B : Assembly.{u}} (f : Hom A B) (t : ℕ → ℕ)
    (ht : ∃ k, ∀ e, App k e (t e))
    (htrack : ∀ x e, e ∈ A.realizes x → t e ∈ B.realizes (f.toFun x)) :
    FunctionalRelation A.toPER B.toPER where
  val := trackedRelationValue f t
  strict := by
    apply reduces_and_intro
    · exact reduces_of_subset fun _ _ h => ⟨rfl,h.1⟩
    · obtain ⟨k,hk⟩ := ht
      exact (reduces_iff _ _).mpr ⟨k,fun _ e h => ⟨t e,hk e,rfl,h.2.1⟩⟩
  extensional := by
    have hp := (projection_computes false).comp (projection_computes true)
    obtain ⟨k,hk⟩ := Term.closedProgram_surjective _ hp.1
    apply (reduces_iff _ _).mpr
    refine ⟨k,fun p e he => ⟨e.unpair.1.unpair.2,?_,?_⟩⟩
    · unfold App; rw [hk]; exact hp.2 e
    · rcases p with ⟨x,x',y,y'⟩
      have hxx' : x = x' := he.1.1.1
      have hyy' : y = y' := he.2.1
      cases hxx'
      cases hyy'
      exact he.1.2
  single := by
    obtain ⟨k,hk⟩ := ht
    have hp : NumericalComputes (evalProgram k) t :=
      ⟨evalProgram_closed k,fun e => (evalProgram_runs_iff k e (t e)).mpr (hk e)⟩
    have hc := hp.comp (projection_computes true)
    obtain ⟨s,hs⟩ := Term.closedProgram_surjective _ hc.1
    apply (reduces_iff _ _).mpr
    refine ⟨s,fun p e he => ⟨t e.unpair.1,?_,?_,he.1.2.1⟩⟩
    · unfold App; rw [hs]; exact hc.2 e
    · exact he.1.2.2.trans he.2.2.2.symm
  total := reduces_of_subset fun x e he => ⟨f.toFun x,he.2,htrack x e he.2,rfl⟩

/-- The input-realizer presentation and the usual paired graph give the same arrow. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    Finally, $e\mapsto\NatPair{e}{t(e)}$ also sends $D(x,y)$ into the graph relation
    $\Gamma_d(x,y)=E_A(x)\land(d(x)\sim_A y)$. Both are functional relations, so the one-inclusion criterion gives
    $D\equiv\Gamma_d$. Thus this presentation represents exactly the morphism obtained from the assembly embedding.
    \end{proof}
-/
theorem trackedRelation_equiv_graph {A B : Assembly.{u}} (f : Hom A B) (t : ℕ → ℕ)
    (ht : ∃ k, ∀ e, App k e (t e))
    (htrack : ∀ x e, e ∈ A.realizes x → t e ∈ B.realizes (f.toFun x)) :
    (trackedRelation f t ht htrack).Equivalent f.toRelation := by
  apply FunctionalRelation.equivalent_of_le
  apply reduces_and_intro
  · exact reduces_of_subset fun _ _ h => ⟨rfl,h.1⟩
  · obtain ⟨k,hk⟩ := ht
    exact (reduces_iff _ _).mpr
      ⟨k,fun p e h => ⟨t e,hk e,h.2.2.symm,htrack p.1 e h.1⟩⟩

end Assembly
end PolishSpaceBook.LambdaIndexPCA
