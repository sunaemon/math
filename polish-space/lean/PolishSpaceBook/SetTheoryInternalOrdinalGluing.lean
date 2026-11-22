module

public import PolishSpaceBook.SetTheoryOrdinalGluing
public import PolishSpaceBook.SetTheoryInitialOrdinalFormulas

@[expose] public section

/-! # Replacement assembles internal predecessor representations

The hypothesis supplies only representations of proper predecessor segments.
The ordinal of the whole order and its graph are constructed by two explicit
Replacement instances, using the uniquely defined predecessor order type.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: prose
  excerpt: |
    Replacement for $\psi$ collects the values, and Replacement for its ordered-pair selector collects the graph:
    $$\alpha:=\{\beta_a:a\in W\}\in M,\qquad
      F:=\{\langle a,\beta_a\rangle:a\in W\}\in M.$$
    The graph construction is the definable-graph lemma in §{sec:internal-model-closure}; Pairing supplies
    its ordered-pair witnesses. These are explicit Replacement instances, so no external choice of a graph in $M$
    is being assumed.
    The set $\alpha$ is transitive. If $\delta\in\beta_a$, surjectivity of $f_a$ gives $xRa$ with
    $f_a(x)=\delta$. The compatibility just proved gives $\beta_x=f_a(x)=\delta$, hence $\delta\in\alpha$.
    Every member $\beta_a$ is an ordinal. The transitive-set-of-ordinals characterization therefore makes $\alpha$
    an ordinal, and the membership equivalence makes $F$ an order-isomorphism onto it.
    The recognition lemma supplies the internal assertion and uniqueness. This also covers $W=\emptyset$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-internal-models.md
  target: statement
  kind: lemma
  title: Gluing internal ordinal representations
-/
theorem internal_ordinalIso_glue {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (A R : M) [IsStrictTotalOrder A.val (fun x y : A.val => pair x.val y.val ∈ R.val)]
    (hlocal : ∀ a : A.val, ∃ β : M,
      initialOrdinalFormula.Realize Empty.elim ![A, R, ⟨a.val, hM.mem_trans a.property A.property⟩, β]) :
    ∃ α F : M, ordinalIsoFormula.Realize Empty.elim ![A, R, α, F] := by
  let β : A.val → M := fun a => Classical.choose (hlocal a)
  have hβ (a : A.val) : initialOrdinalFormula.Realize Empty.elim
      ![A, R, ⟨a.val, hM.mem_trans a.property A.property⟩, β a] := Classical.choose_spec (hlocal a)
  have hdef (a : A.val) (b : M) : initialOrdinalFormula.Realize Empty.elim
      (Fin.snoc (Fin.snoc ![A, R] ⟨a.val, hM.mem_trans a.property A.property⟩) b) ↔ b = β a := by
    have hs : Fin.snoc (Fin.snoc ![A, R] ⟨a.val, hM.mem_trans a.property A.property⟩) b =
        ![A, R, ⟨a.val, hM.mem_trans a.property A.property⟩, b] := by
      funext i
      fin_cases i <;> rfl
    rw [hs]
    exact ⟨fun hb => initialOrdinal_unique hM A R _ b (β a) hb (hβ a), fun he => he.symm ▸ hβ a⟩
  have hrange : ZFSet.range (fun a => (β a).val) ∈ M :=
    replacement_image_mem hM initialOrdinalFormula (hrep _) ![A, R] A.property β hdef
  have hgraph : functionGraph (fun a => (β a).val) ∈ M :=
    replacement_graph_mem hM hpair initialOrdinalFormula (hrep _) ![A, R] A.property β hdef
  have hre (a : A.val) : (β a).val.IsOrdinal ∧ Nonempty
      ((fun x y : orderPredecessors A.val R.val a.val => pair x.val y.val ∈ R.val) ≃r
        (fun b c : (β a).val => b.val ∈ c.val)) := by
    obtain ⟨D, f, hD, hf⟩ := (realize_initialOrdinalFormula hM A R _ (β a)).mp (hβ a)
    obtain ⟨ho, e, _⟩ := (realize_ordinalIsoFormula hM D R (β a) f).mp hf
    rw [hD] at e
    exact ⟨ho, ⟨e⟩⟩
  let e := fun a => (hre a).2.some
  let α : M := ⟨ZFSet.range (fun a => (β a).val), hrange⟩
  let F : M := ⟨functionGraph (fun a => (β a).val), hgraph⟩
  refine ⟨α, F, (realize_ordinalIsoFormula hM A R α F).mpr ?_⟩
  refine ⟨ordinalInitial_range_isOrdinal (fun a => (β a).val) (fun a => (hre a).1) e,
    ordinalGluingIso (fun a => (β a).val) (fun a => (hre a).1) e, rfl⟩

end PolishSpaceBook.SetTheoryModels
