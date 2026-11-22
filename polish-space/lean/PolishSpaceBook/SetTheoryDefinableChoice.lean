module

public import PolishSpaceBook.SetTheoryCollection
public import PolishSpaceBook.SetTheoryLeastChoice
public import PolishSpaceBook.SetTheoryFunctionClosure

@[expose] public section

/-! # Whole choice graphs for internally definable families

The predicate need not be absolute. Separation forms its internal fibers,
Replacement collects their family and graph, and internal Choice selects from
those fibers. Collection first bounds witnesses when no bound is supplied.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Parameters ps,B; input a and output r. The last quantified variable is a candidate value. -/
def choiceFiberFormula {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 3) :=
  ((memberAt (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc).iff
    (memberAt (Fin.last (n + 3)) (Fin.last n).castSucc.castSucc.castSucc ⊓
      reindex φ (Fin.snoc (Fin.snoc (fun i => i.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 1)).castSucc.castSucc) (Fin.last (n + 3))))).all

lemma realize_choiceFiberFormula {M : ZFSet.{u}} {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (B a r : M) :
    (choiceFiberFormula φ).Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps B) a) r) ↔
      ∀ b : M, b.val ∈ r.val ↔ b.val ∈ B.val ∧
        φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  simp only [choiceFiberFormula, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf, realize_memberAt_model, realize_reindex,
    apply_snoc, Function.comp_def, Fin.snoc_castSucc, Fin.snoc_last]

/-- Select internally from a bounded definable family, without assuming absoluteness of its predicate. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal definable choice
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The internal Collection theorem gives $\mathcal W\in M$ containing a suitable witness for every input.
    For each $\alpha\in \mathcal D$, internal Separation gives the nonempty set
    $$R_\alpha:=\{\beta\in \mathcal W:M\models\varphi(\alpha,\beta,\vec p)\}\in M.$$
    The first-order formula
    $$\psi(\alpha,r):\equiv\forall \beta\;
    \bigl(\beta\in r\longleftrightarrow \beta\in \mathcal W\land\varphi(\alpha,\beta,\vec p)\bigr)$$
    defines this set uniquely inside $M$, by Extensionality. Replacement and the graph-construction lemma give
    $$\mathcal R:=\{R_\alpha:\alpha\in \mathcal D\}\in M,\qquad
     g:=\{\Pair{\alpha}{R_\alpha}:\alpha\in \mathcal D\}\in M.$$
    Choice inside $M$ gives a graph $c:\mathcal R\to\bigcup\mathcal R$ in $M$ with $c(r)\in r$.
    The formula
    $$\theta(\alpha,\beta):\equiv\exists r\;
    \bigl(\Pair{\alpha}{r}\in g\land\Pair{r}{\beta}\in c\bigr)$$
    defines a unique value for each input. Applying the same graph-construction lemma gives the entire graph
    $f\in M$. Its value belongs to $R_\alpha$, hence to $\mathcal W$, and satisfies the original formula inside $M$.
    If a witness bound $\mathcal W\in M$ is already available, the Collection step is unnecessary.
-/
theorem internal_bounded_definable_choice {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence ψ)
    (hrep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence ψ)
    (hchoice : M ⊨ choiceSentence) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (D B : M)
    (htotal : ∀ a : M, a.val ∈ D.val → ∃ b : M, b.val ∈ B.val ∧
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃ f : M, IsFunc D.val B.val f.val ∧ ∀ a b : M, pair a.val b.val ∈ f.val →
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  let input (a : D.val) : M := ⟨a.val, hM.mem_trans a.property D.property⟩
  have hex (a : D.val) : ∃ r : M, ∀ b : M, b.val ∈ r.val ↔ b.val ∈ B.val ∧
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps (input a)) b) :=
    (realize_separation M φ).mp (hsep _) (Fin.snoc ps (input a)) B
  choose r hr using hex
  have hdef (a : D.val) (z : M) :
      (choiceFiberFormula φ).Realize Empty.elim
        (Fin.snoc (Fin.snoc (Fin.snoc ps B) (input a)) z) ↔ z = r a := by
    rw [realize_choiceFiberFormula]
    constructor
    · intro hz
      apply (models_extensionality_iff M).mp (models_extensionality hM) z (r a)
      intro b
      exact (hz b).trans (hr a b).symm
    · rintro rfl
      exact hr a
  let R := ZFSet.range (fun a : D.val => (r a).val)
  have hRM : R ∈ M := replacement_image_mem hM (choiceFiberFormula φ) (hrep _)
    (Fin.snoc ps B) D.property r hdef
  let G := functionGraph (fun a : D.val => (r a).val)
  have hGM : G ∈ M := replacement_graph_mem hM hpair (choiceFiberFormula φ) (hrep _)
    (Fin.snoc ps B) D.property r hdef
  have hnonempty : ∀ z ∈ R, ∃ b, b ∈ z := by
    intro z hz
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hz
    obtain ⟨b, hb, hφ⟩ := htotal (input a) a.property
    exact ⟨b.val, (hr a b).mpr ⟨hb, hφ⟩⟩
  obtain ⟨c, hc, hs⟩ := (models_choice_iff hM hunion).mp hchoice ⟨R, hRM⟩ hnonempty
  have hpick (a : D.val) : ∃ b : M, b.val ∈ (r a).val ∧ pair (r a).val b.val ∈ c.val := by
    obtain ⟨b, hb, hcb⟩ := hs (r a).val (ZFSet.mem_range.mpr ⟨a, rfl⟩)
    exact ⟨⟨b, hM.mem_trans hb (r a).property⟩, hb, hcb⟩
  choose pick hmem hpairpick using hpick
  have hthrough (a : D.val) : ThroughGraphs G c.val a.val (pick a).val :=
    ⟨(r a).val, ZFSet.mem_range.mpr ⟨a, rfl⟩, hpairpick a⟩
  have hselector (a : D.val) (b : M) :
      (throughGraphsFormula (0 : Fin 4) 1 2 3).Realize Empty.elim
        (Fin.snoc (Fin.snoc ![⟨G, hGM⟩, c] (input a)) b) ↔ b = pick a := by
    rw [realize_throughGraphsFormula hM hunion]
    change ThroughGraphs G c.val a.val b.val ↔ b = pick a
    exact ⟨fun hb => Subtype.ext (throughGraphs_unique (functionGraph_isFunc _) hc hb (hthrough a)),
      fun hb => hb ▸ hthrough a⟩
  let f := functionGraph (fun a : D.val => (pick a).val)
  have hfM : f ∈ M := replacement_graph_mem hM hpair (throughGraphsFormula (0 : Fin 4) 1 2 3)
    (hrep _) ![⟨G, hGM⟩, c] D.property pick hselector
  refine ⟨⟨f, hfM⟩, ⟨?_, (functionGraph_isFunc _).2⟩, ?_⟩
  · intro p hp
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨a.property, ((hr a (pick a)).mp (hmem a)).1⟩
  · intro a b hab
    obtain ⟨d, hd⟩ := ZFSet.mem_range.mp hab
    obtain ⟨ha, hb⟩ := ZFSet.pair_inj.mp hd
    have ha' : input d = a := Subtype.ext ha
    have hb' : pick d = b := Subtype.ext hb
    simpa only [ha', hb'] using ((hr d (pick d)).mp (hmem d)).2

/-- Collection supplies a common bound before the bounded choice construction is used. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal definable choice
-/
theorem internal_definable_choice {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence ψ)
    (hrep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence ψ)
    (hchoice : M ⊨ choiceSentence) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (D : M)
    (htotal : ∀ a : M, a.val ∈ D.val → ∃ b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b)) :
    ∃ B f : M, IsFunc D.val B.val f.val ∧ ∀ a b : M, pair a.val b.val ∈ f.val →
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  obtain ⟨B, hB⟩ := collection_in_model hM hinf hpair hunion hpower hsep hrep φ ps D htotal
  obtain ⟨f, hf, hφ⟩ := internal_bounded_definable_choice hM hpair hunion hsep hrep hchoice φ ps D B hB
  exact ⟨B, f, hf, hφ⟩

end PolishSpaceBook.SetTheoryModels
