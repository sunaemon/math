module

public import PolishSpaceBook.CantorApproximationAdmissibility
public import PolishSpaceBook.SetTheoryCountableChoice

@[expose] public section

/-! # Collecting an internally specified family of admissible approximations

The input graphs contain the internal Borel sets and the two natural-number
error parameters. Internal choice collects pairs of tree codes; no inference
from individual internal values to an internal infinite sequence is used.
-/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels
universe u

/-- Seven common parameters, three input graphs, input index, and output pair. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For countable selection, fix all common parameters of $\mathrm{Adm}$. Let $B_n$ be the internal Borel sets
    in question, and let $a_n,b_n\in\omega$ satisfy $0<a_n\le b_n$. The input consists of the three complete graphs
    $$\begin{gathered}
    G_B:=\{\langle n,B_n\rangle:n\in\omega\},\\
    G_a:=\{\langle n,a_n\rangle:n\in\omega\},\qquad
    G_b:=\{\langle n,b_n\rangle:n\in\omega\}.
    \end{gathered}$$
    We require $G_B,G_a,G_b\in M$.
-/
def approximationFamilyFormula : ForcingFormulas.Formula 12 :=
  (pairMemberFormula (7 : Fin 17) 10 12 ⊓
    (pairMemberFormula 8 10 13 ⊓ (pairMemberFormula 9 10 14 ⊓
      (orderedPairFormula 11 15 16 ⊓
        reindex approximationAdmissibleFormula ![0, 1, 2, 3, 4, 5, 12, 6, 15, 16, 13, 14])))).ex.ex.ex.ex.ex

lemma realize_approximationFamilyFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω Mul Pow Add F X F₂ GB Ga Gb n z : M) :
    approximationFamilyFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, F, X, F₂, GB, Ga, Gb, n, z] ↔
      ∃ B a b W V : M, pair n.val B.val ∈ GB.val ∧ pair n.val a.val ∈ Ga.val ∧
        pair n.val b.val ∈ Gb.val ∧ z.val = pair W.val V.val ∧
        approximationAdmissibleFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, F, X, B, F₂, W, V, a, b] := by
  have hp {k : ℕ} (p x y : Fin k) (xs : Fin k → M) :
      (orderedPairFormula p x y).Realize Empty.elim xs ↔ (xs p).val = pair (xs x).val (xs y).val :=
    realize_orderedPairFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) p x y xs
  simp only [approximationFamilyFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_pairMemberFormula_model hM, hp, realize_reindex]
  have he (B a b W V : M) :
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc
        ![Ω, Mul, Pow, Add, F, X, F₂, GB, Ga, Gb, n, z] B) a) b) W) V ∘
        ![(0 : Fin 17), 1, 2, 3, 4, 5, 12, 6, 15, 16, 13, 14] =
        ![Ω, Mul, Pow, Add, F, X, B, F₂, W, V, a, b] := by
    funext i; fin_cases i <;> rfl
  simp only [he]
  rfl

/-- The three lookup graphs are fixed parameters, and the output is the entire graph of code pairs. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal families of admissible approximations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Keep the common parameters and $G_B,G_a,G_b$ fixed. Define a first-order predicate on an input $n$ and
    an output $z$ by
    $$\begin{aligned}
    \Psi(n,z):\equiv{}&\exists B,a,b,W,V\;[\\
    &\langle n,B\rangle\in G_B\land\langle n,a\rangle\in G_a\\
    &{}\land\langle n,b\rangle\in G_b\land z=\langle W,V\rangle\\
    &{}\land\mathrm{Adm}(B,W,V,a,b)].
    \end{aligned}$$
    The lookup graphs force the first three values to be $B_n,a_n,b_n$. The assumed witnesses and Pairing
    show that $\Psi$ is total internally on $\omega$. Apply internal definable choice from
    §{sec:internal-finite-measure-bounds}. It gives an internal function graph on $\omega$ whose value at $n$
    is a pair satisfying $\Psi$.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Reindex this function by the actual natural numbers. Its value at each index is unique, so the resulting
    sequence has exactly the same graph. Unpack each chosen value as $\langle W_n,V_n\rangle$.
    Ordered-pair injectivity and uniqueness of the input lookups give the required admissibility conditions.
    The paired graph $H$ is still the graph supplied by internal choice; it is not a newly chosen external
    sequence of unrelated internal values.
-/
theorem internal_admissible_family {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (Ω Mul Pow Add F X F₂ : M)
    (hΩ : Ω.val = Ordinal.omega0.toZFSet) (B a b : ℕ → M)
    (hGB : sequenceGraph (fun n => (B n).val) ∈ M)
    (hGa : sequenceGraph (fun n => (a n).val) ∈ M)
    (hGb : sequenceGraph (fun n => (b n).val) ∈ M)
    (htotal : ∀ n, ∃ W V : M,
      approximationAdmissibleFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, F, X, B n, F₂, W, V, a n, b n]) :
    ∃ W V : ℕ → M, sequenceGraph (fun n => pair (W n).val (V n).val) ∈ M ∧
      ∀ n, approximationAdmissibleFormula.Realize Empty.elim
        ![Ω, Mul, Pow, Add, F, X, B n, F₂, W n, V n, a n, b n] := by
  let GB : M := ⟨_, hGB⟩
  let Ga : M := ⟨_, hGa⟩
  let Gb : M := ⟨_, hGb⟩
  let ps : Fin 10 → M := ![Ω, Mul, Pow, Add, F, X, F₂, GB, Ga, Gb]
  have hφ (n z : M) :
      approximationFamilyFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ps n) z) ↔
        ∃ C a' b' W V : M, pair n.val C.val ∈ GB.val ∧ pair n.val a'.val ∈ Ga.val ∧
          pair n.val b'.val ∈ Gb.val ∧ z.val = pair W.val V.val ∧
          approximationAdmissibleFormula.Realize Empty.elim
            ![Ω, Mul, Pow, Add, F, X, C, F₂, W, V, a', b'] := by
    have he : Fin.snoc (Fin.snoc ps n) z = ![Ω, Mul, Pow, Add, F, X, F₂, GB, Ga, Gb, n, z] := by
      funext i; fin_cases i <;> rfl
    rw [he, realize_approximationFamilyFormula hM]
  obtain ⟨s, hs, hsel⟩ := internal_countable_choice hM hinf hpair hunion hpower hsep hrep hchoice
    approximationFamilyFormula ps Ω hΩ (by
      intro n hn
      obtain ⟨i, hi⟩ := mem_omegaOrdinal.mp (hΩ ▸ hn)
      obtain ⟨W, V, hWV⟩ := htotal i
      refine ⟨⟨pair W.val V.val, orderedPair_mem hM hpair W.property V.property⟩, (hφ _ _).mpr ?_⟩
      refine ⟨B i, a i, b i, W, V, ?_, ?_, ?_, rfl, hWV⟩ <;>
        rw [← hi] <;> exact (pair_mem_sequenceGraph _ i _).mpr rfl)
  have hex (i : ℕ) : ∃ W V : M, (s i).val = pair W.val V.val ∧
      approximationAdmissibleFormula.Realize Empty.elim ![Ω, Mul, Pow, Add, F, X, B i, F₂, W, V, a i, b i] := by
    let n : M := ⟨natOrdinal i, hM.mem_trans (hΩ ▸ mem_omegaOrdinal.mpr ⟨i, rfl⟩) Ω.property⟩
    obtain ⟨C, a', b', W, V, hC, ha, hb, he, hWV⟩ := (hφ n (s i)).mp (hsel n i rfl)
    have hC' : C = B i := Subtype.ext ((pair_mem_sequenceGraph _ i _).mp hC)
    have ha' : a' = a i := Subtype.ext ((pair_mem_sequenceGraph _ i _).mp ha)
    have hb' : b' = b i := Subtype.ext ((pair_mem_sequenceGraph _ i _).mp hb)
    exact ⟨W, V, he, by simpa only [hC', ha', hb'] using hWV⟩
  choose W V hpairval hWV using hex
  refine ⟨W, V, ?_, hWV⟩
  have he : (fun n => pair (W n).val (V n).val) = fun n => (s n).val :=
    funext (fun n => (hpairval n).symm)
  rwa [he]

end PolishSpaceBook.CantorTreeMeasure
