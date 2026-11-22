module

public import PolishSpaceBook.BorelInternalCodeFibers
public import PolishSpaceBook.BorelExpressionBoolean
public import PolishSpaceBook.SetTheoryDefinableSequences

@[expose] public section

/-! # Selecting Borel representatives with the entire label table inside the model -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate CantorTreeMeasure
universe u

/-- Select codes over the internal range, then read that same selector along the input sequence. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal selection of Borel code sequences
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The set $S:=\GraphRange{H}$ belongs to $M$. For each $A\in S$, the preceding formula defines the nonempty
    set of all $\ell\in\mathcal C$ representing $A$. Apply internal definable choice to this relation to obtain
    one function graph $f:S\to\mathcal C$ in $M$, with $M\models\Psi(A,f(A))$ for every $A\in S$.
    For each $n$, let $c_n$ be the unique expression with label graph $f(V_n)$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The whole output table $H'$ is obtained by two graph lookups:
    $$\langle n,\ell\rangle\in H'\quad\Longleftrightarrow\quad
    \exists A\in S\;(\langle n,A\rangle\in H\ \land\ \langle A,\ell\rangle\in f).$$
    This bounded condition determines exactly one output for each $n\in\omega$.
    Shared reflection and graph collection put the entire table in $M$.
    The formula $\Psi$ gives the required interpretation identity at every entry.
    In particular, the proof retains one internal selector throughout; it does not replace it by separate external choices.
-/
theorem internal_borel_code_sequence {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (V : ℕ → ZFSet.{u}) (hV : sequenceGraph V ∈ M)
    (hex : ∀ n, ∃ (c : BorelExpression) (hc : c.Valid), c.labelGraph ∈ M ∧
      internalBorelCantorSet M c hc.2.2.2.2.2 = V n) :
    ∃ c : ℕ → Code, sequenceGraph (fun n => (c n).val.labelGraph) ∈ M ∧
      ∀ n, internalBorelCantorSet M (c n).val (c n).property.2.2.2.2.2 = V n := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let T : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let K : M := ⟨_, prod_mem_of_separation hM hpair hunion hpower (hsep _) T.property T.property⟩
  have hn (n : ℕ) : natOrdinal n ∈ M :=
    hM.mem_trans (mem_omegaOrdinal.mpr ⟨n,rfl⟩) Ω.property
  let z : M := ⟨_, hn 0⟩
  let o : M := ⟨_, hn 1⟩
  let b : M := ⟨_, hn 2⟩
  let e : M := ⟨_, hM.mem_trans (mem_finiteSequences.mpr ⟨[],rfl⟩) T.property⟩
  let B : M := ⟨_, canonicalBasisWordGraph_mem hM hinf hpair hunion hpower hsep⟩
  let Y : M := ⟨_, internalCantor_mem hM hinf hpair hunion hpower hsep⟩
  let Codes : M := ⟨_, internalValidCodes_mem hM hinf hpair hunion hpower hsep hrep hchoice⟩
  let S : M := ⟨graphRange (sequenceGraph V), graphRange_mem hM hunion (hsep _) hV⟩
  let ps : Fin 10 → M := ![Ω,T,z,o,b,e,K,B,Y,Codes]
  have hmeaning (A l : M) :
      representsCodeFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ps A) l) ↔
        ∃ (c : BorelExpression) (hc : c.Valid), c.labelGraph = l.val ∧
          A.val = internalBorelCantorSet M c hc.2.2.2.2.2 := by
    have hv : Fin.snoc (Fin.snoc ps A) l = ![Ω,T,z,o,b,e,K,B,Y,Codes,A,l] := by
      funext i; fin_cases i <;> rfl
    rw [hv]
    exact realize_representsCodeFormula hM hinf hpair hunion hpower hsep
      Ω T z o b e K B Y Codes A l rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have htotal (A : M) (hA : A.val ∈ S.val) : ∃ l : M, l.val ∈ Codes.val ∧
      representsCodeFormula.Realize Empty.elim (Fin.snoc (Fin.snoc ps A) l) := by
    change A.val ∈ graphRange (sequenceGraph V) at hA
    obtain ⟨a, ha⟩ := mem_graphRange.mp hA
    obtain ⟨n, he⟩ := ZFSet.mem_range.mp ha
    have hnA : V n = A.val := (ZFSet.pair_inj.mp he).2
    obtain ⟨c,hc,hcM,hcA⟩ := hex n
    let l : M := ⟨c.labelGraph,hcM⟩
    refine ⟨l, mem_internalValidCodes.mpr ⟨hcM,c,hc,rfl⟩, (hmeaning A l).mpr ?_⟩
    exact ⟨c,hc,rfl,hnA.symm.trans hcA.symm⟩
  obtain ⟨f,hf,hφ⟩ := internal_bounded_definable_choice hM hpair hunion hsep hrep hchoice
    representsCodeFormula ps S Codes htotal
  have hVS (n : ℕ) : V n ∈ S.val :=
    mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph V n _).mpr rfl⟩
  have hsel (n : ℕ) : ∃ c : Code, pair (V n) c.val.labelGraph ∈ f.val ∧
      internalBorelCantorSet M c.val c.property.2.2.2.2.2 = V n := by
    obtain ⟨l,hl,_⟩ := hf.2 _ (hVS n)
    have hlC := (ZFSet.pair_mem_prod.mp (hf.1 hl)).2
    let A : M := ⟨_, hM.mem_trans (hVS n) S.property⟩
    let L : M := ⟨l, hM.mem_trans hlC Codes.property⟩
    obtain ⟨c,hc,hcl,hcA⟩ := (hmeaning A L).mp (hφ A L hl)
    exact ⟨⟨c,hc⟩, hcl.symm ▸ hl, hcA.symm⟩
  choose c hcf hcV using hsel
  have hcm (n : ℕ) : (c n).val.labelGraph ∈ M :=
    hM.mem_trans (ZFSet.pair_mem_prod.mp (hf.1 (hcf n))).2 Codes.property
  let values (n : ℕ) : M := ⟨(c n).val.labelGraph, hcm n⟩
  let p : BoundedSetPredicate 5 := .ex 2 (.conj (.pairMember 0 3 5) (.pairMember 1 5 4))
  have hgraph : sequenceGraph (fun n => (values n).val) ∈ M := by
    apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep p ![⟨_,hV⟩,f,S] values
    intro n y
    change (∃ A ∈ S.val, pair (natOrdinal n) A ∈ sequenceGraph V ∧ pair A y.val ∈ f.val) ↔
      y = values n
    constructor
    · rintro ⟨A,_,hA,hy⟩
      have he := (pair_mem_sequenceGraph V n A).mp hA
      rw [he] at hy
      exact Subtype.ext ((hf.2 _ (hVS n)).unique hy (hcf n))
    · rintro rfl
      exact ⟨V n,hVS n,(pair_mem_sequenceGraph V n _).mpr rfl,hcf n⟩
  exact ⟨c,hgraph,hcV⟩

end PolishSpaceBook.BorelExpression
