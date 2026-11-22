import PolishSpaceBook.ForcingOrdinalPreservation
import PolishSpaceBook.SetTheoryInternalListCodes
import PolishSpaceBook.LambdaBorelSyntax
import Lean

open PolishSpaceBook ZFSet
open PolishSpaceBook.ForcingNames PolishSpaceBook.SetTheoryModels
open PolishSpaceBook.NamedLambda

namespace SortPilot

-- Named interfaces retain the type distinction hidden by book notation.
noncomputable def forcingValue (G : Set ZFSet.{0}) (τ : ZFSet.{0}) : ZFSet.{0} := valuation G τ
noncomputable def rankOrdinal (τ : ZFSet.{0}) : ZFSet.{0} := τ.rank.toZFSet

theorem forcingBound (G : Set ZFSet.{0}) (τ : ZFSet.{0}) :
    (forcingValue G τ).rank ≤ τ.rank := rank_valuation_le G τ

theorem rankBridge (τ : ZFSet.{0}) : (rankOrdinal τ).rank = τ.rank :=
  Ordinal.rank_toZFSet τ.rank

theorem checkValue (P : ZFSet.{0}) (G : Set ZFSet.{0})
    (hne : G.Nonempty) (hsub : ∀ p ∈ G, p ∈ P) (x : ZFSet.{0}) :
    forcingValue G (check P x) = x := by
  obtain ⟨p, hp⟩ := hne
  exact valuation_check P G ⟨p, hp, hsub p hp⟩ x

-- A checked specialization follows the source proof, including the rank/set bridge.
theorem ordinalSourceProof {M P α : ZFSet.{0}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hP : P ∈ M) (G : Set ZFSet.{0}) (hne : G.Nonempty)
    (hsub : ∀ p ∈ G, p ∈ P) (hα : α.IsOrdinal) :
    α ∈ extension P M G ↔ α ∈ M := by
  constructor
  · intro hαE
    obtain ⟨τ, hτM, _hname, he⟩ := (mem_extension P M G α).mp hαE
    let β := τ.rank.toZFSet
    have hβ : β.IsOrdinal := ZFSet.isOrdinal_toZFSet τ.rank
    have hβM : β ∈ M := rank_mem_of_axioms hM hinf hpair hunion hpower hsep hrep ⟨τ, hτM⟩
    have hτβ : τ.rank ≤ β.rank := by dsimp [β]; rw [Ordinal.rank_toZFSet]
    exact ordinal_valuation_mem_ground (β := β) hM G hα hβ hβM hτβ he
  · intro hαM
    apply (mem_extension P M G α).mpr
    exact ⟨check P α,
      check_mem_of_axioms hM hinf hpair hunion hpower hsep hrep ⟨P, hP⟩ ⟨α, hαM⟩,
      check_isName P α, checkValue P G hne hsub α⟩

-- Extensionality is an explicit step, rather than an implicit interpretation of ↔.
theorem ordinalClasses {M P : ZFSet.{0}} (G : Set ZFSet.{0})
    (h : ∀ α : ZFSet.{0}, α.IsOrdinal → (α ∈ extension P M G ↔ α ∈ M)) :
    {α : ZFSet.{0} | α ∈ extension P M G ∧ α.IsOrdinal} =
      {α : ZFSet.{0} | α ∈ M ∧ α.IsOrdinal} := by
  ext α
  constructor
  · rintro ⟨hm, ho⟩
    exact ⟨(h α ho).mp hm, ho⟩
  · rintro ⟨hm, ho⟩
    exact ⟨(h α ho).mpr hm, ho⟩

theorem ordinalSourceClasses {M P : ZFSet.{0}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hP : P ∈ M) (G : Set ZFSet.{0}) (hne : G.Nonempty)
    (hsub : ∀ p ∈ G, p ∈ P) :
    {α : ZFSet.{0} | α ∈ extension P M G ∧ α.IsOrdinal} =
      {α : ZFSet.{0} | α ∈ M ∧ α.IsOrdinal} :=
  ordinalClasses G (fun _ hα => ordinalSourceProof hM hinf hpair hunion hpower hsep hrep hP G hne hsub hα)

-- The internal reading of Ord is checked on both transitive set domains.
theorem internalOrdinal (M : ZFSet.{0}) (hM : M.IsTransitive) (α : M) :
    (ordinalFormula (0 : Fin 1)).Realize Empty.elim ![α] ↔ α.val.IsOrdinal := by
  exact realize_ordinalFormula (fun x => x ∈ M) (fun _ ha _ hb => hM.mem_trans hb ha)
    (0 : Fin 1) ![α]

theorem internalExtensionOrdinal {P M : ZFSet.{0}} (G : Set ZFSet.{0})
    (hM : M.IsTransitive) (α : extension P M G) :
    (ordinalFormula (0 : Fin 1)).Realize Empty.elim ![α] ↔ α.val.IsOrdinal :=
  internalOrdinal _ (extension_isTransitive P M G hM) α

noncomputable def wordAsSet (s : List ℕ) : ZFSet.{0} := wordGraph s
def wordCode (s : List ℕ) : ℕ := NatListCode.encode s
def decodedWord (n : ℕ) : List ℕ := NatListCode.decode n
noncomputable def decodedGraph (n : ℕ) : ZFSet.{0} := wordAsSet (decodedWord n)

theorem encodingEntry (s : List ℕ) (n : ℕ) :
    pair (wordAsSet s) (natOrdinal n) ∈ (listCodeGraph : ZFSet.{0}) ↔ n = wordCode s :=
  pair_mem_listCodeGraph s n

theorem fixedEncodingEntry (C : ZFSet.{0}) (hC : C = listCodeGraph) (s : List ℕ) (n : ℕ) :
    pair (wordAsSet s) (natOrdinal n) ∈ C ↔ n = wordCode s := by
  rw [hC]
  exact encodingEntry s n

theorem decodingEntry (n : ℕ) (s : List ℕ) :
    pair (natOrdinal n) (wordAsSet s) ∈ (listDecodeGraph : ZFSet.{0}) ↔ s = decodedWord n :=
  pair_mem_listDecodeGraph n s

theorem decodeEncode (s : List ℕ) : decodedWord (wordCode s) = s := NatListCode.decode_encode s

-- The witness stores a word code and a child number, not the word itself.
def chainWord (q : ℕ → ℕ) (n : ℕ) : List ℕ := decodedWord (q n).unpair.1
def chainChild (q : ℕ → ℕ) (n : ℕ) : ℕ := (q n).unpair.2

theorem chainCode (q : ℕ → ℕ) (n : ℕ) :
    q n = Nat.pair (wordCode (chainWord q n)) (chainChild q n) := by
  simp [wordCode, chainWord, decodedWord, chainChild, NatListCode.encode_decode]

theorem chainRow (c : BorelExpression) (q : ℕ → ℕ) (n : ℕ) :
    BorelExpression.chainPair c (q n) (q (n + 1)) ↔
      c (chainWord q n) ≠ 0 ∧ c (chainWord q (n + 1)) ≠ 0 ∧
      chainWord q (n + 1) = chainWord q n ++ [chainChild q n] := by
  unfold BorelExpression.chainPair chainWord chainChild decodedWord
  constructor
  · rintro ⟨h0, h1, hstep⟩
    exact ⟨h0, h1, by rw [hstep, NatListCode.decode_encode]⟩
  · rintro ⟨h0, h1, hstep⟩
    refine ⟨h0, h1, ?_⟩
    have h := congrArg NatListCode.encode hstep
    simpa only [NatListCode.encode_decode] using h

theorem chainWitness (c : BorelExpression) :
    ¬ WellFounded c.Child ↔ ∃ q : ℕ → ℕ, ∀ n,
      c (chainWord q n) ≠ 0 ∧ c (chainWord q (n + 1)) ≠ 0 ∧
      chainWord q (n + 1) = chainWord q n ++ [chainChild q n] := by
  simp only [BorelExpression.not_wellFounded_iff_chain, chainRow]

-- Prefix access uses zero off-domain; this is independent of label runtime.
example (c : ℕ → BorelExpression) (n : ℕ) (z : LambdaTree.PrefixPair) :
    BorelExpression.finiteChainClause c n z =
      BorelExpression.chainPair (c (z.1.getD 0 0)) (z.2.getD n 0) (z.2.getD (n + 1) 0) := rfl

end SortPilot

open Lean Meta Elab Command
run_cmd liftTermElabM do
  for name in [``SortPilot.forcingValue, ``SortPilot.rankOrdinal, ``SortPilot.forcingBound,
      ``SortPilot.rankBridge, ``SortPilot.checkValue,
      ``SortPilot.internalExtensionOrdinal, ``SortPilot.ordinalSourceClasses, ``SortPilot.ordinalSourceProof, ``SortPilot.ordinalClasses, ``SortPilot.internalOrdinal,
      ``ForcingNames.mem_extension, ``ForcingNames.extension_isTransitive,
      ``ForcingNames.check_isName, ``ForcingNames.valuation_check,
      ``SetTheoryModels.rank_mem_of_axioms, ``SetTheoryModels.check_mem_of_axioms,
      ``SetTheoryModels.realize_ordinalFormula,
      ``ForcingNames.rank_valuation_le, ``ForcingNames.ordinal_valuation_mem_ground,
      ``SetTheoryModels.ordinal_mem_extension_iff_of_axioms,
      ``SortPilot.wordAsSet, ``SortPilot.wordCode, ``SortPilot.decodedWord, ``SortPilot.decodedGraph, ``SortPilot.fixedEncodingEntry,
      ``SortPilot.encodingEntry, ``SortPilot.decodingEntry, ``SortPilot.decodeEncode,
      ``SetTheoryModels.listCodeGraph_mem, ``SetTheoryModels.listDecodeGraph_mem,
      ``SortPilot.chainCode, ``SortPilot.chainWord, ``SortPilot.chainChild, ``SortPilot.chainRow, ``SortPilot.chainWitness,
      ``BorelExpression.finiteChainClause, ``BorelExpression.projected_not_wellFounded] do
    let info ← getConstInfo name
    forallTelescope info.type fun xs result => do
      let mut binders : Array Json := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        binders := binders.push <| Json.mkObj [
          ("name", toJson d.userName.toString), ("type", toJson (← ppExpr d.type).pretty)]
      logInfo m!"SORT_PILOT {(Json.mkObj [
        ("declaration", toJson name.toString), ("binders", toJson binders),
        ("result", toJson (← ppExpr result).pretty),
        ("signature", toJson (reprStr info.type)),
        ("body", toJson (reprStr info.value?))]).compress}"
