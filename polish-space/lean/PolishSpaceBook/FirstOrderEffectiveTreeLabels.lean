module

public import PolishSpaceBook.FirstOrderEffectiveContextGrammar
public import PolishSpaceBook.FirstOrderProofTreeParsing

@[expose] public section

/-! # Unannotated tree labels for every effective signature

The numerical tree shape is unchanged. Its sequent labels represent finite
sets of formula alpha-classes through the given signature encoding.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda
open FirstOrderLambdaEncoding.ProofTreeProgram (Data)
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

inductive TreeRep (S : EffectiveSignature L) : Data → SequentTree L → Prop where
  | node {n : ℕ} {s : Sequent L} {ds : List Data} {ts : List (SequentTree L)} :
      S.SequentRep n s → List.Forall₂ (TreeRep S) ds ts →
      TreeRep S (.node n ds) (.node s ts)

theorem TreeRep.root {D : Data} {T : SequentTree L} (h : S.TreeRep D T) :
    S.SequentRep D.root T.root := by
  cases h with
  | node hs _ => exact hs

theorem treeRep_roots {ds : List Data} {ts : List (SequentTree L)}
    (h : List.Forall₂ (TreeRep S) ds ts) :
    List.Forall₂ (SequentRep S) (ds.map Data.root) (ts.map SequentTree.root) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (TreeRep.root S h) ih

theorem tree_has_code (T : SequentTree L) : ∃ D, S.TreeRep D T := by
  cases T with
  | node s ts =>
    obtain ⟨n, hn⟩ := S.sequent_has_code s
    have hc : ∀ t ∈ ts, ∃ d, S.TreeRep d t := by
      intro t ht
      exact tree_has_code t
    have hl : ∃ ds, List.Forall₂ (TreeRep S) ds ts := by
      clear hn
      induction ts with
      | nil => exact ⟨[], .nil⟩
      | cons t ts ih =>
        obtain ⟨d, hd⟩ := hc t (by simp)
        obtain ⟨ds, hds⟩ := ih (fun t ht => hc t (by simp [ht]))
        exact ⟨d :: ds, .cons hd hds⟩
    obtain ⟨ds, hds⟩ := hl
    exact ⟨.node n ds, .node hn hds⟩
termination_by sizeOf T
decreasing_by
  have h := List.sizeOf_lt_of_mem ht
  simp only [SequentTree.node.sizeOf_spec]
  omega

end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
