module

public import PolishSpaceBook.SectionTreeBorelCodes
public import PolishSpaceBook.LambdaJointRankBound
public import PolishSpaceBook.LambdaRankLabelComputation

@[expose] public section

/-! # Closed lambda programs for section-edge Borel labels -/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm BorelExpression
namespace LambdaTree
open LambdaRelative
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
local instance edgePairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Input is `(child word code, (parent word code, address code))`. -/
def edgeAddressTerm : AlphaTerm := numericalCompose (numericalProjectionTerm false)
  (numericalProjectionTerm false)
def edgeAddress (z : ℕ) := z.unpair.2.unpair.2

theorem edgeAddress_computes : NumericalComputes edgeAddressTerm edgeAddress := by
  have h := (projection_computes false).comp (projection_computes false)
  exact h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the edge-label program, the input is $z=\NatPair{b}{\NatPair{a}{w}}$. Inside its body put
    $$\begin{aligned}
    b&:= \LambdaNumericProjection{1}z,&a&:= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}z),&w&:=
    \LambdaNumericProjection{2}( \LambdaNumericProjection{2}z),\\
    k&:=\LambdaNumericProjection{1}(\LambdaPred w),&r&:=\LambdaNumericProjection{2}(\LambdaPred w).
    \end{aligned}$$
    For a nonempty address, $k$ is its first entry and $r$ is its remaining word code. The guard is
    computed by
    $$\begin{aligned}
    \LambdaTermName{witnessNode}(o,k,b)&:= \LambdaMul\,( \LambdaEqual\, \LambdaTermName{length}(k)\,
    \LambdaTermName{length}(b))\,(Qo \LambdaNumericPairValue{k}{b}),\\
    \LambdaTermName{edgeGuard}(o,z)&:=\LambdaMul\,(\LambdaListPrefix\LambdaNumericPairValue{a}{b})\,
     ( \LambdaMul\,( \LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b)))\,(
    \LambdaTermName{witnessNode}(o,k,b))).
    \end{aligned}$$
    It returns one exactly when $H(b,a,k)$ holds. All its calls terminate even when $w$ is the empty-word code.
-/
def edgeLeafIndexTerm : AlphaTerm := numericalCompose (numericalProjectionTerm true)
  (numericalCompose predecessorTerm edgeAddressTerm)
def edgeLeafIndex (z : ℕ) := (edgeAddress z - 1).unpair.1

theorem edgeLeafIndex_computes : NumericalComputes edgeLeafIndexTerm edgeLeafIndex :=
  (projection_computes true).comp (predecessor_computes.comp edgeAddress_computes)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the edge-label program, the input is $z=\NatPair{b}{\NatPair{a}{w}}$. Inside its body put
    $$\begin{aligned}
    b&:= \LambdaNumericProjection{1}z,&a&:= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}z),&w&:=
    \LambdaNumericProjection{2}( \LambdaNumericProjection{2}z),\\
    k&:=\LambdaNumericProjection{1}(\LambdaPred w),&r&:=\LambdaNumericProjection{2}(\LambdaPred w).
    \end{aligned}$$
    For a nonempty address, $k$ is its first entry and $r$ is its remaining word code. The guard is
    computed by
    $$\begin{aligned}
    \LambdaTermName{witnessNode}(o,k,b)&:= \LambdaMul\,( \LambdaEqual\, \LambdaTermName{length}(k)\,
    \LambdaTermName{length}(b))\,(Qo \LambdaNumericPairValue{k}{b}),\\
    \LambdaTermName{edgeGuard}(o,z)&:=\LambdaMul\,(\LambdaListPrefix\LambdaNumericPairValue{a}{b})\,
     ( \LambdaMul\,( \LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b)))\,(
    \LambdaTermName{witnessNode}(o,k,b))).
    \end{aligned}$$
    It returns one exactly when $H(b,a,k)$ holds. All its calls terminate even when $w$ is the empty-word code.
-/
def edgeLabelTailTerm : AlphaTerm := numericalCompose (numericalProjectionTerm false)
  (numericalCompose predecessorTerm edgeAddressTerm)
def edgeLabelTail (z : ℕ) := (edgeAddress z - 1).unpair.2

theorem edgeLabelTail_computes : NumericalComputes edgeLabelTailTerm edgeLabelTail :=
  (projection_computes false).comp (predecessor_computes.comp edgeAddress_computes)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the edge-label program, the input is $z=\NatPair{b}{\NatPair{a}{w}}$. Inside its body put
    $$\begin{aligned}
    b&:= \LambdaNumericProjection{1}z,&a&:= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}z),&w&:=
    \LambdaNumericProjection{2}( \LambdaNumericProjection{2}z),\\
    k&:=\LambdaNumericProjection{1}(\LambdaPred w),&r&:=\LambdaNumericProjection{2}(\LambdaPred w).
    \end{aligned}$$
    For a nonempty address, $k$ is its first entry and $r$ is its remaining word code. The guard is
    computed by
    $$\begin{aligned}
    \LambdaTermName{witnessNode}(o,k,b)&:= \LambdaMul\,( \LambdaEqual\, \LambdaTermName{length}(k)\,
    \LambdaTermName{length}(b))\,(Qo \LambdaNumericPairValue{k}{b}),\\
    \LambdaTermName{edgeGuard}(o,z)&:=\LambdaMul\,(\LambdaListPrefix\LambdaNumericPairValue{a}{b})\,
     ( \LambdaMul\,( \LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b)))\,(
    \LambdaTermName{witnessNode}(o,k,b))).
    \end{aligned}$$
    It returns one exactly when $H(b,a,k)$ holds. All its calls terminate even when $w$ is the empty-word code.
-/
theorem sectionEdgeGuard_decidable {ε : ℕ → ℕ} (S : PairTree ε) :
    DecidablePredicate ε (fun z : ℕ =>
      sectionEdgeGuard S z.unpair.1 z.unpair.2.unpair.1 (edgeLeafIndex z)) := by
  have hb := projection_computes true
  have ha := (projection_computes true).comp (projection_computes false)
  have hk := edgeLeafIndex_computes
  have hp := word_prefix_decidable ha hb ε
  have hl := numerical_lt_decidable (listLength_computes.comp ha) (listLength_computes.comp hb) ε
  have he := (numerical_le_decidable (listLength_computes.comp hk) (listLength_computes.comp hb) ε).and
    (numerical_le_decidable (listLength_computes.comp hb) (listLength_computes.comp hk) ε)
  have hm := S.decidable.precompNumerical
    (g := fun z : ℕ => (NatListCode.decode (edgeLeafIndex z),NatListCode.decode z.unpair.1))
    (hk.pair hb) (fun z => by simp [Encodable.encode])
  simpa [sectionEdgeGuard,← le_antisymm_iff] using hp.and (hl.and (he.and hm))

/-- The selector receives `(original input, guard bit)`. -/
def edgeSelectorAddressTerm := numericalCompose edgeAddressTerm (numericalProjectionTerm true)
def edgeSelectorTailTerm := numericalCompose edgeLabelTailTerm (numericalProjectionTerm true)
def edgeSelectorIndexTerm := numericalCompose edgeLeafIndexTerm (numericalProjectionTerm true)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The two possible child-label bodies are
    $$\begin{aligned}
    \LambdaTermName{emptyLabel}(r)&:=\LambdaTermName{chooseLe}(r,\ChurchNumeral{0};\ChurchNumeral{2},
     \LambdaTermName{chooseLe}(r,\ChurchNumeral{1};\ChurchNumeral{3},\ChurchNumeral{0})),\\
    \LambdaTermName{cylinderLabel}(k,r)&:= \LambdaTermName{chooseLe}(r, \ChurchNumeral{0}; \LambdaAdd\,k\,
    \ChurchNumeral{3}, \ChurchNumeral{0}).
    \end{aligned}$$
    They give the empty expression and the basic-cylinder leaf, respectively. The joint label program is
    $$\LambdaTermName{edgeLabel}_Q:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{chooseLe}(w, \ChurchNumeral{0};
    \ChurchNumeral{1},
     \LambdaTermName{chooseLe}( \LambdaTermName{edgeGuard}(o,z), \ChurchNumeral{0}; \LambdaTermName{emptyLabel}(r),
    \LambdaTermName{cylinderLabel}(k,r)))}}.$$
    It computes $e_{b,a}(\LambdaListDecode{w})$.
-/
def edgeEmptyLabelTerm := numericalIfLe edgeSelectorTailTerm (numericalConstant 0)
  (numericalConstant 2) (numericalIfLe edgeSelectorTailTerm (numericalConstant 1)
    (numericalConstant 3) (numericalConstant 0))
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The two possible child-label bodies are
    $$\begin{aligned}
    \LambdaTermName{emptyLabel}(r)&:=\LambdaTermName{chooseLe}(r,\ChurchNumeral{0};\ChurchNumeral{2},
     \LambdaTermName{chooseLe}(r,\ChurchNumeral{1};\ChurchNumeral{3},\ChurchNumeral{0})),\\
    \LambdaTermName{cylinderLabel}(k,r)&:= \LambdaTermName{chooseLe}(r, \ChurchNumeral{0}; \LambdaAdd\,k\,
    \ChurchNumeral{3}, \ChurchNumeral{0}).
    \end{aligned}$$
    They give the empty expression and the basic-cylinder leaf, respectively. The joint label program is
    $$\LambdaTermName{edgeLabel}_Q:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{chooseLe}(w, \ChurchNumeral{0};
    \ChurchNumeral{1},
     \LambdaTermName{chooseLe}( \LambdaTermName{edgeGuard}(o,z), \ChurchNumeral{0}; \LambdaTermName{emptyLabel}(r),
    \LambdaTermName{cylinderLabel}(k,r)))}}.$$
    It computes $e_{b,a}(\LambdaListDecode{w})$.
-/
def edgeBasicLabelTerm := numericalIfLe edgeSelectorTailTerm (numericalConstant 0)
  (addNumerical edgeSelectorIndexTerm (numericalConstant 3)) (numericalConstant 0)
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The two possible child-label bodies are
    $$\begin{aligned}
    \LambdaTermName{emptyLabel}(r)&:=\LambdaTermName{chooseLe}(r,\ChurchNumeral{0};\ChurchNumeral{2},
     \LambdaTermName{chooseLe}(r,\ChurchNumeral{1};\ChurchNumeral{3},\ChurchNumeral{0})),\\
    \LambdaTermName{cylinderLabel}(k,r)&:= \LambdaTermName{chooseLe}(r, \ChurchNumeral{0}; \LambdaAdd\,k\,
    \ChurchNumeral{3}, \ChurchNumeral{0}).
    \end{aligned}$$
    They give the empty expression and the basic-cylinder leaf, respectively. The joint label program is
    $$\LambdaTermName{edgeLabel}_Q:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{chooseLe}(w, \ChurchNumeral{0};
    \ChurchNumeral{1},
     \LambdaTermName{chooseLe}( \LambdaTermName{edgeGuard}(o,z), \ChurchNumeral{0}; \LambdaTermName{emptyLabel}(r),
    \LambdaTermName{cylinderLabel}(k,r)))}}.$$
    It computes $e_{b,a}(\LambdaListDecode{w})$.
-/
def edgeLabelSelectorTerm := numericalIfLe edgeSelectorAddressTerm (numericalConstant 0)
  (numericalConstant 1) (numericalIfLe (numericalProjectionTerm false) (numericalConstant 0)
    edgeEmptyLabelTerm edgeBasicLabelTerm)

def edgeLabelSelector (z : ℕ) : ℕ :=
  if edgeAddress z.unpair.1 = 0 then 1 else
  if z.unpair.2 = 0 then
    if edgeLabelTail z.unpair.1 = 0 then 2 else if edgeLabelTail z.unpair.1 ≤ 1 then 3 else 0
  else if edgeLabelTail z.unpair.1 = 0 then edgeLeafIndex z.unpair.1 + 3 else 0

theorem edgeLabelSelector_computes : NumericalComputes edgeLabelSelectorTerm edgeLabelSelector := by
  have hw := edgeAddress_computes.comp (projection_computes true)
  have ht := edgeLabelTail_computes.comp (projection_computes true)
  have hk := edgeLeafIndex_computes.comp (projection_computes true)
  have he := ht.ifLe (numericalConstant_computes 0) (numericalConstant_computes 2)
    (ht.ifLe (numericalConstant_computes 1) (numericalConstant_computes 3) (numericalConstant_computes 0))
  have hb := ht.ifLe (numericalConstant_computes 0)
    (hk.add (numericalConstant_computes 3)) (numericalConstant_computes 0)
  have h := hw.ifLe (numericalConstant_computes 0) (numericalConstant_computes 1)
    ((projection_computes false).ifLe (numericalConstant_computes 0) he hb)
  refine ⟨h.1,fun z => ?_⟩
  simpa [edgeLabelSelectorTerm,edgeEmptyLabelTerm,edgeBasicLabelTerm,
    edgeSelectorAddressTerm,edgeSelectorTailTerm,edgeSelectorIndexTerm,edgeLabelSelector,Nat.le_zero_eq] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The two possible child-label bodies are
    $$\begin{aligned}
    \LambdaTermName{emptyLabel}(r)&:=\LambdaTermName{chooseLe}(r,\ChurchNumeral{0};\ChurchNumeral{2},
     \LambdaTermName{chooseLe}(r,\ChurchNumeral{1};\ChurchNumeral{3},\ChurchNumeral{0})),\\
    \LambdaTermName{cylinderLabel}(k,r)&:= \LambdaTermName{chooseLe}(r, \ChurchNumeral{0}; \LambdaAdd\,k\,
    \ChurchNumeral{3}, \ChurchNumeral{0}).
    \end{aligned}$$
    They give the empty expression and the basic-cylinder leaf, respectively. The joint label program is
    $$\LambdaTermName{edgeLabel}_Q:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{chooseLe}(w, \ChurchNumeral{0};
    \ChurchNumeral{1},
     \LambdaTermName{chooseLe}( \LambdaTermName{edgeGuard}(o,z), \ChurchNumeral{0}; \LambdaTermName{emptyLabel}(r),
    \LambdaTermName{cylinderLabel}(k,r)))}}.$$
    It computes $e_{b,a}(\LambdaListDecode{w})$.
-/
def sectionEdgeLabelProgram (Q : AlphaTerm) : AlphaTerm :=
  mapOutputProgram edgeLabelSelectorTerm
    (pairOutputProgram (liftNumericalProgram numericalIdentity) Q)

theorem edgeLabelSelector_correct {ε : ℕ → ℕ} (S : PairTree ε) (z : ℕ) :
    edgeLabelSelector (Nat.pair z
      (if sectionEdgeGuard S z.unpair.1 z.unpair.2.unpair.1 (edgeLeafIndex z) then 1 else 0)) =
      (sectionEdgeCode S z.unpair.1 z.unpair.2.unpair.1).val (NatListCode.decode (edgeAddress z)) := by
  classical
  simp only [edgeLabelSelector,Nat.unpair_pair]
  cases hw : edgeAddress z with
  | zero => simp [sectionEdgeCode,Code.iUnion,union,graft,NatListCode.decode]
  | succ n =>
    have hk : edgeLeafIndex z = n.unpair.1 := by simp [edgeLeafIndex,hw]
    have ht : edgeLabelTail z = n.unpair.2 := by simp [edgeLabelTail,hw]
    by_cases h : sectionEdgeGuard S z.unpair.1 z.unpair.2.unpair.1 n.unpair.1
    · cases hv : n.unpair.2 <;>
        simp [hk,ht,h,sectionEdgeCode,Code.iUnion,Code.leaf,union,graft,basic,NatListCode.decode,hv]
    · have he := RankBound.emptyLabel_eq (NatListCode.decode n.unpair.2)
      simp only [NatListCode.encode_decode] at he
      simpa [hw,hk,ht,h,sectionEdgeCode,Code.iUnion,Code.empty,Code.compl,Code.leaf,
        union,graft,NatListCode.decode] using he

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The two possible child-label bodies are
    $$\begin{aligned}
    \LambdaTermName{emptyLabel}(r)&:=\LambdaTermName{chooseLe}(r,\ChurchNumeral{0};\ChurchNumeral{2},
     \LambdaTermName{chooseLe}(r,\ChurchNumeral{1};\ChurchNumeral{3},\ChurchNumeral{0})),\\
    \LambdaTermName{cylinderLabel}(k,r)&:= \LambdaTermName{chooseLe}(r, \ChurchNumeral{0}; \LambdaAdd\,k\,
    \ChurchNumeral{3}, \ChurchNumeral{0}).
    \end{aligned}$$
    They give the empty expression and the basic-cylinder leaf, respectively. The joint label program is
    $$\LambdaTermName{edgeLabel}_Q:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{chooseLe}(w, \ChurchNumeral{0};
    \ChurchNumeral{1},
     \LambdaTermName{chooseLe}( \LambdaTermName{edgeGuard}(o,z), \ChurchNumeral{0}; \LambdaTermName{emptyLabel}(r),
    \LambdaTermName{cylinderLabel}(k,r)))}}.$$
    It computes $e_{b,a}(\LambdaListDecode{w})$.
-/
theorem sectionEdgeLabelProgram_computes {ε : ℕ → ℕ} (S : PairTree ε) {Q : AlphaTerm}
    (hQ : Decides ε Q (fun z : ℕ =>
      sectionEdgeGuard S z.unpair.1 z.unpair.2.unpair.1 (edgeLeafIndex z))) :
    Computes ε (sectionEdgeLabelProgram Q) (fun z : ℕ =>
      (sectionEdgeCode S z.unpair.1 z.unpair.2.unpair.1).val
        (NatListCode.decode z.unpair.2.unpair.2)) := by
  classical
  have hq : Computes ε Q (fun z : ℕ =>
      if sectionEdgeGuard S z.unpair.1 z.unpair.2.unpair.1 (edgeLeafIndex z) then 1 else 0) :=
    ⟨hQ.1,fun z => hQ.runs z⟩
  have h := ((ofNumerical numericalIdentity_computes ε).pair hq).map edgeLabelSelector_computes
  change Computes ε (mapOutputProgram edgeLabelSelectorTerm
    (pairOutputProgram (liftNumericalProgram numericalIdentity) Q)) _
  refine ⟨h.1,fun z => ?_⟩
  have hz := h.2 z
  simpa only [id_eq,edgeLabelSelector_correct,edgeAddress] using hz

theorem sectionEdgeLabels_computable {ε : ℕ → ℕ} (S : PairTree ε) :
    ∃ P, Computes ε P (fun z : ℕ => (sectionEdgeCode S z.unpair.1 z.unpair.2.unpair.1).val
      (NatListCode.decode z.unpair.2.unpair.2)) := by
  obtain ⟨Q,hQ⟩ := sectionEdgeGuard_decidable S
  exact ⟨_,sectionEdgeLabelProgram_computes S hQ⟩

end LambdaTree
end PolishSpaceBook
