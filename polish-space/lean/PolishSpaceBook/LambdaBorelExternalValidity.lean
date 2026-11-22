module

public import PolishSpaceBook.LambdaUniformPredicates
public import PolishSpaceBook.LambdaBorelSyntax
public import PolishSpaceBook.LambdaBaireQuantifiers

@[expose] public section

/-! # Relative tree presentations of invalid external Borel labels

The input sequence supplies every label directly. All tests share one closed
lambda program, including when the queried word codes depend on witness data.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace BorelExpression
open LambdaRelative
open LambdaRelative.UniformDecidablePredicate

def streamLabels (x : ℕ → ℕ) : BorelExpression := fun s => x (NatListCode.encode s)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Use the five syntax clauses from the preceding proposition with labels read from $z$. One closed
    program decides the row $S(z,i,j)$ for every input sequence: numerical operations compute the
    queried word codes, and each label query returns its prescribed digit. The Boolean operations use
    the same terms for every input; no separate decision program is chosen for each sequence.
    The syntax condition is $\forall i\,\exists j\ S(z,i,j)$, so §{sec:edst-baire-quantifiers} supplies
    tree presentations of syntax and its failure.

    For failure of well-foundedness, use the same chain witness as before. Each row reads two consecutive
    witness entries and the two labels at the encoded words. These label addresses may depend on the
    witness values, but the row is still decided by one total program. Apply the universal-row construction
    of §{sec:edst-baire-quantifiers} to the coded point and witness, then project onto the point.
    The equivalence with a descending child chain is the same as in the preceding proof. Finally take the
    union with syntax failure. The accessors are given in §{sec:lambda-recursive-borel-separation}.
-/
theorem uniform_syntaxRow {C : AlphaTerm} (c : (ℕ → ℕ) → BorelExpression)
    (hc : UniformNumericalComputes C (fun p z => c p (NatListCode.decode z))) :
    UniformDecidablePredicate (fun p (z : ℕ) => syntaxRow (c p) z.unpair.1 z.unpair.2) := by
  have hi := projection_computes true
  have hj := projection_computes false
  have hs := (projection_computes true).comp hi
  have hk := (projection_computes true).comp ((projection_computes false).comp hi)
  have hl := (projection_computes false).comp ((projection_computes false).comp hi)
  have ha := hc.reindex hs
  have hr := hc.reindex (numericalConstant_computes 0)
  have hd := hc.reindex (rowChild_computes.comp (hs.pair hk))
  have hb := hc.reindex (rowChild_computes.comp (hs.pair hl))
  have hw := hc.reindex (rowChild_computes.comp (hs.pair hj))
  have ha0 := (eq ha (uniform_constant 0)).not
  have ha1 := eq ha (uniform_constant 1)
  have ha2 := eq ha (uniform_constant 2)
  have hd0 := eq hd (uniform_constant 0)
  have hb0 := (eq hb (uniform_constant 0)).not
  have hw0 := (eq hw (uniform_constant 0)).not
  have hkl := eq hk.uniform hl.uniform
  have h := ((eq hr (uniform_constant 0)).not).and
    ((hd0.not.imp ha0).and ((le (uniform_constant 3) ha).imp hd0 |>.and
      (((ha1.or ha2).imp hw0).and (ha2.imp (hd0.not.imp (hb0.imp hkl))))))
  simpa [syntaxRow,rowChild,rowWord,Nat.unpair_pair,NatListCode.decode_encode,NatListCode.decode] using h

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Use the five syntax clauses from the preceding proposition with labels read from $z$. One closed
    program decides the row $S(z,i,j)$ for every input sequence: numerical operations compute the
    queried word codes, and each label query returns its prescribed digit. The Boolean operations use
    the same terms for every input; no separate decision program is chosen for each sequence.
    The syntax condition is $\forall i\,\exists j\ S(z,i,j)$, so §{sec:edst-baire-quantifiers} supplies
    tree presentations of syntax and its failure.

    For failure of well-foundedness, use the same chain witness as before. Each row reads two consecutive
    witness entries and the two labels at the encoded words. These label addresses may depend on the
    witness values, but the row is still decided by one total program. Apply the universal-row construction
    of §{sec:edst-baire-quantifiers} to the coded point and witness, then project onto the point.
    The equivalence with a descending child chain is the same as in the preceding proof. Finally take the
    union with syntax failure. The accessors are given in §{sec:lambda-recursive-borel-separation}.
-/
theorem complemented_streamSyntax (ε : ℕ → ℕ) :
    LambdaTree.Complemented ε {x | (streamLabels x).Syntax} := by
  have hc := numericalIdentity_computes.uniform.query.map (projection_computes false)
  have hc' : UniformNumericalComputes (mapOutputProgram (numericalProjectionTerm false)
      (queryOutputProgram (liftNumericalProgram numericalIdentity)))
      (fun p z => streamLabels (rightBaire p) (NatListCode.decode z)) := by
    simpa [streamLabels,rightBaire] using hc
  obtain ⟨P,hP⟩ := uniform_syntaxRow (fun p => streamLabels (rightBaire p)) hc'
  have hh : ∀ x, Decides (pairBaire ε x) P
      (fun z : ℕ => syntaxRow (streamLabels x) z.unpair.1 z.unpair.2) := by
    intro x
    simpa only [rightBaire_pair] using hP (pairBaire ε x)
  simpa only [syntax_iff_rows] using
    LambdaTree.complemented_forall_exists_baire (R := fun x i j => syntaxRow (streamLabels x) i j) hh

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The accessor $\LambdaTermName{witnessEntry}$ reads a witness entry and $\LambdaTermName{streamLabel}$ reads a
    label. Pair projections extract the word codes
    and chosen child. The first two factors require present words, and the third checks that the next word
    is the chosen child. All accesses are to the supplied total input sequence, even when their positions
    are computed from witness values. Thus every row terminates. The universal-row construction of
    §{sec:edst-baire-quantifiers} applies without a predetermined bound on these positions. This gives the
    chain projection; combining it with failure of the five syntax conditions gives invalid label streams.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For chain witnesses, supply $\NamePair{\varepsilon}{\NamePair{x}{q}}$ and put
    $$\begin{aligned}
    \LambdaTermName{witnessEntry}(o,n)&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}(on)),\\
    \LambdaTermName{streamLabel}(o,w)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(ow)),\\
    h_0&:=\LambdaTermName{witnessEntry}(o,n),\quad h_1:=\LambdaTermName{witnessEntry}(o,\LambdaSucc n),\\
    w&:=\LambdaNumericProjection{1}h_0,\quad k:=\LambdaNumericProjection{2}h_0,
     \quad u:=\LambdaNumericProjection{1}h_1.
    \end{aligned}$$
    Using $\LambdaTermName{childCode}, \LambdaTermName{equal}, \LambdaTermName{zero}$ defined above,
    expand and abstract $o,n$ in
    $$\LambdaMul\,(\LambdaTermName{zero}(\LambdaTermName{zero}(\LambdaTermName{streamLabel}(o,w))))\,
     ( \LambdaMul\,( \LambdaTermName{zero}( \LambdaTermName{zero}( \LambdaTermName{streamLabel}(o,u))))\,(
    \LambdaTermName{equal}(u, \LambdaTermName{childCode}(w,k)))).$$
-/
theorem uniform_streamChain : UniformDecidablePredicate (fun p (n : ℕ) =>
    chainPair (streamLabels (leftBaire (rightBaire p)))
      (rightBaire (rightBaire p) n) (rightBaire (rightBaire p) (n+1))) := by
  have ha := numericalIdentity_computes.uniform.query.map
    ((projection_computes false).comp (projection_computes false))
  have hb := successor_computes.uniform.query.map
    ((projection_computes false).comp (projection_computes false))
  have has := ha.map (projection_computes true)
  have hbs := hb.map (projection_computes true)
  have hlabela := has.query.map ((projection_computes true).comp (projection_computes false))
  have hlabelb := hbs.query.map ((projection_computes true).comp (projection_computes false))
  have hchild := ha.map rowChild_computes
  have h := ((eq hlabela (uniform_constant 0)).not).and
    (((eq hlabelb (uniform_constant 0)).not).and (eq hbs hchild))
  simpa [chainPair,streamLabels,leftBaire,rightBaire,rowChild,rowWord] using h

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Use the five syntax clauses from the preceding proposition with labels read from $z$. One closed
    program decides the row $S(z,i,j)$ for every input sequence: numerical operations compute the
    queried word codes, and each label query returns its prescribed digit. The Boolean operations use
    the same terms for every input; no separate decision program is chosen for each sequence.
    The syntax condition is $\forall i\,\exists j\ S(z,i,j)$, so §{sec:edst-baire-quantifiers} supplies
    tree presentations of syntax and its failure.

    For failure of well-foundedness, use the same chain witness as before. Each row reads two consecutive
    witness entries and the two labels at the encoded words. These label addresses may depend on the
    witness values, but the row is still decided by one total program. Apply the universal-row construction
    of §{sec:edst-baire-quantifiers} to the coded point and witness, then project onto the point.
    The equivalence with a descending child chain is the same as in the preceding proof. Finally take the
    union with syntax failure. The accessors are given in §{sec:lambda-recursive-borel-separation}.
-/
theorem projected_streamNotWellFounded (ε : ℕ → ℕ) :
    LambdaTree.Projected ε {x | ¬ WellFounded (streamLabels x).Child} := by
  obtain ⟨P,hP⟩ := uniform_streamChain
  have hh : ∀ x, Decides (pairBaire ε x) P (fun n =>
      chainPair (streamLabels (leftBaire x)) (rightBaire x n) (rightBaire x (n+1))) := by
    intro x
    simpa only [rightBaire_pair] using hP (pairBaire ε x)
  have h := (LambdaTree.projected_forall_baire hh).projectLeft
  convert h using 1
  ext x
  rw [mem_ofPred_eq,not_wellFounded_iff_chain]
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨pairBaire x q,by simpa using hq,by simp⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨rightBaire z,hz⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Invalid label streams
-/
theorem projected_streamNotValid (ε : ℕ → ℕ) :
    LambdaTree.Projected ε {x | ¬ (streamLabels x).Valid} := by
  have hsyntax := LambdaTree.UniformProjected.const (complemented_streamSyntax ε).2
  have hchain := LambdaTree.UniformProjected.const (projected_streamNotWellFounded ε)
  obtain ⟨T,_,hT⟩ := hsyntax.union hchain
  have h := (show LambdaTree.Projected ε
      (({x | (streamLabels x).Syntax} : Set (ℕ → ℕ))ᶜ ∪
        {x | ¬ WellFounded (streamLabels x).Child}) from ⟨T 0,hT 0⟩)
  convert h using 1
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_compl_iff,valid_iff_syntax_wellFounded]
  tauto

end BorelExpression
end PolishSpaceBook
