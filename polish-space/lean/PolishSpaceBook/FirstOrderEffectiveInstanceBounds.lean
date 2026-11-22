module

public import PolishSpaceBook.FirstOrderEffectiveGrammarCorrectness
public import PolishSpaceBook.FirstOrderEffectiveQuantifierBounds

@[expose] public section

/-! # Finite witness completeness for general quantifier instances

The candidates are all raw term codes below a proved syntax bound. Grammar,
capture-avoiding substitution and alpha comparison are actual closed lambda
programs. Completeness works for arbitrary raw representatives of the source
and target, including function terms and vacuous substitutions.
-/
namespace PolishSpaceBook.NamedFirstOrder.EffectiveSignature
open FirstOrder Language NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open FirstOrderLambdaEncoding (LTerm)
open FirstOrderLambdaEncoding.Grammar (Program)
open EffectiveGrammar QuantifierBounds
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace InstancePrograms

def input (a x b : ℕ) := Nat.pair a (Nat.pair x b)

def test (p c : ℕ) : Prop := IsTermCode S c ∧
  ((Term.decode p.unpair.1).subst p.unpair.2.unpair.1 (Term.decode c)).Alpha
    (Term.decode p.unpair.2.unpair.2)
instance (p c : ℕ) : Decidable (test S p c) := inferInstanceAs (Decidable (_ ∧ _))

/-- Arbitrary raw representatives may be used at all three syntax positions. -/
theorem raw_instance_iff {A B C : LTerm} {φ ψ : Formula L} {r : L.Term ℕ} (x : ℕ)
    (hA : A.Alpha (S.encodeFormula φ)) (hB : B.Alpha (S.encodeFormula ψ))
    (hC : C.Alpha (S.encodeTerm r)) :
    (A.subst x C).Alpha B ↔ (φ.subst x r).Alpha ψ := by
  have hs := (hA.subst hC x).trans (S.encodeFormula_subst_alpha φ x r)
  constructor
  · intro h
    exact (S.encodeFormula_alpha_iff _ _).mp (hs.symm.trans (h.trans hB))
  · intro h
    exact hs.trans (((S.encodeFormula_alpha_iff _ _).mpr h).trans hB.symm)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For $(\forall\mathrm E)$ and $(\exists\mathrm I)$, suppose the displayed instance has raw code $b$ and the
    designated variable occurs freely in the quantified body. Such a substitution inserts the whole replacement
    syntax, so its node count is at most that of the instance; every free name of the replacement also survives.
    The canonical encoding of that replacement
    has at most $2b+1$ nodes and all its names at most $b$, since its tag binders have index zero.
    It therefore suffices to search codes through $\LambdaSyntaxSizeBound{b}{2b+1}$, retaining only term codes and
    testing the actual substitution up to $\alpha$-equivalence. If the designated variable is absent, the variable of
    index zero supplies an instance whenever any term does.
-/
/-- The bound depends only on the observed raw target code. -/
theorem instance_witness_bounded (a b x : ℕ) (φ ψ : Formula L)
    (hA : (Term.decode a).Alpha (S.encodeFormula φ))
    (hB : (Term.decode b).Alpha (S.encodeFormula ψ)) :
    (∃ r : L.Term ℕ, (φ.subst x r).Alpha ψ) ↔
      ∃ c < witnessBound b + 1, test S (input a x b) c := by
  constructor
  · rintro ⟨r, hr⟩
    by_cases hx : x ∈ φ.fv
    · have ht : (Term.decode b).Alpha (S.encodeFormula (φ.subst x r)) :=
        hB.trans ((S.encodeFormula_alpha_iff _ _).mpr hr).symm
      have hb := witness_code_le S φ x r (Term.decode b) hx ht
      rw [Term.code_decode] at hb
      refine ⟨(S.encodeTerm r).code, by omega, ⟨?_, ?_⟩⟩
      · exact ⟨r, by rw [Term.decode_code]; exact .refl _⟩
      · simp only [input, Nat.unpair_pair, Term.decode_code]
        exact (raw_instance_iff S x hA hB (.refl _)).mpr hr
    · have hr0 : (φ.subst x (.var 0)).Alpha ψ :=
        (Formula.alpha_subst_not_free φ x (.var 0) hx).trans
          ((Formula.alpha_subst_not_free φ x r hx).symm.trans hr)
      have hz : (Term.decode 0).Alpha (S.encodeTerm (.var 0)) := by
        rw [show Term.decode 0 = NamedLambda.Term.var 0 from Term.decode_code (.var 0)]
        exact .refl _
      refine ⟨0, by omega, ⟨?_, ?_⟩⟩
      · exact ⟨.var 0, hz⟩
      · simp only [input, Nat.unpair_pair]
        exact (raw_instance_iff S x hA hB hz).mpr hr0
  · rintro ⟨c, _, hc, hh⟩
    obtain ⟨r, hr⟩ := hc
    refine ⟨r, (raw_instance_iff S x hA hB hr).mp ?_⟩
    simpa only [input, Nat.unpair_pair] using hh

end InstancePrograms
end PolishSpaceBook.NamedFirstOrder.EffectiveSignature
