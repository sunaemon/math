module

public import PolishSpaceBook.SetTheoryPredicateComposition
public import PolishSpaceBook.BorelInternalRowChild

@[expose] public section

/-! # Reflected arithmetic conditions in a Borel certificate row -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
open BoundedSetPredicate
universe u

def wordLookupAt {n : ℕ} (Ω z s i v : Fin n) : BoundedSetPredicate n :=
  wordLookupPredicate.rename ![Ω, z, s, i, v]

lemma eval_wordLookupAt {n : ℕ} (Ω z s i v : Fin n) (xs : Fin n → ZFSet.{u}) :
    (wordLookupAt Ω z s i v).eval xs ↔ SetWordLookup (xs Ω) (xs z) (xs s) (xs i) (xs v) := by
  rw [wordLookupAt, eval_rename]
  have he : xs ∘ ![Ω, z, s, i, v] = ![xs Ω, xs z, xs s, xs i, xs v] := by funext j; fin_cases j <;> rfl
  rw [he]
  rfl

/-- The ordinary set-theoretic meaning of the row's numerical clauses. -/
def SetCertificateArithmetic (zero one two three A a d u v j k : ZFSet.{u}) (leaf : Prop) : Prop :=
  one ∉ u ∧ (a = zero → u = zero) ∧
  (a = one → u = one → j = k → d ≠ zero ∧ v = one) ∧
  (a = one → d ≠ zero → v = one → u = one) ∧
  (a = two → d ≠ zero → pair (pair u v) one ∈ A) ∧
  (pair (pair k three) a ∈ A → (u = one ↔ leaf))

/-- Parameters for constants and graph access remain explicit under every composition. -/
def certificateArithmeticAt {n : ℕ} (zero one two three A a d u v j k : Fin n)
    (leaf : BoundedSetPredicate n) : BoundedSetPredicate n :=
  .conj (.neg (.member one u))
    (.conj ((BoundedSetPredicate.equal a zero).imply (.equal u zero))
      (.conj ((BoundedSetPredicate.equal a one).imply ((BoundedSetPredicate.equal u one).imply ((BoundedSetPredicate.equal j k).imply
        (.conj (.neg (.equal d zero)) (.equal v one)))))
        (.conj ((BoundedSetPredicate.equal a one).imply ((BoundedSetPredicate.neg (.equal d zero)).imply ((BoundedSetPredicate.equal v one).imply (.equal u one))))
          (.conj ((BoundedSetPredicate.equal a two).imply ((BoundedSetPredicate.neg (.equal d zero)).imply (binaryMemberAt A u v one)))
            ((binaryMemberAt A k three a).imply (.iff (.equal u one) leaf))))))

lemma eval_certificateArithmeticAt {n : ℕ} (zero one two three A a d u v j k : Fin n)
    (leaf : BoundedSetPredicate n) (xs : Fin n → ZFSet.{u}) :
    (certificateArithmeticAt zero one two three A a d u v j k leaf).eval xs ↔
      SetCertificateArithmetic (xs zero) (xs one) (xs two) (xs three) (xs A)
        (xs a) (xs d) (xs u) (xs v) (xs j) (xs k) (leaf.eval xs) := by
  simp only [certificateArithmeticAt, eval_imply, eval_binaryMemberAt, eval, SetCertificateArithmetic]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Each numerical comparison is a bounded membership condition on finite ordinals. Addition uses its internal
    graph,
-/
lemma setCertificateArithmetic_nat (a d u v j k : ℕ) (leaf : Prop) :
    SetCertificateArithmetic.{u} (natOrdinal 0) (natOrdinal 1) (natOrdinal 2) (natOrdinal 3)
      (naturalBinaryGraph (fun i j => i + j)) (natOrdinal a) (natOrdinal d)
      (natOrdinal u) (natOrdinal v) (natOrdinal j) (natOrdinal k) leaf ↔
        BorelExpression.certificateArithmetic a d u v j k leaf := by
  simp only [SetCertificateArithmetic, ne_eq, natOrdinal_mem_natOrdinal, Nat.not_lt,
    natOrdinal_injective.eq_iff, pair_mem_naturalBinaryGraph]
  simp only [BorelExpression.certificateArithmetic, eq_comm (a := 1) (b := u + v)]

end PolishSpaceBook.SetTheoryModels
