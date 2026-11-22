module

public import PolishSpaceBook.BorelExpressionCertificates
public import PolishSpaceBook.LambdaFiniteLists
public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-!
# Natural-sequence certificates for Borel expression evaluation

Pairing the truth bit and the chosen child at each encoded finite word
turns the closed certificate into one Baire-space witness. The local
clauses below expose precisely the finite coordinate tests needed by the
relative recursive tree construction.
-/

namespace PolishSpaceBook
namespace BorelExpression
open Set NamedLambda

/-- The standard clopen basis, with the fixed effective word numbering. -/
def cylinderBasis (n : ℕ) : Set (ℕ → ℕ) := cyl (NatListCode.decode n)

def witnessBit (q : ℕ → ℕ) (s : List ℕ) : ℕ := (q (NatListCode.encode s)).unpair.1

def witnessChoice (q : ℕ → ℕ) (s : List ℕ) : ℕ := (q (NatListCode.encode s)).unpair.2

def decodeBits (q : ℕ → ℕ) (s : List ℕ) : Bool := decide (witnessBit q s = 1)

def encodeCertificate (v : List ℕ → Bool) (choice : List ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.pair (if v (NatListCode.decode n) then 1 else 0)
    (choice (NatListCode.decode n))

@[simp] theorem witnessBit_encode (v : List ℕ → Bool) (choice : List ℕ → ℕ) (s : List ℕ) :
    witnessBit (encodeCertificate v choice) s = if v s then 1 else 0 := by
  simp [witnessBit, encodeCertificate, NatListCode.decode_encode]

@[simp] theorem witnessChoice_encode (v : List ℕ → Bool) (choice : List ℕ → ℕ) (s : List ℕ) :
    witnessChoice (encodeCertificate v choice) s = choice s := by
  simp [witnessChoice, encodeCertificate, NatListCode.decode_encode]

/-- A single row uses the current node, its k-th child, and the k-th basic
cylinder. Universal quantification over s and k covers every certificate clause. -/
def NatClause (c : BorelExpression) (x q : ℕ → ℕ) (s : List ℕ) (k : ℕ) : Prop :=
  witnessBit q s ≤ 1 ∧
  (c s = 0 → witnessBit q s = 0) ∧
  (c s = 1 → witnessBit q s = 1 → witnessChoice q s = k →
    c (s ++ [k]) ≠ 0 ∧ witnessBit q (s ++ [k]) = 1) ∧
  (c s = 1 → c (s ++ [k]) ≠ 0 → witnessBit q (s ++ [k]) = 1 → witnessBit q s = 1) ∧
  (c s = 2 → c (s ++ [k]) ≠ 0 → witnessBit q s + witnessBit q (s ++ [k]) = 1) ∧
  (c s = k + 3 → (witnessBit q s = 1 ↔ x ∈ cylinderBasis k))

def NatCertificate (c : BorelExpression) (x q : ℕ → ℕ) : Prop := ∀ s k, c.NatClause x q s k

/-- Decoding keeps the true/false assignment and all chosen children. -/
theorem NatCertificate.toLocal {c : BorelExpression} {x q : ℕ → ℕ}
    (h : c.NatCertificate x q) : c.LocalCertificate cylinderBasis x (decodeBits q) (witnessChoice q) := by
  intro s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hs
    have hzero := (h s 0).2.1 hs
    simp [decodeBits, hzero]
  · intro k hs hv hk
    have ht : witnessBit q s = 1 := by simpa [decodeBits] using hv
    obtain ⟨hc, hb⟩ := (h s k).2.2.1 hs ht hk
    exact ⟨hc, by simp [decodeBits, hb]⟩
  · intro k hs hc hv
    have ht : witnessBit q (s ++ [k]) = 1 := by simpa [decodeBits] using hv
    have hp := (h s k).2.2.2.1 hs hc ht
    simp [decodeBits, hp]
  · intro k hs hc
    have hadd := (h s k).2.2.2.2.1 hs hc
    apply Bool.eq_iff_iff.mpr
    simp [decodeBits]
    omega
  · intro k hs
    simpa [decodeBits] using (h s k).2.2.2.2.2 hs

theorem LocalCertificate.toNat {c : BorelExpression} {x : ℕ → ℕ}
    {v : List ℕ → Bool} {choice : List ℕ → ℕ}
    (h : c.LocalCertificate cylinderBasis x v choice) :
    c.NatCertificate x (encodeCertificate v choice) := by
  intro s k
  simp only [NatClause, witnessBit_encode, witnessChoice_encode]
  refine ⟨by cases v s <;> decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro hs
    simp [(h s).1 hs]
  · intro hs hv hk
    have ht : v s = true := by cases he : v s <;> simp_all
    obtain ⟨hc, hb⟩ := (h s).2.1 k hs ht hk
    exact ⟨hc, by simp [hb]⟩
  · intro hs hc hb
    have ht : v (s ++ [k]) = true := by cases he : v (s ++ [k]) <;> simp_all
    simp [(h s).2.2.1 k hs hc ht]
  · intro hs hc
    have hn := (h s).2.2.2.1 k hs hc
    rw [hn]
    cases v (s ++ [k]) <;> decide
  · intro hs
    have he := (h s).2.2.2.2 k hs
    cases hvs : v s <;> simpa [hvs] using he

/-- Natural witnesses express exactly the earlier Boolean certificates,
including the specified root bit. The code need not be valid for this bridge. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let a witness $w\in\BaireSpace$ store the pair of a truth bit $u_s$ and a selected child number $j_s$ at
    coordinate $\LambdaListCode{s}$. Require $u_s\le1$ at every word. For every word $s$ and number $k$,
    put $t=s\concat(k)$ and impose the following clauses:
    $$\begin{aligned}
    c(s)=0&\ \Longrightarrow\ u_s=0,\\
    c(s)=1\ \land\ u_s=1\ \land\ j_s=k&\ \Longrightarrow\ c(t)\ne0\ \land\ u_t=1,\\
    c(s)=1\ \land\ c(t)\ne0\ \land\ u_t=1&\ \Longrightarrow\ u_s=1,\\
    c(s)=2\ \land\ c(t)\ne0&\ \Longrightarrow\ u_s+u_t=1,\\
    c(s)=k+3&\ \Longrightarrow\ (u_s=1\ \Longleftrightarrow\ x\in U_k).
    \end{aligned}$$
    The selected child supplies the existential witness at a true union node. Thus these local clauses are
    exactly the truth-assignment rules, with the additional selected-child data. For a valid expression,
    well-founded induction gives the unique truth assignment. Choose a true child at each true union node
    to obtain a certificate, and assign zero to absent nodes. A certificate with root bit one exists exactly
    when $x\in A_c$; a certificate with root bit zero exists exactly when $x\notin A_c$.

    Number the rows by $i=\NatPair{\LambdaListCode{s}}{k}$, and set
    $$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,\Length{\LambdaListDecode{k}}\}.$$
    The row reads the witness at the codes of $s,t$ and the root, and reads $x$ only through its prefix of
    length $\Length{\LambdaListDecode{k}}$. Hence the first $b(i)$ entries of $x,w$ suffice, including the prescribed
    root bit. The bound is computed by list concatenation, length, pairing, successor, and maximum.
    The clause tester runs the supplied label program at $s,t$, extracts the witness entries, compares
    the indicated prefix with $\LambdaListDecode{k}$, and combines the resulting decision bits.
    The explicit lambda constructions are given in §{sec:lambda-recursive-borel-separation}.

    At length $n$, test each row $i<n$ with $b(i)\le n$, using the prefixes truncated to length $b(i)$.
    Require these tests at every shorter prefix as well, so that the accepted equal-length pairs form a tree.
    Every row is tested once $n\ge\max\{i+1,b(i)\}$. Consequently a branch is exactly a point together with a
    certificate of the prescribed root bit. Projecting the two trees gives $A_c$ and its complement.
    These programs decide finite certificate tests; validity is a hypothesis of the conclusion, and the
    construction does not decide validity or membership in $A_c$ from $x$.
    \end{proof}
-/
theorem natCertificate_root_iff (c : BorelExpression) (x : ℕ → ℕ) (b : Bool) :
    (∃ q, c.NatCertificate x q ∧ witnessBit q [] = if b then 1 else 0) ↔
      (c, x) ∈ EvaluationSide cylinderBasis b := by
  constructor
  · rintro ⟨q, hq, hb⟩
    refine ⟨decodeBits q, witnessChoice q, (c.certificate_iff_local _ _ _ _).mpr hq.toLocal, ?_⟩
    cases b <;> simp [decodeBits, hb]
  · rintro ⟨v, choice, hv, hb⟩
    refine ⟨encodeCertificate v choice, ((c.certificate_iff_local _ _ _ _).mp hv).toNat, ?_⟩
    simp [hb]

end BorelExpression
end PolishSpaceBook
