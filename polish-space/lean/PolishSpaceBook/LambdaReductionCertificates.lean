module

public import PolishSpaceBook.LambdaFiniteLists
public import PolishSpaceBook.LambdaSyntaxCoding

@[expose] public section

/-! # Finite certificates for beta-reduction on alpha-classes -/
namespace PolishSpaceBook.NamedLambda.Term

/-- Contract each redex once, traversing both application branches and abstractions. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For a named term $M$, form the finite list $\LambdaBetaSuccessors{M}$ of its one-step reducts as follows. A variable has no reducts. At an application $AB$, include the root contraction when $A$ is an abstraction, then include the reducts obtained by reducing the left side and those obtained by reducing the right side. Under an abstraction, put the binder around each reduct of the body. Root contraction uses the capture-avoiding substitution already constructed. Induction on a term shows that every listed term is a one-step reduct; induction on a beta-step derivation shows that every reduct is listed.
-/
def betaSuccessors : Term → List Term
  | .var _ => []
  | .app M N =>
    (match M with | .lam x A => [A.subst x N] | _ => []) ++
    (betaSuccessors M).map (fun M' => .app M' N) ++
    (betaSuccessors N).map (fun N' => .app M N')
  | .lam x M => (betaSuccessors M).map (.lam x)

theorem betaSuccessors_sound {M N : Term} (h : N ∈ betaSuccessors M) : Beta M N := by
  induction M generalizing N with
  | var x => simp [betaSuccessors] at h
  | app M P ihM ihP =>
    simp only [betaSuccessors, List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨M', hM', rfl⟩) | ⟨P', hP', rfl⟩
    · cases M with
      | var x => simp at h
      | app A B => simp at h
      | lam x A =>
        simp only [List.mem_singleton] at h
        subst N
        exact .contract x A P
    · exact .app_left P (ihM hM')
    · exact .app_right M (ihP hP')
  | lam x M ih =>
    obtain ⟨N', hN', rfl⟩ := List.mem_map.mp h
    exact .lam x (ih hN')

theorem betaSuccessors_complete {M N : Term} (h : Beta M N) : N ∈ betaSuccessors M := by
  induction h with
  | contract x M N => simp [betaSuccessors]
  | app_left N h ih =>
    simp only [betaSuccessors, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨_, ih, rfl⟩)
  | app_right M h ih =>
    simp only [betaSuccessors, List.mem_append, List.mem_map]
    exact Or.inr ⟨_, ih, rfl⟩
  | lam x h ih => exact List.mem_map.mpr ⟨_, ih, rfl⟩

theorem mem_betaSuccessors_iff (M N : Term) : N ∈ betaSuccessors M ↔ Beta M N :=
  ⟨betaSuccessors_sound, betaSuccessors_complete⟩

/-- Each pair records one raw step. Binding-tree equality joins consecutive representatives. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    A \termdefine{lambda reduction certificate} from $M$ to $N$ is a finite list of pairs of named terms. The empty list is accepted exactly when $M$ and $N$ are alpha-equivalent. A nonempty list beginning with $(A,B)$ is accepted exactly when $M$ is alpha-equivalent to $A$, the term $B$ belongs to $\LambdaBetaSuccessors{A}$, and the remaining list is accepted from $B$ to $N$. Each test terminates: lists are finite, the reduct list is finite, and alpha-equivalence is decidable by comparison of the named terms. The checks at the joins account for changes of representative when passing between named reductions and reductions of alpha-classes.
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the finite syntactic checks here and in §{sec:lambda-reduction-certificates}, apply the beta rules to named terms
    using the prescribed capture-avoiding substitution. Keep variable names in these checks. Changes of representative under
    alpha-equivalence will be handled separately when joining the steps of a certificate.
-/
def checkBetaCertificate (M N : Term) : List (Term × Term) → Bool
  | [] => decide (M.Alpha N)
  | (A, B) :: cs => decide (M.Alpha A) && decide (B ∈ betaSuccessors A) &&
      checkBetaCertificate B N cs

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Induct on an accepted list. The empty list gives equality of alpha-classes. For a nonempty list, its first pair gives a raw beta step, which projects to a class step; prepend it to the reduction supplied by the remaining list. Conversely, induct on a finite class reduction. For its first step, choose raw representatives witnessing that step, as established in the beta-reduction lemma of §{sec:lambda-calculus}. Prepend this pair to a certificate for the remaining reduction, using alpha-equivalence at the join. For the empty reduction, use the empty list. The same argument covers arbitrary choices of the two endpoint representatives.
-/
theorem checkBetaCertificate_sound {M N : Term} {cs : List (Term × Term)}
    (h : checkBetaCertificate M N cs = true) :
    Relation.ReflTransGen AlphaTerm.Beta (AlphaTerm.mk M) (AlphaTerm.mk N) := by
  induction cs generalizing M with
  | nil =>
    have he : M.Alpha N := by simpa [checkBetaCertificate] using h
    rw [(AlphaTerm.mk_eq_iff M N).mpr he]
  | cons c cs ih =>
    obtain ⟨A, B⟩ := c
    simp only [checkBetaCertificate, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [(AlphaTerm.mk_eq_iff M A).mpr h.1.1]
    exact .head (AlphaTerm.beta_of_raw (betaSuccessors_sound h.1.2)) (ih h.2)

theorem checkBetaCertificate_complete {P Q : AlphaTerm}
    (h : Relation.ReflTransGen AlphaTerm.Beta P Q) :
    ∀ M N : Term, AlphaTerm.mk M = P → AlphaTerm.mk N = Q →
      ∃ cs, checkBetaCertificate M N cs = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro M N hM hN
    refine ⟨[], ?_⟩
    have he : M.Alpha N := (AlphaTerm.mk_eq_iff M N).mp (hM.trans hN.symm)
    simpa [checkBetaCertificate] using he
  | @head P R hPR hRQ ih =>
    intro M N hM hN
    obtain ⟨A, B, hA, hB, hAB⟩ := hPR.exists_raw
    obtain ⟨cs, hcs⟩ := ih B N hB hN
    refine ⟨(A, B) :: cs, ?_⟩
    have he : M.Alpha A := (AlphaTerm.mk_eq_iff M A).mp (hM.trans hA.symm)
    simp only [checkBetaCertificate, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨he, betaSuccessors_complete hAB⟩, hcs⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Finite certificates for beta-reduction
-/
theorem beta_steps_iff_certificate (M N : Term) :
    Relation.ReflTransGen AlphaTerm.Beta (AlphaTerm.mk M) (AlphaTerm.mk N) ↔
      ∃ cs, checkBetaCertificate M N cs = true := by
  constructor
  · intro h
    exact checkBetaCertificate_complete h M N rfl rfl
  · rintro ⟨cs, hcs⟩
    exact checkBetaCertificate_sound hcs

/-- The empty certificate is zero; each cons cell uses the existing numerical pair. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Encode certificate lists by
    $$\begin{aligned}
    \LambdaCertificateCode{[]}&:=0,\\
    \LambdaCertificateCode{(A,B)::c}&:=
    \NatPair{\NatPair{\LambdaSyntaxCode{A}}{\LambdaSyntaxCode{B}}}{\LambdaCertificateCode{c}}+1.
    \end{aligned}$$
    Decode zero as the empty list. For a positive code $e$, unpair $e-1$, decode the first component as a pair of term codes, and recursively decode the second as the tail. The tail code is at most $e-1$, hence smaller than $e$, so this recursion terminates. Induction on lists shows that decoding their codes returns the original lists. For $s\in\NN$, let $\LambdaBetaTest{s}{M}{N}$ be true when at least one certificate with code less than $s$ is accepted from $M$ to $N$, and false otherwise.
-/
def certificateCode : List (Term × Term) → ℕ
  | [] => 0
  | (M, N) :: cs => Nat.pair (Nat.pair M.code N.code) (certificateCode cs) + 1

def decodeCertificate : ℕ → List (Term × Term)
  | 0 => []
  | e + 1 =>
    (decode (Nat.unpair (Nat.unpair e).1).1,
     decode (Nat.unpair (Nat.unpair e).1).2) :: decodeCertificate (Nat.unpair e).2
termination_by e => e
decreasing_by have := Nat.unpair_right_le e; omega

@[simp] theorem decode_certificateCode (cs : List (Term × Term)) :
    decodeCertificate (certificateCode cs) = cs := by
  induction cs with
  | nil => simp [certificateCode, decodeCertificate]
  | cons c cs ih =>
    obtain ⟨M, N⟩ := c
    simp [certificateCode, decodeCertificate, ih]

/-- The generic list programs use exactly the certificate coding already fixed here. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Encode certificate lists by
    $$\begin{aligned}
    \LambdaCertificateCode{[]}&:=0,\\
    \LambdaCertificateCode{(A,B)::c}&:=
    \NatPair{\NatPair{\LambdaSyntaxCode{A}}{\LambdaSyntaxCode{B}}}{\LambdaCertificateCode{c}}+1.
    \end{aligned}$$
    Decode zero as the empty list. For a positive code $e$, unpair $e-1$, decode the first component as a pair of term codes, and recursively decode the second as the tail. The tail code is at most $e-1$, hence smaller than $e$, so this recursion terminates. Induction on lists shows that decoding their codes returns the original lists. For $s\in\NN$, let $\LambdaBetaTest{s}{M}{N}$ be true when at least one certificate with code less than $s$ is accepted from $M$ to $N$, and false otherwise.
-/
theorem certificateCode_eq_listCode (cs : List (Term × Term)) :
    certificateCode cs = NatListCode.encode (cs.map (fun c => Nat.pair c.1.code c.2.code)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c; simp [certificateCode, NatListCode.encode, ih]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Encode certificate lists by
    $$\begin{aligned}
    \LambdaCertificateCode{[]}&:=0,\\
    \LambdaCertificateCode{(A,B)::c}&:=
    \NatPair{\NatPair{\LambdaSyntaxCode{A}}{\LambdaSyntaxCode{B}}}{\LambdaCertificateCode{c}}+1.
    \end{aligned}$$
    Decode zero as the empty list. For a positive code $e$, unpair $e-1$, decode the first component as a pair of term codes, and recursively decode the second as the tail. The tail code is at most $e-1$, hence smaller than $e$, so this recursion terminates. Induction on lists shows that decoding their codes returns the original lists. For $s\in\NN$, let $\LambdaBetaTest{s}{M}{N}$ be true when at least one certificate with code less than $s$ is accepted from $M$ to $N$, and false otherwise.
-/
theorem decodeCertificate_eq_listDecode (e : ℕ) :
    decodeCertificate e = (NatListCode.decode e).map
      (fun c => (decode (Nat.unpair c).1, decode (Nat.unpair c).2)) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    cases e with
    | zero => simp [decodeCertificate, NatListCode.decode]
    | succ e =>
      rw [decodeCertificate, NatListCode.decode, List.map_cons,
        ih _ (by have := Nat.unpair_right_le e; omega)]

/-- A finite-stage test enumerates certificate codes, not a single reduction path. -/
def boundedBetaTest (M N : Term) (s : ℕ) : Bool :=
  (List.range s).any (fun e => checkBetaCertificate M N (decodeCertificate e))

theorem boundedBetaTest_spec (M N : Term) (s : ℕ) :
    boundedBetaTest M N s = true ↔
      ∃ e < s, checkBetaCertificate M N (decodeCertificate e) = true := by
  simp [boundedBetaTest, List.any_eq_true]

theorem boundedBetaTest_mono {M N : Term} {s t : ℕ} (hst : s ≤ t)
    (h : boundedBetaTest M N s = true) : boundedBetaTest M N t = true := by
  obtain ⟨e, he, hc⟩ := (boundedBetaTest_spec M N s).mp h
  exact (boundedBetaTest_spec M N t).mpr ⟨e, he.trans_le hst, hc⟩

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Finite-stage detection of beta-reduction
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    At a fixed stage only finitely many finite certificates are checked. Increasing the stage retains every code already checked. If a stage accepts, its successful certificate yields the reduction by the proposition. Conversely, take an accepted certificate for the reduction and choose a stage greater than its code. At that stage the certificate is decoded and accepted. Thus every finite successful reduction is eventually detected, even if some other reduction paths are infinite.
-/
theorem beta_steps_iff_bounded_test (M N : Term) :
    Relation.ReflTransGen AlphaTerm.Beta (AlphaTerm.mk M) (AlphaTerm.mk N) ↔
      ∃ s, boundedBetaTest M N s = true := by
  rw [beta_steps_iff_certificate]
  constructor
  · rintro ⟨cs, hc⟩
    refine ⟨certificateCode cs + 1, (boundedBetaTest_spec _ _ _).mpr
      ⟨certificateCode cs, Nat.lt_succ_self _, ?_⟩⟩
    simpa only [decode_certificateCode] using hc
  · rintro ⟨s, hs⟩
    obtain ⟨e, _, he⟩ := (boundedBetaTest_spec M N s).mp hs
    exact ⟨decodeCertificate e, he⟩

end PolishSpaceBook.NamedLambda.Term
