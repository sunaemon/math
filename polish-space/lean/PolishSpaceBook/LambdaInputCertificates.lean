module

public import PolishSpaceBook.LambdaReductionCertificates
public import PolishSpaceBook.LambdaNumeralCodes
public import PolishSpaceBook.LambdaOraclePrograms

@[expose] public section

/-! # Finite answer tables and certificates for input-query reduction

Tables are finite lists of input/output pairs. They are data for checking
reductions of the existing lambda syntax, not a second program language.
-/
namespace PolishSpaceBook.NamedLambda
namespace Term

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Finite-use statements describe how an existing computation depends on its input. To search for computations, we also need finite objects that certify them. An \termdefine{input answer table} is a finite list $t$ of pairs $(i,v)$ of natural numbers. It agrees with a name $p$ if $p(i)=v$ for every pair in the list. Repeated pairs are allowed, and the table need not be minimal. Agreement rules out conflicting answers at the same address.
-/
abbrev AnswerTable := List (ℕ × ℕ)

def AnswersAgree (p : ℕ → ℕ) (t : AnswerTable) : Prop :=
  ∀ i v, (i, v) ∈ t → p i = v

inductive QueryStep (t : AnswerTable) : Term → Term → Prop where
  | query (i v : ℕ) : (i, v) ∈ t →
      QueryStep t (.app (.var 0) (churchNumeral i)) (churchNumeral v)
  | app_left {M M'} (N) : QueryStep t M M' → QueryStep t (.app M N) (.app M' N)
  | app_right (M) {N N'} : QueryStep t N N' → QueryStep t (.app M N) (.app M N')
  | lam (x : ℕ) : x ≠ 0 → QueryStep t M M' → QueryStep t (.lam x M) (.lam x M')

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Work first with named terms and the fixed named representatives of Church numerals from §{sec:lambda-program-input-codes}. Form the finite list $\LambdaQuerySuccessors{t}{M}$ recursively. At an application $AB$, first scan $t$: a pair $(i,v)$ contributes $\ChurchNumeral{v}$ exactly when $A$ is literally $o$ and $B$ is literally the fixed representative of $\ChurchNumeral{i}$. Then append the lists obtained by taking a query step in the left and right subterms, restoring the other subterm in each case. At an abstraction with binder different from $o$, restore that binder around each query reduct of the body. At an abstraction binding $o$, and at a variable, the list is empty. Equality in the root test is syntactic equality of finite named terms.

    Combine this list with the ordinary beta reducts:
    $$\LambdaInputSuccessors{t}{M}:=
    \LambdaBetaSuccessors{M}\mathbin{+\!+}\LambdaQuerySuccessors{t}{M}.$$
    Here $+\!+$ denotes list concatenation. Beta steps are still allowed under every binder; only queries are blocked by a binder equal to $o$. Every list is finite. The chosen traversal order and repeated entries do not affect membership.
-/
def querySuccessors (t : AnswerTable) : Term → List Term
  | .var _ => []
  | .app M N =>
    (t.filterMap (fun a => if M = .var 0 ∧ N = churchNumeral a.1 then
      some (churchNumeral a.2) else none)) ++
    (querySuccessors t M).map (fun M' => .app M' N) ++
    (querySuccessors t N).map (fun N' => .app M N')
  | .lam x M => if x = 0 then [] else (querySuccessors t M).map (.lam x)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induction on the source term identifies the query list with the query rule and its allowed contexts. At a root query, agreement supplies the asserted answer from $p$; application contexts and abstractions with binder different from $o$ preserve the step. The beta list already has the corresponding soundness property. For the converse, induct on the input-query step. A beta step uses raw representatives and the empty table. A root query uses the fixed numeral representatives and the singleton table containing its address and actual answer. Lift these representatives through application contexts or an allowed abstraction. Finally, adding table entries preserves root-query membership, hence all query contexts by induction, while the beta list is unchanged.
    \end{proof}
-/
theorem querySuccessors_sound {t : AnswerTable} {M N : Term}
    (h : N ∈ querySuccessors t M) : QueryStep t M N := by
  induction M generalizing N with
  | var x => simp [querySuccessors] at h
  | app M P ihM ihP =>
    simp only [querySuccessors, List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨M', hM', rfl⟩) | ⟨P', hP', rfl⟩
    · obtain ⟨⟨i,v⟩, ht, hv⟩ := List.mem_filterMap.mp h
      split_ifs at hv with hc
      · obtain ⟨rfl,rfl⟩ := hc
        have he : churchNumeral v = N := Option.some.inj hv
        subst N
        exact .query i v ht
    · exact .app_left P (ihM hM')
    · exact .app_right M (ihP hP')
  | lam x M ih =>
    simp only [querySuccessors] at h
    split_ifs at h with hx
    · simp at h
    · obtain ⟨N', hN', rfl⟩ := List.mem_map.mp h
      exact .lam x hx (ih hN')

theorem querySuccessors_complete {t : AnswerTable} {M N : Term}
    (h : QueryStep t M N) : N ∈ querySuccessors t M := by
  induction h with
  | query i v ht =>
    simp only [querySuccessors, List.mem_append]
    apply Or.inl ∘ Or.inl
    exact List.mem_filterMap.mpr ⟨(i,v), ht, by simp⟩
  | app_left N h ih =>
    simp only [querySuccessors, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨_,ih,rfl⟩)
  | app_right M h ih =>
    simp only [querySuccessors, List.mem_append, List.mem_map]
    exact Or.inr ⟨_,ih,rfl⟩
  | lam x hx h ih =>
    simp only [querySuccessors, ite_eq_right hx]
    exact List.mem_map.mpr ⟨_,ih,rfl⟩

theorem QueryStep.mono {t u : AnswerTable} (htu : ∀ a ∈ t, a ∈ u)
    {M N : Term} (h : QueryStep t M N) : QueryStep u M N := by
  induction h with
  | query i v ht => exact .query i v (htu _ ht)
  | app_left N h ih => exact .app_left N ih
  | app_right M h ih => exact .app_right M ih
  | lam x hx h ih => exact .lam x hx ih

def inputSuccessors (t : AnswerTable) (M : Term) : List Term :=
  betaSuccessors M ++ querySuccessors t M

def InputStep (t : AnswerTable) (M N : Term) : Prop := Beta M N ∨ QueryStep t M N

theorem mem_inputSuccessors_iff (t : AnswerTable) (M N : Term) :
    N ∈ inputSuccessors t M ↔ InputStep t M N := by
  simp only [inputSuccessors, List.mem_append, InputStep, mem_betaSuccessors_iff]
  exact or_congr Iff.rfl ⟨querySuccessors_sound, querySuccessors_complete⟩

theorem InputStep.mono {t u : AnswerTable} (htu : ∀ a ∈ t, a ∈ u)
    {M N : Term} (h : InputStep t M N) : InputStep u M N :=
  h.imp id (QueryStep.mono htu)

theorem InputStep.app_left {t : AnswerTable} {M M' : Term} (N : Term)
    (h : InputStep t M M') : InputStep t (.app M N) (.app M' N) :=
  h.imp (Beta.app_left N) (QueryStep.app_left N)

theorem InputStep.app_right {t : AnswerTable} (M : Term) {N N' : Term}
    (h : InputStep t N N') : InputStep t (.app M N) (.app M N') :=
  h.imp (Beta.app_right M) (QueryStep.app_right M)

theorem InputStep.lam {t : AnswerTable} (x : ℕ) (hx : x ≠ 0) {M N : Term}
    (h : InputStep t M N) : InputStep t (.lam x M) (.lam x N) :=
  h.imp (Beta.lam x) (QueryStep.lam x hx)

theorem QueryStep.to_oracle {t : AnswerTable} {p : ℕ → ℕ} (hp : AnswersAgree p t)
    {M N : Term} (h : QueryStep t M N) :
    AlphaTerm.OracleStep p (AlphaTerm.mk M) (AlphaTerm.mk N) := by
  induction h with
  | query i v ht =>
    change AlphaTerm.OracleStep p
      (AlphaTerm.app (AlphaTerm.var 0) (AlphaTerm.mk (churchNumeral i)))
      (AlphaTerm.mk (churchNumeral v))
    rw [mk_churchNumeral, mk_churchNumeral, ← hp i v ht]
    exact .query i
  | app_left N h ih => exact .app_left (AlphaTerm.mk N) ih
  | app_right M h ih => exact .app_right (AlphaTerm.mk M) ih
  | lam x hx h ih => exact .lam x hx ih

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: One-step reductions with finite answer tables
-/
theorem InputStep.to_oracle {t : AnswerTable} {p : ℕ → ℕ} (hp : AnswersAgree p t)
    {M N : Term} (h : InputStep t M N) :
    AlphaTerm.OracleStep p (AlphaTerm.mk M) (AlphaTerm.mk N) := by
  rcases h with h | h
  · exact .beta (AlphaTerm.beta_of_raw h)
  · exact h.to_oracle hp

end Term
namespace AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: One-step reductions with finite answer tables
-/
theorem OracleStep.exists_table_step {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : OracleStep p M N) :
    ∃ t : Term.AnswerTable, Term.AnswersAgree p t ∧
      ∃ A B : Term, mk A = M ∧ mk B = N ∧ Term.InputStep t A B := by
  induction h with
  | beta hb =>
    obtain ⟨A,B,hA,hB,hAB⟩ := hb.exists_raw
    exact ⟨[], by simp [Term.AnswersAgree], A,B,hA,hB, Or.inl hAB⟩
  | query i =>
    refine ⟨[(i,p i)], ?_, .app (.var 0) (Term.churchNumeral i), Term.churchNumeral (p i), ?_, ?_, ?_⟩
    · intro j v hv
      have he : (j,v) = (i,p i) := by simpa using hv
      cases he
      rfl
    · change app (var 0) (mk (Term.churchNumeral i)) = _
      rw [Term.mk_churchNumeral]
    · exact Term.mk_churchNumeral _
    · exact Or.inr (.query i (p i) (by simp))
  | app_left N h ih =>
    obtain ⟨t,ht,A,B,hA,hB,hAB⟩ := ih
    obtain ⟨C,rfl⟩ := Quotient.exists_rep N
    refine ⟨t,ht,.app A C,.app B C,?_,?_,hAB.app_left C⟩
    · exact congrArg (fun R => app R (mk C)) hA
    · exact congrArg (fun R => app R (mk C)) hB
  | app_right M h ih =>
    obtain ⟨t,ht,A,B,hA,hB,hAB⟩ := ih
    obtain ⟨C,rfl⟩ := Quotient.exists_rep M
    refine ⟨t,ht,.app C A,.app C B,?_,?_,hAB.app_right C⟩
    · exact congrArg (app (mk C)) hA
    · exact congrArg (app (mk C)) hB
  | lam x hx h ih =>
    obtain ⟨t,ht,A,B,hA,hB,hAB⟩ := ih
    exact ⟨t,ht,.lam x A,.lam x B,congrArg (AlphaTerm.lam x) hA,congrArg (AlphaTerm.lam x) hB,hAB.lam x hx⟩

end AlphaTerm
namespace Term

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For a table $t$, define the Boolean certificate check $\LambdaInputCertificate{t}{M}{N}{c}$ just as in §{sec:lambda-reduction-certificates}, using $\LambdaInputSuccessors{t}{A}$ for each listed step. The empty certificate is accepted exactly when $M$ and $N$ are alpha-equivalent. A certificate beginning with $(A,B)$ is accepted exactly when $M$ is alpha-equivalent to $A$, the term $B$ belongs to $\LambdaInputSuccessors{t}{A}$, and the remaining certificate is accepted from $B$ to $N$. All checks on terms and lists are finite. Changes of representative are checked at the joins, so the use of fixed numeral representatives in root queries loses no reductions.
-/
def checkInputCertificate (t : AnswerTable) (M N : Term) : List (Term × Term) → Bool
  | [] => decide (M.Alpha N)
  | (A,B) :: cs => decide (M.Alpha A) && decide (B ∈ inputSuccessors t A) &&
      checkInputCertificate t B N cs

theorem checkInputCertificate_mono {t u : AnswerTable} (htu : ∀ a ∈ t, a ∈ u)
    {M N : Term} {cs : List (Term × Term)} (h : checkInputCertificate t M N cs = true) :
    checkInputCertificate u M N cs = true := by
  induction cs generalizing M with
  | nil => exact h
  | cons c cs ih =>
    obtain ⟨A,B⟩ := c
    simp only [checkInputCertificate, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨h.1.1,(mem_inputSuccessors_iff u A B).mpr
      (((mem_inputSuccessors_iff t A B).mp h.1.2).mono htu)⟩,ih h.2⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For soundness, induct on an accepted certificate. The empty case gives equality of alpha-classes. Otherwise, its first pair gives a valid input-query step by the lemma, and the induction hypothesis supplies the rest of the reduction.

    Conversely, induct on a finite input-query reduction, keeping arbitrary named representatives of its endpoints. For an empty reduction, use the empty table and certificate. For the first step of a nonempty reduction, take the representatives and table supplied by the lemma. Apply the induction hypothesis to the tail, starting with the chosen target representative of that first step. Concatenate the two answer tables. Both agree with $p$, so their concatenation does too. Table enlargement preserves the first step and every step of the tail certificate. Prepend the first pair to the tail certificate; alpha-equivalence at the join handles the chosen source representative.
    \end{proof}
-/
theorem checkInputCertificate_sound {t : AnswerTable} {p : ℕ → ℕ}
    (hp : AnswersAgree p t) {M N : Term} {cs : List (Term × Term)}
    (h : checkInputCertificate t M N cs = true) :
    Relation.ReflTransGen (AlphaTerm.OracleStep p) (AlphaTerm.mk M) (AlphaTerm.mk N) := by
  induction cs generalizing M with
  | nil =>
    have he : M.Alpha N := by simpa [checkInputCertificate] using h
    rw [(AlphaTerm.mk_eq_iff M N).mpr he]
  | cons c cs ih =>
    obtain ⟨A,B⟩ := c
    simp only [checkInputCertificate, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [(AlphaTerm.mk_eq_iff M A).mpr h.1.1]
    exact .head (((mem_inputSuccessors_iff t A B).mp h.1.2).to_oracle hp) (ih h.2)

theorem checkInputCertificate_complete {p : ℕ → ℕ} {P Q : AlphaTerm}
    (h : Relation.ReflTransGen (AlphaTerm.OracleStep p) P Q) :
    ∀ M N : Term, AlphaTerm.mk M = P → AlphaTerm.mk N = Q →
      ∃ t : AnswerTable, AnswersAgree p t ∧ ∃ cs, checkInputCertificate t M N cs = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro M N hM hN
    refine ⟨[], by simp [AnswersAgree], [], ?_⟩
    have he : M.Alpha N := (AlphaTerm.mk_eq_iff M N).mp (hM.trans hN.symm)
    simpa [checkInputCertificate] using he
  | @head P R hPR hRQ ih =>
    intro M N hM hN
    obtain ⟨t,ht,A,B,hA,hB,hAB⟩ := hPR.exists_table_step
    obtain ⟨u,hu,cs,hcs⟩ := ih B N hB hN
    refine ⟨t ++ u, ?_, (A,B) :: cs, ?_⟩
    · intro i v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact ht i v hv
      · exact hu i v hv
    · have he : M.Alpha A := (AlphaTerm.mk_eq_iff M A).mp (hM.trans hA.symm)
      simp only [checkInputCertificate, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨he,(mem_inputSuccessors_iff _ A B).mpr
        (hAB.mono (fun a ha => List.mem_append_left _ ha))⟩,
        checkInputCertificate_mono (fun a ha => List.mem_append_right _ ha) hcs⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Finite certificates for input-query reduction
-/
theorem oracle_steps_iff_certificate (p : ℕ → ℕ) (M N : Term) :
    Relation.ReflTransGen (AlphaTerm.OracleStep p) (AlphaTerm.mk M) (AlphaTerm.mk N) ↔
      ∃ t : AnswerTable, AnswersAgree p t ∧ ∃ cs, checkInputCertificate t M N cs = true := by
  constructor
  · intro h
    exact checkInputCertificate_complete h M N rfl rfl
  · rintro ⟨t,ht,cs,hcs⟩
    exact checkInputCertificate_sound ht hcs

/-- Check only the finitely many answers explicitly listed in the table. -/
def answersAgreeTest (p : ℕ → ℕ) (t : AnswerTable) : Bool :=
  t.all (fun a => decide (p a.1 = a.2))

theorem answersAgreeTest_spec (p : ℕ → ℕ) (t : AnswerTable) :
    answersAgreeTest p t = true ↔ AnswersAgree p t := by
  simp only [answersAgreeTest, List.all_eq_true, decide_eq_true_eq, AnswersAgree]
  constructor
  · intro h i v hv
    exact h (i,v) hv
  · intro h a ha
    exact h a.1 a.2 ha

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Encode an answer table by the existing numerical list and pairing codes:
    $$\begin{aligned}
    &\LambdaAnswerTableCode{[(i_0,v_0),\ldots,(i_{r-1},v_{r-1})]}\\
    &\qquad :=\LambdaListCode{[\NatPair{i_0}{v_0},\ldots,\NatPair{i_{r-1}}{v_{r-1}}]}.
    \end{aligned}$$
    Decode a number as a list and unpair each entry. The list and pairing identities show that encoding and decoding are mutual inverses. A candidate code $e$ is a pair of an answer-table code and a certificate code; write $t_e,c_e$ for the decoded objects. Check the finitely many equations $p(i)=v$ in $t_e$ and the finite test $\LambdaInputCertificate{t_e}{M}{N}{c_e}$. Define $\LambdaInputTest{p}{s}{M}{N}$ to be true exactly when at least one candidate code $e<s$ passes both checks.
-/
def answerTableCode (t : AnswerTable) : ℕ :=
  NatListCode.encode (t.map (fun a => Nat.pair a.1 a.2))

def decodeAnswerTable (e : ℕ) : AnswerTable :=
  (NatListCode.decode e).map Nat.unpair

@[simp] theorem decode_answerTableCode (t : AnswerTable) :
    decodeAnswerTable (answerTableCode t) = t := by
  simp [decodeAnswerTable, answerTableCode, List.map_map, Function.comp_def]

/-- A candidate pairs one table code with one reduction-certificate code. -/
def inputCertificateTest (p : ℕ → ℕ) (M N : Term) (e : ℕ) : Bool :=
  answersAgreeTest p (decodeAnswerTable (Nat.unpair e).1) &&
    checkInputCertificate (decodeAnswerTable (Nat.unpair e).1) M N
      (decodeCertificate (Nat.unpair e).2)

def boundedInputTest (p : ℕ → ℕ) (M N : Term) (s : ℕ) : Bool :=
  (List.range s).any (inputCertificateTest p M N)

theorem boundedInputTest_spec (p : ℕ → ℕ) (M N : Term) (s : ℕ) :
    boundedInputTest p M N s = true ↔
      ∃ e < s, inputCertificateTest p M N e = true := by
  simp [boundedInputTest, List.any_eq_true]

theorem boundedInputTest_mono {p : ℕ → ℕ} {M N : Term} {s r : ℕ}
    (hsr : s ≤ r) (h : boundedInputTest p M N s = true) :
    boundedInputTest p M N r = true := by
  obtain ⟨e,he,hc⟩ := (boundedInputTest_spec p M N s).mp h
  exact (boundedInputTest_spec p M N r).mpr ⟨e,he.trans_le hsr,hc⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Only finitely many candidate codes occur at a fixed stage, and each decoded table and certificate is finite. Increasing the stage retains every earlier candidate. If a candidate is accepted, its consistent table and valid certificate give the reduction by the proposition. Conversely, encode a table and certificate for an existing reduction, pair their codes, and choose a stage larger than that pair code. Decoding recovers the same witnesses, so the candidate is accepted at that stage. The final assertion is the definition of a program's numerical output.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: corollary
  title: Finite-stage detection with input queries
-/
theorem oracle_steps_iff_bounded_input_test (p : ℕ → ℕ) (M N : Term) :
    Relation.ReflTransGen (AlphaTerm.OracleStep p) (AlphaTerm.mk M) (AlphaTerm.mk N) ↔
      ∃ s, boundedInputTest p M N s = true := by
  rw [oracle_steps_iff_certificate]
  constructor
  · rintro ⟨t,ht,cs,hcs⟩
    let e := Nat.pair (answerTableCode t) (certificateCode cs)
    refine ⟨e + 1, (boundedInputTest_spec p M N _).mpr ⟨e,Nat.lt_succ_self _,?_⟩⟩
    simpa only [inputCertificateTest, e, Nat.unpair_pair, decode_answerTableCode,
      decode_certificateCode, Bool.and_eq_true] using
      And.intro ((answersAgreeTest_spec p t).mpr ht) hcs
  · rintro ⟨s,hs⟩
    obtain ⟨e,_,he⟩ := (boundedInputTest_spec p M N s).mp hs
    simp only [inputCertificateTest, Bool.and_eq_true] at he
    exact ⟨_,(answersAgreeTest_spec p _).mp he.1,_,he.2⟩

/-- One greater than every queried address, with zero for the empty table. -/
def answerBound : AnswerTable → ℕ
  | [] => 0
  | (i,_) :: t => max (i + 1) (answerBound t)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Induction on a table shows that agreement below $K(t)$ preserves the truth of all its answer checks. The certificate check itself does not use the name. Now induct on the stage. Stage zero checks no candidates. Passing from stage $s$ to stage $s+1$ retains the earlier candidates and adds just candidate $s$. The two bounds in the maximum preserve the earlier result and the new candidate's answer check, respectively. Hence the Boolean result of the whole stage is unchanged, whether it is true or false.
    \end{proof}
-/
theorem answersAgreeTest_eq_of_prefix {p q : ℕ → ℕ} (t : AnswerTable)
    (h : ∀ i < answerBound t, q i = p i) :
    answersAgreeTest q t = answersAgreeTest p t := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨i,v⟩ := a
    have hi : q i = p i := h i ((Nat.lt_succ_self i).trans_le (le_max_left _ _))
    have ht := ih (fun j hj => h j (hj.trans_le (le_max_right _ _)))
    simpa only [answersAgreeTest, List.all_cons, hi] using
      congrArg (fun b => decide (p i = v) && b) ht

theorem inputCertificateTest_eq_of_prefix {p q : ℕ → ℕ} (M N : Term) (e : ℕ)
    (h : ∀ i < answerBound (decodeAnswerTable (Nat.unpair e).1), q i = p i) :
    inputCertificateTest q M N e = inputCertificateTest p M N e := by
  unfold inputCertificateTest
  rw [answersAgreeTest_eq_of_prefix _ h]

@[simp] theorem answerTableCode_decode (e : ℕ) :
    answerTableCode (decodeAnswerTable e) = e := by
  simp [answerTableCode, decodeAnswerTable, List.map_map, Function.comp_def]

def inputTestBound : ℕ → ℕ
  | 0 => 0
  | s + 1 => max (inputTestBound s) (answerBound (decodeAnswerTable (Nat.unpair s).1))

theorem boundedInputTest_succ (p : ℕ → ℕ) (M N : Term) (s : ℕ) :
    boundedInputTest p M N (s + 1) =
      (boundedInputTest p M N s || inputCertificateTest p M N s) := by
  simp [boundedInputTest, List.range_succ, List.any_append]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: A uniform input bound for each test stage
-/
theorem boundedInputTest_eq_of_prefix {p q : ℕ → ℕ} (M N : Term) (s : ℕ)
    (h : ∀ i < inputTestBound s, q i = p i) :
    boundedInputTest q M N s = boundedInputTest p M N s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [boundedInputTest_succ, boundedInputTest_succ]
    rw [ih (fun i hi => h i (hi.trans_le (le_max_left _ _)))]
    rw [inputCertificateTest_eq_of_prefix M N s
      (fun i hi => h i (hi.trans_le (le_max_right _ _)))]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: corollary
  title: Finite-stage detection with input queries
-/
theorem oracle_runs_iff_bounded_input_test (p : ℕ → ℕ) (P : Term) (n m : ℕ) :
    AlphaTerm.OracleRuns p (AlphaTerm.mk P) n m ↔
      ∃ s, boundedInputTest p (.app (.app P (.var 0)) (churchNumeral n))
        (churchNumeral m) s = true := by
  have h := oracle_steps_iff_bounded_input_test p
    (.app (.app P (.var 0)) (churchNumeral n)) (churchNumeral m)
  change Relation.ReflTransGen (AlphaTerm.OracleStep p)
      (AlphaTerm.app (AlphaTerm.app (AlphaTerm.mk P) (AlphaTerm.var 0))
        (AlphaTerm.mk (churchNumeral n))) (AlphaTerm.mk (churchNumeral m)) ↔ _ at h
  simpa only [mk_churchNumeral, AlphaTerm.OracleRuns] using h

end Term
end PolishSpaceBook.NamedLambda
