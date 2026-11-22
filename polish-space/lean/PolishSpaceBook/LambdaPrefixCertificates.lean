module

public import PolishSpaceBook.LambdaPrefixMargins
public import PolishSpaceBook.LambdaInputCertificateChecker

@[expose] public section

/-! # Ordinary lambda certificates supported by a finite input prefix

Every queried address must be inside the prefix. In particular the default zero
returned by list access outside the prefix cannot create a spurious certificate.
The checker is total on all numerical codes and uses no input oracle.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-- Check entry `j` of the answer table in `pair prefixCode tableCode`. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The finite-table checker of §{sec:lambda-input-certificates} can be used without an input name when all proposed answers
    are supplied by a finite prefix. Let $s$ be a finite sequence and $\theta$ a finite answer table. For each entry
    $\Pair{i}{v}$ of
    $\theta$, test both
    $$i<\Length{s}\qquad\text{and}\qquad s(i)=v.$$
    The first condition is essential: the zero returned by list access outside its domain is not an answer supplied by the
    prefix. Compute each condition as zero or one, multiply the two results, and take the bounded product over the entries
    of $\theta$. This gives a closed total term $\LambdaTermName{tableSupport}$ on $\NatPair{ \LambdaListCode{s}}{
    \LambdaAnswerTableCode{ \theta}}$. Here the code of an
    answer table is the list code of its numerically paired entries.
-/
def prefixAnswerStage : AlphaTerm :=
  let W := numericalProjectionTerm true
  let J := numericalProjectionTerm false
  let S := firstOutput W
  let T := secondOutput W
  let A := numericalCompose listGetTerm (pairNumerical T J)
  let I := firstOutput A
  let V := secondOutput A
  mulNumerical
    (numericalCombine strictLessTerm I (numericalCompose listLengthTerm S))
    (numericalCombine equalityTerm (numericalCompose listGetTerm (pairNumerical S I)) V)

def prefixAnswerStageValue (z : ℕ) : ℕ :=
  let s := NatListCode.decode z.unpair.1.unpair.1
  let a := ((NatListCode.decode z.unpair.1.unpair.2).getD z.unpair.2 0).unpair
  (if a.1 < s.length then 1 else 0) * (if s.getD a.1 0 = a.2 then 1 else 0)

theorem prefixAnswerStage_computes : NumericalComputes prefixAnswerStage prefixAnswerStageValue := by
  have hw := projection_computes true
  have hj := projection_computes false
  have hs := hw.first
  have ha := listGet_computes.comp (hw.second.pair hj)
  have hi := ha.first
  have hv := ha.second
  have hlt := hi.combine (listLength_computes.comp hs) strictLessTerm_closed (fun a b => if a < b then 1 else 0) strictLessTerm_apply
  have heq := (listGet_computes.comp (hs.pair hi)).combine hv equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply
  unfold prefixAnswerStageValue
  simpa [prefixAnswerStage,Nat.unpair_pair] using hlt.mul heq

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The finite-table checker of §{sec:lambda-input-certificates} can be used without an input name when all proposed answers
    are supplied by a finite prefix. Let $s$ be a finite sequence and $\theta$ a finite answer table. For each entry
    $\Pair{i}{v}$ of
    $\theta$, test both
    $$i<\Length{s}\qquad\text{and}\qquad s(i)=v.$$
    The first condition is essential: the zero returned by list access outside its domain is not an answer supplied by the
    prefix. Compute each condition as zero or one, multiply the two results, and take the bounded product over the entries
    of $\theta$. This gives a closed total term $\LambdaTermName{tableSupport}$ on $\NatPair{ \LambdaListCode{s}}{
    \LambdaAnswerTableCode{ \theta}}$. Here the code of an
    answer table is the list code of its numerically paired entries.
-/
def prefixAnswerProgram := numericalCompose (boundedProductTerm prefixAnswerStage)
  (pairNumerical numericalIdentity (numericalCompose listLengthTerm (numericalProjectionTerm false)))

def prefixAnswerValue (w : ℕ) :=
  boundedProduct prefixAnswerStageValue w (NatListCode.decode w.unpair.2).length

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The finite-table checker of §{sec:lambda-input-certificates} can be used without an input name when all proposed answers
    are supplied by a finite prefix. Let $s$ be a finite sequence and $\theta$ a finite answer table. For each entry
    $\Pair{i}{v}$ of
    $\theta$, test both
    $$i<\Length{s}\qquad\text{and}\qquad s(i)=v.$$
    The first condition is essential: the zero returned by list access outside its domain is not an answer supplied by the
    prefix. Compute each condition as zero or one, multiply the two results, and take the bounded product over the entries
    of $\theta$. This gives a closed total term $\LambdaTermName{tableSupport}$ on $\NatPair{ \LambdaListCode{s}}{
    \LambdaAnswerTableCode{ \theta}}$. Here the code of an
    answer table is the list code of its numerically paired entries.
-/
theorem prefixAnswerProgram_computes : NumericalComputes prefixAnswerProgram prefixAnswerValue := by
  unfold prefixAnswerValue
  simpa [prefixAnswerProgram,Nat.unpair_pair] using
    (boundedProduct_computes prefixAnswerStage_computes).comp
      (numericalIdentity_computes.pair (listLength_computes.comp (projection_computes false)))

def PrefixAnswersAgree (s : List ℕ) (t : Term.AnswerTable) : Prop :=
  ∀ a ∈ t, a.1 < s.length ∧ s.getD a.1 0 = a.2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The finite-table checker of §{sec:lambda-input-certificates} can be used without an input name when all proposed answers
    are supplied by a finite prefix. Let $s$ be a finite sequence and $\theta$ a finite answer table. For each entry
    $\Pair{i}{v}$ of
    $\theta$, test both
    $$i<\Length{s}\qquad\text{and}\qquad s(i)=v.$$
    The first condition is essential: the zero returned by list access outside its domain is not an answer supplied by the
    prefix. Compute each condition as zero or one, multiply the two results, and take the bounded product over the entries
    of $\theta$. This gives a closed total term $\LambdaTermName{tableSupport}$ on $\NatPair{ \LambdaListCode{s}}{
    \LambdaAnswerTableCode{ \theta}}$. Here the code of an
    answer table is the list code of its numerically paired entries.
-/
theorem prefixAnswerValue_success (w : ℕ) :
    prefixAnswerValue w ≠ 0 ↔
      PrefixAnswersAgree (NatListCode.decode w.unpair.1) (Term.decodeAnswerTable w.unpair.2) := by
  simp only [prefixAnswerValue,boundedProduct_ne_zero]
  constructor
  · intro h a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,hj,hc⟩ := List.mem_iff_getElem.mp hc
    have ht := h j hj
    have he : (NatListCode.decode w.unpair.2).getD j 0 = c := by simp [List.getD,hj,hc]
    simp only [prefixAnswerStageValue,Nat.unpair_pair] at ht
    rw [he] at ht
    simpa [and_comm] using ht
  · intro h j hj
    have hm : (NatListCode.decode w.unpair.2).getD j 0 ∈ NatListCode.decode w.unpair.2 := by
      simp [List.getD,hj]
    have ht := h _ (List.mem_map.mpr ⟨_,hm,rfl⟩)
    simpa [prefixAnswerStageValue,Nat.unpair_pair,and_comm] using ht

theorem prefixAnswerValue_zero_or_one (w : ℕ) :
    prefixAnswerValue w = 0 ∨ prefixAnswerValue w = 1 := by
  apply boundedProduct_zero_or_one
  intro j
  dsimp only [prefixAnswerStageValue]
  split_ifs <;> simp

/-- Package the four arguments to the already constructed certificate checker. -/
def numericalInputCertificateBody (Z : AlphaTerm) :=
  let T := app (numericalProjectionTerm true) Z
  let R := app (numericalProjectionTerm false) Z
  let C := app (numericalProjectionTerm true) R
  let E := app (numericalProjectionTerm false) R
  app (app (app (app inputCertificateTerm T) C)
    (app (numericalProjectionTerm true) E)) (app (numericalProjectionTerm false) E)

def numericalInputCertificate := lam 40 (numericalInputCertificateBody (var 40))

def numericalInputCertificateValue (z : ℕ) : ℕ :=
  if Term.checkInputCertificate (Term.decodeAnswerTable z.unpair.1)
    (Term.decode z.unpair.2.unpair.2.unpair.1) (Term.decode z.unpair.2.unpair.2.unpair.2)
    (Term.decodeCertificate z.unpair.2.unpair.1) then 1 else 0

theorem numericalInputCertificate_computes :
    NumericalComputes numericalInputCertificate numericalInputCertificateValue := by
  have hf (b : Bool) : (numericalProjectionTerm b).fv = ∅ := numericalProjectionTerm_closed b
  constructor
  · unfold numericalInputCertificate numericalInputCertificateBody Closed
    simp only [fv_lam,fv_app,fv_var,(show inputCertificateTerm.fv = ∅ from inputCertificateTerm_closed),hf,Finset.empty_union,Finset.union_self]
    simp
  · intro z
    have he : (numericalInputCertificateBody (var 40)).subst 40 (numeral z) =
        numericalInputCertificateBody (numeral z) := by
      simp [numericalInputCertificateBody,subst_app,subst_var,
        subst_closed _ _ _ inputCertificateTerm_closed,
        subst_closed _ _ _ (numericalProjectionTerm_closed true),
        subst_closed _ _ _ (numericalProjectionTerm_closed false)]
    have hs : Beta (app numericalInputCertificate (numeral z))
        (numericalInputCertificateBody (numeral z)) := by
      rw [← he]; exact Beta.contract 40 _ _
    apply (Relation.ReflTransGen.single hs).trans
    have ht := numericalProjectionTerm_apply true z
    have hr := numericalProjectionTerm_apply false z
    have hc := (beta_steps_app_right (numericalProjectionTerm true) hr).trans
      (numericalProjectionTerm_apply true z.unpair.2)
    have hp := (beta_steps_app_right (numericalProjectionTerm false) hr).trans
      (numericalProjectionTerm_apply false z.unpair.2)
    have hm := (beta_steps_app_right (numericalProjectionTerm true) hp).trans
      (numericalProjectionTerm_apply true z.unpair.2.unpair.2)
    have hn := (beta_steps_app_right (numericalProjectionTerm false) hp).trans
      (numericalProjectionTerm_apply false z.unpair.2.unpair.2)
    exact (beta_steps_app (beta_steps_app (beta_steps_app
      (beta_steps_app_right inputCertificateTerm ht) hc) hm) hn).trans
      (inputCertificateTerm_apply _ _ _ _)

/-- Input: `pair prefixCode (pair tableCode (pair certificateCode (pair source target)))`. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $B,D$ and a reduction certificate $\gamma$, encode the whole input as
    $$z:=\NatPair{\LambdaListCode{s}}{
     \NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{
     \NatPair{\LambdaSyntaxCode{B}}{\LambdaSyntaxCode{D}}}}}.$$
    Define $\LambdaPrefixCertificate$ by projecting these five components, multiplying the result of
    $\LambdaTermName{tableSupport}$ by the result of
    the finite-table certificate checker applied to $\theta, \gamma,B,D$, and abstracting the input variable.
    Composition, numerical
    projections and multiplication give a fixed closed term.
-/
def prefixCertificateProgram := mulNumerical
  (numericalCompose prefixAnswerProgram
    (pairNumerical (numericalProjectionTerm true) (firstOutput (numericalProjectionTerm false))))
  (numericalCompose numericalInputCertificate (numericalProjectionTerm false))

def prefixCertificateValue (z : ℕ) :=
  prefixAnswerValue (Nat.pair z.unpair.1 z.unpair.2.unpair.1) *
    numericalInputCertificateValue z.unpair.2

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact finite-prefix certificate test
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    List length, indexing, comparisons and the finite-table certificate checker are total on all codes. Their zero-or-one
    product therefore has exactly the stated acceptance condition. If $p$ extends $s$, each supported answer is also the
    corresponding digit of $p$. Soundness of the certificate checker gives the displayed reduction on every such $p$. For
    the converse, take a finite answer table and certificate for the given reduction. Choose a prefix length greater than
    every address in the table; length zero suffices for an empty table. Each table entry then lies within the prefix and
    has the correct value, so the product and the certificate check both return one.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $B,D$ and a reduction certificate $\gamma$, encode the whole input as
    $$z:=\NatPair{\LambdaListCode{s}}{
     \NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{
     \NatPair{\LambdaSyntaxCode{B}}{\LambdaSyntaxCode{D}}}}}.$$
    Define $\LambdaPrefixCertificate$ by projecting these five components, multiplying the result of
    $\LambdaTermName{tableSupport}$ by the result of
    the finite-table certificate checker applied to $\theta, \gamma,B,D$, and abstracting the input variable.
    Composition, numerical
    projections and multiplication give a fixed closed term.
-/
theorem prefixCertificateProgram_computes :
    NumericalComputes prefixCertificateProgram prefixCertificateValue := by
  exact (prefixAnswerProgram_computes.comp
    ((projection_computes true).pair (projection_computes false).first)).mul
      (numericalInputCertificate_computes.comp (projection_computes false))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact finite-prefix certificate test
-/
theorem prefixCertificateValue_success (z : ℕ) :
    prefixCertificateValue z ≠ 0 ↔
      PrefixAnswersAgree (NatListCode.decode z.unpair.1) (Term.decodeAnswerTable z.unpair.2.unpair.1) ∧
      Term.checkInputCertificate (Term.decodeAnswerTable z.unpair.2.unpair.1)
        (Term.decode z.unpair.2.unpair.2.unpair.2.unpair.1)
        (Term.decode z.unpair.2.unpair.2.unpair.2.unpair.2)
        (Term.decodeCertificate z.unpair.2.unpair.2.unpair.1) = true := by
  simp [prefixCertificateValue,prefixAnswerValue_success,
    numericalInputCertificateValue,Nat.unpair_pair,and_comm]

theorem prefixCertificateValue_zero_or_one (z : ℕ) :
    prefixCertificateValue z = 0 ∨ prefixCertificateValue z = 1 := by
  unfold prefixCertificateValue numericalInputCertificateValue
  rcases prefixAnswerValue_zero_or_one (Nat.pair z.unpair.1 z.unpair.2.unpair.1) with h | h <;>
    simp only [h] <;> split_ifs <;> simp

/-- A successful table remains valid on every infinite extension of the prefix. -/
theorem PrefixAnswersAgree.extension {s : List ℕ} {t : Term.AnswerTable}
    (h : PrefixAnswersAgree s t) {p : ℕ → ℕ} (hp : p ∈ cyl s) : Term.AnswersAgree p t := by
  intro i v hv
  obtain ⟨hi,he⟩ := h (i,v) hv
  have hs := seqPrefix_eq_of_mem_cyl hp
  have hg := congrArg (fun l : List ℕ => l.getD i 0) hs
  simp [seqPrefix,hi] at hg
  exact hg.trans (by simpa [List.getD,hi] using he)

theorem answerBound_mem {t : Term.AnswerTable} {a : ℕ × ℕ} (ha : a ∈ t) :
    a.1 < Term.answerBound t := by
  induction t with
  | nil => simp at ha
  | cons b t ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih ha) (le_max_right _ _)

/-- Any finite table agreeing with an input fits inside a finite prefix. -/
theorem prefixAnswersAgree_seqPrefix {p : ℕ → ℕ} {t : Term.AnswerTable}
    (h : Term.AnswersAgree p t) : PrefixAnswersAgree (seqPrefix p (Term.answerBound t)) t := by
  intro a ha
  have hi := answerBound_mem ha
  refine ⟨by simpa using hi, ?_⟩
  simpa [seqPrefix,hi] using h a.1 a.2 ha

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact finite-prefix certificate test
-/
theorem prefixCertificateValue_sound {z : ℕ} (hz : prefixCertificateValue z ≠ 0)
    {p : ℕ → ℕ} (hp : p ∈ cyl (NatListCode.decode z.unpair.1)) :
    Relation.ReflTransGen (OracleStep p)
      (mk (Term.decode z.unpair.2.unpair.2.unpair.2.unpair.1))
      (mk (Term.decode z.unpair.2.unpair.2.unpair.2.unpair.2)) := by
  obtain ⟨ha,hc⟩ := (prefixCertificateValue_success z).mp hz
  exact Term.checkInputCertificate_sound (ha.extension hp) hc

/-- Every finite input computation has a certificate accepted on some prefix. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact finite-prefix certificate test
-/
theorem prefixCertificateValue_complete {p : ℕ → ℕ} {M N : Term}
    (h : Relation.ReflTransGen (OracleStep p) (mk M) (mk N)) :
    ∃ k t c, prefixCertificateValue
      (Nat.pair (NatListCode.encode (seqPrefix p k))
        (Nat.pair t (Nat.pair c (Nat.pair M.code N.code)))) ≠ 0 := by
  obtain ⟨t,ht,cs,hcs⟩ := (Term.oracle_steps_iff_certificate p M N).mp h
  refine ⟨Term.answerBound t,Term.answerTableCode t,Term.certificateCode cs,?_⟩
  apply (prefixCertificateValue_success _).mpr
  simpa only [Nat.unpair_pair,NatListCode.decode_encode,Term.decode_answerTableCode,
    Term.decode_certificateCode,Term.decode_code] using ⟨prefixAnswersAgree_seqPrefix ht,hcs⟩

end PolishSpaceBook.NamedLambda.AlphaTerm
