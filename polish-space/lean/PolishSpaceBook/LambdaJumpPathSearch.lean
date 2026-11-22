module

public import PolishSpaceBook.LambdaJumpAccessors

@[expose] public section

/-! # Searching finite jump paths and reading a computable family of rows

Every trial validates a finite list, without testing notation validity.
When a computable family lies below one notation, numerical search is total
on that family and supplies a single joint row reader.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
open LambdaRelative
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

noncomputable def pathStateStep (r z : ℕ) : ℕ := by
  classical
  exact Nat.pair (if r.unpair.1 = 1 ∧ z.unpair.2.unpair.1 = r.unpair.2 ∧ edgeCertificate z
    then 1 else 0) z.unpair.1

noncomputable def pathState (b : ℕ) (s : List ℕ) : ℕ :=
  s.foldl pathStateStep (Nat.pair 1 b)

theorem AccessPath.state {b a : ℕ} {s : List ℕ} (h : AccessPath b a s) :
    pathState b s = Nat.pair 1 a := by
  induction h with
  | nil => rfl
  | @snoc a c s z h hz ih =>
    simp only [pathState,List.foldl_append,List.foldl_cons,List.foldl_nil] at *
    rw [ih]
    simp [pathStateStep,Nat.unpair_pair,hz]

theorem pathState_sound (b : ℕ) (s : List ℕ) :
    (pathState b s).unpair.1 = 1 → AccessPath b (pathState b s).unpair.2 s := by
  classical
  induction s using List.reverseRecOn with
  | nil => simp only [pathState,List.foldl_nil,Nat.unpair_pair]; exact fun _ => .nil
  | append_singleton s z ih =>
    have hstep : pathState b (s ++ [z]) = pathStateStep (pathState b s) z := by
      simp only [pathState,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [hstep]
    simp only [pathStateStep,Nat.unpair_pair,ite_eq_left_iff,zero_ne_one,imp_false,not_not]
    intro hh
    have hc := ih hh.1
    have he : Nat.pair z.unpair.1 (Nat.pair z.unpair.2.unpair.1 z.unpair.2.unpair.2) = z := by
      simp only [Nat.pair_unpair]
    rw [← hh.2.1] at hc
    have hp := AccessPath.snoc (c := z.unpair.1) (z := z.unpair.2.unpair.2) hc
      (by simpa only [he] using hh.2.2)
    simpa only [he] using hp

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We must also find the paths uniformly. Scan a candidate list starting with state $\NatPair{1}{b}$.
    The state consists of an acceptance bit and the current endpoint. On input $w=\NatPair{r}{z}$,
    the projections of $r$ give the acceptance bit and the current endpoint. Expand
    $$\begin{aligned}
    \LambdaTermName{acceptStep}(w)&:=\LambdaMul\,
     \bigl(\LambdaMul\,(\LambdaEqual\,(\LambdaNumericProjection{1}(\LambdaNumericProjection{1}w))\,\ChurchNumeral{1})\\
    & \qquad \qquad ( \LambdaEqual\,( \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{2}w)))\,( \LambdaNumericProjection{2}( \LambdaNumericProjection{1}w))) \bigr)\,(
    \LambdaTermName{cert}( \LambdaNumericProjection{2}w)),\\
    \LambdaTermName{pathStep}&:= \lambdaab{w}{ \LambdaNumericPair\, \LambdaTermName{acceptStep}(w)\,(
    \LambdaNumericProjection{1}( \LambdaNumericProjection{2}w))}.
    \end{aligned}$$
    A rejected edge or a mismatched lower endpoint sets the bit to zero, and it stays zero thereafter.
    The numerical test $\Theta$ on input $\NatPair{\NatPair{b}{a}}{c}$ compares
    $\LambdaTermName{fold}_{ \LambdaTermName{pathStep}} \ChurchNumeral{ \NatPair{c}{ \NatPair{1}{b}}}$ with
    $\ChurchNumeral{ \NatPair{1}{a}}$ using numerical equality.
    It returns one exactly when the decoded list is an accepted path from $b$ to $a$. The empty path is accepted
    exactly when $b=a$. Projections, pairing, the list accumulator, and equality give a closed total term for $\Theta$.
-/
theorem pathState_iff (b a : ℕ) (s : List ℕ) :
    pathState b s = Nat.pair 1 a ↔ AccessPath b a s := by
  constructor
  · intro h
    have hp := pathState_sound b s (by simp only [h,Nat.unpair_pair])
    simpa only [h,Nat.unpair_pair] using hp
  · exact AccessPath.state

/-- The trial input is ((b,a),c), where c codes an upward path. -/
noncomputable def pathTest (z : ℕ) : ℕ := by
  classical
  exact if pathState z.unpair.1.unpair.1 (NatListCode.decode z.unpair.2) =
    Nat.pair 1 z.unpair.1.unpair.2 then 1 else 0

private theorem exists_edgeBit_program :
    ∃ C : AlphaTerm, NumericalComputes C (fun z => if edgeCertificate z then 1 else 0) := by
  classical
  obtain ⟨C,hC⟩ := edgeCertificate_decidable (fun _ => 0)
  have h := hC.toPure (numericalConstant_computes 0)
  refine ⟨app C (numericalConstant 0),h.1,fun z => ?_⟩
  dsimp only
  split_ifs with hz
  · exact (h.2 z).1 hz
  · exact (h.2 z).2 hz

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We must also find the paths uniformly. Scan a candidate list starting with state $\NatPair{1}{b}$.
    The state consists of an acceptance bit and the current endpoint. On input $w=\NatPair{r}{z}$,
    the projections of $r$ give the acceptance bit and the current endpoint. Expand
    $$\begin{aligned}
    \LambdaTermName{acceptStep}(w)&:=\LambdaMul\,
     \bigl(\LambdaMul\,(\LambdaEqual\,(\LambdaNumericProjection{1}(\LambdaNumericProjection{1}w))\,\ChurchNumeral{1})\\
    & \qquad \qquad ( \LambdaEqual\,( \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{2}w)))\,( \LambdaNumericProjection{2}( \LambdaNumericProjection{1}w))) \bigr)\,(
    \LambdaTermName{cert}( \LambdaNumericProjection{2}w)),\\
    \LambdaTermName{pathStep}&:= \lambdaab{w}{ \LambdaNumericPair\, \LambdaTermName{acceptStep}(w)\,(
    \LambdaNumericProjection{1}( \LambdaNumericProjection{2}w))}.
    \end{aligned}$$
    A rejected edge or a mismatched lower endpoint sets the bit to zero, and it stays zero thereafter.
    The numerical test $\Theta$ on input $\NatPair{\NatPair{b}{a}}{c}$ compares
    $\LambdaTermName{fold}_{ \LambdaTermName{pathStep}} \ChurchNumeral{ \NatPair{c}{ \NatPair{1}{b}}}$ with
    $\ChurchNumeral{ \NatPair{1}{a}}$ using numerical equality.
    It returns one exactly when the decoded list is an accepted path from $b$ to $a$. The empty path is accepted
    exactly when $b=a$. Projections, pairing, the list accumulator, and equality give a closed total term for $\Theta$.
-/
private theorem exists_pathStateStep_program :
    ∃ H : AlphaTerm, NumericalComputes H (fun z => pathStateStep z.unpair.1 z.unpair.2) := by
  classical
  obtain ⟨C,hC⟩ := exists_edgeBit_program
  have hr := projection_computes true
  have hz := projection_computes false
  have hflag := (projection_computes true).comp hr
  have hnode := (projection_computes false).comp hr
  have hchild := (projection_computes true).comp ((projection_computes false).comp hz)
  have hparent := (projection_computes true).comp hz
  have hbit := hflag.combine (numericalConstant_computes 1) equalityTerm_closed
    (fun a b => if a = b then 1 else 0) equalityTerm_apply
  have heq := hchild.combine hnode equalityTerm_closed
    (fun a b => if a = b then 1 else 0) equalityTerm_apply
  have h := ((hbit.mul heq).mul (hC.comp hz)).pair hparent
  refine ⟨_,h.1,fun z => ?_⟩
  by_cases hb : z.unpair.1.unpair.1 = 1 <;>
    by_cases he : z.unpair.2.unpair.2.unpair.1 = z.unpair.1.unpair.2 <;>
    by_cases hc : edgeCertificate z.unpair.2 <;>
    simpa [pathStateStep,hb,he,hc] using h.2 z

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We must also find the paths uniformly. Scan a candidate list starting with state $\NatPair{1}{b}$.
    The state consists of an acceptance bit and the current endpoint. On input $w=\NatPair{r}{z}$,
    the projections of $r$ give the acceptance bit and the current endpoint. Expand
    $$\begin{aligned}
    \LambdaTermName{acceptStep}(w)&:=\LambdaMul\,
     \bigl(\LambdaMul\,(\LambdaEqual\,(\LambdaNumericProjection{1}(\LambdaNumericProjection{1}w))\,\ChurchNumeral{1})\\
    & \qquad \qquad ( \LambdaEqual\,( \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{2}w)))\,( \LambdaNumericProjection{2}( \LambdaNumericProjection{1}w))) \bigr)\,(
    \LambdaTermName{cert}( \LambdaNumericProjection{2}w)),\\
    \LambdaTermName{pathStep}&:= \lambdaab{w}{ \LambdaNumericPair\, \LambdaTermName{acceptStep}(w)\,(
    \LambdaNumericProjection{1}( \LambdaNumericProjection{2}w))}.
    \end{aligned}$$
    A rejected edge or a mismatched lower endpoint sets the bit to zero, and it stays zero thereafter.
    The numerical test $\Theta$ on input $\NatPair{\NatPair{b}{a}}{c}$ compares
    $\LambdaTermName{fold}_{ \LambdaTermName{pathStep}} \ChurchNumeral{ \NatPair{c}{ \NatPair{1}{b}}}$ with
    $\ChurchNumeral{ \NatPair{1}{a}}$ using numerical equality.
    It returns one exactly when the decoded list is an accepted path from $b$ to $a$. The empty path is accepted
    exactly when $b=a$. Projections, pairing, the list accumulator, and equality give a closed total term for $\Theta$.
-/
theorem exists_pathTest_program : ∃ C : AlphaTerm, NumericalComputes C pathTest := by
  classical
  obtain ⟨H,hH⟩ := exists_pathStateStep_program
  have hf := addressFoldProgram_computes (g := pathStateStep) hH
  have hleft := (projection_computes true).comp (projection_computes true)
  have hright := (projection_computes false).comp (projection_computes true)
  have hin := (projection_computes false).pair ((numericalConstant_computes 1).pair hleft)
  have hs := hf.comp hin
  have hout := (numericalConstant_computes 1).pair hright
  have h := hs.combine hout equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply
  refine ⟨_,h.1,fun z => ?_⟩
  by_cases he : pathState z.unpair.1.unpair.1 (NatListCode.decode z.unpair.2) =
      Nat.pair 1 z.unpair.1.unpair.2
  all_goals
    simp only [pathState] at he
    simpa [pathTest,pathState,he] using h.2 z

/-- The search is total for a computable family known to have paths to one target. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose a closed numerical term $\LambdaTermName{baseProg}$ computes $g$ and every $g(n)$ has a finite accepted
    path to a fixed $a$.
    Define, with fresh binders,
    $$\begin{aligned}
    \LambdaTermName{pathTrial}&:=\lambdaab{w}{\Theta(\LambdaNumericPair\,
    ( \LambdaNumericPair\,( \LambdaTermName{baseProg}( \LambdaNumericProjection{1}w))\, \ChurchNumeral{a})\,(
    \LambdaNumericProjection{2}w))},\\
    \LambdaTermName{reject}&:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    \LambdaTermName{findPath}&:=\lambdaab{n}{\LambdaResultSearch\,
     (\lambdaab{k}{\LambdaTermName{reject}(\LambdaTermName{pathTrial}(\LambdaNumericPair\,n\,k))})\,(\lambdaab{j}{j})},\\
    \LambdaTermName{readRow}&:= \lambdaab{o}{ \lambdaab{w}{o( \LambdaTermName{addr}( \LambdaNumericPair\,(
    \LambdaTermName{findPath}( \LambdaNumericProjection{1}w))\,( \LambdaNumericProjection{2}w)))}}.
    \end{aligned}$$
    The search $\LambdaTermName{findPath}$ returns the least accepted list code, not merely an acceptance bit.
-/
theorem computable_path_selection {G : AlphaTerm} {g : ℕ → ℕ} (hG : NumericalComputes G g)
    (a : ℕ) (hp : ∀ n, ∃ s, AccessPath (g n) a s) :
    ∃ (S : AlphaTerm) (c : ℕ → ℕ), NumericalComputes S c ∧
      ∀ n, AccessPath (g n) a (NatListCode.decode (c n)) := by
  classical
  obtain ⟨C,hC⟩ := exists_pathTest_program
  have ht := hC.comp (((hG.comp (projection_computes true)).pair (numericalConstant_computes a)).pair
    (projection_computes false))
  let test := fun z : ℕ => pathTest (Nat.pair (Nat.pair (g z.unpair.1) a) z.unpair.2)
  simp only [Bool.false_eq_true,ite_false,ite_true] at ht
  have hex (n : ℕ) : ∃ k, test (Nat.pair n k) ≠ 0 := by
    obtain ⟨s,hs⟩ := hp n
    exact ⟨NatListCode.encode s,by simp [test,pathTest,NatListCode.decode_encode,hs.state]⟩
  refine ⟨_,_,numericalSearch_computes ht hex,fun n => ?_⟩
  have h := Nat.find_spec (hex n)
  simpa only [test,pathTest,Nat.unpair_pair,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,
    not_not,pathState_iff,firstNumericalHit] using h

/-- The path search and address map are both total before querying the upper row. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: A uniform jump-row reader
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The numerical recursor theorem proves the accumulator formula by induction on the number of processed
    entries. Applied to $\LambdaTermName{pathStep}$, induction shows that the final state is $\NatPair{1}{a}$
    exactly for an accepted
    path with the prescribed endpoints: each update checks the edge and its connection to the preceding
    endpoint. Once the bit is zero it cannot return to one. This proves the specification of $\Theta$.
    Every trial of $\LambdaTermName{pathTrial}$ terminates. The assumed path has a finite code, so parameterized
    numerical search
    returns the least successful code. Thus $\LambdaTermName{findPath}$ is one total program on all $n$.

    For the address identity, induct on the path by removing its last edge. Downward closure puts the
    preceding endpoint in $D$. The single-edge identity followed by the induction hypothesis gives
    $G_a(\mathcal A(c,m))=G_{g(n)}(m)$ for every accepted code $c$ found by $\LambdaTermName{findPath}$.
    The terms computing the path and address terminate before the query in $\LambdaTermName{readRow}$, so their finite beta
    reductions followed by one input-query step give the required output. No choice of a separate reader
    for each $n$ occurs. Taking the canonical table gives the iterated-jump reader in
    §{sec:edst-hyperarithmetic-inclusion}.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Suppose a closed numerical term $\LambdaTermName{baseProg}$ computes $g$ and every $g(n)$ has a finite accepted
    path to a fixed $a$.
    Define, with fresh binders,
    $$\begin{aligned}
    \LambdaTermName{pathTrial}&:=\lambdaab{w}{\Theta(\LambdaNumericPair\,
    ( \LambdaNumericPair\,( \LambdaTermName{baseProg}( \LambdaNumericProjection{1}w))\, \ChurchNumeral{a})\,(
    \LambdaNumericProjection{2}w))},\\
    \LambdaTermName{reject}&:=\lambdaab{b}{\LambdaZeroTest\,b\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    \LambdaTermName{findPath}&:=\lambdaab{n}{\LambdaResultSearch\,
     (\lambdaab{k}{\LambdaTermName{reject}(\LambdaTermName{pathTrial}(\LambdaNumericPair\,n\,k))})\,(\lambdaab{j}{j})},\\
    \LambdaTermName{readRow}&:= \lambdaab{o}{ \lambdaab{w}{o( \LambdaTermName{addr}( \LambdaNumericPair\,(
    \LambdaTermName{findPath}( \LambdaNumericProjection{1}w))\,( \LambdaNumericProjection{2}w)))}}.
    \end{aligned}$$
    The search $\LambdaTermName{findPath}$ returns the least accepted list code, not merely an acceptance bit.
-/
theorem uniform_family_from_upper {G : AlphaTerm} {g : ℕ → ℕ} (hG : NumericalComputes G g)
    (a : ℕ) (hp : ∀ n, ∃ s, AccessPath (g n) a s) :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ (A : Set ℕ) (q : ℕ → ℕ), JumpTable A q → tableDomain q a →
      Computes (tableRow q a) P (fun z : ℕ => tableRow q (g z.unpair.1) z.unpair.2) := by
  obtain ⟨S,c,hS,hc⟩ := computable_path_selection hG a hp
  obtain ⟨F,f,hF,hf⟩ := exists_pathAddress_program
  have hin := (hS.comp (projection_computes true)).pair (projection_computes false)
  have hadd := hF.comp hin
  have hquery := hadd.uniform.query
  refine ⟨_,hquery.1,fun A q hq ha => ⟨hquery.1,fun z => ?_⟩⟩
  have h := hquery.2 (tableRow q a) z
  simpa only [Encodable.encode_nat,Nat.unpair_pair,Bool.false_eq_true,ite_false,ite_true,
    hf A q hq (g z.unpair.1) a (NatListCode.decode (c z.unpair.1)) (hc z.unpair.1) ha z.unpair.2] using h

/-- Validity remains an external hypothesis and is never tested by the reader. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Every candidate edge has a finite certificate. A finite path from $g(n)$ to $a$ therefore has a finite
    certificate list. List scanning gives a total checker for such paths with prescribed endpoints.
    Search all list codes in numerical order. The precedence hypothesis ensures that the search terminates
    for every $n$, so one closed numerical term supplies the path code from $n$.

    For a successor edge, use the fixed index map $f$ that recovers a bit from its jump: a query at $m$ in
    the lower row becomes a query at $f(m)$ in the upper row. For a certified limit edge at component $i$,
    it becomes a query at $\NatPair{i}{m}$. Process the path upward, composing these address changes by
    finite numerical recursion. The table equations show at each step that the queried bit is unchanged.
    All rows on the path lie in the domain of the canonical table. Its row identities therefore give the
    required output after one query to the supplied upper row. The same program handles every $n,m$,
    which proves the assertion about the effective join. §{sec:lambda-certified-descent} gives the checker,
    search, and address-transforming terms. None of them tests whether a notation is valid.
    \end{proof}
-/
theorem uniform_iteratedJump_family {G : AlphaTerm} {g : ℕ → ℕ} (hG : NumericalComputes G g)
    (a : ℕ) (ha : Valid a) (hg : ∀ n, RawPrecedes (g n) a) :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ A : Set ℕ,
      Computes (characteristic (iteratedJump A a ha)) P
        (fun z : ℕ => characteristic (iteratedJump A (g z.unpair.1) (ha.down (hg z.unpair.1))) z.unpair.2) := by
  obtain ⟨P,hP,h⟩ := uniform_family_from_upper hG a (fun n => AccessPath.exists_of_raw (hg n))
  refine ⟨P,hP,fun A => ?_⟩
  have hh := h A (canonicalJumpTable A) (canonicalJumpTable_spec A) ((canonicalJumpTable_domain A a).mpr ha)
  have hr : tableRow (canonicalJumpTable A) a = characteristic (iteratedJump A a ha) :=
    funext (canonicalJumpTable_row A a ha)
  rw [hr] at hh
  simpa only [canonicalJumpTable_row A _ (ha.down (hg _))] using hh

/-- One upper jump computes the entire effective join, not only each fixed row. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Uniform access to lower jumps
-/
theorem uniform_iteratedJump_join {G : AlphaTerm} {g : ℕ → ℕ} (hG : NumericalComputes G g)
    (a : ℕ) (ha : Valid a) (hg : ∀ n, RawPrecedes (g n) a) :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ A : Set ℕ,
      Computes (characteristic (iteratedJump A a ha)) P
        (characteristic (effectiveJoin (fun n => iteratedJump A (g n) (ha.down (hg n))))) := by
  classical
  obtain ⟨P,hP,h⟩ := uniform_iteratedJump_family hG a ha hg
  refine ⟨P,hP,fun A => ?_⟩
  have he : characteristic (effectiveJoin (fun n => iteratedJump A (g n) (ha.down (hg n)))) =
      (fun z : ℕ => characteristic (iteratedJump A (g z.unpair.1) (ha.down (hg z.unpair.1))) z.unpair.2) := by
    rfl
  rw [he]
  exact h A

end KleeneNotation
end PolishSpaceBook
