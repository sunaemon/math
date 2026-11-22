module

public import PolishSpaceBook.LambdaFiniteSubcovers
public import PolishSpaceBook.LambdaListTabulation

@[expose] public section

/-! # Exact coverage semidecision for uniformly enumerated families

A single numerical parameter selects a total ball enumeration. Searching pairs
of prefix length and net precision gives exactly the parameters whose union covers.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set
universe u
variable {X : Type u} [MetricSpace X]

def coverFamilyPrefixProgram (F : AlphaTerm) : AlphaTerm :=
  listTabulateTerm (numericalCompose predecessorTerm F)

theorem coverFamilyPrefixProgram_computes {F : AlphaTerm} {f : ℕ → ℕ}
    (hf : NumericalComputes F f) : NumericalComputes (coverFamilyPrefixProgram F)
      (fun z => enumeratedCoverPrefix (fun i => f (Nat.pair z.unpair.1 i)) z.unpair.2) := by
  have h := listTabulate_computes (predecessor_computes.comp hf)
  exact h

def coverFamilyStageBit {q : ℕ → X} (A : RationalMetricApproximation q)
    (E : ℕ → List ℕ) (f : ℕ → ℕ) (z : ℕ) : ℕ :=
  subcoverStageBit A E (fun i => f (Nat.pair z.unpair.1 i)) z.unpair.2

def coverFamilyStageProgram (M N F : AlphaTerm) : AlphaTerm :=
  numericalCompose (netCoverStageProgram M N)
    (pairNumerical
      (numericalCompose (coverFamilyPrefixProgram F)
        (pairNumerical (numericalProjectionTerm true)
          (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))

theorem coverFamilyStageProgram_computes {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) :
    NumericalComputes (coverFamilyStageProgram A.program E.program F)
      (coverFamilyStageBit A.toRationalMetricApproximation E.centers f) := by
  have hp := (coverFamilyPrefixProgram_computes hf).comp ((projection_computes true).pair
    ((projection_computes true).comp (projection_computes false)))
  have hn := (projection_computes false).comp (projection_computes false)
  have h := (netCoverStageProgram_computes A E).comp (hp.pair hn)
  refine ⟨h.1,fun z => ?_⟩
  simpa only [coverFamilyStageProgram,coverFamilyStageBit,subcoverStageBit,Nat.unpair_pair,
    Bool.false_eq_true,ite_false,ite_true] using h.2 z

def coverFamilySemidecider (M N F : AlphaTerm) : AlphaTerm :=
  numericalSearch (coverFamilyStageProgram M N F)

theorem coverFamilySemidecider_closed {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) :
    (coverFamilySemidecider A.program E.program F).Closed :=
  numericalSearch_closed (coverFamilyStageProgram_computes A E hf).1

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For each $b$, apply the prefix construction to $p_b(i):=e(b,i)$. Let $c(b,m)$ be the code of the first $m$
    converted ball codes. Using the notation $\pi_i:=\LambdaNumericProjection{i}$ and the finite-net test $T$, define
    $$\begin{aligned}
    L_F&:=\LambdaListTabulate{\lambdaab{z}{\LambdaPred(Fz)}},\\
    D&:=\lambdaab{z}{T(\LambdaNumericPair\,
     (L_F(\LambdaNumericPair\,(\pi_1z)\,(\pi_1(\pi_2z))))\,(\pi_2(\pi_2z)))},\\
    G_b&:=\lambdaab{k}{Z(D(\LambdaNumericPair\,b\,k))},\\
    S_F&:=\lambdaab{b}{\LambdaResultSearch\,G_b\,I}.
    \end{aligned}$$
    Here $Z$ and $I$ are the bit negation and identity terms used above. The tabulator returns $c(b,m)$ from
    $\NatPair{b}{m}$. For $k=\NatPair{m}{n}$, the test $D\ChurchNumeral{\NatPair{b}{k}}$ returns a nonzero numeral
    exactly when that prefix passes the finite-net test at precision $n$. These are total rational tests.
    If the enumerated balls cover $K$, compactness gives a covering prefix, and the finite-net lemma gives a successful
    precision. Conversely, every successful test certifies a covering prefix. The exact numerical-search theorem now
    shows that $S_F\ChurchNumeral{b}$ has a numeral output exactly for covering parameters; if there is no successful
    pair, no reduction order produces a numeral. Expanding $G_b$ binds the parameter, so $S_F$ is closed.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Uniform coverage semidecision
-/
theorem coverFamilySemidecider_spec [CompactSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)
    (E : LambdaFiniteNets q) {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) (b : ℕ) :
    (∃ m, Relation.ReflTransGen Beta
      (app (coverFamilySemidecider A.program E.program F) (numeral b)) (numeral m)) ↔
        IsEnumeratedCover q (fun i => f (Nat.pair b i)) := by
  rw [coverFamilySemidecider,numericalSearch_domain (coverFamilyStageProgram_computes A E hf)]
  simp only [coverFamilyStageBit,Nat.unpair_pair]
  constructor
  · rintro ⟨k,hk⟩ x
    obtain ⟨i,_,hi⟩ := subcoverStageBit_sound A.toRationalMetricApproximation E.covers _ hk x
    exact ⟨i,hi⟩
  · exact subcoverStageBit_exists A.toRationalMetricApproximation E.centers

end PolishSpaceBook
