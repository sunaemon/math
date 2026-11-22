module

public import PolishSpaceBook.LambdaJumpTables

@[expose] public section

/-! # Finite certificates give uniform access to lower jump rows

A successor edge redirects a query through one fixed recovery index map;
a limit edge prefixes its certified component index. A numerical list fold
composes these redirects before the single query to the supplied upper row.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
open LambdaRelative
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

/-- Scan a coded list from left to right with a numerical accumulator. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For any closed total numerical term $H$ receiving $\NatPair{r}{z}$, define a list accumulator by
    $$\begin{aligned}
    \LambdaTermName{foldBase}&:=\lambdaab{w}{\LambdaNumericProjection{2}w},\\
    \LambdaTermName{foldStep}_{H}&:=\lambdaab{w}{\lambdaab{j}{\lambdaab{r}{
     H(\LambdaNumericPair\,r\,(\LambdaListGet\,(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,j)))}}},\\
    \LambdaTermName{fold}_{H}&:= \lambdaab{w}{ \LambdaParamRec{ \LambdaTermName{foldBase}}{
    \LambdaTermName{foldStep}_{H}}\,w\,( \LambdaListLength\,( \LambdaNumericProjection{1}w))}.
    \end{aligned}$$
    Let $\mathbf{z}$ be a word of length $k$, with $j$-th entry $z_j$ for $j<k$.
    On input $\NatPair{\LambdaListCode{\mathbf{z}}}{m}$, this starts with $r_0=m$ and applies
    $H$ successively to $\NatPair{r_j}{z_j}$ for $j<k$. The empty list returns $m$.
    Numerical currying and uncurrying give the same recursion on paired inputs.
    With $H:= \lambdaab{w}{ \LambdaTermName{edgeAddr}( \LambdaNumericPair\,( \LambdaNumericProjection{2}w)\,(
    \LambdaNumericProjection{1}w))}$, let $\LambdaTermName{addr}:= \LambdaTermName{fold}_{H}$.
    Let $\mathcal A(c,m)$ be the final address obtained by decoding $c$ as a finite word and starting at $m$,
    then replacing the current address $r$ by $\tau(z_j,r)$ at each entry $z_j$.
    The term $\LambdaTermName{addr}$ computes $\mathcal A(c,m)$ on the paired numerical input $\NatPair{c}{m}$.
-/
def addressFoldProgram (H : AlphaTerm) : AlphaTerm :=
  numericalCompose
    (numericalRecursion (numericalProjectionTerm false)
      (numericalCompose H (pairNumerical
        (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
        (numericalCompose listGetTerm (pairNumerical
          (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))
          (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)))))))
    (pairNumerical numericalIdentity (numericalCompose listLengthTerm (numericalProjectionTerm true)))

private theorem fold_prefix (g : ℕ → ℕ → ℕ) (s : List ℕ) (m : ℕ) :
    ∀ k ≤ s.length, primitiveRec m (fun i r => g r (s.getD i 0)) k = (s.take k).foldl g m := by
  intro k hk
  induction k with
  | zero => simp [primitiveRec]
  | succ k ih =>
    have hkl : k < s.length := by omega
    rw [primitiveRec,ih (by omega),List.take_succ_eq_append_getElem hkl]
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hkl,Option.getD_some]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For any closed total numerical term $H$ receiving $\NatPair{r}{z}$, define a list accumulator by
    $$\begin{aligned}
    \LambdaTermName{foldBase}&:=\lambdaab{w}{\LambdaNumericProjection{2}w},\\
    \LambdaTermName{foldStep}_{H}&:=\lambdaab{w}{\lambdaab{j}{\lambdaab{r}{
     H(\LambdaNumericPair\,r\,(\LambdaListGet\,(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,j)))}}},\\
    \LambdaTermName{fold}_{H}&:= \lambdaab{w}{ \LambdaParamRec{ \LambdaTermName{foldBase}}{
    \LambdaTermName{foldStep}_{H}}\,w\,( \LambdaListLength\,( \LambdaNumericProjection{1}w))}.
    \end{aligned}$$
    Let $\mathbf{z}$ be a word of length $k$, with $j$-th entry $z_j$ for $j<k$.
    On input $\NatPair{\LambdaListCode{\mathbf{z}}}{m}$, this starts with $r_0=m$ and applies
    $H$ successively to $\NatPair{r_j}{z_j}$ for $j<k$. The empty list returns $m$.
    Numerical currying and uncurrying give the same recursion on paired inputs.
    With $H:= \lambdaab{w}{ \LambdaTermName{edgeAddr}( \LambdaNumericPair\,( \LambdaNumericProjection{2}w)\,(
    \LambdaNumericProjection{1}w))}$, let $\LambdaTermName{addr}:= \LambdaTermName{fold}_{H}$.
    Let $\mathcal A(c,m)$ be the final address obtained by decoding $c$ as a finite word and starting at $m$,
    then replacing the current address $r$ by $\tau(z_j,r)$ at each entry $z_j$.
    The term $\LambdaTermName{addr}$ computes $\mathcal A(c,m)$ on the paired numerical input $\NatPair{c}{m}$.
-/
theorem addressFoldProgram_computes {H : AlphaTerm} {g : ℕ → ℕ → ℕ}
    (hH : NumericalComputes H (fun z => g z.unpair.1 z.unpair.2)) :
    NumericalComputes (addressFoldProgram H)
      (fun z => (NatListCode.decode z.unpair.1).foldl g z.unpair.2) := by
  have hz := projection_computes true
  have hk := (projection_computes true).comp (projection_computes false)
  have hr := (projection_computes false).comp (projection_computes false)
  have hl := (projection_computes true).comp hz
  have he := listGet_computes.comp (hl.pair hk)
  have hs := hH.comp (hr.pair he)
  have hf := (numericalRecursion_computes (projection_computes false) hs).comp
    (numericalIdentity_computes.pair (listLength_computes.comp hz))
  have eq (z : ℕ) := fold_prefix g (NatListCode.decode z.unpair.1) z.unpair.2
    (NatListCode.decode z.unpair.1).length (le_refl _)
  simp only [List.take_length] at eq
  simpa only [addressFoldProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,id_eq,eq] using hf

/-- An edge certificate z and an address m are supplied as the pair (z,m). -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $G_b$ be the rows of a jump witness table with domain $D$. Use the closed certificate decider
    $\LambdaTermName{cert}$
    from §{sec:lambda-certified-descent}. A certificate has numerical code
    $$z=\NatPair{p}{\NatPair{b}{\NatPair{e}{\NatPair{i}{s}}}}.$$
    Write $\chi(z),\delta(z),\zeta(z)$ for the corresponding numerical projections. An accepted certificate describes
    an edge from $\delta(z)$ up to $\chi(z)$. Fix the pure numerical program $F$ and its function $f$ from
    §{sec:lambda-relative-jump}, so that $f(m)\in K^\varepsilon$ exactly when $\varepsilon(m)\ne0$.
    Define the address change
    $$\tau(z,m):=\begin{cases}
    f(m)&\chi(z)=2^{\delta(z)},\\
    \NatPair{\zeta(z)}{m}&\chi(z)\ne2^{\delta(z)}.
    \end{cases}$$
    It is total even on rejected certificates. On an accepted certificate whose upper endpoint belongs to $D$,
    $$G_{\chi(z)}(\tau(z,m))=G_{\delta(z)}(m).$$
    For the successor case, the jump equation and the bit-valued rows prove this identity. For the limit case,
    the finite output certificate and the join equation prove it. The two numerical forms are disjoint.
-/
def edgeAddress (f : ℕ → ℕ) (z : ℕ) : ℕ :=
  if z.unpair.1.unpair.1 = successorCode z.unpair.1.unpair.2.unpair.1
  then f z.unpair.2
  else Nat.pair z.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1 z.unpair.2

def addressParent := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true)
def addressChild := numericalCompose (numericalProjectionTerm true)
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm true))
def addressComponent := numericalCompose (numericalProjectionTerm true)
  (numericalCompose (numericalProjectionTerm false)
    (numericalCompose (numericalProjectionTerm false)
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm true))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here are explicit terms for composing these changes. Let
    $\LambdaTermName{powTwo}$ be the closed term computing $b\mapsto2^b$ used in the certificate decider. Inside a term with
    argument $w$, abbreviate
    $$\begin{aligned}
    \LambdaTermName{upperTarget}(w)&:=\LambdaTermName{parent}(\LambdaNumericProjection{1}w),\\
    \LambdaTermName{successorTarget}(w)&:=\LambdaTermName{powTwo}(\LambdaTermName{child}(\LambdaNumericProjection{1}w)),\\
    \LambdaTermName{jumpInput}(w)&:=F(\LambdaNumericProjection{2}w),\\
    \LambdaTermName{joinInput}(w)&:=\LambdaNumericPair\,
     (\LambdaTermName{position}(\LambdaNumericProjection{1}w))\,(\LambdaNumericProjection{2}w),\\
    \LambdaTermName{edgeAddr}&:= \lambdaab{w}{ \LambdaLeCase{ \LambdaTermName{upperTarget}(w)}{
    \LambdaTermName{successorTarget}(w)}{
    \LambdaLeCase{ \LambdaTermName{successorTarget}(w)}{ \LambdaTermName{upperTarget}(w)}{
    \LambdaTermName{jumpInput}(w)}{ \LambdaTermName{joinInput}(w)}}{ \LambdaTermName{joinInput}(w)}}.
    \end{aligned}$$
    The field expressions stand for compositions of numerical projection terms. Expand them before abstraction.
    The two comparisons in $\LambdaTermName{edgeAddr}$ test equality, so $\LambdaTermName{edgeAddr}$ computes
    $\tau(z,m)$ on input $\NatPair{z}{m}$.
-/
def edgeAddressProgram (F : AlphaTerm) : AlphaTerm :=
  numericalIfLe addressParent (numericalCompose powerTwoTerm addressChild)
    (numericalIfLe (numericalCompose powerTwoTerm addressChild) addressParent
      (numericalCompose F (numericalProjectionTerm false))
      (pairNumerical addressComponent (numericalProjectionTerm false)))
    (pairNumerical addressComponent (numericalProjectionTerm false))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here are explicit terms for composing these changes. Let
    $\LambdaTermName{powTwo}$ be the closed term computing $b\mapsto2^b$ used in the certificate decider. Inside a term with
    argument $w$, abbreviate
    $$\begin{aligned}
    \LambdaTermName{upperTarget}(w)&:=\LambdaTermName{parent}(\LambdaNumericProjection{1}w),\\
    \LambdaTermName{successorTarget}(w)&:=\LambdaTermName{powTwo}(\LambdaTermName{child}(\LambdaNumericProjection{1}w)),\\
    \LambdaTermName{jumpInput}(w)&:=F(\LambdaNumericProjection{2}w),\\
    \LambdaTermName{joinInput}(w)&:=\LambdaNumericPair\,
     (\LambdaTermName{position}(\LambdaNumericProjection{1}w))\,(\LambdaNumericProjection{2}w),\\
    \LambdaTermName{edgeAddr}&:= \lambdaab{w}{ \LambdaLeCase{ \LambdaTermName{upperTarget}(w)}{
    \LambdaTermName{successorTarget}(w)}{
    \LambdaLeCase{ \LambdaTermName{successorTarget}(w)}{ \LambdaTermName{upperTarget}(w)}{
    \LambdaTermName{jumpInput}(w)}{ \LambdaTermName{joinInput}(w)}}{ \LambdaTermName{joinInput}(w)}}.
    \end{aligned}$$
    The field expressions stand for compositions of numerical projection terms. Expand them before abstraction.
    The two comparisons in $\LambdaTermName{edgeAddr}$ test equality, so $\LambdaTermName{edgeAddr}$ computes
    $\tau(z,m)$ on input $\NatPair{z}{m}$.
-/
theorem edgeAddressProgram_computes {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) : NumericalComputes (edgeAddressProgram F) (edgeAddress f) := by
  have hp := (projection_computes true).comp (projection_computes true)
  have hb := (projection_computes true).comp
    ((projection_computes false).comp (projection_computes true))
  have hi := (projection_computes true).comp ((projection_computes false).comp
    ((projection_computes false).comp ((projection_computes false).comp (projection_computes true))))
  have hs := powerTwo_computes.comp hb
  have hm := projection_computes false
  have hpair := hi.pair hm
  have h := hp.ifLe hs (hs.ifLe hp (hF.comp hm) hpair) hpair
  convert h using 1
  · rfl
  · funext z
    simp only [Bool.false_eq_true,ite_true,ite_false]
    unfold edgeAddress successorCode
    split_ifs <;> omega

/-- Sound for every witness table, including domains containing invalid indices. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $G_b$ be the rows of a jump witness table with domain $D$. Use the closed certificate decider
    $\LambdaTermName{cert}$
    from §{sec:lambda-certified-descent}. A certificate has numerical code
    $$z=\NatPair{p}{\NatPair{b}{\NatPair{e}{\NatPair{i}{s}}}}.$$
    Write $\chi(z),\delta(z),\zeta(z)$ for the corresponding numerical projections. An accepted certificate describes
    an edge from $\delta(z)$ up to $\chi(z)$. Fix the pure numerical program $F$ and its function $f$ from
    §{sec:lambda-relative-jump}, so that $f(m)\in K^\varepsilon$ exactly when $\varepsilon(m)\ne0$.
    Define the address change
    $$\tau(z,m):=\begin{cases}
    f(m)&\chi(z)=2^{\delta(z)},\\
    \NatPair{\zeta(z)}{m}&\chi(z)\ne2^{\delta(z)}.
    \end{cases}$$
    It is total even on rejected certificates. On an accepted certificate whose upper endpoint belongs to $D$,
    $$G_{\chi(z)}(\tau(z,m))=G_{\delta(z)}(m).$$
    For the successor case, the jump equation and the bit-valued rows prove this identity. For the limit case,
    the finite output certificate and the join equation prove it. The two numerical forms are disjoint.
-/
theorem JumpTable.edge_address {A : Set ℕ} {q : ℕ → ℕ} (h : JumpTable A q)
    {f : ℕ → ℕ} (hf : ∀ ε n, f n ∈ Jump ε ↔ ε n ≠ 0)
    {z : ℕ} (hz : edgeCertificate z) (hp : tableDomain q z.unpair.1) (m : ℕ) :
    tableRow q z.unpair.1 (edgeAddress f (Nat.pair z m)) = tableRow q z.unpair.2.unpair.1 m := by
  rcases hz with ⟨hb,he⟩ | ⟨he,ht⟩
  · simp only [edgeAddress,Nat.unpair_pair,he,ite_true]
    have hs := (h.succ _ hb (he ▸ hp) (f m)).trans (hf _ m)
    rcases h.bits (successorCode z.unpair.2.unpair.1) (f m) with hp0 | hp1 <;>
      rcases h.bits z.unpair.2.unpair.1 m with hm0 | hm1 <;> simp_all
  · have hn : z.unpair.1 ≠ successorCode z.unpair.2.unpair.1 := by
      rw [he]
      exact (successorCode_ne_limitCode _ _).symm
    simp only [edgeAddress,Nat.unpair_pair]
    rw [ite_eq_right hn,he]
    exact h.limit _ _ _ _ (he ▸ hp) ht m

/-- Paths are listed upward, so addresses are transformed in list order. -/
inductive AccessPath (b : ℕ) : ℕ → List ℕ → Prop
  | nil : AccessPath b b []
  | snoc {a c : ℕ} {s : List ℕ} {z : ℕ} (h : AccessPath b a s)
      (hz : edgeCertificate (Nat.pair c (Nat.pair a z))) :
      AccessPath b c (s ++ [Nat.pair c (Nat.pair a z)])

def pathAddress (f : ℕ → ℕ) (s : List ℕ) (m : ℕ) : ℕ :=
  s.foldl (fun r z => edgeAddress f (Nat.pair z r)) m

theorem AccessPath.down {b a : ℕ} {s : List ℕ} (h : AccessPath b a s)
    {A : Set ℕ} {q : ℕ → ℕ} (hq : JumpTable A q) (ha : tableDomain q a) : tableDomain q b := by
  induction h with
  | nil => exact ha
  | @snoc a c s z h hz ih => exact ih (hq.down c a z ha hz)

theorem AccessPath.address_eq {b a : ℕ} {s : List ℕ} (h : AccessPath b a s)
    {A : Set ℕ} {q : ℕ → ℕ} (hq : JumpTable A q) (ha : tableDomain q a)
    {f : ℕ → ℕ} (hf : ∀ ε n, f n ∈ Jump ε ↔ ε n ≠ 0) (m : ℕ) :
    tableRow q a (pathAddress f s m) = tableRow q b m := by
  induction h with
  | nil => rfl
  | @snoc a c s z h hz ih =>
    have hc := hq.edge_address hf hz (by simpa only [Nat.unpair_pair] using ha) (pathAddress f s m)
    simp only [Nat.unpair_pair] at hc
    simpa only [pathAddress,List.foldl_append,List.foldl_cons,List.foldl_nil] using
      hc.trans (ih (hq.down c a z ha hz))

theorem AccessPath.exists_of_raw {b a : ℕ} (h : RawPrecedes b a) : ∃ s, AccessPath b a s := by
  induction h with
  | single h =>
    obtain ⟨z,hz⟩ := edgeCertificate_complete _ _ h
    exact ⟨_,.snoc .nil hz⟩
  | tail h hab ih =>
    obtain ⟨s,hs⟩ := ih
    obtain ⟨z,hz⟩ := edgeCertificate_complete _ _ hab
    exact ⟨_,.snoc hs hz⟩

/-- One total pure address compiler for all paths, rows, parameters and inputs. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For any closed total numerical term $H$ receiving $\NatPair{r}{z}$, define a list accumulator by
    $$\begin{aligned}
    \LambdaTermName{foldBase}&:=\lambdaab{w}{\LambdaNumericProjection{2}w},\\
    \LambdaTermName{foldStep}_{H}&:=\lambdaab{w}{\lambdaab{j}{\lambdaab{r}{
     H(\LambdaNumericPair\,r\,(\LambdaListGet\,(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,j)))}}},\\
    \LambdaTermName{fold}_{H}&:= \lambdaab{w}{ \LambdaParamRec{ \LambdaTermName{foldBase}}{
    \LambdaTermName{foldStep}_{H}}\,w\,( \LambdaListLength\,( \LambdaNumericProjection{1}w))}.
    \end{aligned}$$
    Let $\mathbf{z}$ be a word of length $k$, with $j$-th entry $z_j$ for $j<k$.
    On input $\NatPair{\LambdaListCode{\mathbf{z}}}{m}$, this starts with $r_0=m$ and applies
    $H$ successively to $\NatPair{r_j}{z_j}$ for $j<k$. The empty list returns $m$.
    Numerical currying and uncurrying give the same recursion on paired inputs.
    With $H:= \lambdaab{w}{ \LambdaTermName{edgeAddr}( \LambdaNumericPair\,( \LambdaNumericProjection{2}w)\,(
    \LambdaNumericProjection{1}w))}$, let $\LambdaTermName{addr}:= \LambdaTermName{fold}_{H}$.
    Let $\mathcal A(c,m)$ be the final address obtained by decoding $c$ as a finite word and starting at $m$,
    then replacing the current address $r$ by $\tau(z_j,r)$ at each entry $z_j$.
    The term $\LambdaTermName{addr}$ computes $\mathcal A(c,m)$ on the paired numerical input $\NatPair{c}{m}$.
-/
theorem exists_pathAddress_program :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F
      (fun z => pathAddress f (NatListCode.decode z.unpair.1) z.unpair.2) ∧
      ∀ (A : Set ℕ) (q : ℕ → ℕ), JumpTable A q →
      ∀ (b a : ℕ) (s : List ℕ), AccessPath b a s → tableDomain q a → ∀ m,
        tableRow q a (pathAddress f s m) = tableRow q b m := by
  obtain ⟨F,f,hF,hf⟩ := parameterBits_reduce_to_jump
  let H := numericalCompose (edgeAddressProgram F)
    (pairNumerical (numericalProjectionTerm false) (numericalProjectionTerm true))
  have hs : NumericalComputes H
      (fun z => edgeAddress f (Nat.pair z.unpair.2 z.unpair.1)) := by
    simpa only [Bool.false_eq_true,ite_true,ite_false] using
      (edgeAddressProgram_computes hF).comp
        ((projection_computes false).pair (projection_computes true))
  have hh := addressFoldProgram_computes (g := fun r z => edgeAddress f (Nat.pair z r)) hs
  exact ⟨addressFoldProgram H,f,hh,fun A q hq b a s hs ha m => hs.address_eq hq ha hf m⟩

end KleeneNotation
end PolishSpaceBook
