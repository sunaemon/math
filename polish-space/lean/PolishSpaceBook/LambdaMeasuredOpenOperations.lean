module

public import PolishSpaceBook.LambdaComputableClosedSupport

@[expose] public section

/-! # Finite operations on open sets with computable measure
The open name and the fast name of its measure are computed by closed lambda
terms. Union measure is approximated by finite cylinder unions with small tails.
-/
namespace PolishSpaceBook.LambdaRandomness
open Set Filter Topology MeasureTheory Metric NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open CantorMeasure CantorDerivative
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Both pieces of effective data are witnessed by actual numerical lambda terms. -/
def ComputablyMeasuredOpen (U : Set (ℕ → Bool)) : Prop :=
  ∃ (P Q : AlphaTerm) (p : ℕ → ℕ) (q : realRepresentation.domain),
    NumericalComputes P p ∧ ValidOpenName p ∧ U = namedOpen p ∧
    NumericalComputes Q q.val ∧ realRepresentation.toFun q = fairCoinProduct.real U

theorem ComputablyMeasuredOpen.isOpen {U : Set (ℕ → Bool)} (h : ComputablyMeasuredOpen U) :
    IsOpen U := by
  obtain ⟨P,Q,p,q,hp,hv,rfl,hq,he⟩ := h
  exact isOpen_namedOpen p

def unionOpenName (p r : ℕ → ℕ) (z : ℕ) : ℕ :=
  if z.unpair.1 = 0 then p z.unpair.2 else r z.unpair.2

def unionOpenProgram (P R : AlphaTerm) : AlphaTerm := numericalIfZero (numericalProjectionTerm true)
  (numericalCompose P (numericalProjectionTerm false)) (numericalCompose R (numericalProjectionTerm false))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Computable measure of finite unions
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Let $P,R$ compute $p,\rho$, respectively, and let $\pi_i:=\LambdaNumericProjection{i}$.
    A name of the union is given by
    $$v(\NatPair{i}{m}):=\begin{cases}p(m),&i=0,\\r(m),&i>0,\end{cases}
    \qquad V:=\lambdaab{z}{\LambdaZeroTest\,(\pi_1z)\,(P(\pi_2z))\,(R(\pi_2z))}.$$
    Rows $0$ and $1$ include both names, and the repeated rows add no new points.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Use the finite-approximation lemma to compute stages $a(k),b(k)$ for the two names.
    At precision $k$, form the finite list
    $$L_k:=(p(0),\ldots,p(a(k+1)-1))\concat(r(0),\ldots,r(b(k+1)-1)).$$
    A list with stage $0$ is empty. Put $F_k:=U_{L_k}$. Then $F_k\IncludedIn U_p\cup U_r$, and
    $$\begin{aligned}
    \SetDifference{(U_p\cup U_r)}{F_k}
    &\IncludedIn\bigl(\SetDifference{U_p}{U_{(p(0),\ldots,p(a(k+1)-1))}}\bigr)\\
    &\qquad\cup\bigl(\SetDifference{U_r}{U_{(r(0),\ldots,r(b(k+1)-1))}}\bigr),\\
    0\le\mu(U_p\cup U_r)-\mu(F_k)&<2^{-(k+2)}+2^{-(k+2)}=2^{-(k+1)}.
    \end{aligned}$$
    The rational values $\mu(F_k)$ therefore form a fast Cauchy name of the union's measure.
    The finite-union algorithm accounts for overlaps between the two lists.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Let $A,B$ compute $a,b$, and let $M$ be the exact finite-union measure program. The term is
    $$\begin{aligned}
    L_P&:=\lambdaab{k}{\LambdaInputPrefix\,P\,(A(\LambdaSucc\,k))},\\
    L_R&:=\lambdaab{k}{\LambdaInputPrefix\,R\,(B(\LambdaSucc\,k))},\\
    H&:=\lambdaab{k}{M(\LambdaListAppend\,(L_Pk)\,(L_Rk))}.
    \end{aligned}$$
    The prefix and append reductions, followed by the reduction for $M$, give
    $H\ChurchNumeral{k}\to_\beta^*\ChurchNumeral{h(k)}$ with $q_{h(k)}=\mu(F_k)$.
    All stage searches terminate by the preceding lemma, and the precision remains an input.
-/
theorem unionOpenProgram_computes {P R : AlphaTerm} {p r : ℕ → ℕ}
    (hp : NumericalComputes P p) (hr : NumericalComputes R r) :
    NumericalComputes (unionOpenProgram P R) (unionOpenName p r) := by
  have h := numericalIfZero_computes (projection_computes true)
    (hp.comp (projection_computes false)) (hr.comp (projection_computes false))
  change NumericalComputes _ (fun z => if z.unpair.1 = 0 then p z.unpair.2 else r z.unpair.2)
  simpa only [unionOpenProgram,ite_true,Bool.false_eq_true,ite_false] using h

theorem unionOpenName_valid {p r : ℕ → ℕ} (hp : ValidOpenName p) (hr : ValidOpenName r) :
    ValidOpenName (unionOpenName p r) := by
  intro z
  unfold unionOpenName
  split_ifs <;> first | exact hp _ | exact hr _

theorem namedOpen_unionOpenName (p r : ℕ → ℕ) :
    namedOpen (unionOpenName p r) = namedOpen p ∪ namedOpen r := by
  ext x
  simp only [namedOpen,mem_iUnion,mem_union]
  constructor
  · rintro ⟨z,h⟩
    unfold unionOpenName at h
    split_ifs at h
    · exact Or.inl ⟨_,h⟩
    · exact Or.inr ⟨_,h⟩
  · rintro (⟨s,h⟩ | ⟨s,h⟩)
    · exact ⟨Nat.pair 0 s,by simpa [unionOpenName] using h⟩
    · exact ⟨Nat.pair 1 s,by simpa [unionOpenName] using h⟩

theorem finiteOpen_append (L M : List ℕ) : finiteOpen (L ++ M) = finiteOpen L ∪ finiteOpen M := by
  ext x
  simp [finiteOpen,or_and_right,exists_or]

/-- Each input tail is estimated one precision beyond the requested output. -/
def unionMassCode (p r a b : ℕ → ℕ) (k : ℕ) : ℕ :=
  finiteMeasureCode (seqPrefix p (a (k+1)) ++ seqPrefix r (b (k+1)))

def finitePrefixAtProgram (P A : AlphaTerm) : AlphaTerm :=
  numericalCompose (app prefixProgram P) (numericalCompose A successorTerm)

def unionMassProgram (P R A B : AlphaTerm) : AlphaTerm := numericalCompose finiteMeasureProgram
  (numericalCombine listAppendTerm (finitePrefixAtProgram P A) (finitePrefixAtProgram R B))

theorem finitePrefixAtProgram_computes {P A : AlphaTerm} {p a : ℕ → ℕ}
    (hp : NumericalComputes P p) (ha : NumericalComputes A a) :
    NumericalComputes (finitePrefixAtProgram P A) (fun k => NatListCode.encode (seqPrefix p (a (k+1)))) := by
  have hpre : NumericalComputes (app prefixProgram P) (fun s => NatListCode.encode (seqPrefix p s)) :=
    ⟨closed_app prefixProgram_closed hp.1,
      fun s => (prefixProgram_runs p s).apply_numerical prefixProgram_closed hp⟩
  exact hpre.comp (ha.comp successor_computes)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Computable measure of finite unions
-/
theorem unionMassProgram_computes {P R A B : AlphaTerm} {p r a b : ℕ → ℕ}
    (hp : NumericalComputes P p) (hr : NumericalComputes R r)
    (ha : NumericalComputes A a) (hb : NumericalComputes B b) :
    NumericalComputes (unionMassProgram P R A B) (unionMassCode p r a b) := by
  have hlist := (finitePrefixAtProgram_computes hp ha).combine (finitePrefixAtProgram_computes hr hb)
    listAppendTerm_closed (fun x y => NatListCode.encode (NatListCode.decode x ++ NatListCode.decode y))
    listAppendTerm_apply
  have h := finiteMeasureProgram_computes.comp hlist
  change NumericalComputes _ (fun k => finiteMeasureCode (seqPrefix p (a (k+1)) ++ seqPrefix r (b (k+1))))
  simpa only [unionMassProgram,NatListCode.decode_encode] using h

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Computable measure of finite unions
-/
theorem unionMassCode_error {p r a b : ℕ → ℕ} (hp : ValidOpenName p) (hr : ValidOpenName r)
    (ha : ∀ k, fairCoinProduct.real (namedOpen p \ stageOpen p (a k)) < (1/2:ℝ)^(k+1))
    (hb : ∀ k, fairCoinProduct.real (namedOpen r \ stageOpen r (b k)) < (1/2:ℝ)^(k+1)) (k : ℕ) :
    dist (rationalPoint (unionMassCode p r a b k))
      (fairCoinProduct.real (namedOpen p ∪ namedOpen r)) ≤ (1/2:ℝ)^(k+1) := by
  let L := seqPrefix p (a (k+1)) ++ seqPrefix r (b (k+1))
  have hvalid : ∀ x ∈ L, ValidEntry x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact prefixEntries_valid hp _ _ hx
    · exact prefixEntries_valid hr _ _ hx
  have hfin : finiteOpen L = stageOpen p (a (k+1)) ∪ stageOpen r (b (k+1)) := by
    rw [finiteOpen_append,finiteOpen_prefix,finiteOpen_prefix]
  have hsub : finiteOpen L ⊆ namedOpen p ∪ namedOpen r := by
    rw [hfin]
    exact union_subset_union (stageOpen_subset _ _) (stageOpen_subset _ _)
  have htail : (namedOpen p ∪ namedOpen r) \ finiteOpen L ⊆
      (namedOpen p \ stageOpen p (a (k+1))) ∪ (namedOpen r \ stageOpen r (b (k+1))) := by
    rw [hfin]
    intro x hx
    rcases hx.1 with hx1 | hx1
    · exact Or.inl ⟨hx1,fun h => hx.2 (Or.inl h)⟩
    · exact Or.inr ⟨hx1,fun h => hx.2 (Or.inr h)⟩
  have hbound := (measureReal_mono (μ := fairCoinProduct) htail).trans (measureReal_union_le _ _)
  have hdiff := measureReal_sdiff (μ := fairCoinProduct) hsub (isOpen_finiteOpen L).measurableSet
  have hmono := measureReal_mono (μ := fairCoinProduct) hsub
  change dist (rationalPoint (finiteMeasureCode L)) _ ≤ _
  rw [finiteMeasureCode_value _ hvalid,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hmono)]
  have hsum := add_lt_add (ha (k+1)) (hb (k+1))
  have heq : (1/2:ℝ)^(k+1+1) + (1/2:ℝ)^(k+1+1) = (1/2:ℝ)^(k+1) := by rw [pow_succ]; ring
  rw [heq] at hsum
  linarith

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Computable measure of finite unions
-/
theorem ComputablyMeasuredOpen.union {U V : Set (ℕ → Bool)}
    (hU : ComputablyMeasuredOpen U) (hV : ComputablyMeasuredOpen V) : ComputablyMeasuredOpen (U ∪ V) := by
  obtain ⟨P,Q,p,q,hp,hvp,rfl,hq,heq⟩ := hU
  obtain ⟨R,S,r,s,hr,hvr,rfl,hs,hes⟩ := hV
  obtain ⟨a,ha,hea⟩ := tailStageProgram_computes hp hvp q hq heq
  obtain ⟨b,hb,heb⟩ := tailStageProgram_computes hr hvr s hs hes
  have herr := unionMassCode_error hvp hvr hea heb
  refine ⟨unionOpenProgram P R,unionMassProgram P R (tailStageProgram P Q) (tailStageProgram R S),
    unionOpenName p r,⟨unionMassCode p r a b,isCauchyName_of_halfError_le herr⟩,
    unionOpenProgram_computes hp hr,unionOpenName_valid hvp hvr,(namedOpen_unionOpenName p r).symm,
    unionMassProgram_computes hp hr ha hb,?_⟩
  exact cauchyRepresentation_eq_of_halfError_le _ _ herr


/-- A finite list is enumerated with zero padding. -/
def finiteOpenName (L : List ℕ) (s : ℕ) : ℕ := L.getD s 0

def finiteOpenProgram (L : List ℕ) : AlphaTerm := numericalCompose listGetTerm
  (pairNumerical (numericalConstant (NatListCode.encode L)) numericalIdentity)

theorem finiteOpenProgram_computes (L : List ℕ) :
    NumericalComputes (finiteOpenProgram L) (finiteOpenName L) := by
  have h := listGet_computes.comp ((numericalConstant_computes (NatListCode.encode L)).pair
    numericalIdentity_computes)
  change NumericalComputes _ (fun s => L.getD s 0)
  simpa only [finiteOpenProgram,Nat.unpair_pair,NatListCode.decode_encode,id_eq] using h

theorem finiteOpenName_valid (L : List ℕ) (hv : ∀ a ∈ L, ValidEntry a) : ValidOpenName (finiteOpenName L) := by
  intro s
  by_cases hs : s < L.length
  · simpa [finiteOpenName,List.getD,hs] using hv L[s] (List.getElem_mem hs)
  · simp [finiteOpenName,List.getD,hs,ValidEntry]

theorem namedOpen_finiteOpenName (L : List ℕ) : namedOpen (finiteOpenName L) = finiteOpen L := by
  ext x
  simp only [namedOpen,finiteOpen,mem_iUnion]
  constructor
  · rintro ⟨s,h⟩
    by_cases hs : s < L.length
    · refine ⟨L[s],List.getElem_mem hs,?_⟩
      simpa [finiteOpenName,List.getD,hs] using h
    · simp [finiteOpenName,List.getD,hs,entrySet] at h
  · rintro ⟨a,ha,h⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_iff_getElem.mp ha
    exact ⟨s,by simpa [finiteOpenName,List.getD,hs] using h⟩

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Finite open sets and cylinder complements
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For a finite list $L$ of valid entries, enumerate its entries in order and then return $0$ forever.
    Writing $\ell:=\LambdaListCode{L}$, the open-name and measure-name terms are
    $$P_L:=\lambdaab{s}{\LambdaListGet(\LambdaNumericPair\,\ChurchNumeral{\ell}\,s)},
    \qquad Q_L:=\lambdaab{k}{M\ChurchNumeral{\ell}}.$$
    The list-access term returns $0$ beyond the end of the list, and $M\ChurchNumeral{\ell}$ reduces to a code
    of the exact rational $\mu(U_L)$. The constant rational sequence is a fast Cauchy name.
    For the complement of $\cyl{w}$, take the finite list of entries for all binary words $t$ of length $|w|$
    with $t\ne w$, in any fixed order. Each entry is $1+\LambdaListCode{t}$. The cylinders in this list have union
    $\SetDifference{\CantorSpace}{\cyl{w}}$, since each point has exactly one prefix of that length.
    If $w$ is empty, the list is empty and represents the empty set.
-/
theorem computablyMeasured_finiteOpen (L : List ℕ) (hv : ∀ a ∈ L, ValidEntry a) :
    ComputablyMeasuredOpen (finiteOpen L) := by
  have herr : ∀ k, dist (rationalPoint (finiteMeasureCode L)) (fairCoinProduct.real (finiteOpen L)) ≤
      (1/2:ℝ)^(k+1) := by
    intro k
    rw [finiteMeasureCode_value _ hv,dist_self]
    positivity
  refine ⟨finiteOpenProgram L,numericalCompose finiteMeasureProgram (numericalConstant (NatListCode.encode L)),
    finiteOpenName L,
    ⟨fun _ => finiteMeasureCode L,isCauchyName_of_halfError_le herr⟩,
    finiteOpenProgram_computes L,finiteOpenName_valid L hv,(namedOpen_finiteOpenName L).symm,
    ?_,?_⟩
  · simpa only [NatListCode.decode_encode] using
      finiteMeasureProgram_computes.comp (numericalConstant_computes (NatListCode.encode L))
  · exact cauchyRepresentation_eq_of_halfError_le _ _ herr

/-- List all words of the fixed length except the specified word. -/
noncomputable def cylinderComplementEntries (w : List Bool) : List ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin w.length → Bool)).toList.filter (fun t => List.ofFn t ≠ w)).map
    (fun t => encodeWord (List.ofFn t) + 1)

theorem cylinderComplementEntries_valid (w : List Bool) :
    ∀ a ∈ cylinderComplementEntries w, ValidEntry a := by
  classical
  intro a ha
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ha
  exact Or.inr (by simpa using binary_encodeWord (List.ofFn t))

theorem finiteOpen_cylinderComplementEntries (w : List Bool) :
    finiteOpen (cylinderComplementEntries w) = (cyl w)ᶜ := by
  classical
  rw [compl_cyl_eq_iUnion_same_length_ne]
  ext x
  simp only [finiteOpen,mem_iUnion]
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ha
    have ht' : List.ofFn t ≠ w := by simpa using (List.mem_filter.mp ht).2
    refine ⟨⟨List.ofFn t,by simp,ht'⟩,?_⟩
    simpa [entrySet] using hx
  · rintro ⟨⟨t,hlen,hne⟩,hx⟩
    let f : Fin w.length → Bool := fun i => t[i.val]'(by omega)
    have hf : List.ofFn f = t := by
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro i hi ht
        simp [f]
    refine ⟨encodeWord t+1,?_,by simpa [entrySet] using hx⟩
    apply List.mem_map.mpr
    refine ⟨f,?_,by rw [hf]⟩
    apply List.mem_filter.mpr
    exact ⟨by simp,by simpa [hf] using hne⟩

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Finite open sets and cylinder complements
-/
theorem computablyMeasured_cylinder_complement (w : List Bool) : ComputablyMeasuredOpen (cyl w)ᶜ := by
  rw [← finiteOpen_cylinderComplementEntries w]
  exact computablyMeasured_finiteOpen _ (cylinderComplementEntries_valid w)

/-- The data for a positive closed condition are maintained through open complements. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Finite open sets and cylinder complements
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Finally,
    $$\SetDifference{\CantorSpace}{(K\cap\cyl{w})}
    =\bigl(\SetDifference{\CantorSpace}{K}\bigr)\cup
     \bigl(\SetDifference{\CantorSpace}{\cyl{w}}\bigr).$$
    Apply the finite-union proposition to these two open sets, and subtract the resulting measure from $1$.
    Thus intersecting the closed set with a fixed cylinder preserves the required effective data.
-/
theorem computablyMeasured_complement_inter_cylinder {K : Set (ℕ → Bool)}
    (hK : ComputablyMeasuredOpen Kᶜ) (w : List Bool) : ComputablyMeasuredOpen (K ∩ cyl w)ᶜ := by
  rw [compl_inter]
  exact hK.union (computablyMeasured_cylinder_complement w)

end PolishSpaceBook.LambdaRandomness
