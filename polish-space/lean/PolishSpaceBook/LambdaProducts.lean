module

public import PolishSpaceBook.LambdaRealizers
public import PolishSpaceBook.RepresentedProducts
public import PolishSpaceBook.LambdaNumericalProjections
public import PolishSpaceBook.LambdaOracleRecursion

@[expose] public section

/-! # Product realizers constructed from actual lambda terms -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm

/-- Apply a closed numerical operation to every output coordinate. -/
def mapOutputProgram (A P : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app A (app (app P (var 1)) (var 2))))

theorem mapOutputProgram_closed {A P : AlphaTerm} (hA : A.Closed) (hP : P.Closed) :
    (mapOutputProgram A P).Closed := by
  unfold Closed mapOutputProgram
  simp only [fv_lam, fv_app, fv_var]
  rw [hA, hP]
  decide

theorem mapOutputProgram_start {A P : AlphaTerm} (hA : A.Closed) (hP : P.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (mapOutputProgram A P) (var 0)) (numeral n))
      (app A (app (app P (var 0)) (numeral n))) := by
  have h₁ : Beta (app (mapOutputProgram A P) (var 0))
      (lam 2 (app A (app (app P (var 0)) (var 2)))) := by
    convert Beta.contract 1 (lam 2 (app A (app (app P (var 1)) (var 2)))) (var 0)
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app, subst_var, subst_closed _ _ _ hA, subst_closed _ _ _ hP]
  have h₂ : Beta (app (lam 2 (app A (app (app P (var 0)) (var 2)))) (numeral n))
      (app A (app (app P (var 0)) (numeral n))) := by
    convert Beta.contract 2 (app A (app (app P (var 0)) (var 2))) (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ hA, subst_closed _ _ _ hP]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Fix $p\in D$ and $n\in\NN$. Two beta steps unfold the pairing program to
    $$\LambdaNumericPair\,(P\,o\,\ChurchNumeral{n})\,(Q\,o\,\ChurchNumeral{n}).$$
    Reduce the two component applications to $\ChurchNumeral{F(p)(n)}$ and $\ChurchNumeral{G(p)(n)}$. The numerical pairing reduction then returns $\ChurchNumeral{\NatPair{F(p)(n)}{G(p)(n)}}$. Similarly, two beta steps unfold the projection program to
    $$\LambdaNumericProjection{i}\,(P\,o\,\ChurchNumeral{n}).$$
    Reduce the component application and apply the numerical projection reduction. This returns the required coordinate of $\NameProjection{i}{F(p)}$. Closedness of the component programs prevents capture in the outer substitutions. All reductions are finite, and confluence excludes other numeral outputs. The argument uses no behavior outside $D$.
-/
theorem mapOutputProgram_runs {p : ℕ → ℕ} {A P : AlphaTerm}
    (hA : A.Closed) (hP : P.Closed) {n m r : ℕ} (hp : OracleRuns p P n m)
    (ha : Relation.ReflTransGen Beta (app A (numeral m)) (numeral r)) :
    OracleRuns p (mapOutputProgram A P) n r :=
  (beta_steps_oracle (mapOutputProgram_start hA hP n)).trans
    ((oracle_steps_app_right A hp).trans (beta_steps_oracle ha))

/-- Both component programs receive the same name and coordinate. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Choose closed lambda terms $\LambdaNumericPair$ and $\LambdaNumericProjection{i}$ implementing these numerical functions on Church numerals. Their concrete constructions and reductions are given in §{sec:lambda-numerical-pairing} and §{sec:lambda-numerical-projections}; only their stated numerical behavior is used here. Given closed programs $P,Q$, define
    $$\begin{aligned}
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{a}{\lambdaab{b}{\LambdaNumericPair\,(Pab)\,(Qab)}},\\
    \LambdaProjectOutput{i}{P}&:=\lambdaab{a}{\lambdaab{b}{\LambdaNumericProjection{i}\,(Pab)}}\qquad(i=1,2).
    \end{aligned}$$
    Both constructions yield closed finite lambda terms. The arguments $a,b$ pass the same input name and output coordinate to the component programs.
-/
def pairOutputProgram (P Q : AlphaTerm) : AlphaTerm :=
  lam 1 (lam 2 (app (app numericalPairTerm (app (app P (var 1)) (var 2)))
    (app (app Q (var 1)) (var 2))))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For named terms $P,Q$, use the templates
    $$\begin{aligned}
    C_{P,Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{P\,(Qx_1)\,x_2}},\\
    \LambdaPairOutputs{P}{Q}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaNumericPair\,(Px_1x_2)\,(Qx_1x_2)}},\\
    \LambdaNamePrefix{e}&:=\lambdaab{x_1}{\lambdaab{x_2}{
    \LambdaZeroTest\,x_2\,\ChurchNumeral{e}\,
    \bigl(x_1(\LambdaPred\,x_2)\bigr)}}.
    \end{aligned}$$
    When the inserted terms are closed, these templates are closed too. Their alpha-classes are the same composition,
    pairing and prefixing terms used for name computations.
-/
theorem pairOutputProgram_closed {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) :
    (pairOutputProgram P Q).Closed := by
  unfold Closed pairOutputProgram
  simp only [fv_lam, fv_app, fv_var]
  rw [numericalPairTerm_closed, hP, hQ]
  decide

theorem pairOutputProgram_start {P Q : AlphaTerm} (hP : P.Closed) (hQ : Q.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (app (pairOutputProgram P Q) (var 0)) (numeral n))
      (app (app numericalPairTerm (app (app P (var 0)) (numeral n)))
        (app (app Q (var 0)) (numeral n))) := by
  have h₁ : Beta (app (pairOutputProgram P Q) (var 0))
      (lam 2 (app (app numericalPairTerm (app (app P (var 0)) (var 2)))
        (app (app Q (var 0)) (var 2)))) := by
    convert Beta.contract 1 (lam 2 (app (app numericalPairTerm (app (app P (var 1)) (var 2)))
      (app (app Q (var 1)) (var 2)))) (var 0) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app, subst_var, subst_closed _ _ _ numericalPairTerm_closed,
      subst_closed _ _ _ hP, subst_closed _ _ _ hQ]
  have h₂ : Beta (app (lam 2 (app (app numericalPairTerm (app (app P (var 0)) (var 2)))
      (app (app Q (var 0)) (var 2)))) (numeral n))
      (app (app numericalPairTerm (app (app P (var 0)) (numeral n)))
        (app (app Q (var 0)) (numeral n))) := by
    convert Beta.contract 2 (app (app numericalPairTerm (app (app P (var 0)) (var 2)))
      (app (app Q (var 0)) (var 2))) (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ numericalPairTerm_closed,
      subst_closed _ _ _ hP, subst_closed _ _ _ hQ]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Fix $p\in D$ and $n\in\NN$. Two beta steps unfold the pairing program to
    $$\LambdaNumericPair\,(P\,o\,\ChurchNumeral{n})\,(Q\,o\,\ChurchNumeral{n}).$$
    Reduce the two component applications to $\ChurchNumeral{F(p)(n)}$ and $\ChurchNumeral{G(p)(n)}$. The numerical pairing reduction then returns $\ChurchNumeral{\NatPair{F(p)(n)}{G(p)(n)}}$. Similarly, two beta steps unfold the projection program to
    $$\LambdaNumericProjection{i}\,(P\,o\,\ChurchNumeral{n}).$$
    Reduce the component application and apply the numerical projection reduction. This returns the required coordinate of $\NameProjection{i}{F(p)}$. Closedness of the component programs prevents capture in the outer substitutions. All reductions are finite, and confluence excludes other numeral outputs. The argument uses no behavior outside $D$.
-/
theorem pairOutputProgram_runs {p : ℕ → ℕ} {P Q : AlphaTerm}
    (hP : P.Closed) (hQ : Q.Closed) {n m r : ℕ}
    (hp : OracleRuns p P n m) (hq : OracleRuns p Q n r) :
    OracleRuns p (pairOutputProgram P Q) n (Nat.pair m r) :=
  (beta_steps_oracle (pairOutputProgram_start hP hQ n)).trans
    ((oracle_steps_app (oracle_steps_app_right numericalPairTerm hp) hq).trans
      (beta_steps_oracle (numericalPairTerm_apply m r)))

def projectOutputProgram (first : Bool) (P : AlphaTerm) : AlphaTerm :=
  mapOutputProgram (numericalProjectionTerm first) P

end NamedLambda.AlphaTerm

theorem TypeTwoComputes.map_output {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    {P A : AlphaTerm} (hP : TypeTwoComputes P F) (hA : A.Closed) (f : ℕ → ℕ)
    (ha : ∀ m, Relation.ReflTransGen Beta (app A (numeral m)) (numeral (f m))) :
    TypeTwoComputes (mapOutputProgram A P) (fun p n => f (F p n)) := by
  obtain ⟨hc, hr⟩ := typeTwoComputes_iff_runs.mp hP
  exact typeTwoComputes_iff_runs.mpr ⟨mapOutputProgram_closed hA hc,
    fun p n => mapOutputProgram_runs hA hc (hr p n) (ha _)⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Pairing and projection of names
-/
theorem TypeTwoComputes.pair {D : Set (ℕ → ℕ)} {F G : D → (ℕ → ℕ)}
    {P Q : AlphaTerm} (hP : TypeTwoComputes P F) (hQ : TypeTwoComputes Q G) :
    TypeTwoComputes (pairOutputProgram P Q) (fun p => typeTwoPairName (F p) (G p)) := by
  obtain ⟨hc, hr⟩ := typeTwoComputes_iff_runs.mp hP
  obtain ⟨hd, hs⟩ := typeTwoComputes_iff_runs.mp hQ
  exact typeTwoComputes_iff_runs.mpr ⟨pairOutputProgram_closed hc hd,
    fun p n => pairOutputProgram_runs hc hd (hr p n) (hs p n)⟩

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Pairing and projection of names
-/
theorem TypeTwoComputes.left {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    {P : AlphaTerm} (hP : TypeTwoComputes P F) :
    TypeTwoComputes (projectOutputProgram true P) (fun p => typeTwoLeftName (F p)) :=
  hP.map_output (numericalProjectionTerm_closed true) (fun m => m.unpair.1)
    (numericalProjectionTerm_apply true)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: lemma
  title: Pairing and projection of names
-/
theorem TypeTwoComputes.right {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    {P : AlphaTerm} (hP : TypeTwoComputes P F) :
    TypeTwoComputes (projectOutputProgram false P) (fun p => typeTwoRightName (F p)) :=
  hP.map_output (numericalProjectionTerm_closed false) (fun m => m.unpair.2)
    (numericalProjectionTerm_apply false)

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Suppose that a closed program $P$ computes a name realizer $H$ of $h$. By §{sec:tte-name-pairs}, $\LambdaProjectOutput{1}{P}$ and $\LambdaProjectOutput{2}{P}$ compute the corresponding projections of $H$. The definition of the product representation makes these valid names of the two coordinates of $h(\delta_Z(p))$ for every valid input name $p$. Thus they realize the coordinate maps.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Product criterion
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, let closed programs $P,Q$ compute name realizers $H_X,H_Y$ of the coordinate maps. The pairing lemma shows that $\LambdaPairOutputs{P}{Q}$ computes
    $$p\longmapsto\NamePair{H_X(p)}{H_Y(p)}.$$
    For every valid $p$, the inverse identities place this paired name in the product representation's domain, and the defining equation sends it to $h(\delta_Z(p))$. This proves the reverse implication. Apply the criterion to the identity map of the product to obtain computability of its two projections. These constructions use the same fixed lambda expressions for any supplied component programs; they require no decision procedure for the name domains.
-/
theorem hasComputableRealizer_product_iff (δZ : Representation Z) (δX : Representation X)
    (δY : Representation Y) (h : Z → X × Y) :
    HasComputableRealizer δZ (typeTwoProductRepresentation δX δY) h ↔
      HasComputableRealizer δZ δX (Prod.fst ∘ h) ∧
      HasComputableRealizer δZ δY (Prod.snd ∘ h) := by
  constructor
  · rintro ⟨H, ⟨P, hp⟩, hH⟩
    constructor
    · refine ⟨fun p => ⟨typeTwoLeftName (H p).val, (H p).property.1⟩,
        ⟨projectOutputProgram true P, hp.left⟩, ?_⟩
      intro p
      exact congrArg Prod.fst (hH p)
    · refine ⟨fun p => ⟨typeTwoRightName (H p).val, (H p).property.2⟩,
        ⟨projectOutputProgram false P, hp.right⟩, ?_⟩
      intro p
      exact congrArg Prod.snd (hH p)
  · rintro ⟨⟨F, ⟨P, hp⟩, hF⟩, ⟨G, ⟨Q, hq⟩, hG⟩⟩
    let H : δZ.domain → (typeTwoProductRepresentation δX δY).domain := fun p =>
      ⟨typeTwoPairName (F p).val (G p).val, by simp [typeTwoProductRepresentation]⟩
    refine ⟨H, ⟨pairOutputProgram P Q, hp.pair hq⟩, ?_⟩
    intro p
    change (δX.toFun _, δY.toFun _) = h (δZ.toFun p)
    simpa [H] using Prod.ext (hF p) (hG p)

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, let closed programs $P,Q$ compute name realizers $H_X,H_Y$ of the coordinate maps. The pairing lemma shows that $\LambdaPairOutputs{P}{Q}$ computes
    $$p\longmapsto\NamePair{H_X(p)}{H_Y(p)}.$$
    For every valid $p$, the inverse identities place this paired name in the product representation's domain, and the defining equation sends it to $h(\delta_Z(p))$. This proves the reverse implication. Apply the criterion to the identity map of the product to obtain computability of its two projections. These constructions use the same fixed lambda expressions for any supplied component programs; they require no decision procedure for the name domains.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Product criterion
-/
theorem hasComputableRealizer_fst (δX : Representation X) (δY : Representation Y) :
    HasComputableRealizer (typeTwoProductRepresentation δX δY) δX Prod.fst :=
  ((hasComputableRealizer_product_iff _ δX δY id).mp (hasComputableRealizer_id _)).1

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Product criterion
-/
theorem hasComputableRealizer_snd (δX : Representation X) (δY : Representation Y) :
    HasComputableRealizer (typeTwoProductRepresentation δX δY) δY Prod.snd :=
  ((hasComputableRealizer_product_iff _ δX δY id).mp (hasComputableRealizer_id _)).2

end PolishSpaceBook
