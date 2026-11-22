module

public import PolishSpaceBook.LambdaContinuousReader

@[expose] public section

/-! # Coding continuous partial maps by cylinder certificates

The infinite certificate name may be noncomputable. The reader is one fixed
closed lambda term, independent of both the domain and the function. Triple
codes use numerical pairing and the lambda list code explicitly.
-/
namespace PolishSpaceBook.LambdaContinuousCode
open NamedLambda NamedLambda.AlphaTerm

/-- Constancy on a cylinder relative to the prescribed domain. -/
def Certificate {D : Set (ℕ → ℕ)} (F : D → (ℕ → ℕ)) (n : ℕ) (s : List ℕ) (v : ℕ) : Prop :=
  ∀ p : D, p.val ∈ cyl s → F p n = v

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Encode finite lists by $\LambdaListCode{[]}=0$ and $\LambdaListCode{a::s}=\NatPair{a}{\LambdaListCode{s}}+1$. Use
    $\NatPair{n}{\NatPair{\LambdaListCode{s}}{v}}$ for the code of $(n,s,v)$. These numerical functions are primitive
    recursive and have lambda implementations. Define a certificate relation by
    $$
    R(n,s,v)\quad\Longleftrightarrow\quad
    \forall q\in D\cap\cyl{s},\ F(q)(n)=v.
    $$
    Let $r$ return one on codes satisfying this relation and zero on all other inputs. This defines an infinite oracle; it
    does not assert that the relation is decidable or that the oracle can be computed from a description of $F$.
    Certificates for cylinders disjoint from $D$ may be vacuous, but such cylinders never contain a valid input.
-/
/-- No effectiveness of the certificate relation is asserted or required. -/
noncomputable def certificateName {D : Set (ℕ → ℕ)} (F : D → (ℕ → ℕ)) (e : ℕ) : ℕ := by
  classical
  exact if Certificate F e.unpair.1 (NatListCode.decode e.unpair.2.unpair.1) e.unpair.2.unpair.2
    then 1 else 0

theorem certificateName_code {D : Set (ℕ → ℕ)} (F : D → (ℕ → ℕ))
    (n : ℕ) (s : List ℕ) (v : ℕ) :
    certificateName F (Nat.pair n (Nat.pair (NatListCode.encode s) v)) ≠ 0 ↔ Certificate F n s v := by
  classical
  simp only [certificateName, Nat.unpair_pair, NatListCode.decode_encode]
  split_ifs <;> simp_all

/-- Continuity supplies a finite prefix on which one output coordinate is fixed. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $r$ have value one at the code of $(n,s,v)$ exactly when $F(q)(n)=v$ for all $q\in D\cap\cyl{s}$, and zero otherwise. Pairing and list coding are bijective, so this specifies a name on all coordinates. This name need not be computable. On valid input $p$, every successful trial gives the correct value because $p$ lies in the cylinder of its own prefix. Continuity of the coordinate map into discrete $\NN$ makes its fiber through $p$ open in $D$. Write this fiber as $D\cap U$ with $U$ open in Baire space, and choose a prefix cylinder containing $p$ and contained in $U$. Its length, together with $F(p)(n)$, gives a successful trial. The reader lemma now proves termination and the exact output identity. Certificates for cylinders disjoint from $D$ do not affect valid inputs.
-/
theorem exists_certificate {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    (hF : Continuous F) (p : D) (n : ℕ) :
    ∃ N, Certificate F n (seqPrefix p.val N) (F p n) := by
  let U : Set D := {q | F q n = F p n}
  have hU : IsOpen U := (isOpen_discrete {F p n}).preimage ((continuous_apply n).comp hF)
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
  have hpO : p.val ∈ O := by
    change p ∈ Subtype.val ⁻¹' O
    rw [hOU]
    rfl
  obtain ⟨s, hps, hsO⟩ := exists_cyl_subset_of_mem_open hpO hO
  refine ⟨s.length, ?_⟩
  rw [seqPrefix_eq_of_mem_cyl hps]
  intro q hq
  have : q ∈ U := by rw [← hOU]; exact hsO hq
  exact this

theorem query_sound {D : Set (ℕ → ℕ)} (F : D → (ℕ → ℕ)) (p : D) (n k : ℕ)
    (hk : continuousQuery (typeTwoPairName (certificateName F) p.val) n k ≠ 0) :
    k.unpair.2 = F p n := by
  simp only [continuousQuery, typeTwoLeft_pair, typeTwoRight_pair] at hk
  exact ((certificateName_code F _ _ _).mp hk p (mem_cyl_seqPrefix p.val _)).symm

theorem query_complete {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)} (hF : Continuous F)
    (p : D) (n : ℕ) :
    ∃ k, continuousQuery (typeTwoPairName (certificateName F) p.val) n k ≠ 0 := by
  obtain ⟨N,hN⟩ := exists_certificate hF p n
  refine ⟨Nat.pair N (F p n), ?_⟩
  simpa only [continuousQuery, typeTwoLeft_pair, typeTwoRight_pair, Nat.unpair_pair,
    certificateName_code] using hN

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    If a trial succeeds on $p\in D$, its prefix satisfies $p\in\cyl{s}$, so the certificate implies $F(p)(n)=v$. Thus every
    successful trial gives the correct value. For termination, the coordinate map $q\mapsto F(q)(n)$ is continuous into the
    discrete space $\NN$. Its fiber through $p$ is a neighborhood of $p$ in $D$, and the cylinder basis supplies a prefix
    $s=\restrict{p}{N}$ on which this coordinate is constantly $F(p)(n)$ relative to $D$. The trial $(N,F(p)(n))$ therefore
    succeeds. It occurs at a finite stage of the search; any earlier success has the same value. This proves both
    termination and correctness on the whole prescribed domain.
-/
/-- The same finite program realizes every continuous map after adjoining its code. -/
theorem reader_runs {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)} (hF : Continuous F)
    (p : D) (n : ℕ) :
    OracleRuns (typeTwoPairName (certificateName F) p.val) continuousReaderProgram n (F p n) := by
  have h := query_complete hF p n
  have hv := query_sound F p n (Nat.find h) (Nat.find_spec h)
  simpa only [hv] using continuousReaderProgram_hit _ n h

theorem reader_runs_iff {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)} (hF : Continuous F)
    (p : D) (n m : ℕ) :
    OracleRuns (typeTwoPairName (certificateName F) p.val) continuousReaderProgram n m ↔ m = F p n := by
  constructor
  · exact fun h => h.output_unique (reader_runs hF p n)
  · rintro rfl
    exact reader_runs hF p n

/-- Fixing one component preserves continuity of the joined name. -/
theorem continuous_parameter {D : Set (ℕ → ℕ)} (r : ℕ → ℕ) :
    Continuous (fun p : D => typeTwoPairName r p.val) := by
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology (f := fun k => Nat.pair (r i) k)).comp
    ((continuous_apply i).comp continuous_subtype_val)

/-- Finite use proves the converse for any lambda reader and any fixed parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    For the converse, a terminating computation uses only finitely many digits of the joined name. Fixing the auxiliary name and varying the input within a sufficiently small cylinder preserves that computation. Uniqueness of numeral outputs forces the coordinate of the computed map to remain constant there, relative to $D$. Each coordinate map is therefore continuous, and so is the map into Baire space.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Conversely, fix the auxiliary oracle $r$ and a program computing $F$ on $D$. A terminating computation of $F(p)(n)$ uses
    only finitely many coordinates of $\langle r,p\rangle$. Keep $r$ fixed and require $q\in D$ to agree with $p$ below a
    bound for those coordinates. The same computation then returns the same value on $\langle r,q\rangle$. Hence each output
    coordinate is locally constant on $D$, and $F$ is continuous in the product topology.
-/
theorem continuous_of_parameter {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    (r : ℕ → ℕ) (P : AlphaTerm)
    (h : ∀ p n, OracleRuns (typeTwoPairName r p.val) P n (F p n)) : Continuous F := by
  apply continuous_pi
  intro n
  have h_fiber (v : ℕ) : IsOpen {p : D | F p n = v} := by
    have he : {p : D | F p n = v} =
        (fun p : D => typeTwoPairName r p.val) ⁻¹' {w | OracleRuns w P n v} := by
      ext p
      constructor
      · intro hv
        exact hv ▸ h p n
      · intro hv
        exact (h p n).output_unique hv
    rw [he]
    exact (isOpen_oracleRuns P n v).preimage (continuous_parameter r)
  rw [continuous_def]
  intro U _
  rw [isOpen_iff_mem_nhds]
  intro p hp
  apply Filter.mem_of_superset ((h_fiber (F p n)).mem_nhds rfl)
  intro q hq
  change F q n ∈ U
  change F q n = F p n at hq
  change F p n ∈ U at hp
  simpa only [hq] using hp

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Oracle coding of continuous partial maps
-/
theorem continuous_iff_exists_parameter {D : Set (ℕ → ℕ)} (F : D → (ℕ → ℕ)) :
    Continuous F ↔ ∃ (r : ℕ → ℕ) (P : AlphaTerm), P.Closed ∧
      ∀ p n, OracleRuns (typeTwoPairName r p.val) P n (F p n) := by
  constructor
  · intro hF
    exact ⟨certificateName F, continuousReaderProgram, continuousReaderProgram_closed, reader_runs hF⟩
  · rintro ⟨r,P,_,h⟩
    exact continuous_of_parameter r P h

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Coding continuous maps by a fixed lambda reader
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Oracle coding of continuous partial maps
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The infinite oracle in a function name is essential for representing arbitrary continuous realizers. The following
    construction shows that a single finite reader suffices; all information about the particular realizer can be placed in
    its auxiliary oracle.
-/
theorem exists_fixed_reader :
    ∃ P : AlphaTerm, P.Closed ∧ ∀ (D : Set (ℕ → ℕ)) (F : D → (ℕ → ℕ)),
      Continuous F → ∃ r : ℕ → ℕ, ∀ p n m,
        OracleRuns (typeTwoPairName r p.val) P n m ↔ m = F p n :=
  ⟨continuousReaderProgram, continuousReaderProgram_closed,
    fun _ _ hF => ⟨certificateName _, reader_runs_iff hF⟩⟩

end PolishSpaceBook.LambdaContinuousCode
