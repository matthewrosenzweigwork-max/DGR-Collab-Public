import DGRHS.Decoupling.FiniteCubeNoiseWalshCutoff

/-!
Records-only scalar Walsh mixed-degree moment input for the translated
finite-cube small-ball argument. This file is intentionally expressed in
terms of the already aggregated Boolean-mask coefficient map `c`; the
ordered-tuple source adapter feeds its coefficients into this map by summing
all contributions with the same parity mask. No symmetry of those ordered
coefficients is assumed.

Pinned checked inputs:
* `FiniteCubeNoiseWalshCutoff.lean`, SHA-256
  `5eb959af22bd94ebe6bddda10f152d6948ba9e82b0a9cc61b0f04ad191221781`;
* `FiniteCubeCharacterMask.lean`, SHA-256
  `f6d97e83906054b9dbbbe53f0675eceeb0f6f635c8e004d9b225d663da2871de`.

The checked degree-`≤ k` noise estimate gives the stronger factor `9^k`.
For `k ≥ 1`, this is bounded by `k^3 * Σ_{r=1}^k 9^r`, the source-compatible
mixed-degree factor. Mean zero follows from character orthogonality because
all supported masks have degree at least one. Parseval gives the exact second
moment as the coefficient square sum. The `n=0` case is covered by the same
support premise, which forces the coefficient map to vanish.

No compiler, proof source, or campaign forest was modified.
-/

noncomputable section
open MeasureTheory ProbabilityTheory DGRHS.Decoupling

namespace DGRHS.Decoupling.FiniteCube

abbrev SourceOrderedTuple (n k : ℕ) :=
  {t : Fin k → Fin n // Function.Injective t}

def sourceOrderedTupleMask {n k : ℕ} (t : SourceOrderedTuple n k) : Cube n :=
  sourceSupportMask ((Finset.univ : Finset (Fin k)).image t.1)

noncomputable def sourceOrderedTupleCoefficient {n k : ℕ}
    (a : SourceOrderedTuple n k → ℝ) (s : Cube n) : ℝ := by
  classical
  exact ∑ t : SourceOrderedTuple n k,
    if sourceOrderedTupleMask t = s then a t else 0

noncomputable def sourceOrderedTuplePolynomial {n k : ℕ}
    (a : SourceOrderedTuple n k → ℝ) (ω : Cube n) : ℝ := by
  classical
  exact ∑ t : SourceOrderedTuple n k,
    a t * ∏ j : Fin k, rademacherSign (ω (t.1 j))

theorem sourceOrderedTupleMask_character {n k : ℕ}
    (t : SourceOrderedTuple n k) (ω : Cube n) :
    boolMaskCharacter (sourceOrderedTupleMask t) ω =
      ∏ j : Fin k, rademacherSign (ω (t.1 j)) := by
  rw [sourceOrderedTupleMask, boolMaskCharacter_sourceSupportMask]
  unfold rademacherCharacter
  rw [Finset.prod_image (fun i hi j hj hij => t.2 hij)]

theorem sourceOrderedTuplePolynomial_eq_walsh {n k : ℕ}
    (a : SourceOrderedTuple n k → ℝ) (ω : Cube n) :
    sourceOrderedTuplePolynomial a ω =
      cubeWalshPolynomial (sourceOrderedTupleCoefficient a) ω := by
  classical
  calc
    sourceOrderedTuplePolynomial a ω =
        ∑ t : SourceOrderedTuple n k,
          a t * boolMaskCharacter (sourceOrderedTupleMask t) ω := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [sourceOrderedTupleMask_character]
    _ = ∑ t : SourceOrderedTuple n k,
          ∑ s : Cube n,
            (if sourceOrderedTupleMask t = s then a t else 0) *
              boolMaskCharacter s ω := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_eq_single (sourceOrderedTupleMask t)]
      · simp
      · intro s hs hne
        simp [eq_comm, hne]
      · simp
    _ = ∑ s : Cube n, ∑ t : SourceOrderedTuple n k,
          (if sourceOrderedTupleMask t = s then a t else 0) *
            boolMaskCharacter s ω := by
      rw [Finset.sum_comm]
    _ = cubeWalshPolynomial (sourceOrderedTupleCoefficient a) ω := by
      unfold cubeWalshPolynomial sourceOrderedTupleCoefficient
      apply Finset.sum_congr rfl
      intro s hs
      simp_rw [← cubeWalsh_eq_boolMaskCharacter]
      rw [← Finset.sum_mul]

theorem sourceOrderedTupleCoefficient_degree
    {n k : ℕ} (a : SourceOrderedTuple n k → ℝ) (s : Cube n)
    (hc : sourceOrderedTupleCoefficient a s ≠ 0) :
    cubeWalshDegree n s = k := by
  classical
  have hwitness : ∃ t : SourceOrderedTuple n k,
      sourceOrderedTupleMask t = s ∧ a t ≠ 0 := by
    by_contra h
    have hterm : ∀ t : SourceOrderedTuple n k,
        (if sourceOrderedTupleMask t = s then a t else 0) = 0 := by
      intro t
      by_cases hts : sourceOrderedTupleMask t = s
      · have hzero : a t = 0 := by
          by_contra hne
          exact h ⟨t, hts, hne⟩
        simp [hts, hzero]
      · simp [hts]
    have hsum :
        (∑ t : SourceOrderedTuple n k,
          if sourceOrderedTupleMask t = s then a t else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      exact hterm t
    exact hc (by simpa [sourceOrderedTupleCoefficient] using hsum)
  rcases hwitness with ⟨t, rfl, ha⟩
  change cubeWalshDegree n
    (sourceSupportMask ((Finset.univ : Finset (Fin k)).image t.1)) = k
  rw [cubeWalshDegree_sourceSupportMask]
  rw [Finset.card_image_of_injective _ t.2]
  simp

def sourceMixedDegreeWeight (k : ℕ) : ℝ :=
  (k : ℝ) ^ 3 * ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1)

/-- The squared energy carried by exactly Walsh degree `r+1`. -/
def sourceMixedDegreeLevelEnergy {n k : ℕ}
    (c : Cube n → ℝ) (r : Fin k) : ℝ :=
  ∑ s : Cube n,
    if cubeWalshDegree n s = r.val + 1 then c s ^ 2 else 0

private lemma levelMaskEnergy_partition
    {n k : ℕ} (c : Cube n → ℝ)
    (hc : ∀ s, c s ≠ 0 →
      1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k) :
    ∀ s : Cube n,
      (∑ r : Fin k,
        if cubeWalshDegree n s = r.val + 1 then c s ^ 2 else 0) = c s ^ 2 := by
  intro s
  by_cases hcs : c s = 0
  · simp [hcs]
  · have hds := hc s hcs
    let r : Fin k := ⟨cubeWalshDegree n s - 1, by omega⟩
    have hr : r.val + 1 = cubeWalshDegree n s := by
      dsimp [r]
      omega
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro q hq hqr
      have hdegree_ne : cubeWalshDegree n s ≠ q.val + 1 := by
        intro hdegree
        apply hqr
        apply Fin.ext
        omega
      simp [hdegree_ne]
    · intro hnot
      exact (hnot (Finset.mem_univ r)).elim

private lemma sourceMixedDegreeLevelEnergy_sum
    {n k : ℕ} (c : Cube n → ℝ)
    (hc : ∀ s, c s ≠ 0 →
      1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k) :
    (∑ r : Fin k, sourceMixedDegreeLevelEnergy c r) =
      ∑ s : Cube n, c s ^ 2 := by
  unfold sourceMixedDegreeLevelEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  exact levelMaskEnergy_partition c hc s

private lemma pow_le_sourceMixedDegreeWeight {k : ℕ} (hk : 0 < k) :
    (9 : ℝ) ^ k ≤ sourceMixedDegreeWeight k := by
  have hklt : k - 1 < k := Nat.sub_lt hk (by omega)
  have hterm : (9 : ℝ) ^ ((k - 1) + 1) ≤
      ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1) := by
    exact Finset.single_le_sum
      (s := Finset.range k)
      (f := fun r : ℕ => (9 : ℝ) ^ (r + 1))
      (fun r hr => by positivity)
      (Finset.mem_range.mpr hklt)
  have hpow : k - 1 + 1 = k := by omega
  have hweight_nonneg :
      0 ≤ ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1) := by
    apply Finset.sum_nonneg
    intro r hr
    positivity
  have hkcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))
  have hkcube : (1 : ℝ) ≤ (k : ℝ) ^ 3 := by
    have hfac : (k : ℝ) ^ 3 - 1 = ((k : ℝ) - 1) * ((k : ℝ) ^ 2 + (k : ℝ) + 1) := by ring
    have hright : 0 ≤ (k : ℝ) ^ 2 + (k : ℝ) + 1 := by positivity
    have hleft : 0 ≤ (k : ℝ) - 1 := by linarith
    have hdiff : 0 ≤ (k : ℝ) ^ 3 - 1 := by
      rw [hfac]
      exact mul_nonneg hleft hright
    linarith
  have hterm' : (9 : ℝ) ^ k ≤
      ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1) := by
    simpa [hpow] using hterm
  unfold sourceMixedDegreeWeight
  calc
    (9 : ℝ) ^ k ≤ ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1) := hterm'
    _ = 1 * (∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1)) := by ring
    _ ≤ (k : ℝ) ^ 3 * (∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1)) :=
      mul_le_mul_of_nonneg_right hkcube hweight_nonneg

private lemma cubeWalshPolynomial_mean_zero_of_positive_degree
    {n : ℕ} (c : Cube n → ℝ)
    (hc : ∀ s, c s ≠ 0 → 1 ≤ cubeWalshDegree n s) :
    cubeAvg (cubeWalshPolynomial c) = 0 := by
  classical
  let z : Cube n := fun _ => false
  have hzero_char (s : Cube n) :
      ∫ ω, cubeWalsh n s ω ∂selectorLaw (Fin n) = if s = z then 1 else 0 := by
    calc
      ∫ ω, cubeWalsh n s ω ∂selectorLaw (Fin n) =
          ∫ ω, boolMaskCharacter s ω * boolMaskCharacter z ω ∂selectorLaw (Fin n) := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [cubeWalsh_eq_boolMaskCharacter]
        simp [boolMaskCharacter, boolMaskSupport, rademacherCharacter, z]
      _ = if s = z then 1 else 0 := integral_boolMaskCharacter_mul s z
  calc
    cubeAvg (cubeWalshPolynomial c) =
        ∫ ω, cubeWalshPolynomial c ω ∂selectorLaw (Fin n) :=
      cubeAvg_eq_selectorLaw_integral _
    _ = ∑ s : Cube n, c s *
          (∫ ω, cubeWalsh n s ω ∂selectorLaw (Fin n)) := by
      unfold cubeWalshPolynomial
      rw [integral_finsetSum _ (fun s _ =>
        (Integrable.of_finite : Integrable
          (fun ω : Cube n => cubeWalsh n s ω) (selectorLaw (Fin n))).const_mul (c s))]
      simp_rw [integral_const_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      by_cases hcs : c s = 0
      · simp [hcs]
      · have hsne : s ≠ z := by
          intro heq
          subst s
          have hpos := hc z hcs
          have hzdegree : cubeWalshDegree n z = 0 := by
            rw [cubeWalshDegree_eq_support_card]
            simp [boolMaskSupport, z]
          rw [hzdegree] at hpos
          omega
        simp [hzero_char s, hsne]

/--
For explicit scalar Walsh coefficients supported on degrees `1,…,k`, the
finite-cube polynomial is centered, its variance is its coefficient square
sum, and its fourth moment has the source-compatible mixed-degree bound.
This is the moment premise consumed by
`translated_cube_norm_event_of_scalar_moments` after scalarizing a fixed
Banach-valued polynomial with Hahn–Banach.
-/
theorem source_scalar_mixed_degree_moments
    {n k : ℕ} (hk : 0 < k) (c : Cube n → ℝ)
    (hc : ∀ s, c s ≠ 0 →
      1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k) :
    cubeAvg (cubeWalshPolynomial c) = 0 ∧
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) = ∑ s : Cube n, c s ^ 2 ∧
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) =
      ∑ r : Fin k, sourceMixedDegreeLevelEnergy c r ∧
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 4) ≤
      sourceMixedDegreeWeight k *
        (cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2)) ^ 2 := by
  have hmean : cubeAvg (cubeWalshPolynomial c) = 0 :=
    cubeWalshPolynomial_mean_zero_of_positive_degree c (fun s hs => (hc s hs).1)
  have hparseval := cubeWalshPolynomial_parseval c
  have hρ : (Real.sqrt (1 / 3 : ℝ)) ^ 2 = 1 / 3 := by
    exact Real.sq_sqrt (by norm_num)
  have hfour := cubeWalshPolynomial_fourth_le_of_degree
    n k c (Real.sqrt (1 / 3 : ℝ)) hρ (fun s hs => (hc s hs).2)
  have hfactor : (9 : ℝ) ^ k ≤ sourceMixedDegreeWeight k :=
    pow_le_sourceMixedDegreeWeight hk
  have hfactor_mul := mul_le_mul_of_nonneg_right hfactor
    (sq_nonneg (cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2)))
  have hlevels :
      cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) =
        ∑ r : Fin k, sourceMixedDegreeLevelEnergy c r := by
    rw [hparseval]
    exact (sourceMixedDegreeLevelEnergy_sum c hc).symm
  exact ⟨hmean, hparseval, hlevels,
    hfour.trans (by simpa using hfactor_mul)⟩

/-- In dimension zero, positive-degree support forces every Walsh coefficient to vanish. -/
theorem cube_zero_coefficients_of_positive_degree
    (c : Cube 0 → ℝ)
    (hc : ∀ s, c s ≠ 0 → 1 ≤ cubeWalshDegree 0 s) :
    ∀ s, c s = 0 := by
  intro s
  by_contra hs
  have hpos := hc s hs
  have hdeg : cubeWalshDegree 0 s = 0 := by
    simp [cubeWalshDegree, boolMaskSupport]
  omega

/-- Separate degenerate maximum-degree case: no positive-degree coefficients can occur. -/
theorem source_scalar_degree_zero_moments
    {n : ℕ} (c : Cube n → ℝ)
    (hc : ∀ s, c s ≠ 0 →
      1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ 0) :
    (∀ s, c s = 0) ∧
    cubeAvg (cubeWalshPolynomial c) = 0 ∧
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) = 0 ∧
    cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 4) = 0 := by
  have hc0 : ∀ s, c s = 0 := by
    intro s
    by_contra hne
    have h := hc s hne
    omega
  have hpoly : cubeWalshPolynomial c = fun _ => 0 := by
    funext ω
    simp [cubeWalshPolynomial, hc0]
  exact ⟨hc0, by simp [hpoly, cubeAvg, avgOn], by simp [hpoly, cubeAvg, avgOn],
    by simp [hpoly, cubeAvg, avgOn]⟩

/--
The checked moment input specialized directly to an arbitrary ordered
injective-tuple polynomial. The tuple coefficient `a t` may depend on the
entire ordered tuple; no permutation invariance is imposed. Grouping by the
parity mask gives a homogeneous degree-`k` Walsh polynomial, so it is included
in the more general levels-`1,…,k` statement above.
-/
theorem source_ordered_tuple_mixed_degree_moments
    {n k : ℕ} (hk : 0 < k)
    (a : SourceOrderedTuple n k → ℝ) :
    cubeAvg (sourceOrderedTuplePolynomial a) = 0 ∧
    cubeAvg (fun ω => sourceOrderedTuplePolynomial a ω ^ 2) =
      ∑ s : Cube n, (sourceOrderedTupleCoefficient a s) ^ 2 ∧
    cubeAvg (fun ω => sourceOrderedTuplePolynomial a ω ^ 2) =
      ∑ r : Fin k, sourceMixedDegreeLevelEnergy
        (sourceOrderedTupleCoefficient a) r ∧
    cubeAvg (fun ω => sourceOrderedTuplePolynomial a ω ^ 4) ≤
      sourceMixedDegreeWeight k *
        (cubeAvg (fun ω => sourceOrderedTuplePolynomial a ω ^ 2)) ^ 2 := by
  have h := source_scalar_mixed_degree_moments hk
    (sourceOrderedTupleCoefficient a)
    (fun s hs => by
      have hdeg := sourceOrderedTupleCoefficient_degree a s hs
      exact ⟨by omega, by omega⟩)
  rcases h with ⟨hmean, hparseval, hlevels, hfour⟩
  have hpoly : sourceOrderedTuplePolynomial a =
      cubeWalshPolynomial (sourceOrderedTupleCoefficient a) := by
    funext ω
    exact sourceOrderedTuplePolynomial_eq_walsh a ω
  exact ⟨by rw [hpoly]; exact hmean,
    by simpa only [hpoly] using hparseval,
    by simpa only [hpoly] using hlevels,
    by simpa only [hpoly] using hfour⟩

#print DGRHS.Decoupling.FiniteCube.source_scalar_mixed_degree_moments
#print DGRHS.Decoupling.FiniteCube.source_scalar_degree_zero_moments
#print DGRHS.Decoupling.FiniteCube.source_ordered_tuple_mixed_degree_moments
#print axioms DGRHS.Decoupling.FiniteCube.source_scalar_mixed_degree_moments
#print axioms DGRHS.Decoupling.FiniteCube.source_scalar_degree_zero_moments
#print axioms DGRHS.Decoupling.FiniteCube.source_ordered_tuple_mixed_degree_moments

end DGRHS.Decoupling.FiniteCube
