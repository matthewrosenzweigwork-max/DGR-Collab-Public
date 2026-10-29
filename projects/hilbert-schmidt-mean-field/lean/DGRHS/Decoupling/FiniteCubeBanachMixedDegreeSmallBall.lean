import DGRHS.Decoupling.FiniteCubeScalarMixedDegreeMoments
import DGRHS.Decoupling.TranslatedBanachSmallBall

/-!
Mixed-degree Banach-valued Walsh adapter for the checked scalar moment and
translated small-ball results. Scalarizing a finite Banach Walsh polynomial
produces an ordinary scalar Walsh polynomial, so the checked mixed-degree
estimate applies uniformly to every continuous linear functional.

Pinned inputs:
* `FiniteCubeScalarMixedDegreeMoments.lean`, SHA-256
  `7adc3ec4b6a46e68e2fb1353494a359069b8d1523cfeca1e566b2a0d22549a52`;
* `TranslatedBanachSmallBall.lean`, SHA-256
  `3186c63e2ec136508d9beea2a5a0ddd8e31b70d74ba47e000bf51f3356ae0bd0`.
-/

noncomputable section
open DGRHS.Decoupling.FiniteCube

namespace DGRHS.Decoupling.FiniteCube

/-- The finite Banach-valued Walsh polynomial with coefficient map `v`. -/
def sourceBanachWalshPolynomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (v : Cube n → E) : Cube n → E :=
  fun ω => ∑ s : Cube n, (cubeWalsh n s ω) • v s

theorem sourceBanachWalshPolynomial_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (v : Cube n → E) (φ : StrongDual ℝ E) (ω : Cube n) :
    φ (sourceBanachWalshPolynomial v ω) =
      cubeWalshPolynomial (fun s => φ (v s)) ω := by
  classical
  simp [sourceBanachWalshPolynomial, cubeWalshPolynomial, map_sum, map_smul,
    mul_comm]

/--
For an `E`-valued Walsh polynomial supported in degrees `1,…,k`, every
translation has selector probability at least the reciprocal of four times
the source mixed-degree moment weight of not decreasing the norm.
-/
theorem translated_cube_norm_event_of_mixed_walsh_coefficients
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} (hk : 0 < k) (v : Cube n → E) (x : E)
    (hsupport : ∀ s, v s ≠ 0 →
      1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k) :
    cubeAvg (fun ω =>
      if ‖x + sourceBanachWalshPolynomial v ω‖ ≥ ‖x‖ then (1 : ℝ) else 0)
      ≥ 1 / (4 * sourceMixedDegreeWeight k) := by
  let A : ℝ := sourceMixedDegreeWeight k
  have hkcast : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))
  have hsum : (9 : ℝ) ≤
      ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1) := by
    simpa using (Finset.single_le_sum
      (s := Finset.range k)
      (f := fun r : ℕ => (9 : ℝ) ^ (r + 1))
      (fun r hr => by positivity)
      (Finset.mem_range.mpr hk))
  have hsum_nonneg : 0 ≤
      ∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1) := by
    apply Finset.sum_nonneg
    intro r hr
    positivity
  have hkcube : (1 : ℝ) ≤ (k : ℝ) ^ 3 := by
    have hfac : (k : ℝ) ^ 3 - 1 =
        ((k : ℝ) - 1) * ((k : ℝ) ^ 2 + (k : ℝ) + 1) := by ring
    have hleft : 0 ≤ (k : ℝ) - 1 := by linarith
    have hright : 0 ≤ (k : ℝ) ^ 2 + (k : ℝ) + 1 := by positivity
    have hdiff : 0 ≤ (k : ℝ) ^ 3 - 1 := by
      rw [hfac]
      exact mul_nonneg hleft hright
    linarith
  have hweight : (9 : ℝ) ≤ sourceMixedDegreeWeight k := by
    unfold sourceMixedDegreeWeight
    calc
      9 = 1 * 9 := by ring
      _ ≤ (k : ℝ) ^ 3 *
          (∑ r ∈ Finset.range k, (9 : ℝ) ^ (r + 1)) :=
        mul_le_mul hkcube hsum (by norm_num)
          (pow_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity) 3)
  have hA : 1 ≤ 4 * A := by
    dsimp [A]
    linarith
  apply translated_cube_norm_event_of_scalar_moments
    (P := sourceBanachWalshPolynomial v) x A hA
  · intro φ
    let c : Cube n → ℝ := fun s => φ (v s)
    have hc : ∀ s, c s ≠ 0 →
        1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k := by
      intro s hcs
      apply hsupport s
      intro hzero
      apply hcs
      simp [c, hzero]
    have hscalar := source_scalar_mixed_degree_moments hk c hc
    have hpoly : (fun ω => φ (sourceBanachWalshPolynomial v ω)) =
        cubeWalshPolynomial c := by
      funext ω
      exact sourceBanachWalshPolynomial_apply v φ ω
    change avgOn (fun ω => φ (sourceBanachWalshPolynomial v ω)) = 0
    rw [hpoly]
    simpa [cubeAvg, c] using hscalar.1
  · intro φ
    let c : Cube n → ℝ := fun s => φ (v s)
    have hc : ∀ s, c s ≠ 0 →
        1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k := by
      intro s hcs
      apply hsupport s
      intro hzero
      apply hcs
      simp [c, hzero]
    have hscalar := source_scalar_mixed_degree_moments hk c hc
    have hpoly : (fun ω => φ (sourceBanachWalshPolynomial v ω)) =
        cubeWalshPolynomial c := by
      funext ω
      exact sourceBanachWalshPolynomial_apply v φ ω
    change avgOn (fun ω => φ (sourceBanachWalshPolynomial v ω) ^ 4) ≤
      A * (avgOn (fun ω => φ (sourceBanachWalshPolynomial v ω) ^ 2)) ^ 2
    have hfour_eq : avgOn
        (fun ω => φ (sourceBanachWalshPolynomial v ω) ^ 4) =
        cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 4) := by
      unfold cubeAvg
      apply avgOn_congr
      intro ω
      rw [sourceBanachWalshPolynomial_apply]
    have htwo_eq : avgOn
        (fun ω => φ (sourceBanachWalshPolynomial v ω) ^ 2) =
        cubeAvg (fun ω => cubeWalshPolynomial c ω ^ 2) := by
      unfold cubeAvg
      apply avgOn_congr
      intro ω
      rw [sourceBanachWalshPolynomial_apply]
    rw [hfour_eq, htwo_eq]
    simpa [A, cubeAvg, c] using hscalar.2.2.2

#print DGRHS.Decoupling.FiniteCube.sourceBanachWalshPolynomial_apply
#print DGRHS.Decoupling.FiniteCube.translated_cube_norm_event_of_mixed_walsh_coefficients
#print axioms DGRHS.Decoupling.FiniteCube.sourceBanachWalshPolynomial_apply
#print axioms DGRHS.Decoupling.FiniteCube.translated_cube_norm_event_of_mixed_walsh_coefficients

end DGRHS.Decoupling.FiniteCube
