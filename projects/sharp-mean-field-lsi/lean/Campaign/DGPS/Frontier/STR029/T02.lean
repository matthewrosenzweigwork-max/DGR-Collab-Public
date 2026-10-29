import Mathlib.Algebra.QuadraticDiscriminant
import DGPS.Frontier.STR029.T34

/-!
# STR029.02: Complementary Fourier quadratic inequalities

Task id: STR029.02. Title: Complementary Fourier quadratic inequalities (node STR029, size M).

Provides:
* `DGPS.Frontier.STR029.continuous_trigPoly_STR02902`: a trigonometric polynomial is continuous.
* `DGPS.Frontier.STR029.integrable_mul_trigPoly_STR02902`: `u * p` is integrable when `u` is integrable and `p` is a
  trigonometric polynomial.
* `DGPS.Frontier.STR029.normInt_sub_STR02902`: the normalized integral of a difference is the difference of the
  normalized integrals, for integrable summands.
* `DGPS.Frontier.STR029.normInt_sq_trigPoly_STR02902`: `∫ p^2 dm = (1/2) ∑ (a_k^2 + b_k^2)` for `p` the mean-zero
  trigonometric polynomial with coefficients `a, b` over `k < N` at frequencies `k + 1`.
* `DGPS.Frontier.STR029.normInt_sq_deriv_trigPoly_STR02902`: `∫ p'^2 dm = (1/2) ∑ (k+1)^2 (a_k^2 + b_k^2)` for the
  same mean-zero trigonometric polynomial `p`.
* `DGPS.Frontier.STR029.lam_nonneg_STR02902`: the weight `(k+1)^2 - 1` is nonnegative for every `k : ℕ`.
* `DGPS.Frontier.STR029.quad_nonneg_imp_STR02902`: a real quadratic that is nonnegative on `ℝ` satisfies `B^2 ≤ A C`.
* `DGPS.Frontier.STR029.cs_weighted_STR02902`: Cauchy-Schwarz for finite sums with nonnegative weights.
* `DGPS.Frontier.STR029.final_ineq_STR02902`: the closing arithmetic step `(S/2)^2 ≤ (T/2)(Q/2)`.
* `DGPS.Frontier.STR029.str029_02_complementary_fourier_quadratic_inequalities`: for a periodic `H^1` function `w`
  orthogonal to `1, cos t, sin t`, the inequalities `B0(w) ≥ 3 ‖w‖_2^2`, `∫(w'^2 + w^2) ≤ (5/3) B0(w)`, and, for every
  complementary trigonometric polynomial `v`, `B0(w, v)^2 ≤ B0(w) B0(v)`.

R5 notes:
* Carriers: `w` and its weak derivative `g` are concrete `2π`-periodic functions `ℝ → ℝ` in the sense of
  `IsPeriodicWeakDerivative_STR02933` (STR029.33): periodic `L^2` functions on `(0, 2π]`, with `g` the weak derivative
  against all smooth periodic tests. The weak derivative is the given `g`; no existence or uniqueness is used.
* Measure: `∫ f dm` is `normInt_STR02933 f = (2π)⁻¹ ∫_{(0,2π]} f`. The norm is `‖w‖_2^2 = ∫ w^2 dm`, and
  `B0(w) = ∫ (w'^2 - w^2) dm` is written with `g` in place of `w'`.
* Orthogonality of `w` to `1, cos t, sin t` is read literally in the normalized inner product:
  `∫ w dm = 0`, `∫ w cos t dm = 0`, `∫ w sin t dm = 0`. The hypotheses `h0`, `hc`, `hs` are exactly these.
  The proof uses `hc`, `hs` only at frequency one, to make the zero-frequency term of the Parseval series vanish.
* "Complementary trigonometric polynomial" is read as a real trigonometric polynomial
  `v = a0 + ∑_{k<N} (a_k cos((k+1) t) + b_k sin((k+1) t))` (`trigPoly_STR02934`) that is orthogonal to `1, cos t, sin t`
  in the same sense as `w`. The proof uses only `∫ v dm = 0`, that is `a0 = 0`. The frequency-one weight `1^2 - 1`
  vanishes, so the first-harmonic orthogonality of `v` is not used. Those two hypotheses are kept for faithfulness to
  the complementary class and are bound as `_` in the proof.
* `v'` in `B0(v)` and `B0(w, v) = ∫ (w' v' - w v) dm` is the classical derivative `deriv v`, valid since `v` is smooth.
  The pairing is written `g t * deriv v t - w t * v t`.
* The Cauchy-Schwarz bound is stated for the square of the integral, using the real `^ 2`.
* Constants `3` and `5/3` are as specified. The termwise bound `4 c_n ≤ (n+1)^2 c_n` uses `n+1 ≥ 2` for `n ≥ 1`, and
  for `n = 0` the bound holds because `c_0 = cosCoeff w 1 ^ 2 + sinCoeff w 1 ^ 2 = 0` by orthogonality.
* Inputs: Parseval identities and the bilinear identities from STR029.34, and integrability from `MemLp` via
  STR029.34. The Bochner convention (value `0` when not integrable) is not relied on: every integrand used is
  integrable on `Ioc 0 (2π)`.
* The interval is `(0, 2π]` rather than `[0, 2π)`, as in STR029.33; the endpoint is a null set.
-/

open MeasureTheory Set Real

namespace DGPS.Frontier.STR029

/-- A trigonometric polynomial is continuous. -/
theorem continuous_trigPoly_STR02902 (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) :
    Continuous (trigPoly_STR02934 a0 a b N) := by
  change Continuous fun t => a0 + ∑ k ∈ Finset.range N,
    (a k * Real.cos (((k + 1 : ℕ) : ℝ) * t) + b k * Real.sin (((k + 1 : ℕ) : ℝ) * t))
  fun_prop

/-- Multiplying an integrable function by a trigonometric polynomial keeps integrability. -/
theorem integrable_mul_trigPoly_STR02902 {u : ℝ → ℝ}
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π)))) (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) :
    Integrable (fun t => u t * trigPoly_STR02934 a0 a b N t) (volume.restrict (Ioc 0 (2 * π))) := by
  have e : (fun t => u t * trigPoly_STR02934 a0 a b N t) = fun t => a0 * u t + ∑ k ∈ Finset.range N,
      (a k * (u t * Real.cos (((k + 1 : ℕ) : ℝ) * t)) + b k * (u t * Real.sin (((k + 1 : ℕ) : ℝ) * t))) := by
    funext t
    simp only [trigPoly_STR02934, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k ∈ Finset.range N, Integrable (fun t => a k * (u t * Real.cos (((k + 1 : ℕ) : ℝ) * t))
      + b k * (u t * Real.sin (((k + 1 : ℕ) : ℝ) * t))) (volume.restrict (Ioc 0 (2 * π))) :=
    fun k _ => ((integrable_mul_cos_STR02934 hu _).const_mul (a k)).add
      ((integrable_mul_sin_STR02934 hu _).const_mul (b k))
  rw [e]
  exact (hu.const_mul a0).add (integrable_finsetSum _ hk)

/-- The normalized integral of a difference of integrable functions is the difference of the integrals. -/
theorem normInt_sub_STR02902 {f h : ℝ → ℝ}
    (hf : Integrable f (volume.restrict (Ioc 0 (2 * π))))
    (hh : Integrable h (volume.restrict (Ioc 0 (2 * π)))) :
    normInt_STR02933 (fun t => f t - h t) = normInt_STR02933 f - normInt_STR02933 h := by
  unfold normInt_STR02933
  rw [integral_sub hf hh]
  ring

/-- Parseval identity for the square of a mean-zero trigonometric polynomial. -/
theorem normInt_sq_trigPoly_STR02902 (a b : ℕ → ℝ) (N : ℕ) :
    normInt_STR02933 (fun t => trigPoly_STR02934 0 a b N t ^ 2)
      = (1 / 2) * ∑ k ∈ Finset.range N, (a k ^ 2 + b k ^ 2) := by
  have hI := integrable_continuous_STR02934 (continuous_trigPoly_STR02902 0 a b N)
  have e : normInt_STR02933 (fun t => trigPoly_STR02934 0 a b N t ^ 2)
      = normInt_STR02933 (fun t => trigPoly_STR02934 0 a b N t * trigPoly_STR02934 0 a b N t) := by
    congr 1
    funext t
    ring
  rw [e, normInt_mul_trigPoly_STR02934 hI 0 a b N, zero_mul, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hlt : k < N := Finset.mem_range.mp hk
  simp only [cosCoeff_trigPoly_STR02934, sinCoeff_trigPoly_STR02934, hlt, ↓reduceIte]
  ring

/-- Parseval identity for the square of the derivative of a mean-zero trigonometric polynomial. -/
theorem normInt_sq_deriv_trigPoly_STR02902 (a b : ℕ → ℝ) (N : ℕ) :
    normInt_STR02933 (fun t => deriv (trigPoly_STR02934 0 a b N) t ^ 2)
      = (1 / 2) * ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 * (a k ^ 2 + b k ^ 2)) := by
  simp only [deriv_trigPoly_STR02934]
  rw [normInt_sq_trigPoly_STR02902]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The weight `(k+1)^2 - 1` is nonnegative. -/
theorem lam_nonneg_STR02902 (k : ℕ) : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 - 1 := by
  have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 k
  nlinarith

/-- A real quadratic that is nonnegative on `ℝ` satisfies `B^2 ≤ A C`. -/
theorem quad_nonneg_imp_STR02902 {A B C : ℝ}
    (h : ∀ y : ℝ, 0 ≤ A * (y * y) + (-2 * B) * y + C) : B ^ 2 ≤ A * C := by
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

/-- Cauchy-Schwarz for finite sums with nonnegative weights. -/
theorem cs_weighted_STR02902 (N : ℕ) (lam x z a b : ℕ → ℝ) (hlam : ∀ k, 0 ≤ lam k) :
    (∑ k ∈ Finset.range N, lam k * (a k * x k + b k * z k)) ^ 2 ≤
      (∑ k ∈ Finset.range N, lam k * (x k ^ 2 + z k ^ 2)) *
        (∑ k ∈ Finset.range N, lam k * (a k ^ 2 + b k ^ 2)) := by
  have hq := quad_nonneg_imp_STR02902
    (A := ∑ k ∈ Finset.range N, lam k * (a k ^ 2 + b k ^ 2))
    (B := ∑ k ∈ Finset.range N, lam k * (a k * x k + b k * z k))
    (C := ∑ k ∈ Finset.range N, lam k * (x k ^ 2 + z k ^ 2)) (fun y => by
      have hnn : 0 ≤ ∑ k ∈ Finset.range N, lam k * ((x k - y * a k) ^ 2 + (z k - y * b k) ^ 2) :=
        Finset.sum_nonneg fun k _ => mul_nonneg (hlam k) (add_nonneg (sq_nonneg _) (sq_nonneg _))
      have e : (∑ k ∈ Finset.range N, lam k * (a k ^ 2 + b k ^ 2)) * (y * y)
          + (-2 * ∑ k ∈ Finset.range N, lam k * (a k * x k + b k * z k)) * y
          + ∑ k ∈ Finset.range N, lam k * (x k ^ 2 + z k ^ 2)
          = ∑ k ∈ Finset.range N, lam k * ((x k - y * a k) ^ 2 + (z k - y * b k) ^ 2) := by
        simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      linarith [e, hnn])
  linarith [hq, mul_comm (∑ k ∈ Finset.range N, lam k * (x k ^ 2 + z k ^ 2))
    (∑ k ∈ Finset.range N, lam k * (a k ^ 2 + b k ^ 2))]

/-- Closing arithmetic step for the bilinear estimate. -/
theorem final_ineq_STR02902 (S P Q T : ℝ) (hcs : S ^ 2 ≤ P * Q) (hPT : P ≤ T) (hQ : 0 ≤ Q) :
    (1 / 2 * S) ^ 2 ≤ 1 / 2 * T * (1 / 2 * Q) := by
  nlinarith [mul_le_mul_of_nonneg_right hPT hQ]

/-- STR029.02. For a periodic `H^1` function `w` (weak derivative `g`) orthogonal to `1, cos t, sin t`,
`B0(w) = ∫ (g^2 - w^2) dm` satisfies `3 ∫ w^2 dm ≤ B0(w)` and `∫ (g^2 + w^2) dm ≤ (5/3) B0(w)`. For every
complementary trigonometric polynomial `v` (orthogonal to `1, cos t, sin t`), the bilinear form
`B0(w, v) = ∫ (g v' - w v) dm` satisfies `B0(w, v)^2 ≤ B0(w) B0(v)`, with `B0(v) = ∫ (v'^2 - v^2) dm`. -/
theorem str029_02_complementary_fourier_quadratic_inequalities
    (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g)
    (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0) :
    3 * normInt_STR02933 (fun t => w t ^ 2) ≤ normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2) ∧
      normInt_STR02933 (fun t => g t ^ 2 + w t ^ 2)
        ≤ 5 / 3 * normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2) ∧
      ∀ v : ℝ → ℝ,
        (∃ (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ), v = trigPoly_STR02934 a0 a b N) →
        normInt_STR02933 v = 0 →
        normInt_STR02933 (fun t => v t * Real.cos t) = 0 →
        normInt_STR02933 (fun t => v t * Real.sin t) = 0 →
        (normInt_STR02933 (fun t => g t * deriv v t - w t * v t)) ^ 2 ≤
          normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2) *
            normInt_STR02933 (fun t => deriv v t ^ 2 - v t ^ 2) := by
  have hwi : Integrable w (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_of_memLp_STR02934 hwg.1.2
  have hgi : Integrable g (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_of_memLp_STR02934 hwg.2.1.2
  have hw2 : Integrable (fun t => w t ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
    hwg.1.2.integrable_sq
  have hg2 : Integrable (fun t => g t ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
    hwg.2.1.2.integrable_sq
  obtain ⟨⟨hS1, hW⟩, ⟨hS2, hG⟩⟩ :=
    str029_34_parseval_adapter_periodic_weak_domain_parseval w g hwg h0
  have hc1 : cosCoeff_STR02933 w 1 = 0 := by
    have e : cosCoeff_STR02933 w 1 = 2 * normInt_STR02933 (fun t => w t * Real.cos t) := by
      unfold cosCoeff_STR02933
      norm_num
    rw [e, hc, mul_zero]
  have hs1 : sinCoeff_STR02933 w 1 = 0 := by
    have e : sinCoeff_STR02933 w 1 = 2 * normInt_STR02933 (fun t => w t * Real.sin t) := by
      unfold sinCoeff_STR02933
      norm_num
    rw [e, hs, mul_zero]
  have hcoef : ∀ n : ℕ,
      4 * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)
        ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2) := by
    intro n
    have hnn : 0 ≤ cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2 := by
      positivity
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hc1, hs1]
    · have h2 : (4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
        have h3 : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 2 ≤ n + 1 by omega)
        nlinarith
      exact mul_le_mul_of_nonneg_right h2 hnn
  have hT : 4 * ∑' n : ℕ, (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)
      ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2
          * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2) := by
    rw [← Summable.tsum_mul_left 4 hS1]
    exact Summable.tsum_le_tsum hcoef (Summable.mul_left 4 hS1) hS2
  have hsubw : normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2)
      = normInt_STR02933 (fun t => g t ^ 2) - normInt_STR02933 (fun t => w t ^ 2) :=
    normInt_sub_STR02902 hg2 hw2
  have hsumw : normInt_STR02933 (fun t => g t ^ 2 + w t ^ 2)
      = normInt_STR02933 (fun t => g t ^ 2) + normInt_STR02933 (fun t => w t ^ 2) :=
    normInt_add_STR02934 hg2 hw2
  have hsumm : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2 - 1)
      * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)) :=
    (hS2.sub hS1).congr fun n => by ring
  have hTl : ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 2 - 1)
      * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)
      = (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2
          * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2))
        - ∑' n : ℕ, (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2) := by
    rw [← hS2.tsum_sub hS1]
    exact tsum_congr fun n => by ring
  have hBw : normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2)
      = 1 / 2 * ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 2 - 1)
          * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2) := by
    rw [hsubw, hG, hW, hTl]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hsubw, hG, hW]
    linarith
  · rw [hsumw, hsubw, hG, hW]
    linarith
  · intro v hv hv0 _ _
    obtain ⟨a0, a, b, N, rfl⟩ := hv
    rw [normInt_trigPoly_STR02934] at hv0
    subst hv0
    obtain ⟨hB1, hB2, -⟩ :=
      str029_34_parseval_adapter_periodic_weak_domain_bilinear w g hwg h0 0 a b N
    have hgv : Integrable (fun t => g t * deriv (trigPoly_STR02934 0 a b N) t)
        (volume.restrict (Ioc 0 (2 * π))) := by
      simp only [deriv_trigPoly_STR02934]
      exact integrable_mul_trigPoly_STR02902 hgi _ _ _ _
    have hwv : Integrable (fun t => w t * trigPoly_STR02934 0 a b N t)
        (volume.restrict (Ioc 0 (2 * π))) :=
      integrable_mul_trigPoly_STR02902 hwi _ _ _ _
    have hdv2 : Integrable (fun t => deriv (trigPoly_STR02934 0 a b N) t ^ 2)
        (volume.restrict (Ioc 0 (2 * π))) := by
      simp only [deriv_trigPoly_STR02934]
      exact integrable_continuous_STR02934 ((continuous_trigPoly_STR02902 _ _ _ _).pow 2)
    have hv2 : Integrable (fun t => trigPoly_STR02934 0 a b N t ^ 2)
        (volume.restrict (Ioc 0 (2 * π))) :=
      integrable_continuous_STR02934 ((continuous_trigPoly_STR02902 0 a b N).pow 2)
    have hBwv : normInt_STR02933 (fun t => g t * deriv (trigPoly_STR02934 0 a b N) t
          - w t * trigPoly_STR02934 0 a b N t)
        = 1 / 2 * ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 - 1)
            * (a k * cosCoeff_STR02933 w (k + 1) + b k * sinCoeff_STR02933 w (k + 1)) := by
      rw [normInt_sub_STR02902 hgv hwv, hB2, hB1, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hBv : normInt_STR02933 (fun t => deriv (trigPoly_STR02934 0 a b N) t ^ 2
          - trigPoly_STR02934 0 a b N t ^ 2)
        = 1 / 2 * ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 - 1) * (a k ^ 2 + b k ^ 2) := by
      rw [normInt_sub_STR02902 hdv2 hv2, normInt_sq_deriv_trigPoly_STR02902,
        normInt_sq_trigPoly_STR02902, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hPT : ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 - 1)
          * (cosCoeff_STR02933 w (k + 1) ^ 2 + sinCoeff_STR02933 w (k + 1) ^ 2)
        ≤ ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ 2 - 1)
          * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2) :=
      Summable.sum_le_tsum _ (fun n _ => mul_nonneg (lam_nonneg_STR02902 n)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))) hsumm
    have hQ : 0 ≤ ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 - 1) * (a k ^ 2 + b k ^ 2) :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (lam_nonneg_STR02902 k) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hcs : (∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 - 1)
          * (a k * cosCoeff_STR02933 w (k + 1) + b k * sinCoeff_STR02933 w (k + 1))) ^ 2
        ≤ (∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 - 1)
            * (cosCoeff_STR02933 w (k + 1) ^ 2 + sinCoeff_STR02933 w (k + 1) ^ 2))
          * (∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2 - 1) * (a k ^ 2 + b k ^ 2)) :=
      cs_weighted_STR02902 N (fun k => ((k + 1 : ℕ) : ℝ) ^ 2 - 1)
        (fun k => cosCoeff_STR02933 w (k + 1)) (fun k => sinCoeff_STR02933 w (k + 1)) a b
        lam_nonneg_STR02902
    rw [hBwv, hBw, hBv]
    exact final_ineq_STR02902 _ _ _ _ hcs hPT hQ

end DGPS.Frontier.STR029
