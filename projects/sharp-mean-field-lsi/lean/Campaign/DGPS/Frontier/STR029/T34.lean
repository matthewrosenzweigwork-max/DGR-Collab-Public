import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import DGPS.Frontier.STR029.T33

/-!
# STR029.34: Parseval adapter for the periodic weak domain

Task id: STR029.34. Title: Parseval adapter for the periodic weak domain (node STR029, size L).

Statement (specification): for `w` as in `.33` with `∫ w dm = 0`,
`∫ w² dm = ½ Σ_{n≥1} (c_n² + s_n²)` and `∫ w'² dm = ½ Σ_{n≥1} n² (c_n² + s_n²)`; the corresponding
bilinear identities hold against every finite trigonometric polynomial; the constant and the
normalized real trigonometric functions form a countable complete orthonormal basis of real `L²(m)`.

Provides:
* `DGPS.Frontier.STR029.str029_34_parseval_adapter_periodic_weak_domain`: the main theorem, for
  `IsPeriodicWeakDerivative_STR02933 w g` and `normInt_STR02933 w = 0`: the conjunction of the Parseval
  identities for `w` and `g` (with summability), of the coefficient identification and the three
  bilinear identities against every finite trigonometric polynomial, and of the Hilbert-basis statement.
* `DGPS.Frontier.STR029.str029_34_parseval_adapter_periodic_weak_domain_parseval`: both Parseval
  identities `∫ w² dm = ½ Σ_{n≥1} (c_n² + s_n²)` and `∫ g² dm = ½ Σ_{n≥1} n² (c_n² + s_n²)`, together with
  the summability of the two series (the coefficients `c_n, s_n` are those of `w`).
* `DGPS.Frontier.STR029.str029_34_parseval_adapter_periodic_weak_domain_bilinear`: for a finite
  trigonometric polynomial `p`, `∫ w p dm`, `∫ g p' dm` and `∫ g p dm` as finite sums of products of the
  coefficients of `p` with the coefficients `c_n, s_n` of `w`.
* `DGPS.Frontier.STR029.str029_34_parseval_adapter_periodic_weak_domain_trigPoly_coeff`: the mean of
  `trigPoly_STR02934 a0 a b N` is `a0` and its `(k+1)`-st cosine/sine coefficients are `a k` / `b k`
  (for `k < N`, else `0`), so the bilinear identities are pairings of coefficient sequences.
* `DGPS.Frontier.STR029.str029_34_parseval_adapter_periodic_weak_domain_basis`: the index type
  `Option (Bool × ℕ)` is countable and carries a `HilbertBasis` of `Lp ℝ 2 circleMeasure_STR02934`
  (real `L²(m)`) whose members are a.e. `1`, `√2 cos((k+1)t)` and `√2 sin((k+1)t)`.
* `DGPS.Frontier.STR029.trigPoly_STR02934`: the finite trigonometric polynomial
  `a0 + Σ_{k<N} (a k cos((k+1)t) + b k sin((k+1)t))`, used in the bilinear statements.
* `DGPS.Frontier.STR029.circleMeasure_STR02934`: the probability measure `m = dt/(2π)` on `(0, 2π]`
  as a `Measure ℝ`, used for the space `L²(m)` in the basis statement.
* `DGPS.Frontier.STR029.trigBasisFun_STR02934`: the enumeration `none ↦ 1`, `some (false,k) ↦ √2 cos((k+1)t)`,
  `some (true,k) ↦ √2 sin((k+1)t)` of the basis functions.

R5 notes:
* Hypotheses are exactly those of the specification: `w` is "as in `.33`", read as
  `IsPeriodicWeakDerivative_STR02933 w g` with `g` the weak derivative `w'` (the derivative in the variable
  `t`; `∫ w'² dm` is `∫ g² dm`), and `∫ w dm = 0` is `normInt_STR02933 w = 0`. No further hypothesis is added.
  The periodicity conjuncts inside `IsPeriodicWeakDerivative_STR02933` are not used by the proofs; only the
  `L²` memberships and the weak identity (through `.33`) are. Carriers, the period `(0, 2π]` and the
  normalization `dm = dt/(2π)` (as `normInt_STR02933`) are those of `.33`.
* The sums over `n ≥ 1` are written as sums over `n : ℕ` of the terms at `n + 1`, with the coefficients
  `cosCoeff_STR02933 w (n + 1)` and `sinCoeff_STR02933 w (n + 1)` (which carry the factor `2`, so the
  normalization `½ (c_n² + s_n²)` is the one of the specification). The `n²` weight is `((n + 1 : ℕ) : ℝ) ^ 2`.
* Non-literal addition: the conclusions also assert `Summable` for both series. Without it the `tsum`
  equalities would be unreliable (Mathlib's `tsum` of a non-summable series is `0`). This strengthens the
  conclusion and adds no hypothesis. The series for `w'` is stated with the coefficients of `w` and the
  weight `n²`; it equals the Parseval series of `g` by the coefficient relations of `.33`
  (`c_n(g) = n s_n(w)`, `s_n(g) = -n c_n(w)`), which is how `∫ g² dm` is evaluated.
* The mean-zero hypothesis is used twice: for `w` it removes the constant term in the Parseval sum (and
  the `a0` term in the pairings), and for `g` the mean zero comes from `.33`. The mean-zero reduction is
  also what lets the two-sided (`ℤ`) Parseval identity of Mathlib be folded into a sum over `n ≥ 1`.
* "Finite trigonometric polynomial" is read as `trigPoly_STR02934 a0 a b N`, the general real finite
  trigonometric polynomial (`N = 0` gives the constants). Its derivative is `deriv (trigPoly_STR02934 ..)`.
  "The corresponding bilinear identities" is read as the pairings `∫ w p dm`, `∫ w' p' dm` and `∫ w' p dm`.
  They are given as finite sums over `k < N` of products of the coefficients of `p` with `c_{k+1}, s_{k+1}`
  of `w` (the terms with `k ≥ N` vanish because `p` has no such coefficients), and, as in the specification,
  they are proved by finite linearity of the integral; `..._trigPoly_coeff` records that the `a k, b k` are the
  Fourier coefficients of `p`, so these are the bilinear Parseval pairings
  `∫ u v dm = u_0 v_0 + ½ Σ (c_n(u) c_n(v) + s_n(u) s_n(v))` restricted to the support of `p`.
* The basis statement is formalized as `Countable (Option (Bool × ℕ))` together with the existence of a
  `HilbertBasis (Option (Bool × ℕ)) ℝ (Lp ℝ 2 circleMeasure_STR02934)` (an orthonormal family with dense
  span, i.e. complete) whose members equal a.e. the functions `1`, `√2 cos((k+1)t)`, `√2 sin((k+1)t)`; real
  `L²(m)` is `Lp ℝ 2 circleMeasure_STR02934` with `circleMeasure_STR02934 = ofReal (2π)⁻¹ • volume.restrict (Ioc 0 (2π))`.
  "Normalized real trigonometric functions" means the factor `√2` (so that the `L²(m)`-norm is `1`); the
  elements of `Lp` are a.e. classes, hence the a.e. equalities.
* Proof route: the Fourier side is Mathlib's circle Parseval (`hasSum_sq_fourierCoeffOn`), applied to
  the complex-valued `ofReal ∘ u` on `[0, 2π]`. In the real notation the complex coefficient at `m : ℤ`
  is `(c_m - i s_m)/2`, with squared modulus `(c_m² + s_m²)/4`, which is even in `m`; the sum over `ℤ` is
  folded to a sum over `n ≥ 1` using this evenness and the vanishing of the `m = 0` term (this is where
  `∫ u dm = 0` enters), giving `∫ u² dm = ½ Σ_{n≥1} (c_n² + s_n²)`. For the basis, orthonormality is a
  product-to-sum computation, and completeness follows from the same Parseval: a real `L²` function
  orthogonal to all the displayed functions has all complex Fourier coefficients zero, so `∫ u² dm = 0` and
  `u = 0` a.e. (`HilbertBasis.mkOfOrthogonalEqBot`), as in the specification.
* All integrals are Bochner integrals (value `0` for non-integrable integrands); every integrand used is
  integrable because the functions are in `L²` on a finite measure space or are bounded and continuous.
-/

open MeasureTheory Set Real

namespace DGPS.Frontier.STR029

theorem integrable_of_memLp_STR02934 {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    Integrable u (volume.restrict (Ioc 0 (2 * π))) :=
  hu.integrable (by norm_num)

theorem integrable_mul_cos_STR02934 {u : ℝ → ℝ}
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π)))) (c : ℝ) :
    Integrable (fun t => u t * Real.cos (c * t)) (volume.restrict (Ioc 0 (2 * π))) :=
  hu.mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun t => by simpa using Real.abs_cos_le_one _)

theorem integrable_mul_sin_STR02934 {u : ℝ → ℝ}
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π)))) (c : ℝ) :
    Integrable (fun t => u t * Real.sin (c * t)) (volume.restrict (Ioc 0 (2 * π))) :=
  hu.mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun t => by simpa using Real.abs_sin_le_one _)

theorem fourierCoeffOn_ofReal_STR02934 (u : ℝ → ℝ)
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π)))) (m : ℤ) :
    fourierCoeffOn (Real.two_pi_pos : (0:ℝ) < 2 * π) (fun t => (u t : ℂ)) m
      = (normInt_STR02933 (fun t => u t * Real.cos (m * t)) : ℂ)
        - Complex.I * (normInt_STR02933 (fun t => u t * Real.sin (m * t)) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have h1 : ∀ x : ℝ, (fourier (-m) (x : AddCircle (2 * π - 0))) • (u x : ℂ)
      = ((u x * Real.cos (m * x) : ℝ) : ℂ) - Complex.I * ((u x * Real.sin (m * x) : ℝ) : ℂ) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul]
    have e : (2 * (π : ℂ) * Complex.I * ((-m : ℤ) : ℂ) * (x : ℂ) / ((2 * π - 0 : ℝ) : ℂ))
        = -((m * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
      ring
    rw [e, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  simp_rw [h1]
  have hi1 : IntervalIntegrable (fun x => ((u x * Real.cos (m * x) : ℝ) : ℂ)) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
    exact (integrable_mul_cos_STR02934 hu m).ofReal
  have hi2 : IntervalIntegrable (fun x => ((u x * Real.sin (m * x) : ℝ) : ℂ)) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
    exact (integrable_mul_sin_STR02934 hu m).ofReal
  rw [intervalIntegral.integral_sub hi1 (hi2.const_mul Complex.I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  unfold normInt_STR02933
  simp only [sub_zero, Complex.real_smul]
  push_cast
  ring

theorem hasSum_int_parseval_STR02934 {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    HasSum (fun m : ℤ => normInt_STR02933 (fun t => u t * Real.cos (m * t)) ^ 2
        + normInt_STR02933 (fun t => u t * Real.sin (m * t)) ^ 2)
      (normInt_STR02933 (fun t => u t ^ 2)) := by
  have hC : MemLp (fun t => (u t : ℂ)) 2 (volume.restrict (Ioc 0 (2 * π))) := hu.ofReal
  have h := hasSum_sq_fourierCoeffOn (Real.two_pi_pos : (0:ℝ) < 2 * π) hC
  have hint := integrable_of_memLp_STR02934 hu
  convert h using 1
  · funext m
    rw [fourierCoeffOn_ofReal_STR02934 u hint m, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  · unfold normInt_STR02933
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    simp [Complex.norm_real, smul_eq_mul]

theorem hasSum_nat_parseval_STR02934 {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) (hu0 : normInt_STR02933 u = 0) :
    HasSum (fun k : ℕ => cosCoeff_STR02933 u (k + 1) ^ 2 + sinCoeff_STR02933 u (k + 1) ^ 2)
      (2 * normInt_STR02933 (fun t => u t ^ 2)) := by
  set P : ℤ → ℝ := fun m => normInt_STR02933 (fun t => u t * Real.cos (m * t)) ^ 2
        + normInt_STR02933 (fun t => u t * Real.sin (m * t)) ^ 2 with hP
  have h : HasSum P (normInt_STR02933 (fun t => u t ^ 2)) := hasSum_int_parseval_STR02934 hu
  have hP0 : P 0 = 0 := by
    have e1 : (fun t => u t * Real.cos (((0 : ℤ) : ℝ) * t)) = u := by funext t; simp
    have e2 : (fun t => u t * Real.sin (((0 : ℤ) : ℝ) * t)) = fun _ => (0 : ℝ) := by
      funext t; simp
    simp only [hP, e1, e2, hu0]
    simp [normInt_STR02933]
  have hPneg : ∀ m : ℤ, P (-m) = P m := by
    intro m
    simp only [hP, Int.cast_neg, neg_mul, Real.cos_neg]
    rw [show (fun t => u t * Real.sin (-(↑m * t))) = fun t => (-1 : ℝ) * (u t * Real.sin (m * t)) by
      funext t; rw [Real.sin_neg]; ring, normInt_mul_const_STR02933]
    ring
  have h1 := h.nat_add_neg
  rw [hP0, add_zero] at h1
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, neg_zero, hP0, add_zero,
    sub_zero] at h2
  have h3 := h2.mul_left 2
  convert h3 using 1
  funext k
  rw [hPneg]
  simp only [hP, cosCoeff_STR02933, sinCoeff_STR02933]
  push_cast
  ring

/-- Finite trigonometric polynomial. -/
noncomputable def trigPoly_STR02934 (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  a0 + ∑ k ∈ Finset.range N,
    (a k * Real.cos (((k + 1 : ℕ) : ℝ) * t) + b k * Real.sin (((k + 1 : ℕ) : ℝ) * t))

theorem normInt_add_STR02934 {f g : ℝ → ℝ} (hf : Integrable f (volume.restrict (Ioc 0 (2 * π))))
    (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) :
    normInt_STR02933 (fun t => f t + g t) = normInt_STR02933 f + normInt_STR02933 g := by
  unfold normInt_STR02933
  rw [integral_add hf hg]
  ring

theorem normInt_sum_STR02934 {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i) (volume.restrict (Ioc 0 (2 * π)))) :
    normInt_STR02933 (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, normInt_STR02933 (f i) := by
  unfold normInt_STR02933
  rw [integral_finsetSum s hf, Finset.mul_sum]

theorem normInt_mul_trigPoly_STR02934 {u : ℝ → ℝ}
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π)))) (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) :
    normInt_STR02933 (fun t => u t * trigPoly_STR02934 a0 a b N t)
      = a0 * normInt_STR02933 u + (1 / 2) * ∑ k ∈ Finset.range N,
          (a k * cosCoeff_STR02933 u (k + 1) + b k * sinCoeff_STR02933 u (k + 1)) := by
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
  rw [e, normInt_add_STR02934 (hu.const_mul a0) (integrable_finsetSum _ hk),
    normInt_mul_const_STR02933, normInt_sum_STR02934 _ hk, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [normInt_add_STR02934 ((integrable_mul_cos_STR02934 hu _).const_mul (a k))
      ((integrable_mul_sin_STR02934 hu _).const_mul (b k)),
    normInt_mul_const_STR02933, normInt_mul_const_STR02933]
  simp only [cosCoeff_STR02933, sinCoeff_STR02933]
  ring

theorem hasDerivAt_trigPoly_STR02934 (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    HasDerivAt (trigPoly_STR02934 a0 a b N)
      (trigPoly_STR02934 0 (fun k => ((k + 1 : ℕ) : ℝ) * b k) (fun k => -(((k + 1 : ℕ) : ℝ) * a k)) N t) t := by
  have hk : ∀ k ∈ Finset.range N, HasDerivAt
      (fun s => a k * Real.cos (((k + 1 : ℕ) : ℝ) * s) + b k * Real.sin (((k + 1 : ℕ) : ℝ) * s))
      (((((k + 1 : ℕ) : ℝ) * b k) * Real.cos (((k + 1 : ℕ) : ℝ) * t))
        + (-(((k + 1 : ℕ) : ℝ) * a k)) * Real.sin (((k + 1 : ℕ) : ℝ) * t)) t := by
    intro k _
    have h1 := ((hasDerivAt_id t).const_mul (((k + 1 : ℕ) : ℝ))).cos
    have h2 := ((hasDerivAt_id t).const_mul (((k + 1 : ℕ) : ℝ))).sin
    refine ((h1.const_mul (a k)).fun_add (h2.const_mul (b k))).congr_deriv ?_
    simp only [id]
    ring
  have h := (HasDerivAt.fun_sum hk).const_add a0
  have e : trigPoly_STR02934 a0 a b N = fun s => a0 + ∑ k ∈ Finset.range N,
      (a k * Real.cos (((k + 1 : ℕ) : ℝ) * s) + b k * Real.sin (((k + 1 : ℕ) : ℝ) * s)) := rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [trigPoly_STR02934, zero_add]

theorem deriv_trigPoly_STR02934 (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    deriv (trigPoly_STR02934 a0 a b N) t
      = trigPoly_STR02934 0 (fun k => ((k + 1 : ℕ) : ℝ) * b k) (fun k => -(((k + 1 : ℕ) : ℝ) * a k)) N t :=
  (hasDerivAt_trigPoly_STR02934 a0 a b N t).deriv

theorem integrable_continuous_STR02934 {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (Ioc 0 (2 * π))) :=
  hf.integrableOn_Ioc

theorem normInt_one_STR02934 : normInt_STR02933 (fun _ => (1 : ℝ)) = 1 := by
  unfold normInt_STR02933
  simp [Real.pi_pos.le]
  field_simp

theorem normInt_cos_int_STR02934 (k : ℤ) :
    normInt_STR02933 (fun t => Real.cos (k * t)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simpa using normInt_one_STR02934
  · simp only [hk, ite_false]
    unfold normInt_STR02933
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (by exact_mod_cast hk),
      integral_cos]
    have h : Real.sin ((k : ℝ) * (2 * π)) = 0 := by
      have h2 := Real.sin_int_mul_pi (2 * k)
      rw [show (k : ℝ) * (2 * π) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring]
      exact h2
    simp [h]

theorem normInt_sin_int_STR02934 (k : ℤ) :
    normInt_STR02933 (fun t => Real.sin (k * t)) = 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [normInt_STR02933]
  · unfold normInt_STR02933
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) (by exact_mod_cast hk),
      integral_sin]
    simp [Real.cos_int_mul_two_pi]


theorem normInt_cos_nat_STR02934 (n : ℕ) :
    normInt_STR02933 (fun t => Real.cos ((n : ℝ) * t)) = if n = 0 then 1 else 0 := by
  simpa using normInt_cos_int_STR02934 (n : ℤ)

theorem normInt_sin_nat_STR02934 (n : ℕ) :
    normInt_STR02933 (fun t => Real.sin ((n : ℝ) * t)) = 0 := by
  simpa using normInt_sin_int_STR02934 (n : ℤ)

theorem normInt_cos_mul_cos_STR02934 (m n : ℕ) (hmn : m + n ≠ 0) :
    normInt_STR02933 (fun t => Real.cos ((m : ℝ) * t) * Real.cos ((n : ℝ) * t))
      = if m = n then 1 / 2 else 0 := by
  have e : (fun t => Real.cos ((m : ℝ) * t) * Real.cos ((n : ℝ) * t))
      = fun t => (1 / 2 : ℝ) * Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * t)
          + (1 / 2 : ℝ) * Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * t) := by
    funext t
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  rw [e, normInt_add_STR02934
      (integrable_continuous_STR02934 (by fun_prop) |>.const_mul _)
      (integrable_continuous_STR02934 (by fun_prop) |>.const_mul _),
    normInt_mul_const_STR02933, normInt_mul_const_STR02933, normInt_cos_int_STR02934,
    normInt_cos_int_STR02934]
  have h1 : ¬ ((m : ℤ) + n = 0) := by omega
  by_cases h : m = n
  · subst h; simp [show m ≠ 0 by omega]
  · have h2 : ¬ ((m : ℤ) - n = 0) := by omega
    simp [h, h1, h2]

theorem normInt_sin_mul_sin_STR02934 (m n : ℕ) (hmn : m + n ≠ 0) :
    normInt_STR02933 (fun t => Real.sin ((m : ℝ) * t) * Real.sin ((n : ℝ) * t))
      = if m = n then 1 / 2 else 0 := by
  have e : (fun t => Real.sin ((m : ℝ) * t) * Real.sin ((n : ℝ) * t))
      = fun t => (1 / 2 : ℝ) * Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * t)
          + (-1 / 2 : ℝ) * Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * t) := by
    funext t
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  rw [e, normInt_add_STR02934
      (integrable_continuous_STR02934 (by fun_prop) |>.const_mul _)
      (integrable_continuous_STR02934 (by fun_prop) |>.const_mul _),
    normInt_mul_const_STR02933, normInt_mul_const_STR02933, normInt_cos_int_STR02934,
    normInt_cos_int_STR02934]
  have h1 : ¬ ((m : ℤ) + n = 0) := by omega
  by_cases h : m = n
  · subst h; simp [show m ≠ 0 by omega]
  · have h2 : ¬ ((m : ℤ) - n = 0) := by omega
    simp [h, h1, h2]

theorem normInt_cos_mul_sin_STR02934 (m n : ℕ) :
    normInt_STR02933 (fun t => Real.cos ((m : ℝ) * t) * Real.sin ((n : ℝ) * t)) = 0 := by
  have e : (fun t => Real.cos ((m : ℝ) * t) * Real.sin ((n : ℝ) * t))
      = fun t => (1 / 2 : ℝ) * Real.sin ((((m : ℤ) + n : ℤ) : ℝ) * t)
          + (1 / 2 : ℝ) * Real.sin ((((n : ℤ) - m : ℤ) : ℝ) * t) := by
    funext t
    push_cast
    rw [sub_mul, add_mul, Real.sin_sub, Real.sin_add]
    ring
  rw [e, normInt_add_STR02934
      (integrable_continuous_STR02934 (by fun_prop) |>.const_mul _)
      (integrable_continuous_STR02934 (by fun_prop) |>.const_mul _),
    normInt_mul_const_STR02933, normInt_mul_const_STR02933, normInt_sin_int_STR02934,
    normInt_sin_int_STR02934]
  ring

/-- Normalized real trigonometric basis: `1`, `√2 cos((k+1)t)`, `√2 sin((k+1)t)`. -/
noncomputable def trigBasisFun_STR02934 : Option (Bool × ℕ) → ℝ → ℝ
  | none => fun _ => 1
  | some (false, k) => fun t => Real.sqrt 2 * Real.cos (((k + 1 : ℕ) : ℝ) * t)
  | some (true, k) => fun t => Real.sqrt 2 * Real.sin (((k + 1 : ℕ) : ℝ) * t)

theorem sqrt_two_mul_STR02934 (x y : ℝ) :
    Real.sqrt 2 * x * (Real.sqrt 2 * y) = 2 * (x * y) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt 2 * x * (Real.sqrt 2 * y) = (Real.sqrt 2 * Real.sqrt 2) * (x * y) := by ring
    _ = 2 * (x * y) := by rw [hs]

theorem normInt_trigBasis_mul_STR02934 (i j : Option (Bool × ℕ)) :
    normInt_STR02933 (fun t => trigBasisFun_STR02934 i t * trigBasisFun_STR02934 j t)
      = if i = j then 1 else 0 := by
  rcases i with _ | ⟨_ | _, k⟩ <;> rcases j with _ | ⟨_ | _, l⟩ <;>
    simp only [trigBasisFun_STR02934]
  · simpa using normInt_one_STR02934
  · simp only [one_mul, normInt_mul_const_STR02933, normInt_cos_nat_STR02934]
    simp
  · simp only [one_mul, normInt_mul_const_STR02933, normInt_sin_nat_STR02934]
    simp
  · simp only [mul_one, normInt_mul_const_STR02933, normInt_cos_nat_STR02934]
    simp
  · simp only [sqrt_two_mul_STR02934, normInt_mul_const_STR02933,
      normInt_cos_mul_cos_STR02934 (k + 1) (l + 1) (by omega)]
    by_cases h : k = l <;> simp [h]
  · simp only [sqrt_two_mul_STR02934, normInt_mul_const_STR02933,
      normInt_cos_mul_sin_STR02934]
    simp
  · simp only [mul_one, normInt_mul_const_STR02933, normInt_sin_nat_STR02934]
    simp
  · simp only [sqrt_two_mul_STR02934, normInt_mul_const_STR02933]
    have e : (fun t => Real.sin (((k + 1 : ℕ) : ℝ) * t) * Real.cos (((l + 1 : ℕ) : ℝ) * t))
        = fun t => Real.cos (((l + 1 : ℕ) : ℝ) * t) * Real.sin (((k + 1 : ℕ) : ℝ) * t) := by
      funext t; ring
    rw [e, normInt_cos_mul_sin_STR02934]
    simp
  · simp only [sqrt_two_mul_STR02934, normInt_mul_const_STR02933,
      normInt_sin_mul_sin_STR02934 (k + 1) (l + 1) (by omega)]
    by_cases h : k = l <;> simp [h]


/-- Normalized Lebesgue measure `m = dt/(2π)` on one period `(0, 2π]`, as a measure on `ℝ`. -/
noncomputable def circleMeasure_STR02934 : Measure ℝ :=
  ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ioc 0 (2 * π))

instance isFiniteMeasure_circleMeasure_STR02934 : IsFiniteMeasure circleMeasure_STR02934 := by
  refine ⟨?_⟩
  rw [circleMeasure_STR02934, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  rw [Set.univ_inter]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioc_lt_top

theorem normInt_eq_integral_STR02934 (f : ℝ → ℝ) :
    normInt_STR02933 f = ∫ t, f t ∂circleMeasure_STR02934 := by
  unfold circleMeasure_STR02934 normInt_STR02933
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem volume_restrict_eq_smul_STR02934 :
    volume.restrict (Ioc 0 (2 * π)) = ENNReal.ofReal (2 * π) • circleMeasure_STR02934 := by
  unfold circleMeasure_STR02934
  rw [smul_smul, ← ENNReal.ofReal_mul Real.two_pi_pos.le, mul_inv_cancel₀ Real.two_pi_pos.ne',
    ENNReal.ofReal_one, one_smul]

theorem memLp_restrict_of_circle_STR02934 {u : ℝ → ℝ} (hu : MemLp u 2 circleMeasure_STR02934) :
    MemLp u 2 (volume.restrict (Ioc 0 (2 * π))) := by
  refine hu.of_measure_le_smul (c := ENNReal.ofReal (2 * π)) ENNReal.ofReal_ne_top ?_
  rw [volume_restrict_eq_smul_STR02934]

theorem continuous_trigBasisFun_STR02934 (i : Option (Bool × ℕ)) :
    Continuous (trigBasisFun_STR02934 i) := by
  rcases i with _ | ⟨_ | _, k⟩ <;> simp only [trigBasisFun_STR02934] <;> fun_prop

theorem abs_trigBasisFun_le_STR02934 (i : Option (Bool × ℕ)) (t : ℝ) :
    ‖trigBasisFun_STR02934 i t‖ ≤ 2 := by
  have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rcases i with _ | ⟨_ | _, k⟩ <;> simp only [trigBasisFun_STR02934, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg h0]
  · norm_num
  · calc Real.sqrt 2 * |Real.cos (((k + 1 : ℕ) : ℝ) * t)| ≤ Real.sqrt 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) h0
      _ ≤ 2 := by linarith
  · calc Real.sqrt 2 * |Real.sin (((k + 1 : ℕ) : ℝ) * t)| ≤ Real.sqrt 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) h0
      _ ≤ 2 := by linarith

theorem memLp_trigBasisFun_STR02934 (i : Option (Bool × ℕ)) :
    MemLp (trigBasisFun_STR02934 i) 2 circleMeasure_STR02934 :=
  MemLp.of_bound (continuous_trigBasisFun_STR02934 i).aestronglyMeasurable 2
    (ae_of_all _ (abs_trigBasisFun_le_STR02934 i))

/-- The normalized real trigonometric functions as elements of `L²(m)`. -/
noncomputable def trigBasisLp_STR02934 (i : Option (Bool × ℕ)) : Lp ℝ 2 circleMeasure_STR02934 :=
  (memLp_trigBasisFun_STR02934 i).toLp (trigBasisFun_STR02934 i)

theorem inner_trigBasisLp_STR02934 (i : Option (Bool × ℕ)) (x : Lp ℝ 2 circleMeasure_STR02934) :
    inner ℝ (trigBasisLp_STR02934 i) x
      = normInt_STR02933 (fun t => x t * trigBasisFun_STR02934 i t) := by
  rw [L2.inner_def, normInt_eq_integral_STR02934]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_trigBasisFun_STR02934 i).coeFn_toLp] with a ha
  rw [trigBasisLp_STR02934, ha]
  simp

theorem orthonormal_trigBasisLp_STR02934 : Orthonormal ℝ trigBasisLp_STR02934 := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_trigBasisLp_STR02934]
  have h2 := (memLp_trigBasisFun_STR02934 j).coeFn_toLp
  have : normInt_STR02933 (fun t => (trigBasisLp_STR02934 j) t * trigBasisFun_STR02934 i t)
      = normInt_STR02933 (fun t => trigBasisFun_STR02934 j t * trigBasisFun_STR02934 i t) := by
    rw [normInt_eq_integral_STR02934, normInt_eq_integral_STR02934]
    refine integral_congr_ae ?_
    filter_upwards [h2] with a ha
    rw [trigBasisLp_STR02934, ha]
  rw [this, normInt_trigBasis_mul_STR02934]
  simp [eq_comm]


theorem normInt_coeff_zero_of_perp_STR02934 {x : Lp ℝ 2 circleMeasure_STR02934}
    (hperp : ∀ i, inner ℝ (trigBasisLp_STR02934 i) x = (0 : ℝ)) (n : ℕ) :
    normInt_STR02933 (fun t => x t * Real.cos ((n : ℝ) * t)) = 0
      ∧ normInt_STR02933 (fun t => x t * Real.sin ((n : ℝ) * t)) = 0 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rcases n with _ | k
  · have h0 := hperp none
    rw [inner_trigBasisLp_STR02934] at h0
    simp only [trigBasisFun_STR02934, mul_one] at h0
    exact ⟨by simpa using h0, by simp [normInt_STR02933]⟩
  · have hc := hperp (some (false, k))
    have hsn := hperp (some (true, k))
    rw [inner_trigBasisLp_STR02934] at hc hsn
    simp only [trigBasisFun_STR02934] at hc hsn
    have ec : (fun t => x t * (Real.sqrt 2 * Real.cos (((k + 1 : ℕ) : ℝ) * t)))
        = fun t => Real.sqrt 2 * (x t * Real.cos (((k + 1 : ℕ) : ℝ) * t)) := by
      funext t; ring
    have es : (fun t => x t * (Real.sqrt 2 * Real.sin (((k + 1 : ℕ) : ℝ) * t)))
        = fun t => Real.sqrt 2 * (x t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
      funext t; ring
    rw [ec, normInt_mul_const_STR02933] at hc
    rw [es, normInt_mul_const_STR02933] at hsn
    exact ⟨(mul_eq_zero.mp hc).resolve_left hs, (mul_eq_zero.mp hsn).resolve_left hs⟩

theorem normInt_coeff_zero_int_STR02934 {u : ℝ → ℝ}
    (h : ∀ n : ℕ, normInt_STR02933 (fun t => u t * Real.cos ((n : ℝ) * t)) = 0
      ∧ normInt_STR02933 (fun t => u t * Real.sin ((n : ℝ) * t)) = 0) (m : ℤ) :
    normInt_STR02933 (fun t => u t * Real.cos ((m : ℝ) * t)) = 0
      ∧ normInt_STR02933 (fun t => u t * Real.sin ((m : ℝ) * t)) = 0 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using h n
  · obtain ⟨h1, h2⟩ := h n
    refine ⟨by simpa using h1, ?_⟩
    have e : (fun t => u t * Real.sin (((-(n : ℤ) : ℤ) : ℝ) * t))
        = fun t => (-1 : ℝ) * (u t * Real.sin ((n : ℝ) * t)) := by
      funext t
      push_cast
      rw [neg_mul, Real.sin_neg]
      ring
    rw [e, normInt_mul_const_STR02933, h2, mul_zero]

theorem orthogonal_trigBasisLp_eq_bot_STR02934 :
    (Submodule.span ℝ (Set.range trigBasisLp_STR02934))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hperp : ∀ i, inner ℝ (trigBasisLp_STR02934 i) x = (0 : ℝ) := fun i =>
    (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmem : MemLp (fun t => x t) 2 circleMeasure_STR02934 := Lp.memLp x
  have hmem' := memLp_restrict_of_circle_STR02934 hmem
  have hint := hasSum_int_parseval_STR02934 hmem'
  have hz := normInt_coeff_zero_int_STR02934 (normInt_coeff_zero_of_perp_STR02934 hperp)
  have hP : (fun m : ℤ => normInt_STR02933 (fun t => x t * Real.cos ((m : ℝ) * t)) ^ 2
      + normInt_STR02933 (fun t => x t * Real.sin ((m : ℝ) * t)) ^ 2) = fun _ => 0 := by
    funext m
    rw [(hz m).1, (hz m).2]
    norm_num
  rw [hP] at hint
  have h0 : normInt_STR02933 (fun t => x t ^ 2) = 0 := hint.unique hasSum_zero
  rw [normInt_eq_integral_STR02934] at h0
  have hnn : (0 : ℝ → ℝ) ≤ fun t => x t ^ 2 := fun t => sq_nonneg _
  have h1 := (integral_eq_zero_iff_of_nonneg hnn hmem.integrable_sq).1 h0
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [h1] with t ht
  simpa using ht

/-- The normalized trigonometric functions form a Hilbert basis of `L²(m)`. -/
theorem exists_hilbertBasis_trig_STR02934 :
    ∃ b : HilbertBasis (Option (Bool × ℕ)) ℝ (Lp ℝ 2 circleMeasure_STR02934),
      ∀ i, (b i : ℝ → ℝ) =ᵐ[circleMeasure_STR02934] trigBasisFun_STR02934 i := by
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot orthonormal_trigBasisLp_STR02934
    orthogonal_trigBasisLp_eq_bot_STR02934, fun i => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact (memLp_trigBasisFun_STR02934 i).coeFn_toLp


theorem cosCoeff_trigPoly_STR02934 (a0 : ℝ) (a b : ℕ → ℝ) (N k : ℕ) :
    cosCoeff_STR02933 (trigPoly_STR02934 a0 a b N) (k + 1) = if k < N then a k else 0 := by
  have hu : Integrable (fun t => Real.cos (((k + 1 : ℕ) : ℝ) * t))
      (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934 (by fun_prop)
  have e : (fun t => trigPoly_STR02934 a0 a b N t * Real.cos (((k + 1 : ℕ) : ℝ) * t))
      = fun t => Real.cos (((k + 1 : ℕ) : ℝ) * t) * trigPoly_STR02934 a0 a b N t := by
    funext t; ring
  unfold cosCoeff_STR02933
  rw [e, normInt_mul_trigPoly_STR02934 hu, normInt_cos_nat_STR02934]
  have hc : ∀ j : ℕ, cosCoeff_STR02933 (fun t => Real.cos (((k + 1 : ℕ) : ℝ) * t)) (j + 1)
      = if k = j then 1 else 0 := by
    intro j
    unfold cosCoeff_STR02933
    rw [normInt_cos_mul_cos_STR02934 (k + 1) (j + 1) (by omega)]
    by_cases h : k = j <;> simp [h]
  have hs : ∀ j : ℕ, sinCoeff_STR02933 (fun t => Real.cos (((k + 1 : ℕ) : ℝ) * t)) (j + 1) = 0 := by
    intro j
    unfold sinCoeff_STR02933
    rw [normInt_cos_mul_sin_STR02934, mul_zero]
  simp only [hc, hs, mul_zero, add_zero, mul_ite, mul_one, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ite_false, zero_add, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs <;> ring

theorem sinCoeff_trigPoly_STR02934 (a0 : ℝ) (a b : ℕ → ℝ) (N k : ℕ) :
    sinCoeff_STR02933 (trigPoly_STR02934 a0 a b N) (k + 1) = if k < N then b k else 0 := by
  have hu : Integrable (fun t => Real.sin (((k + 1 : ℕ) : ℝ) * t))
      (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934 (by fun_prop)
  have e : (fun t => trigPoly_STR02934 a0 a b N t * Real.sin (((k + 1 : ℕ) : ℝ) * t))
      = fun t => Real.sin (((k + 1 : ℕ) : ℝ) * t) * trigPoly_STR02934 a0 a b N t := by
    funext t; ring
  unfold sinCoeff_STR02933
  rw [e, normInt_mul_trigPoly_STR02934 hu, normInt_sin_nat_STR02934]
  have hc : ∀ j : ℕ, cosCoeff_STR02933 (fun t => Real.sin (((k + 1 : ℕ) : ℝ) * t)) (j + 1) = 0 := by
    intro j
    unfold cosCoeff_STR02933
    have e2 : (fun t => Real.sin (((k + 1 : ℕ) : ℝ) * t) * Real.cos (((j + 1 : ℕ) : ℝ) * t))
        = fun t => Real.cos (((j + 1 : ℕ) : ℝ) * t) * Real.sin (((k + 1 : ℕ) : ℝ) * t) := by
      funext t; ring
    rw [e2, normInt_cos_mul_sin_STR02934, mul_zero]
  have hs : ∀ j : ℕ, sinCoeff_STR02933 (fun t => Real.sin (((k + 1 : ℕ) : ℝ) * t)) (j + 1)
      = if k = j then 1 else 0 := by
    intro j
    unfold sinCoeff_STR02933
    rw [normInt_sin_mul_sin_STR02934 (k + 1) (j + 1) (by omega)]
    by_cases h : k = j <;> simp [h]
  simp only [hc, hs, mul_zero, mul_ite, mul_one, zero_add,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs <;> ring

theorem normInt_trigPoly_STR02934 (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) :
    normInt_STR02933 (trigPoly_STR02934 a0 a b N) = a0 := by
  have hu : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 continuous_const
  have h := normInt_mul_trigPoly_STR02934 hu a0 a b N
  have hc : ∀ k : ℕ, cosCoeff_STR02933 (fun _ : ℝ => (1 : ℝ)) (k + 1) = 0 := by
    intro k
    unfold cosCoeff_STR02933
    simp only [one_mul, normInt_cos_nat_STR02934]
    simp
  have hs : ∀ k : ℕ, sinCoeff_STR02933 (fun _ : ℝ => (1 : ℝ)) (k + 1) = 0 := by
    intro k
    unfold sinCoeff_STR02933
    simp only [one_mul, normInt_sin_nat_STR02934]
    simp
  simp only [one_mul, hc, hs, mul_zero, add_zero, Finset.sum_const_zero, normInt_one_STR02934,
    mul_one] at h
  exact h

/-- The coefficients of the finite trigonometric polynomial
`p = a0 + Σ_{k<N} (a k cos((k+1)t) + b k sin((k+1)t))` are exactly the given ones: the mean of `p`
is `a0`, and its `(k+1)`-st cosine/sine Fourier coefficients (in the normalization of `.33`) are
`a k` / `b k` for `k < N` and `0` otherwise. -/
theorem str029_34_parseval_adapter_periodic_weak_domain_trigPoly_coeff
    (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) :
    normInt_STR02933 (trigPoly_STR02934 a0 a b N) = a0 ∧
      (∀ k : ℕ, cosCoeff_STR02933 (trigPoly_STR02934 a0 a b N) (k + 1) = if k < N then a k else 0) ∧
      (∀ k : ℕ, sinCoeff_STR02933 (trigPoly_STR02934 a0 a b N) (k + 1) = if k < N then b k else 0) :=
  ⟨normInt_trigPoly_STR02934 a0 a b N, cosCoeff_trigPoly_STR02934 a0 a b N,
    sinCoeff_trigPoly_STR02934 a0 a b N⟩


/-- Parseval for `w` and for its weak derivative `g = w'` (for `w` of mean zero), in the real
coefficient form `∫ w² dm = ½ Σ_{n≥1} (c_n² + s_n²)`, `∫ w'² dm = ½ Σ_{n≥1} n² (c_n² + s_n²)`;
the sums are indexed by `n + 1` and both series are summable. -/
theorem str029_34_parseval_adapter_periodic_weak_domain_parseval
    (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g)
    (hw0 : normInt_STR02933 w = 0) :
    (Summable (fun n : ℕ => cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2) ∧
      normInt_STR02933 (fun t => w t ^ 2)
        = (1 / 2) * ∑' n : ℕ, (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)) ∧
    (Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2
          * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)) ∧
      normInt_STR02933 (fun t => g t ^ 2)
        = (1 / 2) * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2
          * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)) := by
  have hw := hasSum_nat_parseval_STR02934 hwg.1.2 hw0
  have hg0 := str029_33_fourier_coefficients_weak_derivative_mean w g hwg
  have hg := hasSum_nat_parseval_STR02934 hwg.2.1.2 hg0
  have hg' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2
      * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2))
      (2 * normInt_STR02933 (fun t => g t ^ 2)) := by
    convert hg using 1
    funext n
    obtain ⟨h1, h2, -⟩ := str029_33_fourier_coefficients_weak_derivative w g hwg (n + 1) (by omega)
    rw [h1, h2]
    ring
  refine ⟨⟨hw.summable, ?_⟩, ⟨hg'.summable, ?_⟩⟩
  · rw [hw.tsum_eq]; ring
  · rw [hg'.tsum_eq]; ring

/-- Bilinear identities against a finite trigonometric polynomial
`p = a0 + Σ_{k<N} (a k cos((k+1)t) + b k sin((k+1)t))`, for `w` of mean zero with weak derivative
`g`: `∫ w p dm`, `∫ w' p' dm` and `∫ w' p dm` in terms of the coefficients of `w`. -/
theorem str029_34_parseval_adapter_periodic_weak_domain_bilinear
    (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g)
    (hw0 : normInt_STR02933 w = 0) (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ) :
    normInt_STR02933 (fun t => w t * trigPoly_STR02934 a0 a b N t)
        = (1 / 2) * ∑ k ∈ Finset.range N,
            (a k * cosCoeff_STR02933 w (k + 1) + b k * sinCoeff_STR02933 w (k + 1)) ∧
      normInt_STR02933 (fun t => g t * deriv (trigPoly_STR02934 a0 a b N) t)
        = (1 / 2) * ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2
            * (a k * cosCoeff_STR02933 w (k + 1) + b k * sinCoeff_STR02933 w (k + 1)) ∧
      normInt_STR02933 (fun t => g t * trigPoly_STR02934 a0 a b N t)
        = (1 / 2) * ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)
            * (a k * sinCoeff_STR02933 w (k + 1) - b k * cosCoeff_STR02933 w (k + 1)) := by
  have hwi := integrable_of_memLp_STR02934 hwg.1.2
  have hgi := integrable_of_memLp_STR02934 hwg.2.1.2
  have hg0 := str029_33_fourier_coefficients_weak_derivative_mean w g hwg
  refine ⟨?_, ?_, ?_⟩
  · rw [normInt_mul_trigPoly_STR02934 hwi, hw0, mul_zero, zero_add]
  · have e : (fun t => g t * deriv (trigPoly_STR02934 a0 a b N) t)
        = fun t => g t * trigPoly_STR02934 0 (fun k => ((k + 1 : ℕ) : ℝ) * b k)
            (fun k => -(((k + 1 : ℕ) : ℝ) * a k)) N t := by
      funext t
      rw [deriv_trigPoly_STR02934]
    rw [e, normInt_mul_trigPoly_STR02934 hgi, hg0, mul_zero, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨h1, h2, -⟩ := str029_33_fourier_coefficients_weak_derivative w g hwg (k + 1) (by omega)
    rw [h1, h2]
    ring
  · rw [normInt_mul_trigPoly_STR02934 hgi, hg0, mul_zero, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨h1, h2, -⟩ := str029_33_fourier_coefficients_weak_derivative w g hwg (k + 1) (by omega)
    rw [h1, h2]
    ring

/-- The constant `1` and the normalized functions `√2 cos((k+1)t)`, `√2 sin((k+1)t)` form a
countably indexed Hilbert basis of the real space `L²(m)`, where `m = dt/(2π)` on one period
(`circleMeasure_STR02934`). -/
theorem str029_34_parseval_adapter_periodic_weak_domain_basis :
    Countable (Option (Bool × ℕ)) ∧
      ∃ b : HilbertBasis (Option (Bool × ℕ)) ℝ (Lp ℝ 2 circleMeasure_STR02934),
        ((b none : ℝ → ℝ) =ᵐ[circleMeasure_STR02934] fun _ => (1 : ℝ)) ∧
        (∀ k : ℕ, (b (some (false, k)) : ℝ → ℝ) =ᵐ[circleMeasure_STR02934]
          fun t => Real.sqrt 2 * Real.cos (((k + 1 : ℕ) : ℝ) * t)) ∧
        (∀ k : ℕ, (b (some (true, k)) : ℝ → ℝ) =ᵐ[circleMeasure_STR02934]
          fun t => Real.sqrt 2 * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
  obtain ⟨b, hb⟩ := exists_hilbertBasis_trig_STR02934
  exact ⟨inferInstance, b, hb none, fun k => hb (some (false, k)), fun k => hb (some (true, k))⟩

/-- STR029.34, Parseval adapter for the periodic weak domain: for `w` with weak derivative `g`
(`IsPeriodicWeakDerivative_STR02933 w g`) and `∫ w dm = 0`, (1) the two Parseval identities, (2) for every finite
trigonometric polynomial `p` (whose coefficients are identified) the bilinear identities, (3) the
normalized real trigonometric system is a countable Hilbert basis of real `L²(m)`. -/
theorem str029_34_parseval_adapter_periodic_weak_domain
    (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g)
    (hw0 : normInt_STR02933 w = 0) :
    ((Summable (fun n : ℕ => cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2) ∧
        normInt_STR02933 (fun t => w t ^ 2)
          = (1 / 2) * ∑' n : ℕ,
            (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)) ∧
      (Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2
            * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2)) ∧
        normInt_STR02933 (fun t => g t ^ 2)
          = (1 / 2) * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ 2
            * (cosCoeff_STR02933 w (n + 1) ^ 2 + sinCoeff_STR02933 w (n + 1) ^ 2))) ∧
    (∀ (a0 : ℝ) (a b : ℕ → ℝ) (N : ℕ),
      (normInt_STR02933 (trigPoly_STR02934 a0 a b N) = a0 ∧
        (∀ k : ℕ, cosCoeff_STR02933 (trigPoly_STR02934 a0 a b N) (k + 1)
          = if k < N then a k else 0) ∧
        (∀ k : ℕ, sinCoeff_STR02933 (trigPoly_STR02934 a0 a b N) (k + 1)
          = if k < N then b k else 0)) ∧
      (normInt_STR02933 (fun t => w t * trigPoly_STR02934 a0 a b N t)
          = (1 / 2) * ∑ k ∈ Finset.range N,
              (a k * cosCoeff_STR02933 w (k + 1) + b k * sinCoeff_STR02933 w (k + 1)) ∧
        normInt_STR02933 (fun t => g t * deriv (trigPoly_STR02934 a0 a b N) t)
          = (1 / 2) * ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2
              * (a k * cosCoeff_STR02933 w (k + 1) + b k * sinCoeff_STR02933 w (k + 1)) ∧
        normInt_STR02933 (fun t => g t * trigPoly_STR02934 a0 a b N t)
          = (1 / 2) * ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)
              * (a k * sinCoeff_STR02933 w (k + 1) - b k * cosCoeff_STR02933 w (k + 1)))) ∧
    (Countable (Option (Bool × ℕ)) ∧
      ∃ b : HilbertBasis (Option (Bool × ℕ)) ℝ (Lp ℝ 2 circleMeasure_STR02934),
        ((b none : ℝ → ℝ) =ᵐ[circleMeasure_STR02934] fun _ => (1 : ℝ)) ∧
        (∀ k : ℕ, (b (some (false, k)) : ℝ → ℝ) =ᵐ[circleMeasure_STR02934]
          fun t => Real.sqrt 2 * Real.cos (((k + 1 : ℕ) : ℝ) * t)) ∧
        (∀ k : ℕ, (b (some (true, k)) : ℝ → ℝ) =ᵐ[circleMeasure_STR02934]
          fun t => Real.sqrt 2 * Real.sin (((k + 1 : ℕ) : ℝ) * t))) :=
  ⟨str029_34_parseval_adapter_periodic_weak_domain_parseval w g hwg hw0,
    fun a0 a b N => ⟨str029_34_parseval_adapter_periodic_weak_domain_trigPoly_coeff a0 a b N,
      str029_34_parseval_adapter_periodic_weak_domain_bilinear w g hwg hw0 a0 a b N⟩,
    str029_34_parseval_adapter_periodic_weak_domain_basis⟩

end DGPS.Frontier.STR029
