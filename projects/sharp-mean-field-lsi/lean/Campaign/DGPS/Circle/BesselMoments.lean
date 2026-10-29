import DGPS.Circle.AngularNormalization
/-!
# Bessel integral series and moment derivatives (EX002)

On the angular circle `AngCircle` with normalized Haar measure `angHaar` (`dθ/(2π)`), the modified
Bessel functions `I_n(t) = ∫ exp(t cos θ) cos(nθ) dθ/(2π)` are defined by `besselI`. The main
theorem `DGPS.Examples.bessel_integral_series_and_moment_derivatives` gives the power series for
`I₀` and `I₁/t`, differentiation under the integral, parity, and `g' = Var_{q_t}(cos) > 0` for
`g = I₁/I₀`.
-/

open MeasureTheory Real Filter Topology
open DGPS.Circle.AngularNormalization

namespace DGPS.Circle.BesselMoments

/-- the trigonometric mode `θ ↦ cos (n θ)` on the angular circle -/
noncomputable def angMode (n : ℕ) : AngCircle → ℝ :=
  Function.Periodic.lift (f := fun s : ℝ => Real.cos ((n : ℝ) * s)) (c := 2 * π) (by
    intro x
    have : (n : ℝ) * (x + 2 * π) = (n : ℝ) * x + (n : ℕ) * (2 * π) := by ring
    show Real.cos ((n : ℝ) * (x + 2 * π)) = Real.cos ((n : ℝ) * x)
    rw [this, Real.cos_add_nat_mul_two_pi])

theorem angMode_coe (n : ℕ) (s : ℝ) : angMode n (s : AngCircle) = Real.cos ((n : ℝ) * s) := rfl

theorem continuous_angMode (n : ℕ) : Continuous (angMode n) := by
  unfold angMode
  refine Continuous.quotient_lift (by fun_prop) ?_

theorem abs_angMode_le (n : ℕ) (θ : AngCircle) : |angMode n θ| ≤ 1 := by
  induction θ using QuotientAddGroup.induction_on with
  | H s => exact Real.abs_cos_le_one _

theorem angMode_zero : angMode 0 = fun _ => 1 := by
  funext θ
  induction θ using QuotientAddGroup.induction_on with
  | H s => exact (angMode_coe 0 s).trans (by simp)

/-- cosine on the angular circle -/
noncomputable abbrev angCos : AngCircle → ℝ := angMode 1

/-- the modified Bessel function `I_n(t) = ∫ exp(t cos θ) cos(nθ) dm` -/
noncomputable def besselI (n : ℕ) (t : ℝ) : ℝ :=
  ∫ θ, Real.exp (t * angCos θ) * angMode n θ ∂angHaar

/-- the continuous extension of `I₁(t)/t`, as the series `(1/2) ∑ (t²/4)^j / (j! (j+1)!)` -/
noncomputable def besselI1Over (t : ℝ) : ℝ :=
  ∑' j : ℕ, (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))

/-- the ratio `g = I₁ / I₀` -/
noncomputable def besselRatio (t : ℝ) : ℝ := besselI 1 t / besselI 0 t

/-- the tilted density `q_t = exp(t cos θ) / I₀(t)` with respect to `angHaar` -/
noncomputable def besselDensity (t : ℝ) (θ : AngCircle) : ℝ :=
  Real.exp (t * angCos θ) / besselI 0 t

/-- the variance of `cos` under `q_t dm` -/
noncomputable def besselVariance (t : ℝ) : ℝ :=
  ∫ θ, (angCos θ - besselRatio t) ^ 2 * besselDensity t θ ∂angHaar

/-! ### Integrals over the circle as interval integrals -/

theorem integral_ang (ψ : ℝ → ℝ) (φ : AngCircle → ℝ) (h : ∀ s : ℝ, φ (s : AngCircle) = ψ s) :
    ∫ θ, φ θ ∂angHaar = (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π, ψ s := by
  have hψ : ψ = fun s : ℝ => φ (s : AngCircle) := funext fun s => (h s).symm
  subst hψ
  rw [AddCircle.integral_haarAddCircle, smul_eq_mul,
    ← AddCircle.intervalIntegral_preimage (2 * π) 0 φ]
  simp

theorem besselI_eq_interval (n : ℕ) (t : ℝ) :
    besselI n t = (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos ((n : ℝ) * s) := by
  unfold besselI
  apply integral_ang
  intro s
  simp [angCos, angMode_coe]

/-- average of `cos^m` -/
noncomputable def cosAvg (m : ℕ) : ℝ := ∫ θ, angCos θ ^ m ∂angHaar

theorem cosAvg_eq (m : ℕ) : cosAvg m = (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π, Real.cos s ^ m := by
  unfold cosAvg
  apply integral_ang
  intro s
  simp [angCos, angMode_coe]

theorem cosAvg_zero : cosAvg 0 = 1 := by
  simp [cosAvg]

theorem cosAvg_one : cosAvg 1 = 0 := by
  rw [cosAvg_eq]
  simp

theorem cosAvg_add_two (m : ℕ) : cosAvg (m + 2) = (m + 1) / (m + 2) * cosAvg m := by
  rw [cosAvg_eq, cosAvg_eq, integral_cos_pow]
  simp only [Real.sin_zero, Real.sin_two_pi, mul_zero, sub_zero, zero_div, zero_add]
  ring

theorem cosAvg_odd (j : ℕ) : cosAvg (2 * j + 1) = 0 := by
  induction j with
  | zero => simpa using cosAvg_one
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [this, cosAvg_add_two, ih, mul_zero]

theorem cosAvg_even (j : ℕ) :
    cosAvg (2 * j) = ((2 * j).factorial : ℝ) / (4 ^ j * (j.factorial : ℝ) ^ 2) := by
  induction j with
  | zero => simp [cosAvg_zero]
  | succ k ih =>
    have : 2 * (k + 1) = (2 * k) + 2 := by ring
    rw [this, cosAvg_add_two, ih]
    have h2 : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring
    have h3 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
    rw [h2, h3]
    push_cast
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ### Power series -/

theorem integrable_cont {f : AngCircle → ℝ} (hf : Continuous f) (C : ℝ) (hC : ∀ θ, |f θ| ≤ C) :
    Integrable f angHaar :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun θ => by
    simpa using hC θ)

theorem hasSum_exp_series (x : ℝ) : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem hasSum_moment (p : ℕ) (t : ℝ) :
    HasSum (fun k : ℕ => t ^ k / (k.factorial : ℝ) * cosAvg (k + p))
      (∫ θ, Real.exp (t * angCos θ) * angCos θ ^ p ∂angHaar) := by
  have hc : Continuous angCos := continuous_angMode 1
  have hb : ∀ θ, |angCos θ| ≤ 1 := abs_angMode_le 1
  have key := hasSum_integral_of_dominated_convergence (μ := angHaar)
    (F := fun (k : ℕ) (θ : AngCircle) => (t * angCos θ) ^ k / (k.factorial : ℝ) * angCos θ ^ p)
    (f := fun θ => Real.exp (t * angCos θ) * angCos θ ^ p)
    (fun k _ => |t| ^ k / (k.factorial : ℝ))
    (fun k => by fun_prop)
    (fun k => Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_mul, Nat.abs_cast, abs_pow, mul_pow]
      have h1 : |angCos θ| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (hb θ)
      have h2 : |angCos θ| ^ p ≤ 1 := pow_le_one₀ (abs_nonneg _) (hb θ)
      have h3 : 0 ≤ |t| ^ k / (k.factorial : ℝ) := by positivity
      calc |t| ^ k * |angCos θ| ^ k / (k.factorial : ℝ) * |angCos θ| ^ p
          = (|t| ^ k / (k.factorial : ℝ)) * (|angCos θ| ^ k * |angCos θ| ^ p) := by ring
        _ ≤ (|t| ^ k / (k.factorial : ℝ)) * (1 * 1) := by
          gcongr
        _ = |t| ^ k / (k.factorial : ℝ) := by ring)
    (Filter.Eventually.of_forall fun θ => Real.summable_pow_div_factorial |t|)
    (integrable_const _)
    (Filter.Eventually.of_forall fun θ => (hasSum_exp_series (t * angCos θ)).mul_right _)
  convert key using 2 with k
  have : ∀ θ : AngCircle, (t * angCos θ) ^ k / (k.factorial : ℝ) * angCos θ ^ p
      = t ^ k / (k.factorial : ℝ) * angCos θ ^ (k + p) := by
    intro θ; rw [mul_pow, pow_add]; ring
  simp_rw [this]
  rw [integral_const_mul]
  rfl

theorem besselI_zero (t : ℝ) :
    besselI 0 t = ∫ θ, Real.exp (t * angCos θ) * angCos θ ^ 0 ∂angHaar := by
  simp [besselI, angMode_zero]

theorem besselI_one (t : ℝ) :
    besselI 1 t = ∫ θ, Real.exp (t * angCos θ) * angCos θ ^ 1 ∂angHaar := by
  simp [besselI, angCos]

theorem hasSum_besselI_zero (t : ℝ) :
    HasSum (fun j : ℕ => (t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2) (besselI 0 t) := by
  rw [besselI_zero]
  have h := hasSum_moment 0 t
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by simpa using h
  have h2 := (hinj.hasSum_iff (f := fun k : ℕ => t ^ k / (k.factorial : ℝ) * cosAvg (k + 0))
    (a := ∫ θ, Real.exp (t * angCos θ) * angCos θ ^ 0 ∂angHaar) (by
      intro k hk
      have : Odd k := by
        by_contra hodd
        rw [Nat.not_odd_iff_even] at hodd
        obtain ⟨j, hj⟩ := hodd
        exact hk ⟨j, by simp; omega⟩
      obtain ⟨j, hj⟩ := this
      subst hj
      simp [cosAvg_odd])).mpr h
  convert h2 using 1
  funext j
  simp only [Function.comp, add_zero, cosAvg_even]
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, ← pow_mul]
  field_simp

theorem hasSum_besselI_one (t : ℝ) :
    HasSum (fun j : ℕ => t * ((1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))))
      (besselI 1 t) := by
  rw [besselI_one]
  have h := hasSum_moment 1 t
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := fun a b h => by simpa using h
  have h2 := (hinj.hasSum_iff (f := fun k : ℕ => t ^ k / (k.factorial : ℝ) * cosAvg (k + 1))
    (a := ∫ θ, Real.exp (t * angCos θ) * angCos θ ^ 1 ∂angHaar) (by
      intro k hk
      have : Even k := by
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        obtain ⟨j, hj⟩ := hodd
        exact hk ⟨j, by simp; omega⟩
      obtain ⟨j, hj⟩ := this
      have : k + 1 = 2 * j + 1 := by omega
      rw [this, cosAvg_odd]
      simp)).mpr h
  convert h2 using 1
  funext j
  simp only [Function.comp]
  have e : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
  rw [e, cosAvg_even]
  have h3 : (j + 1).factorial = (j + 1) * j.factorial := Nat.factorial_succ j
  have h5 : (2 * j + 1).factorial * (2 * j + 2) = (2 * j + 2).factorial := by
    rw [Nat.factorial_succ (2 * j + 1)]; ring
  have e2 : 2 * (j + 1) = 2 * j + 2 := by ring
  rw [e2]
  have h6 : (2 * j + 2).factorial = (2 * j + 2) * (2 * j + 1).factorial := Nat.factorial_succ _
  rw [h6, h3]
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  have h4 : ((2 * j + 1).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  rw [div_pow, ← pow_mul, pow_succ (4 : ℝ) j, pow_succ t (2 * j)]
  field_simp
  ring

theorem integrable_exp_mul (t : ℝ) (h : AngCircle → ℝ) (hh : Continuous h) (hb : ∀ θ, |h θ| ≤ 1) :
    Integrable (fun θ => Real.exp (t * angCos θ) * h θ) angHaar := by
  have hc : Continuous angCos := continuous_angMode 1
  refine integrable_cont (by fun_prop) (Real.exp |t|) fun θ => ?_
  rw [abs_mul, Real.abs_exp]
  have h1 : t * angCos θ ≤ |t| := by
    calc t * angCos θ ≤ |t * angCos θ| := le_abs_self _
      _ = |t| * |angCos θ| := abs_mul _ _
      _ ≤ |t| * 1 := by gcongr; exact abs_angMode_le 1 θ
      _ = |t| := mul_one _
  calc Real.exp (t * angCos θ) * |h θ| ≤ Real.exp |t| * 1 := by
        gcongr
        exact hb θ
    _ = Real.exp |t| := mul_one _

theorem besselI_zero_pos (t : ℝ) : 0 < besselI 0 t := by
  have hc : Continuous angCos := continuous_angMode 1
  have hI := integrable_exp_mul t (fun _ => 1) continuous_const (fun _ => by simp)
  have hle : ∫ _θ, Real.exp (-|t|) ∂angHaar ≤ ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar := by
    refine integral_mono (integrable_const _) hI fun θ => ?_
    rw [mul_one]
    apply Real.exp_le_exp.mpr
    have := abs_angMode_le 1 θ
    have h2 : |t * angCos θ| ≤ |t| := by
      rw [abs_mul]
      calc |t| * |angCos θ| ≤ |t| * 1 := by gcongr
        _ = |t| := mul_one _
    linarith [neg_abs_le (t * angCos θ), abs_nonneg (t * angCos θ), (abs_le.mp h2).1]
  have h0 : besselI 0 t = ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar := by
    simp [besselI, angMode_zero]
  rw [h0]
  refine lt_of_lt_of_le ?_ hle
  simp [Real.exp_pos]

theorem hasSum_besselI_one_div (t : ℝ) (ht : t ≠ 0) :
    HasSum (fun j : ℕ => (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
      (besselI 1 t / t) := by
  have := (hasSum_besselI_one t).mul_left t⁻¹
  convert this using 1
  · funext j; field_simp
  · field_simp

theorem besselI1Over_zero : besselI1Over 0 = 1 / 2 := by
  unfold besselI1Over
  rw [tsum_eq_single 0]
  · simp
  · intro j hj
    simp [hj]

theorem besselI1Over_of_ne (t : ℝ) (ht : t ≠ 0) : besselI1Over t = besselI 1 t / t :=
  (hasSum_besselI_one_div t ht).tsum_eq

theorem hasSum_besselI1Over (t : ℝ) :
    HasSum (fun j : ℕ => (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
      (besselI1Over t) := by
  by_cases ht : t = 0
  · subst ht
    rw [besselI1Over_zero]
    have := hasSum_single (f := fun j : ℕ => (1 / 2) * ((0:ℝ) ^ 2 / 4) ^ j /
      ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))) 0 (fun j hj => by simp [hj])
    simpa using this
  · rw [besselI1Over_of_ne t ht]
    exact hasSum_besselI_one_div t ht

theorem series_bound (R : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (-R) R) (j : ℕ) :
    (t ^ 2 / 4) ^ j ≤ (R ^ 2 / 4) ^ j := by
  have : t ^ 2 ≤ R ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (neg_le_iff_add_nonneg.1 ht.1)]
  gcongr

theorem uniform_bound_summable (R : ℝ) : Summable fun j : ℕ => (R ^ 2 / 4) ^ j / (j.factorial : ℝ) :=
  Real.summable_pow_div_factorial _

theorem term_zero_le (R t : ℝ) (ht : t ∈ Set.Icc (-R) R) (j : ℕ) :
    ‖(t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2‖ ≤ (R ^ 2 / 4) ^ j / (j.factorial : ℝ) := by
  have h0 : 0 ≤ (t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg h0]
  have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
  refine div_le_div₀ (by positivity) (series_bound R t ht j) (by positivity) ?_
  nlinarith

theorem term_one_le (R t : ℝ) (ht : t ∈ Set.Icc (-R) R) (j : ℕ) :
    ‖(1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))‖
      ≤ (R ^ 2 / 4) ^ j / (j.factorial : ℝ) := by
  have h0 : 0 ≤ (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)) := by
    positivity
  rw [Real.norm_of_nonneg h0]
  have hf : (1 : ℝ) ≤ (j + 1).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp : 0 ≤ (t ^ 2 / 4) ^ j := by positivity
  have hq := series_bound R t ht j
  refine div_le_div₀ (by positivity) (by nlinarith) (by positivity) ?_
  have : (0 : ℝ) < j.factorial := by positivity
  nlinarith

theorem tendstoUniformlyOn_besselI_zero (R : ℝ) :
    TendstoUniformlyOn
      (fun (s : Finset ℕ) (t : ℝ) => ∑ j ∈ s, (t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2)
      (besselI 0) atTop (Set.Icc (-R) R) := by
  have h := tendstoUniformlyOn_tsum (f := fun (j : ℕ) (t : ℝ) => (t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2)
    (uniform_bound_summable R) (s := Set.Icc (-R) R) (fun j t ht => term_zero_le R t ht j)
  have e : (fun t : ℝ => ∑' j : ℕ, (t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2) = besselI 0 :=
    funext fun t => (hasSum_besselI_zero t).tsum_eq
  rwa [e] at h

theorem tendstoUniformlyOn_besselI1Over (R : ℝ) :
    TendstoUniformlyOn
      (fun (s : Finset ℕ) (t : ℝ) => ∑ j ∈ s,
        (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
      besselI1Over atTop (Set.Icc (-R) R) :=
  tendstoUniformlyOn_tsum (f := fun (j : ℕ) (t : ℝ) =>
    (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
    (uniform_bound_summable R) (s := Set.Icc (-R) R) (fun j t ht => term_one_le R t ht j)

theorem continuous_besselI1Over : Continuous besselI1Over := by
  rw [continuous_iff_continuousAt]
  intro t
  have hon : ContinuousOn besselI1Over (Set.Icc (-(|t| + 1)) (|t| + 1)) :=
    continuousOn_tsum (f := fun (j : ℕ) (t : ℝ) =>
      (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
      (fun j => by fun_prop) (uniform_bound_summable (|t| + 1))
      (fun j t ht => term_one_le _ t ht j)
  refine hon.continuousAt (Icc_mem_nhds ?_ ?_)
  · linarith [neg_abs_le t, abs_nonneg t]
  · linarith [le_abs_self t]

/-! ### Differentiation under the integral -/

theorem mul_angCos_le (x : ℝ) (θ : AngCircle) : x * angCos θ ≤ |x| := by
  calc x * angCos θ ≤ |x * angCos θ| := le_abs_self _
    _ = |x| * |angCos θ| := abs_mul _ _
    _ ≤ |x| * 1 := by gcongr; exact abs_angMode_le 1 θ
    _ = |x| := mul_one _

theorem hasDerivAt_exp_integral (h : AngCircle → ℝ) (hh : Continuous h) (hb : ∀ θ, |h θ| ≤ 1)
    (t : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ θ, Real.exp (x * angCos θ) * h θ ∂angHaar)
      (∫ θ, angCos θ * Real.exp (t * angCos θ) * h θ ∂angHaar) t := by
  have hc : Continuous angCos := continuous_angMode 1
  have hcb : ∀ θ, |angCos θ| ≤ 1 := abs_angMode_le 1
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := angHaar)
    (F := fun (x : ℝ) (θ : AngCircle) => Real.exp (x * angCos θ) * h θ)
    (F' := fun (x : ℝ) (θ : AngCircle) => angCos θ * Real.exp (x * angCos θ) * h θ)
    (s := Metric.ball t 1) (bound := fun _ => Real.exp (|t| + 1)) (x₀ := t)
    (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous _).aestronglyMeasurable)
    (integrable_exp_mul t h hh hb)
    (by fun_prop : Continuous _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ x hx => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun θ x _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    have hx' : |x| ≤ |t| + 1 := by
      have := Metric.mem_ball.mp hx
      rw [Real.dist_eq] at this
      calc |x| = |(x - t) + t| := by ring_nf
        _ ≤ |x - t| + |t| := abs_add_le _ _
        _ ≤ 1 + |t| := by linarith
        _ = |t| + 1 := add_comm _ _
    have he : Real.exp (x * angCos θ) ≤ Real.exp (|t| + 1) :=
      Real.exp_le_exp.mpr ((mul_angCos_le x θ).trans hx')
    have h1 := hcb θ
    have h2 := hb θ
    calc |angCos θ| * Real.exp (x * angCos θ) * |h θ| ≤ 1 * Real.exp (|t| + 1) * 1 := by
          gcongr
      _ = Real.exp (|t| + 1) := by ring
  · have := (((hasDerivAt_id x).mul_const (angCos θ)).exp).mul_const (h θ)
    refine this.congr_deriv ?_
    simp only [id]
    ring

theorem hasDerivAt_besselI (n : ℕ) (t : ℝ) :
    HasDerivAt (besselI n) (∫ θ, angCos θ * Real.exp (t * angCos θ) * angMode n θ ∂angHaar) t :=
  hasDerivAt_exp_integral (angMode n) (continuous_angMode n) (abs_angMode_le n) t

theorem hasDerivAt_besselI_zero (t : ℝ) : HasDerivAt (besselI 0) (besselI 1 t) t := by
  have h := hasDerivAt_besselI 0 t
  rw [angMode_zero] at h
  convert h using 1
  simp [besselI, mul_comm]

/-! ### Parity -/

theorem angMode_add_pi (n : ℕ) (θ : AngCircle) :
    angMode n (θ + ((π : ℝ) : AngCircle)) = (-1) ^ n * angMode n θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    have : ((s : ℝ) : AngCircle) + ((π : ℝ) : AngCircle) = ((s + π : ℝ) : AngCircle) := by
      rfl
    rw [this, angMode_coe, angMode_coe, mul_add, Real.cos_add_nat_mul_pi]

theorem angCos_add_pi (θ : AngCircle) : angCos (θ + ((π : ℝ) : AngCircle)) = - angCos θ := by
  have := angMode_add_pi 1 θ
  simpa using this

theorem besselI_neg (n : ℕ) (t : ℝ) : besselI n (-t) = (-1) ^ n * besselI n t := by
  unfold besselI
  have h := integral_add_right_eq_self (μ := angHaar)
    (fun θ => Real.exp (t * angCos θ) * angMode n θ) ((π : ℝ) : AngCircle)
  simp only [angMode_add_pi] at h
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only
  have : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  calc Real.exp (-t * angCos θ) * angMode n θ
      = ((-1 : ℝ) ^ n * (-1) ^ n) * (Real.exp (-t * angCos θ) * angMode n θ) := by rw [this, one_mul]
    _ = _ := by rw [neg_mul, ← mul_neg]; ring_nf

theorem besselRatio_neg (t : ℝ) : besselRatio (-t) = - besselRatio t := by
  unfold besselRatio
  rw [besselI_neg 1, besselI_neg 0]
  simp [neg_div]

/-! ### The ratio `g = I₁/I₀` and its derivative -/

theorem hasDerivAt_besselRatio (t : ℝ) :
    HasDerivAt besselRatio
      (((∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar) * besselI 0 t
        - besselI 1 t * besselI 1 t) / besselI 0 t ^ 2) t := by
  have h1 := hasDerivAt_besselI 1 t
  have h0 := hasDerivAt_besselI_zero t
  exact h1.div h0 (besselI_zero_pos t).ne'

theorem integrable_cexp (t : ℝ) (h : AngCircle → ℝ) (hh : Continuous h) (hb : ∀ θ, |h θ| ≤ 1) :
    Integrable (fun θ => Real.exp (t * angCos θ) * h θ) angHaar :=
  integrable_exp_mul t h hh hb

theorem besselVariance_eq (t : ℝ) :
    besselVariance t =
      ((∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar) * besselI 0 t
        - besselI 1 t * besselI 1 t) / besselI 0 t ^ 2 := by
  have hc : Continuous angCos := continuous_angMode 1
  have hcb : ∀ θ, |angCos θ| ≤ 1 := abs_angMode_le 1
  have hE := (besselI_zero_pos t).ne'
  set E := besselI 0 t with hEdef
  set g := besselRatio t with hg
  have e0 : ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar = E := by
    rw [hEdef, besselI_zero]; simp
  have e1 : ∫ θ, Real.exp (t * angCos θ) * angCos θ ∂angHaar = besselI 1 t := by
    rw [besselI_one]; simp
  have i0 := integrable_cexp t (fun _ => 1) continuous_const (fun _ => by simp)
  have i1 := integrable_cexp t angCos hc hcb
  have i2 := integrable_cexp t (fun θ => angCos θ * angCos θ) (hc.mul hc) (fun θ => by
    rw [abs_mul]; nlinarith [hcb θ, abs_nonneg (angCos θ)])
  have hpt : ∀ θ : AngCircle, (angCos θ - g) ^ 2 * besselDensity t θ
      = E⁻¹ * (Real.exp (t * angCos θ) * (angCos θ * angCos θ))
        + (-(2 * g * E⁻¹)) * (Real.exp (t * angCos θ) * angCos θ)
        + (g ^ 2 * E⁻¹) * (Real.exp (t * angCos θ) * 1) := by
    intro θ; unfold besselDensity; rw [← hEdef]; ring
  have hv : besselVariance t = ∫ θ, ((E⁻¹ * (Real.exp (t * angCos θ) * (angCos θ * angCos θ))
        + (-(2 * g * E⁻¹)) * (Real.exp (t * angCos θ) * angCos θ))
        + (g ^ 2 * E⁻¹) * (Real.exp (t * angCos θ) * 1)) ∂angHaar :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hv]
  have jA : Integrable (fun θ => E⁻¹ * (Real.exp (t * angCos θ) * (angCos θ * angCos θ))) angHaar :=
    i2.const_mul _
  have jB : Integrable (fun θ => (-(2 * g * E⁻¹)) * (Real.exp (t * angCos θ) * angCos θ)) angHaar :=
    i1.const_mul _
  have jC : Integrable (fun θ => (g ^ 2 * E⁻¹) * (Real.exp (t * angCos θ) * 1)) angHaar :=
    i0.const_mul _
  have jAB : Integrable (fun θ => E⁻¹ * (Real.exp (t * angCos θ) * (angCos θ * angCos θ))
      + (-(2 * g * E⁻¹)) * (Real.exp (t * angCos θ) * angCos θ)) angHaar := jA.add jB
  rw [integral_add jAB jC, integral_add jA jB,
    integral_const_mul, integral_const_mul, integral_const_mul, e0, e1]
  have hK : ∫ θ, Real.exp (t * angCos θ) * (angCos θ * angCos θ) ∂angHaar
      = ∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only; ring
  rw [hK]
  generalize (∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar) = K
  rw [hg]
  unfold besselRatio
  rw [← hEdef]
  field_simp
  ring

theorem besselVariance_pos (t : ℝ) : 0 < besselVariance t := by
  have hc : Continuous angCos := continuous_angMode 1
  have hcb : ∀ θ, |angCos θ| ≤ 1 := abs_angMode_le 1
  have hE := besselI_zero_pos t
  set g := besselRatio t with hg
  have hcont : Continuous fun θ => (angCos θ - g) ^ 2 * besselDensity t θ := by
    unfold besselDensity; fun_prop
  have hnn : 0 ≤ᵐ[angHaar] fun θ => (angCos θ - g) ^ 2 * besselDensity t θ :=
    Filter.Eventually.of_forall fun θ => by
      unfold besselDensity; positivity
  have hint : Integrable (fun θ => (angCos θ - g) ^ 2 * besselDensity t θ) angHaar := by
    refine integrable_cont hcont ((1 + |g|) ^ 2 * (Real.exp |t| / besselI 0 t)) fun θ => ?_
    unfold besselDensity
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity : 0 < Real.exp (t * angCos θ) / besselI 0 t)]
    have h1 : |angCos θ - g| ≤ 1 + |g| := (abs_sub _ _).trans (by linarith [hcb θ])
    have h2 : Real.exp (t * angCos θ) ≤ Real.exp |t| := Real.exp_le_exp.mpr (mul_angCos_le t θ)
    have h3 : (angCos θ - g) ^ 2 ≤ (1 + |g|) ^ 2 := by
      rw [← sq_abs (angCos θ - g)]; gcongr
    gcongr
  unfold besselVariance
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  have hU : IsOpen {θ : AngCircle | angCos θ ≠ g} := isOpen_ne_fun hc continuous_const
  have hne : {θ : AngCircle | angCos θ ≠ g}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : angCos (0 : AngCircle) = g := by
      by_contra h; exact (Set.eq_empty_iff_forall_notMem.mp hemp) 0 h
    have hpi : angCos ((π : ℝ) : AngCircle) = g := by
      by_contra h; exact (Set.eq_empty_iff_forall_notMem.mp hemp) _ h
    have a0 : angCos (0 : AngCircle) = 1 := by
      have := angMode_coe 1 0
      simpa using this
    have a1 : angCos ((π : ℝ) : AngCircle) = -1 := by
      have := angMode_coe 1 π
      simpa using this
    linarith
  refine lt_of_lt_of_le (hU.measure_pos angHaar hne) (measure_mono ?_)
  intro θ hθ
  simp only [Function.mem_support]
  unfold besselDensity
  have : angCos θ - g ≠ 0 := sub_ne_zero.mpr hθ
  positivity

theorem besselRatio_eq_mean (t : ℝ) :
    besselRatio t = ∫ θ, angCos θ * besselDensity t θ ∂angHaar := by
  unfold besselDensity besselRatio
  have : ∀ θ : AngCircle, angCos θ * (Real.exp (t * angCos θ) / besselI 0 t)
      = (besselI 0 t)⁻¹ * (Real.exp (t * angCos θ) * angCos θ) := by
    intro θ; ring
  simp_rw [this]
  rw [integral_const_mul]
  have e1 : ∫ θ, Real.exp (t * angCos θ) * angCos θ ∂angHaar = besselI 1 t := by
    rw [besselI_one]; simp
  rw [e1]
  ring

end DGPS.Circle.BesselMoments

namespace DGPS.Examples

open DGPS.Circle.BesselMoments

/-- EX002: Bessel integral series and moment derivatives.  On the angular circle with normalized
Haar measure `dm`, `I_n(t) = ∫ exp(t cos θ) cos(nθ) dm` has the interval-integral form, `I₀ > 0`,
`I₀(t) = ∑ (t²/4)^j/(j!)²` and `I₁(t)/t = (1/2) ∑ (t²/4)^j/(j!(j+1)!)` with continuous extension
`1/2` at `0` (both series converge uniformly on every compact interval); parameter derivatives
pass under the integral (`I₀' = I₁`), `I_n(-t) = (-1)^n I_n(t)`, and `g = I₁/I₀` is odd with
`g(t) = E_{q_t} cos`, `g' = Var_{q_t}(cos) > 0`. -/
theorem bessel_integral_series_and_moment_derivatives :
    (∀ (n : ℕ) (t : ℝ), besselI n t =
      (2 * Real.pi)⁻¹ * ∫ s in (0 : ℝ)..2 * Real.pi,
        Real.exp (t * Real.cos s) * Real.cos ((n : ℝ) * s)) ∧
    (∀ t : ℝ, 0 < besselI 0 t) ∧
    (∀ t : ℝ, HasSum (fun j : ℕ => (t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2) (besselI 0 t)) ∧
    (∀ R : ℝ, TendstoUniformlyOn
      (fun (s : Finset ℕ) (t : ℝ) => ∑ j ∈ s, (t ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2)
      (besselI 0) Filter.atTop (Set.Icc (-R) R)) ∧
    (∀ t : ℝ, t ≠ 0 → HasSum
      (fun j : ℕ => (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
      (besselI 1 t / t)) ∧
    (∀ t : ℝ, HasSum
      (fun j : ℕ => (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
      (besselI1Over t)) ∧
    (Continuous besselI1Over ∧ besselI1Over 0 = 1 / 2 ∧
      ∀ t : ℝ, t ≠ 0 → besselI1Over t = besselI 1 t / t) ∧
    (∀ R : ℝ, TendstoUniformlyOn
      (fun (s : Finset ℕ) (t : ℝ) => ∑ j ∈ s,
        (1 / 2) * (t ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)))
      besselI1Over Filter.atTop (Set.Icc (-R) R)) ∧
    (∀ (n : ℕ) (t : ℝ), HasDerivAt (besselI n)
      (∫ θ, angCos θ * Real.exp (t * angCos θ) * angMode n θ ∂DGPS.Circle.AngularNormalization.angHaar) t) ∧
    (∀ t : ℝ, HasDerivAt (besselI 0) (besselI 1 t) t) ∧
    (∀ (n : ℕ) (t : ℝ), besselI n (-t) = (-1) ^ n * besselI n t) ∧
    (∀ t : ℝ, besselRatio (-t) = - besselRatio t) ∧
    (∀ t : ℝ, besselRatio t =
      ∫ θ, angCos θ * besselDensity t θ ∂DGPS.Circle.AngularNormalization.angHaar) ∧
    (∀ t : ℝ, HasDerivAt besselRatio (besselVariance t) t ∧ 0 < besselVariance t) :=
  ⟨besselI_eq_interval, besselI_zero_pos, hasSum_besselI_zero, tendstoUniformlyOn_besselI_zero,
    hasSum_besselI_one_div, hasSum_besselI1Over,
    ⟨continuous_besselI1Over, besselI1Over_zero, besselI1Over_of_ne⟩,
    tendstoUniformlyOn_besselI1Over, hasDerivAt_besselI, hasDerivAt_besselI_zero, besselI_neg,
    besselRatio_neg, besselRatio_eq_mean,
    fun t => ⟨(besselVariance_eq t) ▸ hasDerivAt_besselRatio t, besselVariance_pos t⟩⟩

end DGPS.Examples
