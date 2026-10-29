import DGPS.Frontier.STR029.T02
import DGPS.Frontier.STR029.T03
import DGPS.Frontier.STR029.T04

/-!
# STR029.35: Quantitative weighted cross-form estimate

Task id: STR029.35. Title: Quantitative weighted cross-form estimate (node STR029).

Provides:
* `DGPS.Frontier.STR029.str029_35_quantitative_weighted_cross_form_estimate`: main statement. For `|h| ≤ 1/1000`,
  `s = |h|`, `f` periodic `H¹` with weak derivative `g`, `p` the first harmonic of `f`, `w = f - mean - p`, and
  `b = ∫ (w'² - w²) dm` with `w' = g - p'`: (1) `∫ g² q_h dm - Var_{q_h m}(f) ≥ c(s) b - 2 s ℓ(s) ‖p‖₂ √b`;
  (2) `Var_{q_h m}(f) ≥ e^{-2s} (‖p‖₂² + ‖w‖₂²)`.
* `DGPS.Frontier.STR029.varQ_STR02935`: weighted variance `∫ F² q_h dm - (∫ F q_h dm)²`.
* `DGPS.Frontier.STR029.cFun_STR02935`: `c(s) = (4 e^{-2s} - e^{2s})/3`.
* `DGPS.Frontier.STR029.ellFun_STR02935`: `ℓ(s) = √(9/10) + 3√3 s`.
* `DGPS.Frontier.STR029.firstHarm_STR02935`: first harmonic `p = c₁(f) cos t + s₁(f) sin t` of `f`.
* `DGPS.Frontier.STR029.compl_STR02935`: complementary part `w = f - ∫ f dm - p`.
* `DGPS.Frontier.STR029.bForm_STR02935`: `b = ∫ ((g - p')² - w²) dm`.
* `DGPS.Frontier.STR029.harm_STR02935`: the harmonic `A cos t + B sin t`.
* `DGPS.Frontier.STR029.dharm_STR02935`: its derivative `B cos t - A sin t`.
* `DGPS.Frontier.STR029.lower_I_STR02935`: for `w` with weak derivative `gw` and zero mean and zero first Fourier
  coefficients, `c(|h|) ∫ (gw² - w²) dm - 2 |h| ℓ(|h|) √((A²+B²)/2) √(∫ (gw² - w²) dm)` is at most
  `∫ (p' + gw)² q_h dm - ∫ (p + w)² q_h dm`.
* `DGPS.Frontier.STR029.var_lower_STR02935`: for `F ∈ L²` with `∫ F dm = 0`, `e^{-2|h|} ∫ F² dm ≤ Var_{q_h m}(F)`.
* `DGPS.Frontier.STR029.cross_STR02935`: the cross term equals `h ∫ 3 sin(3t) p' w q_h dm`.
* `DGPS.Frontier.STR029.cross_bound_STR02935`: that cross term is at most `|h| ℓ(|h|) √((A²+B²)/2) √(∫ (gw² - w²) dm)`.
* `DGPS.Frontier.STR029.compl_bound_STR02935`: `c(|h|) ∫ (gw² - w²) dm ≤ ∫ (gw² - w²) q_h dm`.
* `DGPS.Frontier.STR029.compl_orth_STR02935`: `w` has zero mean and is orthogonal to `cos` and `sin`.
* `DGPS.Frontier.STR029.compl_weak_STR02935`: `w` has weak derivative `g - p'`.
* `DGPS.Frontier.STR029.weakDeriv_sub_STR02935`: weak derivatives subtract.
* `DGPS.Frontier.STR029.weak_of_smooth_STR02935`: a smooth periodic function has its classical derivative as weak derivative.
* `DGPS.Frontier.STR029.atoms_STR02935`: the six elementary integrals of `cos`, `sin` products over the circle.
* `DGPS.Frontier.STR029.normInt_eq_STR02935`: the two normalized-integral conventions (`normInt_STR02933` and
  `normInt_STR02904`) agree.
* `DGPS.Frontier.STR029.normInt_harm_sq_STR02935`: `∫ (A cos + B sin)² dm = (A²+B²)/2`.
* `DGPS.Frontier.STR029.normInt_dharm_sq_STR02935`: `∫ (B cos - A sin)² dm = (A²+B²)/2`.
* `DGPS.Frontier.STR029.normInt_harm_sq_q_STR02935`: the same two values with the weight `q_h`.
* `DGPS.Frontier.STR029.normInt_qT_STR02935`: `∫ q_h dm = 1`.
* `DGPS.Frontier.STR029.hasDerivAt_qT_STR02935`: `q_h' = -3 h sin(3t) q_h`.
* `DGPS.Frontier.STR029.hasDerivAt_dq_STR02935`: derivative of `p' q_h`.
* `DGPS.Frontier.STR029.hasDerivAt_harm_STR02935`: derivative of the harmonic.
* `DGPS.Frontier.STR029.hasDerivAt_dharm_STR02935`: derivative of its derivative.
* `DGPS.Frontier.STR029.deriv_harm_STR02935`: `deriv (harm A B) = dharm A B`.
* `DGPS.Frontier.STR029.continuous_harm_STR02935`: continuity of the harmonic.
* `DGPS.Frontier.STR029.continuous_dharm_STR02935`: continuity of its derivative.
* `DGPS.Frontier.STR029.contDiff_harm_STR02935`: smoothness of the harmonic.
* `DGPS.Frontier.STR029.contDiff_dharm_STR02935`: smoothness of its derivative.
* `DGPS.Frontier.STR029.periodic_harm_STR02935`: `2π`-periodicity of the harmonic.
* `DGPS.Frontier.STR029.periodic_dharm_STR02935`: `2π`-periodicity of its derivative.
* `DGPS.Frontier.STR029.memLp_of_continuous_STR02935`: a continuous function is `L²` on `(0, 2π]`.
* `DGPS.Frontier.STR029.memLp_mul_continuous_STR02935`: continuous times `L²` is `L²`.
* `DGPS.Frontier.STR029.integrable_mul_memLp_STR02935`: a product of two `L²` functions is integrable.
* `DGPS.Frontier.STR029.integrable_cmul_left_STR02935`: continuous times `L²` is integrable.
* `DGPS.Frontier.STR029.integrable_cmul_STR02935`: continuous times a product of two `L²` functions is integrable.
* `DGPS.Frontier.STR029.integrable_sq_STR02935`: the square of an `L²` function is integrable.
* `DGPS.Frontier.STR029.normInt_mono_STR02935`: monotonicity of `∫ · dm`.
* `DGPS.Frontier.STR029.normInt_nonneg_STR02935`: `∫ · dm` of a nonnegative function is nonnegative.
* `DGPS.Frontier.STR029.normInt_lin2_STR02935`: linearity of `∫ · dm` for two integrable terms.
* `DGPS.Frontier.STR029.normInt_lin3_STR02935`: linearity of `∫ · dm` for three integrable terms.
* `DGPS.Frontier.STR029.normInt_lin4_STR02935`: linearity of `∫ · dm` for four integrable terms.
* `DGPS.Frontier.STR029.normInt_const_STR02935`: `∫ c dm = c`.
* `DGPS.Frontier.STR029.cs_normInt_STR02935`: Cauchy-Schwarz for `∫ · dm` on `L²`.

R5 notes:
* Frozen statement, no extra hypotheses: `h` real with `|h| ≤ 1/1000` (so `s = |h|`), `f g : ℝ → ℝ` with
  `IsPeriodicWeakDerivative_STR02933 f g` (periodic `H¹` in the sense of the shared Fourier infrastructure: `f`, `g`
  periodic and `L²`, with the weak identity against smooth periodic tests). No regularity beyond that is assumed.
* The derivative `f'` of the specification is the given weak derivative `g`; the left side of (1) is
  `∫ g² q_h dm` (`normInt_STR02933 (g² q_h)`). The weight is `qT_STR02904 h` (the density `q_h` of the earlier
  reference-symmetries unit), with `dm = dt/(2π)` realized by `normInt_STR02933` on `Ioc 0 (2π)` (null-set endpoint
  difference from `[0, 2π)`); the bridge `normInt_eq_STR02935` identifies it with the interval-integral convention
  `normInt_STR02904` used for `q_h`. Integrals are Bochner integrals (value `0` if not integrable); every
  integrability needed is proved in the body.
* "Subtract the Haar mean": `f₀ = f - ∫ f dm` is used inside the variance, and the variance is the explicit
  `varQ_STR02935 h F = ∫ F² q_h dm - (∫ F q_h dm)²` applied to `F = f - ∫ f dm`. Var is shift-invariant, so this is
  the specification's `Var_{q_h m}(f)`; the statement is written with the mean subtracted, as in the specification.
* First harmonic and complement: with `A = c₁(f)`, `B = s₁(f)` (`cosCoeff_STR02933 f 1`, `sinCoeff_STR02933 f 1`),
  `p = firstHarm_STR02935 f = A cos t + B sin t` and `w = compl_STR02935 f = f - ∫ f dm - p`. The decomposition
  `f - mean = p + w` is exact for every `t` (not merely almost everywhere).
* `b` is `bForm_STR02935 f g = ∫ ((g - p')² - w²) dm`, where `w' = g - p'` is the weak derivative of `w`
  (`compl_weak_STR02935`) and `p'` is `deriv (firstHarm_STR02935 f)` (equal to `B cos t - A sin t`). By the earlier
  complementary-quadratic unit, `b ≥ 3 ∫ w² dm ≥ 0`, so `Real.sqrt b` is the true square root; the proof of the
  estimate does not need this separately.
* `‖p‖₂` is `Real.sqrt (∫ p² dm)` and `‖w‖₂²` is `∫ w² dm`, with the normalized `L²` norm for `dm`.
  Constants are `cFun_STR02935 s = (4 e^{-2s} - e^{2s})/3` and `ellFun_STR02935 s = √(9/10) + 3√3 s`, evaluated at `s = |h|`.
* Both inequalities are stated with `≥`, as in the specification, and are conjoined in one theorem.
* The Euler range map is not used; only the variational (weighted second variation) form appears.
-/

open MeasureTheory Set Real
open scoped ContDiff

namespace DGPS.Frontier.STR029

theorem normInt_eq_STR02935 (f : ℝ → ℝ) : normInt_STR02933 f = normInt_STR02904 f := by
  unfold normInt_STR02933 normInt_STR02904
  rw [intervalIntegral.integral_of_le (by positivity)]

theorem memLp_of_continuous_STR02935 {c : ℝ → ℝ} (hc : Continuous c) :
    MemLp c 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact ae_of_all _ fun t ht => hC t (Ioc_subset_Icc_self ht)

theorem memLp_mul_continuous_STR02935 {c u : ℝ → ℝ} (hc : Continuous c)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    MemLp (fun t => c t * u t) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  refine hu.of_le_mul (c := C) (hc.aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine ae_of_all _ fun t ht => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC t (Ioc_subset_Icc_self ht)) (norm_nonneg _)

theorem integrable_mul_memLp_STR02935 {u v : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π))))
    (hv : MemLp v 2 (volume.restrict (Ioc 0 (2 * π)))) :
    Integrable (fun t => u t * v t) (volume.restrict (Ioc 0 (2 * π))) :=
  hu.integrable_mul hv

theorem integrable_cmul_left_STR02935 {c u : ℝ → ℝ} (hc : Continuous c)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    Integrable (fun t => c t * u t) (volume.restrict (Ioc 0 (2 * π))) :=
  (memLp_mul_continuous_STR02935 hc hu).integrable (by norm_num)

theorem integrable_cmul_STR02935 {c u v : ℝ → ℝ} (hc : Continuous c)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π))))
    (hv : MemLp v 2 (volume.restrict (Ioc 0 (2 * π)))) :
    Integrable (fun t => c t * (u t * v t)) (volume.restrict (Ioc 0 (2 * π))) :=
  (integrable_mul_memLp_STR02935 (memLp_mul_continuous_STR02935 hc hu) hv).congr
    (ae_of_all _ fun t => by ring)

theorem integrable_sq_STR02935 {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    Integrable (fun t => u t ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
  (integrable_mul_memLp_STR02935 hu hu).congr (ae_of_all _ fun t => by ring)

theorem normInt_mono_STR02935 {f g : ℝ → ℝ}
    (hf : Integrable f (volume.restrict (Ioc 0 (2 * π))))
    (hg : Integrable g (volume.restrict (Ioc 0 (2 * π)))) (h : ∀ t, f t ≤ g t) :
    normInt_STR02933 f ≤ normInt_STR02933 g := by
  unfold normInt_STR02933
  exact mul_le_mul_of_nonneg_left (integral_mono hf hg h) (by positivity)

theorem normInt_nonneg_STR02935 {f : ℝ → ℝ} (h : ∀ t, 0 ≤ f t) : 0 ≤ normInt_STR02933 f := by
  unfold normInt_STR02933
  exact mul_nonneg (by positivity) (integral_nonneg h)

theorem normInt_lin3_STR02935 {u v z : ℝ → ℝ}
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π))))
    (hv : Integrable v (volume.restrict (Ioc 0 (2 * π))))
    (hz : Integrable z (volume.restrict (Ioc 0 (2 * π)))) (α β γ : ℝ) :
    normInt_STR02933 (fun t => α * u t + β * v t + γ * z t)
      = α * normInt_STR02933 u + β * normInt_STR02933 v + γ * normInt_STR02933 z := by
  unfold normInt_STR02933
  have i2 : Integrable (fun t => α * u t + β * v t) (volume.restrict (Ioc 0 (2 * π))) :=
    (hu.const_mul α).add (hv.const_mul β)
  rw [integral_add i2 (hz.const_mul γ), integral_add (hu.const_mul α) (hv.const_mul β),
    integral_const_mul, integral_const_mul, integral_const_mul]
  ring

theorem normInt_lin4_STR02935 {u v z y : ℝ → ℝ}
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π))))
    (hv : Integrable v (volume.restrict (Ioc 0 (2 * π))))
    (hz : Integrable z (volume.restrict (Ioc 0 (2 * π))))
    (hy : Integrable y (volume.restrict (Ioc 0 (2 * π)))) (α β γ δ : ℝ) :
    normInt_STR02933 (fun t => α * u t + β * v t + γ * z t + δ * y t)
      = α * normInt_STR02933 u + β * normInt_STR02933 v + γ * normInt_STR02933 z
        + δ * normInt_STR02933 y := by
  unfold normInt_STR02933
  have i2 : Integrable (fun t => α * u t + β * v t) (volume.restrict (Ioc 0 (2 * π))) :=
    (hu.const_mul α).add (hv.const_mul β)
  have i3 : Integrable (fun t => α * u t + β * v t + γ * z t) (volume.restrict (Ioc 0 (2 * π))) :=
    i2.add (hz.const_mul γ)
  rw [integral_add i3 (hy.const_mul δ), integral_add i2 (hz.const_mul γ),
    integral_add (hu.const_mul α) (hv.const_mul β),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

theorem hasDerivAt_qT_STR02935 (h t : ℝ) :
    HasDerivAt (qT_STR02904 h) (-(3 * h * Real.sin (3 * t)) * qT_STR02904 h t) t := by
  have e : qT_STR02904 h = fun t =>
      (normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))))⁻¹ *
        Real.exp (h * Real.cos (3 * t)) := funext (qT_eq_STR02904 h)
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => 3 * t) 3 t := by
    simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
  have h4 := (((h1.cos).const_mul h).exp).const_mul
    (normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))))⁻¹
  refine h4.congr_deriv ?_
  beta_reduce
  ring

theorem normInt_qT_STR02935 (h : ℝ) : normInt_STR02933 (qT_STR02904 h) = 1 := by
  rw [normInt_eq_STR02935]
  have : qT_STR02904 h = fun t =>
      (normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))))⁻¹ *
        Real.exp (h * Real.cos (3 * t)) := funext (qT_eq_STR02904 h)
  rw [this, normInt_const_mul_STR02904]
  exact inv_mul_cancel₀ (partition_pos_STR02904 h).ne'

theorem cs_normInt_STR02935 {u v : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π))))
    (hv : MemLp v 2 (volume.restrict (Ioc 0 (2 * π)))) :
    (normInt_STR02933 (fun t => u t * v t)) ^ 2
      ≤ normInt_STR02933 (fun t => u t ^ 2) * normInt_STR02933 (fun t => v t ^ 2) := by
  have iu := integrable_sq_STR02935 hu
  have iv := integrable_sq_STR02935 hv
  have iuv := integrable_mul_memLp_STR02935 hu hv
  have key := quad_nonneg_imp_STR02902 (A := normInt_STR02933 (fun t => v t ^ 2))
    (B := normInt_STR02933 (fun t => u t * v t)) (C := normInt_STR02933 (fun t => u t ^ 2))
    (fun y => by
      have e : (fun t => (u t - y * v t) ^ 2)
          = fun t => 1 * (u t ^ 2) + (-2 * y) * (u t * v t) + (y * y) * (v t ^ 2) := by
        funext t; ring
      have h0 : 0 ≤ normInt_STR02933 (fun t => (u t - y * v t) ^ 2) :=
        normInt_nonneg_STR02935 fun t => sq_nonneg _
      rw [e, normInt_lin3_STR02935 iu iuv iv] at h0
      linarith)
  linarith

/-- The first harmonic `A cos t + B sin t`. -/
noncomputable def harm_STR02935 (A B t : ℝ) : ℝ := A * Real.cos t + B * Real.sin t

/-- The derivative `B cos t - A sin t` of the first harmonic. -/
noncomputable def dharm_STR02935 (A B t : ℝ) : ℝ := B * Real.cos t + (-A) * Real.sin t

theorem continuous_harm_STR02935 (A B : ℝ) : Continuous (harm_STR02935 A B) := by
  unfold harm_STR02935; fun_prop

theorem continuous_dharm_STR02935 (A B : ℝ) : Continuous (dharm_STR02935 A B) := by
  unfold dharm_STR02935; fun_prop

theorem contDiff_harm_STR02935 (A B : ℝ) : ContDiff ℝ ∞ (harm_STR02935 A B) :=
  (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)

theorem periodic_harm_STR02935 (A B : ℝ) : Function.Periodic (harm_STR02935 A B) (2 * π) := by
  intro x
  simp [harm_STR02935]

theorem periodic_dharm_STR02935 (A B : ℝ) : Function.Periodic (dharm_STR02935 A B) (2 * π) := by
  intro x
  simp [dharm_STR02935]

theorem deriv_harm_STR02935 (A B : ℝ) : deriv (harm_STR02935 A B) = dharm_STR02935 A B :=
  deriv_harmonic_STR02904 A B

theorem hasDerivAt_harm_STR02935 (A B t : ℝ) :
    HasDerivAt (harm_STR02935 A B) (dharm_STR02935 A B t) t := by
  have := ((Real.hasDerivAt_cos t).const_mul A).add ((Real.hasDerivAt_sin t).const_mul B)
  refine this.congr_deriv ?_
  simp only [dharm_STR02935]
  ring

theorem hasDerivAt_dharm_STR02935 (A B t : ℝ) :
    HasDerivAt (dharm_STR02935 A B) (-harm_STR02935 A B t) t := by
  have := ((Real.hasDerivAt_cos t).const_mul B).add ((Real.hasDerivAt_sin t).const_mul (-A))
  refine this.congr_deriv ?_
  simp only [harm_STR02935]
  ring

theorem normInt_harm_sq_STR02935 (A B : ℝ) :
    normInt_STR02933 (fun t => harm_STR02935 A B t ^ 2) = (A ^ 2 + B ^ 2) / 2 := by
  rw [normInt_eq_STR02935]
  exact str029_04_reference_symmetries_quantitative_density_bounds_harmonic_value A B

theorem normInt_dharm_sq_STR02935 (A B : ℝ) :
    normInt_STR02933 (fun t => dharm_STR02935 A B t ^ 2) = (A ^ 2 + B ^ 2) / 2 := by
  have h := normInt_harm_sq_STR02935 B (-A)
  have e : (fun t => dharm_STR02935 A B t ^ 2) = fun t => harm_STR02935 B (-A) t ^ 2 := rfl
  rw [e, h]
  ring

theorem normInt_harm_sq_q_STR02935 (h A B : ℝ) :
    normInt_STR02933 (fun t => harm_STR02935 A B t ^ 2 * qT_STR02904 h t) = (A ^ 2 + B ^ 2) / 2 ∧
      normInt_STR02933 (fun t => dharm_STR02935 A B t ^ 2 * qT_STR02904 h t)
        = (A ^ 2 + B ^ 2) / 2 := by
  obtain ⟨-, h2, h3⟩ := str029_04_reference_symmetries_quantitative_density_bounds_harmonic h
    (harm_STR02935 A B) ⟨A, B, fun t => rfl⟩
  rw [deriv_harm_STR02935] at h3
  refine ⟨?_, ?_⟩
  · rw [normInt_eq_STR02935]
    exact h2.trans (str029_04_reference_symmetries_quantitative_density_bounds_harmonic_value A B)
  · rw [normInt_eq_STR02935]
    exact h3.trans (str029_04_reference_symmetries_quantitative_density_bounds_harmonic_value A B)

theorem weakDeriv_sub_STR02935 {u v gu gv : ℝ → ℝ}
    (hu : IsPeriodicWeakDerivative_STR02933 u gu) (hv : IsPeriodicWeakDerivative_STR02933 v gv) :
    IsPeriodicWeakDerivative_STR02933 (fun t => u t - v t) (fun t => gu t - gv t) := by
  obtain ⟨⟨hup, hul⟩, ⟨hgup, hgul⟩, hweak⟩ := hu
  obtain ⟨⟨hvp, hvl⟩, ⟨hgvp, hgvl⟩, hweak'⟩ := hv
  refine ⟨⟨fun x => ?_, hul.sub hvl⟩, ⟨fun x => ?_, hgul.sub hgvl⟩, fun φ hφ => ?_⟩
  · show u (x + 2 * π) - v (x + 2 * π) = u x - v x
    rw [hup x, hvp x]
  · show gu (x + 2 * π) - gv (x + 2 * π) = gu x - gv x
    rw [hgup x, hgvp x]
  · have hφc : Continuous φ := hφ.1.continuous
    have hdφ : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
    have i1 := integrable_cmul_left_STR02935 hφc hgul
    have i2 := integrable_cmul_left_STR02935 hφc hgvl
    have i3 := integrable_cmul_left_STR02935 hdφ hul
    have i4 := integrable_cmul_left_STR02935 hdφ hvl
    have e1 := normInt_sub_STR02902 (f := fun t => gu t * φ t) (h := fun t => gv t * φ t)
      (i1.congr (ae_of_all _ fun t => by ring)) (i2.congr (ae_of_all _ fun t => by ring))
    have e2 := normInt_sub_STR02902 (f := fun t => u t * deriv φ t) (h := fun t => v t * deriv φ t)
      (i3.congr (ae_of_all _ fun t => by ring)) (i4.congr (ae_of_all _ fun t => by ring))
    have a1 := hweak φ hφ
    have a2 := hweak' φ hφ
    have f1 : (fun t => (gu t - gv t) * φ t) = fun t => gu t * φ t - gv t * φ t := by
      funext t; ring
    have f2 : (fun t => (u t - v t) * deriv φ t) = fun t => u t * deriv φ t - v t * deriv φ t := by
      funext t; ring
    rw [f1, f2, e1, e2, a1, a2]
    ring

theorem weak_of_smooth_STR02935 {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u (2 * π)) :
    IsPeriodicWeakDerivative_STR02933 u (deriv u) := by
  have hu1 : Continuous u := hu.continuous
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hdper : Function.Periodic (deriv u) (2 * π) := by
    intro x
    have e : u = fun y => u (y + 2 * π) := funext fun y => (hper y).symm
    calc deriv u (x + 2 * π) = deriv (fun y => u (y + 2 * π)) x :=
          (deriv_comp_add_const (f := u) (a := 2 * π) (x := x)).symm
      _ = deriv u x := by rw [← e]
  refine ⟨⟨hper, memLp_of_continuous_STR02935 hu1⟩, ⟨hdper, memLp_of_continuous_STR02935 hdu⟩,
    fun φ hφ => ?_⟩
  obtain ⟨hφs, hφp⟩ := hφ
  have hφc : Continuous φ := hφs.continuous
  have hdφ : Continuous (deriv φ) := hφs.continuous_deriv (by simp)
  have hderiv : ∀ x, HasDerivAt (fun t => u t * φ t) (deriv u x * φ x + u x * deriv φ x) x :=
    fun x => ((hu.differentiable (by simp) x).hasDerivAt).mul
      ((hφs.differentiable (by simp) x).hasDerivAt)
  have hc1 : Continuous (fun t => deriv u t * φ t) := hdu.mul hφc
  have hc2 : Continuous (fun t => u t * deriv φ t) := hu1.mul hdφ
  have hftc : ∫ t in (0 : ℝ)..(2 * π), (deriv u t * φ t + u t * deriv φ t)
      = u (2 * π) * φ (2 * π) - u 0 * φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      ((hc1.add hc2).intervalIntegrable _ _)
  have hu0 : u (2 * π) = u 0 := by simpa using hper 0
  have hφ0 : φ (2 * π) = φ 0 := by simpa using hφp 0
  rw [hu0, hφ0, sub_self,
    intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)] at hftc
  unfold normInt_STR02933
  rw [intervalIntegral.integral_of_le (by positivity)] at hftc
  have hfin : ∫ t in Ioc 0 (2 * π), deriv u t * φ t = -∫ t in Ioc 0 (2 * π), u t * deriv φ t := by
    rw [intervalIntegral.integral_of_le (by positivity)] at hftc
    linarith
  rw [hfin]
  ring

theorem normInt_lin2_STR02935 {u v : ℝ → ℝ}
    (hu : Integrable u (volume.restrict (Ioc 0 (2 * π))))
    (hv : Integrable v (volume.restrict (Ioc 0 (2 * π)))) (α β : ℝ) :
    normInt_STR02933 (fun t => α * u t + β * v t) = α * normInt_STR02933 u + β * normInt_STR02933 v := by
  have := normInt_lin3_STR02935 hu hv hv α β 0
  simpa using this

theorem normInt_const_STR02935 (c : ℝ) : normInt_STR02933 (fun _ => c) = c := by
  rw [normInt_eq_STR02935]
  exact normInt_const_STR02904 c

theorem contDiff_dharm_STR02935 (A B : ℝ) : ContDiff ℝ ∞ (dharm_STR02935 A B) :=
  (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)

theorem hasDerivAt_dq_STR02935 (h A B t : ℝ) :
    HasDerivAt (fun t => dharm_STR02935 A B t * qT_STR02904 h t)
      (-harm_STR02935 A B t * qT_STR02904 h t
        + dharm_STR02935 A B t * (-(3 * h * Real.sin (3 * t)) * qT_STR02904 h t)) t :=
  (hasDerivAt_dharm_STR02935 A B t).mul (hasDerivAt_qT_STR02935 h t)

theorem cross_STR02935 (h A B : ℝ) {w gw : ℝ → ℝ}
    (hw : IsPeriodicWeakDerivative_STR02933 w gw) :
    normInt_STR02933 (fun t =>
        (dharm_STR02935 A B t * gw t - harm_STR02935 A B t * w t) * qT_STR02904 h t)
      = h * normInt_STR02933 (fun t =>
        3 * Real.sin (3 * t) * dharm_STR02935 A B t * w t * qT_STR02904 h t) := by
  obtain ⟨⟨-, hwl⟩, ⟨-, hgl⟩, hweak⟩ := hw
  have cq := continuous_qT_STR02904 h
  have cd := continuous_dharm_STR02935 A B
  have ca := continuous_harm_STR02935 A B
  have hφs : IsSmoothPeriodicTest_STR02933 (fun t => dharm_STR02935 A B t * qT_STR02904 h t) := by
    refine ⟨(contDiff_dharm_STR02935 A B).mul (contDiff_qT_STR02904 h), ?_⟩
    intro x
    show dharm_STR02935 A B (x + 2 * π) * qT_STR02904 h (x + 2 * π)
      = dharm_STR02935 A B x * qT_STR02904 h x
    rw [periodic_dharm_STR02935 A B x, periodic_STR02904 h x]
  have hder : deriv (fun t => dharm_STR02935 A B t * qT_STR02904 h t)
      = fun t => -harm_STR02935 A B t * qT_STR02904 h t
        + dharm_STR02935 A B t * (-(3 * h * Real.sin (3 * t)) * qT_STR02904 h t) :=
    funext fun t => (hasDerivAt_dq_STR02935 h A B t).deriv
  have key := hweak _ hφs
  rw [hder] at key
  beta_reduce at key
  have iA : Integrable (fun t => gw t * (dharm_STR02935 A B t * qT_STR02904 h t))
      (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_left_STR02935 (c := fun t => dharm_STR02935 A B t * qT_STR02904 h t)
      (cd.mul cq) hgl).congr (ae_of_all _ fun t => by ring)
  have iB : Integrable (fun t => w t * (harm_STR02935 A B t * qT_STR02904 h t))
      (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_left_STR02935 (c := fun t => harm_STR02935 A B t * qT_STR02904 h t)
      (ca.mul cq) hwl).congr (ae_of_all _ fun t => by ring)
  have cS : Continuous (fun t : ℝ => Real.sin (3 * t)) := by fun_prop
  have iC : Integrable (fun t => 3 * Real.sin (3 * t) * dharm_STR02935 A B t * w t * qT_STR02904 h t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_left_STR02935 (c := fun t => 3 * Real.sin (3 * t) * dharm_STR02935 A B t
      * qT_STR02904 h t) (((continuous_const.mul cS).mul cd).mul cq) hwl).congr
      (ae_of_all _ fun t => by ring)
  have e1 : (fun t => (dharm_STR02935 A B t * gw t - harm_STR02935 A B t * w t) * qT_STR02904 h t)
      = fun t => gw t * (dharm_STR02935 A B t * qT_STR02904 h t)
        - w t * (harm_STR02935 A B t * qT_STR02904 h t) := by
    funext t; ring
  have e2 : (fun t => w t * (-harm_STR02935 A B t * qT_STR02904 h t
        + dharm_STR02935 A B t * (-(3 * h * Real.sin (3 * t)) * qT_STR02904 h t)))
      = fun t => (-1) * (w t * (harm_STR02935 A B t * qT_STR02904 h t))
        + (-h) * (3 * Real.sin (3 * t) * dharm_STR02935 A B t * w t * qT_STR02904 h t) := by
    funext t; ring
  rw [e2, normInt_lin2_STR02935 iB iC] at key
  rw [e1, normInt_sub_STR02902 iA iB]
  linarith

noncomputable def cFun_STR02935 (s : ℝ) : ℝ := (4 * Real.exp (-(2 * s)) - Real.exp (2 * s)) / 3

noncomputable def ellFun_STR02935 (s : ℝ) : ℝ := Real.sqrt (9 / 10) + 3 * Real.sqrt 3 * s

theorem compl_bound_STR02935 (h : ℝ) {w gw : ℝ → ℝ}
    (hw : IsPeriodicWeakDerivative_STR02933 w gw) (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0) :
    cFun_STR02935 |h| * normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2)
      ≤ normInt_STR02933 (fun t => (gw t ^ 2 - w t ^ 2) * qT_STR02904 h t) := by
  have T2 := (str029_02_complementary_fourier_quadratic_inequalities w gw hw h0 hc hs).1
  obtain ⟨⟨-, hwl⟩, ⟨-, hgl⟩, -⟩ := hw
  have cq := continuous_qT_STR02904 h
  have iG := integrable_sq_STR02935 hgl
  have iW := integrable_sq_STR02935 hwl
  have hb := normInt_sub_STR02902 iG iW
  have iR : Integrable (fun t => (gw t ^ 2 - w t ^ 2) * qT_STR02904 h t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    ((integrable_cmul_STR02935 cq hgl hgl).sub (integrable_cmul_STR02935 cq hwl hwl)).congr
      (ae_of_all _ fun t => by simp only [Pi.sub_apply]; ring)
  have s0 : 0 ≤ |h| := abs_nonneg h
  have pw : ∀ t, Real.exp (-(2 * |h|)) * gw t ^ 2 + (-Real.exp (2 * |h|)) * w t ^ 2
      ≤ (gw t ^ 2 - w t ^ 2) * qT_STR02904 h t := by
    intro t
    obtain ⟨hlo, hhi⟩ := qT_bounds_STR02904 h t
    nlinarith [mul_le_mul_of_nonneg_right hlo (sq_nonneg (gw t)),
      mul_le_mul_of_nonneg_right hhi (sq_nonneg (w t))]
  have iL : Integrable (fun t => Real.exp (-(2 * |h|)) * gw t ^ 2
      + (-Real.exp (2 * |h|)) * w t ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
    (iG.const_mul _).add (iW.const_mul _)
  have mono := normInt_mono_STR02935 iL iR pw
  rw [normInt_lin2_STR02935 iG iW] at mono
  have hE : Real.exp (-(2 * |h|)) ≤ Real.exp (2 * |h|) := Real.exp_le_exp.2 (by linarith)
  rw [hb] at T2
  have hpos := mul_nonneg (sub_nonneg.2 hE) (sub_nonneg.2 T2)
  unfold cFun_STR02935
  rw [hb]
  nlinarith [hpos, mono]

theorem cross_bound_STR02935 {h : ℝ} (hh : |h| ≤ 1 / 1000) (A B : ℝ) {w gw : ℝ → ℝ}
    (hw : IsPeriodicWeakDerivative_STR02933 w gw) (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0) :
    |h * normInt_STR02933 (fun t =>
        3 * Real.sin (3 * t) * dharm_STR02935 A B t * w t * qT_STR02904 h t)|
      ≤ |h| * ellFun_STR02935 |h| * Real.sqrt ((A ^ 2 + B ^ 2) / 2)
        * Real.sqrt (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2)) := by
  have T3 := (str029_03_exact_stable_dual_norm A B).2 w gw hw h0 hc hs
  have T2 := (str029_02_complementary_fourier_quadratic_inequalities w gw hw h0 hc hs).1
  obtain ⟨⟨-, hwl⟩, ⟨-, hgl⟩, -⟩ := hw
  have hP : normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2)
      = (A ^ 2 + B ^ 2) / 2 := normInt_harm_sq_STR02935 A B
  rw [hP] at T3
  have hW0 : 0 ≤ normInt_STR02933 (fun t => w t ^ 2) := normInt_nonneg_STR02935 fun t => sq_nonneg _
  have hb0 : 0 ≤ normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2) := by linarith
  have hP0 : 0 ≤ (A ^ 2 + B ^ 2) / 2 := by positivity
  have s0 : 0 ≤ |h| := abs_nonneg h
  obtain ⟨-, hq3, -⟩ := str029_04_reference_symmetries_quantitative_density_bounds_bounds h hh
  have cq := continuous_qT_STR02904 h
  have cd := continuous_dharm_STR02935 A B
  have cS : Continuous (fun t : ℝ => Real.sin (3 * t)) := by fun_prop
  have hf03 : ∀ t, f_STR02903 A B t = 3 * Real.sin (3 * t) * dharm_STR02935 A B t := by
    intro t
    unfold f_STR02903
    rw [deriv_p_STR02903]
    unfold dharm_STR02935
    ring
  obtain ⟨u, hu⟩ : ∃ u : ℝ → ℝ, u = fun t =>
      3 * Real.sin (3 * t) * dharm_STR02935 A B t * (qT_STR02904 h t - 1) := ⟨_, rfl⟩
  have hut : ∀ t, u t = 3 * Real.sin (3 * t) * dharm_STR02935 A B t * (qT_STR02904 h t - 1) :=
    fun t => by rw [hu]
  have cu : Continuous u := by
    rw [hu]
    exact ((continuous_const.mul cS).mul cd).mul (cq.sub continuous_const)
  have cf : Continuous (f_STR02903 A B) := by
    have : f_STR02903 A B = fun t => 3 * Real.sin (3 * t) * dharm_STR02935 A B t := funext hf03
    rw [this]
    exact (continuous_const.mul cS).mul cd
  have i1 : Integrable (fun t => f_STR02903 A B t * w t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_cmul_left_STR02935 cf hwl
  have i2 : Integrable (fun t => u t * w t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_cmul_left_STR02935 cu hwl
  have hsplit : normInt_STR02933 (fun t =>
        3 * Real.sin (3 * t) * dharm_STR02935 A B t * w t * qT_STR02904 h t)
      = normInt_STR02933 (fun t => f_STR02903 A B t * w t)
        + normInt_STR02933 (fun t => u t * w t) := by
    rw [← normInt_add_STR02934 i1 i2]
    congr 1
    funext t
    rw [hf03, hut]
    ring
  have cs := cs_normInt_STR02935 (memLp_of_continuous_STR02935 cu) hwl
  have hu2 : normInt_STR02933 (fun t => u t ^ 2) ≤ 81 * |h| ^ 2 * ((A ^ 2 + B ^ 2) / 2) := by
    have pw : ∀ t, u t ^ 2 ≤ (81 * |h| ^ 2) * dharm_STR02935 A B t ^ 2 := by
      intro t
      rw [hut]
      have h1 : (qT_STR02904 h t - 1) ^ 2 ≤ (3 * |h|) ^ 2 := by
        have := abs_le.1 (hq3 t)
        nlinarith [this.1, this.2]
      have h2 := Real.sin_sq_le_one (3 * t)
      have h3 : 0 ≤ dharm_STR02935 A B t ^ 2 * (qT_STR02904 h t - 1) ^ 2 := by positivity
      have h4 : dharm_STR02935 A B t ^ 2 * (qT_STR02904 h t - 1) ^ 2
          ≤ dharm_STR02935 A B t ^ 2 * (3 * |h|) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right h2 h3]
    have := normInt_mono_STR02935
      (integrable_continuous_STR02934 (f := fun t => u t ^ 2) (by fun_prop))
      (integrable_continuous_STR02934
        (f := fun t => 81 * |h| ^ 2 * dharm_STR02935 A B t ^ 2) (by fun_prop)) pw
    rw [normInt_mul_const_STR02933, normInt_dharm_sq_STR02935] at this
    exact this
  have hsq : (normInt_STR02933 (fun t => u t * w t)) ^ 2
      ≤ 27 * |h| ^ 2 * ((A ^ 2 + B ^ 2) / 2) * normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2) := by
    calc (normInt_STR02933 (fun t => u t * w t)) ^ 2
        ≤ normInt_STR02933 (fun t => u t ^ 2) * normInt_STR02933 (fun t => w t ^ 2) := cs
      _ ≤ (81 * |h| ^ 2 * ((A ^ 2 + B ^ 2) / 2)) * normInt_STR02933 (fun t => w t ^ 2) :=
          mul_le_mul_of_nonneg_right hu2 hW0
      _ ≤ (81 * |h| ^ 2 * ((A ^ 2 + B ^ 2) / 2))
            * (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2) / 3) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 27 * |h| ^ 2 * ((A ^ 2 + B ^ 2) / 2) * normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2) := by
          ring
  have habs : |normInt_STR02933 (fun t => u t * w t)|
      ≤ 3 * Real.sqrt 3 * |h| * Real.sqrt ((A ^ 2 + B ^ 2) / 2)
        * Real.sqrt (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2)) := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have : (3 * Real.sqrt 3 * |h| * Real.sqrt ((A ^ 2 + B ^ 2) / 2)
        * Real.sqrt (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2))) ^ 2
        = 27 * |h| ^ 2 * ((A ^ 2 + B ^ 2) / 2) * normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hb0, Real.sq_sqrt hP0,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    rw [this]
    exact hsq
  rw [hsplit, abs_mul]
  have habs3 := (abs_add_le _ _).trans (add_le_add T3 habs)
  calc |h| * |normInt_STR02933 (fun t => f_STR02903 A B t * w t)
        + normInt_STR02933 (fun t => u t * w t)|
      ≤ |h| * (Real.sqrt (9 / 10) * Real.sqrt ((A ^ 2 + B ^ 2) / 2)
          * Real.sqrt (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2))
        + 3 * Real.sqrt 3 * |h| * Real.sqrt ((A ^ 2 + B ^ 2) / 2)
          * Real.sqrt (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2))) :=
        mul_le_mul_of_nonneg_left habs3 s0
    _ = |h| * ellFun_STR02935 |h| * Real.sqrt ((A ^ 2 + B ^ 2) / 2)
        * Real.sqrt (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2)) := by
        unfold ellFun_STR02935
        ring

noncomputable def varQ_STR02935 (h : ℝ) (F : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => F t ^ 2 * qT_STR02904 h t)
    - (normInt_STR02933 (fun t => F t * qT_STR02904 h t)) ^ 2

theorem var_lower_STR02935 (h : ℝ) {F : ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict (Ioc 0 (2 * π)))) (hF0 : normInt_STR02933 F = 0) :
    Real.exp (-(2 * |h|)) * normInt_STR02933 (fun t => F t ^ 2) ≤ varQ_STR02935 h F := by
  have cq := continuous_qT_STR02904 h
  have iF2 := integrable_sq_STR02935 hF
  have iF := hF.integrable (by norm_num)
  have iFq : Integrable (fun t => F t * qT_STR02904 h t) (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_left_STR02935 cq hF).congr (ae_of_all _ fun t => by ring)
  have iF2q : Integrable (fun t => F t ^ 2 * qT_STR02904 h t) (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_STR02935 cq hF hF).congr (ae_of_all _ fun t => by ring)
  have iq : Integrable (qT_STR02904 h) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 cq
  have i1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 continuous_const
  set a0 := normInt_STR02933 (fun t => F t * qT_STR02904 h t) with ha0
  -- weighted second moment about a0
  have hW : normInt_STR02933 (fun t => (F t - a0) ^ 2 * qT_STR02904 h t)
      = normInt_STR02933 (fun t => F t ^ 2 * qT_STR02904 h t) - a0 ^ 2 := by
    have e : (fun t => (F t - a0) ^ 2 * qT_STR02904 h t)
        = fun t => 1 * (F t ^ 2 * qT_STR02904 h t) + (-2 * a0) * (F t * qT_STR02904 h t)
          + (a0 ^ 2) * qT_STR02904 h t := by
      funext t; ring
    rw [e, normInt_lin3_STR02935 iF2q iFq iq, normInt_qT_STR02935]
    rw [← ha0]
    ring
  have hU : normInt_STR02933 (fun t => (F t - a0) ^ 2)
      = normInt_STR02933 (fun t => F t ^ 2) + a0 ^ 2 := by
    have e : (fun t => (F t - a0) ^ 2)
        = fun t => 1 * (F t ^ 2) + (-2 * a0) * F t + (a0 ^ 2) * (fun _ : ℝ => (1 : ℝ)) t := by
      funext t; ring
    rw [e, normInt_lin3_STR02935 iF2 iF i1, hF0, normInt_one_STR02934]
    ring
  have pw : ∀ t, Real.exp (-(2 * |h|)) * (F t - a0) ^ 2 ≤ (F t - a0) ^ 2 * qT_STR02904 h t := by
    intro t
    have := mul_le_mul_of_nonneg_right (qT_bounds_STR02904 h t).1 (sq_nonneg (F t - a0))
    linarith
  have iL : Integrable (fun t => Real.exp (-(2 * |h|)) * (F t - a0) ^ 2)
      (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_sq_STR02935 (hF.sub (memLp_of_continuous_STR02935
      (continuous_const (y := a0))))).const_mul _
  have iR : Integrable (fun t => (F t - a0) ^ 2 * qT_STR02904 h t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_STR02935 cq (hF.sub (memLp_of_continuous_STR02935
      (continuous_const (y := a0)))) (hF.sub (memLp_of_continuous_STR02935
      (continuous_const (y := a0))))).congr (ae_of_all _ fun t => by simp only [Pi.sub_apply]; ring)
  have mono := normInt_mono_STR02935 iL iR pw
  rw [normInt_mul_const_STR02933, hU, hW] at mono
  unfold varQ_STR02935
  have hE : 0 < Real.exp (-(2 * |h|)) := Real.exp_pos _
  nlinarith [mul_nonneg hE.le (sq_nonneg a0)]

theorem lower_I_STR02935 {h : ℝ} (hh : |h| ≤ 1 / 1000) (A B : ℝ) {w gw : ℝ → ℝ}
    (hw : IsPeriodicWeakDerivative_STR02933 w gw) (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0) :
    cFun_STR02935 |h| * normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2)
      - 2 * |h| * ellFun_STR02935 |h| * Real.sqrt ((A ^ 2 + B ^ 2) / 2)
        * Real.sqrt (normInt_STR02933 (fun t => gw t ^ 2 - w t ^ 2))
      ≤ normInt_STR02933 (fun t => (dharm_STR02935 A B t + gw t) ^ 2 * qT_STR02904 h t)
        - normInt_STR02933 (fun t => (harm_STR02935 A B t + w t) ^ 2 * qT_STR02904 h t) := by
  have hX := cross_bound_STR02935 hh A B hw h0 hc hs
  have hC := compl_bound_STR02935 h hw h0 hc hs
  have hcr := cross_STR02935 h A B hw
  obtain ⟨⟨-, hwl⟩, ⟨-, hgl⟩, -⟩ := hw
  have cq := continuous_qT_STR02904 h
  have cd := continuous_dharm_STR02935 A B
  have ca := continuous_harm_STR02935 A B
  have mdp : MemLp (dharm_STR02935 A B) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    memLp_of_continuous_STR02935 cd
  have mp : MemLp (harm_STR02935 A B) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    memLp_of_continuous_STR02935 ca
  have iX : Integrable (fun t => (dharm_STR02935 A B t + gw t) ^ 2 * qT_STR02904 h t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_STR02935 cq (mdp.add hgl) (mdp.add hgl)).congr
      (ae_of_all _ fun t => by simp only [Pi.add_apply]; ring)
  have iY : Integrable (fun t => (harm_STR02935 A B t + w t) ^ 2 * qT_STR02904 h t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_STR02935 cq (mp.add hwl) (mp.add hwl)).congr
      (ae_of_all _ fun t => by simp only [Pi.add_apply]; ring)
  have iT1 : Integrable (fun t => dharm_STR02935 A B t ^ 2 * qT_STR02904 h t
      - harm_STR02935 A B t ^ 2 * qT_STR02904 h t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 (by fun_prop)
  have iT2 : Integrable (fun t => (dharm_STR02935 A B t * gw t - harm_STR02935 A B t * w t)
      * qT_STR02904 h t) (volume.restrict (Ioc 0 (2 * π))) :=
    ((integrable_cmul_left_STR02935 (c := fun t => dharm_STR02935 A B t * qT_STR02904 h t)
      (cd.mul cq) hgl).sub (integrable_cmul_left_STR02935
      (c := fun t => harm_STR02935 A B t * qT_STR02904 h t) (ca.mul cq) hwl)).congr
      (ae_of_all _ fun t => by simp only [Pi.sub_apply]; ring)
  have iT3 : Integrable (fun t => (gw t ^ 2 - w t ^ 2) * qT_STR02904 h t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    ((integrable_cmul_STR02935 cq hgl hgl).sub (integrable_cmul_STR02935 cq hwl hwl)).congr
      (ae_of_all _ fun t => by simp only [Pi.sub_apply]; ring)
  have hsub : normInt_STR02933 (fun t => (dharm_STR02935 A B t + gw t) ^ 2 * qT_STR02904 h t)
      - normInt_STR02933 (fun t => (harm_STR02935 A B t + w t) ^ 2 * qT_STR02904 h t)
      = normInt_STR02933 (fun t => 1 * (dharm_STR02935 A B t ^ 2 * qT_STR02904 h t
          - harm_STR02935 A B t ^ 2 * qT_STR02904 h t)
        + 2 * ((dharm_STR02935 A B t * gw t - harm_STR02935 A B t * w t) * qT_STR02904 h t)
        + 1 * ((gw t ^ 2 - w t ^ 2) * qT_STR02904 h t)) := by
    rw [← normInt_sub_STR02902 iX iY]
    congr 1
    funext t
    ring
  have hT1 : normInt_STR02933 (fun t => dharm_STR02935 A B t ^ 2 * qT_STR02904 h t
      - harm_STR02935 A B t ^ 2 * qT_STR02904 h t) = 0 := by
    have iD : Integrable (fun t => dharm_STR02935 A B t ^ 2 * qT_STR02904 h t)
        (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934 (by fun_prop)
    have iH : Integrable (fun t => harm_STR02935 A B t ^ 2 * qT_STR02904 h t)
        (volume.restrict (Ioc 0 (2 * π))) := integrable_continuous_STR02934 (by fun_prop)
    rw [normInt_sub_STR02902 iD iH, (normInt_harm_sq_q_STR02935 h A B).1,
      (normInt_harm_sq_q_STR02935 h A B).2]
    ring
  rw [hsub, normInt_lin3_STR02935 iT1 iT2 iT3, hT1, hcr]
  have := (abs_le.1 hX).1
  nlinarith [this, hC]

noncomputable def firstHarm_STR02935 (f : ℝ → ℝ) : ℝ → ℝ :=
  harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1)

noncomputable def compl_STR02935 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t - normInt_STR02933 f - firstHarm_STR02935 f t

noncomputable def bForm_STR02935 (f g : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => (g t - deriv (firstHarm_STR02935 f) t) ^ 2 - compl_STR02935 f t ^ 2)

theorem atoms_STR02935 :
    normInt_STR02933 (fun t => Real.cos t) = 0 ∧ normInt_STR02933 (fun t => Real.sin t) = 0 ∧
      normInt_STR02933 (fun t => Real.cos t * Real.cos t) = 1 / 2 ∧
      normInt_STR02933 (fun t => Real.sin t * Real.sin t) = 1 / 2 ∧
      normInt_STR02933 (fun t => Real.sin t * Real.cos t) = 0 ∧
      normInt_STR02933 (fun t => Real.cos t * Real.sin t) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using normInt_cos_nat_STR02934 1
  · simpa using normInt_sin_nat_STR02934 1
  · simpa using normInt_cos_mul_cos_STR02934 1 1 (by norm_num)
  · simpa using normInt_sin_mul_sin_STR02934 1 1 (by norm_num)
  · have e : (fun t => Real.sin t * Real.cos t)
        = fun t => Real.cos (((1 : ℕ) : ℝ) * t) * Real.sin (((1 : ℕ) : ℝ) * t) := by
      funext t; simp [mul_comm]
    rw [e]
    exact normInt_cos_mul_sin_STR02934 1 1
  · simpa using normInt_cos_mul_sin_STR02934 1 1

theorem compl_orth_STR02935 {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) :
    normInt_STR02933 (compl_STR02935 f) = 0 ∧
      normInt_STR02933 (fun t => compl_STR02935 f t * Real.cos t) = 0 ∧
      normInt_STR02933 (fun t => compl_STR02935 f t * Real.sin t) = 0 := by
  obtain ⟨n_cos, n_sin, n_cc, n_ss, n_sc, n_cs⟩ := atoms_STR02935
  have hA : cosCoeff_STR02933 f 1 = 2 * normInt_STR02933 (fun t => f t * Real.cos t) := by
    simp [cosCoeff_STR02933]
  have hB : sinCoeff_STR02933 f 1 = 2 * normInt_STR02933 (fun t => f t * Real.sin t) := by
    simp [sinCoeff_STR02933]
  have hfi : Integrable f (volume.restrict (Ioc 0 (2 * π))) := hf.integrable (by norm_num)
  have i1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 continuous_const
  have icos : Integrable (fun t => Real.cos t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 Real.continuous_cos
  have isin : Integrable (fun t => Real.sin t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 Real.continuous_sin
  have ifc : Integrable (fun t => f t * Real.cos t) (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_left_STR02935 Real.continuous_cos hf).congr (ae_of_all _ fun t => by ring)
  have ifs : Integrable (fun t => f t * Real.sin t) (volume.restrict (Ioc 0 (2 * π))) :=
    (integrable_cmul_left_STR02935 Real.continuous_sin hf).congr (ae_of_all _ fun t => by ring)
  have icc : Integrable (fun t => Real.cos t * Real.cos t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 (by fun_prop)
  have iss : Integrable (fun t => Real.sin t * Real.sin t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 (by fun_prop)
  have isc : Integrable (fun t => Real.sin t * Real.cos t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 (by fun_prop)
  have ics : Integrable (fun t => Real.cos t * Real.sin t) (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 (by fun_prop)
  refine ⟨?_, ?_, ?_⟩
  · have e : compl_STR02935 f = fun t => 1 * f t + (-normInt_STR02933 f) * (fun _ : ℝ => (1 : ℝ)) t
        + (-cosCoeff_STR02933 f 1) * Real.cos t + (-sinCoeff_STR02933 f 1) * Real.sin t := by
      funext t
      simp only [compl_STR02935, firstHarm_STR02935, harm_STR02935]
      ring
    rw [e, normInt_lin4_STR02935 hfi i1 icos isin, normInt_one_STR02934, n_cos, n_sin]
    ring
  · have e : (fun t => compl_STR02935 f t * Real.cos t)
        = fun t => 1 * (f t * Real.cos t) + (-normInt_STR02933 f) * Real.cos t
          + (-cosCoeff_STR02933 f 1) * (Real.cos t * Real.cos t)
          + (-sinCoeff_STR02933 f 1) * (Real.sin t * Real.cos t) := by
      funext t
      simp only [compl_STR02935, firstHarm_STR02935, harm_STR02935]
      ring
    rw [e, normInt_lin4_STR02935 ifc icos icc isc, n_cos, n_cc, n_sc, hA]
    ring
  · have e : (fun t => compl_STR02935 f t * Real.sin t)
        = fun t => 1 * (f t * Real.sin t) + (-normInt_STR02933 f) * Real.sin t
          + (-cosCoeff_STR02933 f 1) * (Real.cos t * Real.sin t)
          + (-sinCoeff_STR02933 f 1) * (Real.sin t * Real.sin t) := by
      funext t
      simp only [compl_STR02935, firstHarm_STR02935, harm_STR02935]
      ring
    rw [e, normInt_lin4_STR02935 ifs isin ics iss, n_sin, n_cs, n_ss, hB]
    ring

theorem compl_weak_STR02935 {f g : ℝ → ℝ} (hfg : IsPeriodicWeakDerivative_STR02933 f g) :
    IsPeriodicWeakDerivative_STR02933 (compl_STR02935 f)
      (fun t => g t - dharm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) t) := by
  have hsm : ContDiff ℝ ∞ (fun t => normInt_STR02933 f
      + harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) t) :=
    contDiff_const.add (contDiff_harm_STR02935 _ _)
  have hper : Function.Periodic (fun t => normInt_STR02933 f
      + harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) t) (2 * π) := by
    intro x
    show normInt_STR02933 f + harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) (x + 2 * π)
      = normInt_STR02933 f + harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) x
    rw [periodic_harm_STR02935 _ _ x]
  have key := weakDeriv_sub_STR02935 hfg (weak_of_smooth_STR02935 hsm hper)
  have e2 : deriv (fun t => normInt_STR02933 f
      + harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) t)
      = dharm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) :=
    funext fun t => ((hasDerivAt_harm_STR02935 _ _ t).const_add (normInt_STR02933 f)).deriv
  rw [e2] at key
  have e1 : compl_STR02935 f = fun t => f t - (normInt_STR02933 f
      + harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) t) := by
    funext t
    simp only [compl_STR02935, firstHarm_STR02935]
    ring
  rw [e1]
  exact key

theorem str029_35_quantitative_weighted_cross_form_estimate (h : ℝ) (hh : |h| ≤ 1 / 1000)
    (f g : ℝ → ℝ) (hfg : IsPeriodicWeakDerivative_STR02933 f g) :
    normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t)
          - varQ_STR02935 h (fun t => f t - normInt_STR02933 f)
        ≥ cFun_STR02935 |h| * bForm_STR02935 f g
          - 2 * |h| * ellFun_STR02935 |h|
            * Real.sqrt (normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2))
            * Real.sqrt (bForm_STR02935 f g) ∧
      varQ_STR02935 h (fun t => f t - normInt_STR02933 f)
        ≥ Real.exp (-(2 * |h|)) * (normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2)
            + normInt_STR02933 (fun t => compl_STR02935 f t ^ 2)) := by
  obtain ⟨A, hA⟩ : ∃ A, A = cosCoeff_STR02933 f 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = sinCoeff_STR02933 f 1 := ⟨_, rfl⟩
  have hfl : MemLp f 2 (volume.restrict (Ioc 0 (2 * π))) := hfg.1.2
  have hcw := compl_weak_STR02935 hfg
  obtain ⟨o0, oc, os⟩ := compl_orth_STR02935 hfl
  rw [← hA, ← hB] at hcw
  have hcl : MemLp (compl_STR02935 f) 2 (volume.restrict (Ioc 0 (2 * π))) := hcw.1.2
  have hfh : firstHarm_STR02935 f = harm_STR02935 A B := by rw [hA, hB]; rfl
  have hd : deriv (firstHarm_STR02935 f) = dharm_STR02935 A B := by
    rw [hfh]; exact deriv_harm_STR02935 A B
  have hb : bForm_STR02935 f g
      = normInt_STR02933 (fun t => (g t - dharm_STR02935 A B t) ^ 2 - compl_STR02935 f t ^ 2) := by
    unfold bForm_STR02935; rw [hd]
  have hP : normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2) = (A ^ 2 + B ^ 2) / 2 := by
    rw [hfh]; exact normInt_harm_sq_STR02935 A B
  have hFt : ∀ t, f t - normInt_STR02933 f = harm_STR02935 A B t + compl_STR02935 f t := by
    intro t; simp only [compl_STR02935, hfh]; ring
  have hFmem : MemLp (fun t => f t - normInt_STR02933 f) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    hfl.sub (memLp_of_continuous_STR02935 (continuous_const (y := normInt_STR02933 f)))
  have hfi : Integrable f (volume.restrict (Ioc 0 (2 * π))) := hfl.integrable (by norm_num)
  have hF0 : normInt_STR02933 (fun t => f t - normInt_STR02933 f) = 0 := by
    have i1 : Integrable (fun _ : ℝ => normInt_STR02933 f) (volume.restrict (Ioc 0 (2 * π))) :=
      integrable_continuous_STR02934 continuous_const
    rw [normInt_sub_STR02902 hfi i1, normInt_const_STR02935, sub_self]
  have hvar : varQ_STR02935 h (fun t => f t - normInt_STR02933 f)
      = normInt_STR02933 (fun t => (f t - normInt_STR02933 f) ^ 2 * qT_STR02904 h t)
        - (normInt_STR02933 (fun t => (f t - normInt_STR02933 f) * qT_STR02904 h t)) ^ 2 := rfl
  refine ⟨?_, ?_⟩
  · have core := lower_I_STR02935 hh A B hcw o0 oc os
    have e1 : normInt_STR02933 (fun t => (dharm_STR02935 A B t + (g t - dharm_STR02935 A B t)) ^ 2
        * qT_STR02904 h t) = normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t) := by
      congr 1; funext t; ring
    have e2 : normInt_STR02933 (fun t => (harm_STR02935 A B t + compl_STR02935 f t) ^ 2
        * qT_STR02904 h t)
        = normInt_STR02933 (fun t => (f t - normInt_STR02933 f) ^ 2 * qT_STR02904 h t) := by
      congr 1; funext t; rw [hFt t]
    rw [e1, e2] at core
    rw [hvar, hP, hb]
    have := sq_nonneg (normInt_STR02933 (fun t => (f t - normInt_STR02933 f) * qT_STR02904 h t))
    linarith
  · have iH2 : Integrable (fun t => harm_STR02935 A B t ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
      integrable_continuous_STR02934 ((continuous_harm_STR02935 A B).pow 2)
    have iCc : Integrable (fun t => compl_STR02935 f t * Real.cos t)
        (volume.restrict (Ioc 0 (2 * π))) :=
      (integrable_cmul_left_STR02935 Real.continuous_cos hcl).congr
        (ae_of_all _ fun t => by ring)
    have iCs : Integrable (fun t => compl_STR02935 f t * Real.sin t)
        (volume.restrict (Ioc 0 (2 * π))) :=
      (integrable_cmul_left_STR02935 Real.continuous_sin hcl).congr
        (ae_of_all _ fun t => by ring)
    have iHC : Integrable (fun t => harm_STR02935 A B t * compl_STR02935 f t)
        (volume.restrict (Ioc 0 (2 * π))) :=
      ((iCc.const_mul A).add (iCs.const_mul B)).congr
        (ae_of_all _ fun t => by simp only [Pi.add_apply, harm_STR02935]; ring)
    have iC2 := integrable_sq_STR02935 hcl
    have hHC : normInt_STR02933 (fun t => harm_STR02935 A B t * compl_STR02935 f t) = 0 := by
      have e : (fun t => harm_STR02935 A B t * compl_STR02935 f t)
          = fun t => A * (compl_STR02935 f t * Real.cos t)
            + B * (compl_STR02935 f t * Real.sin t) := by
        funext t; simp only [harm_STR02935]; ring
      rw [e, normInt_lin2_STR02935 iCc iCs, oc, os]
      ring
    have hpyth : normInt_STR02933 (fun t => (f t - normInt_STR02933 f) ^ 2)
        = normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2)
          + normInt_STR02933 (fun t => compl_STR02935 f t ^ 2) := by
      have e : (fun t => (f t - normInt_STR02933 f) ^ 2)
          = fun t => 1 * harm_STR02935 A B t ^ 2
            + 2 * (harm_STR02935 A B t * compl_STR02935 f t) + 1 * compl_STR02935 f t ^ 2 := by
        funext t; rw [hFt t]; ring
      rw [e, normInt_lin3_STR02935 iH2 iHC iC2, hHC, hP, normInt_harm_sq_STR02935]
      ring
    have key : Real.exp (-(2 * |h|)) * normInt_STR02933 (fun t => (f t - normInt_STR02933 f) ^ 2)
        ≤ varQ_STR02935 h (fun t => f t - normInt_STR02933 f) :=
      var_lower_STR02935 h hFmem hF0
    rw [hpyth] at key
    exact key

end DGPS.Frontier.STR029
