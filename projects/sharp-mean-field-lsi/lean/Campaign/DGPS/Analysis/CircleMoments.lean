import Mathlib
import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.RelativeEntropy

/-!
# Circle first harmonic: entropy and Fisher information Taylor estimates (H1044)

On the unit Haar circle `𝕋¹`, consider `ρ_t = 1 + t cos (2π x)`, `0 < |t| ≤ 1/2`, realised as the
absolute-admissible density `u_t² ` with `u_t = √ρ_t` (`firstHarmonicDensity`). We prove, with
the campaign definitions `relativeEntropy` (DEF005, via `homogeneousEntropy`, DEF004) and the
Haar weak gradient `weakGradient` (DEF001):

* `ρ_t` is smooth periodic, positive, of mass one, and `u_t` is a smooth periodic function whose
  weak gradient is its classical gradient (`isWeakGradient_smooth`);
* `H_t = H(ρ_t m | m) > 0` and `|H_t - t²/4| ≤ C |t|⁴`;
* `I_t = 4 ∫ |(√ρ_t)'|² dm` satisfies `|I_t - a₀ t²/2| ≤ C |t|⁴`, with `a₀ = 4π²`;
* `I_t / (2 H_t) → a₀` as `t → 0`,

with one explicit constant `C = 4π²` for all `0 < |t| ≤ 1/2`
(`circle_first_harmonic_estimates`).

Route: the Haar integral of a function of the section `secT` is the interval integral over
`(0, 1]` (`integral_haar_secT`); entropy reduces to `∫₀¹ ψ(t cos 2πs) ds` with the pointwise
fourth-order Taylor bound of `ψ(u) = (1+u) log (1+u) - u`; the Fisher integrand is
`4π²t² sin² / (1 + t cos)` with `1/(1+v) = 1 - v + v²/(1+v)`.
-/

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace DGPS.Analysis.CircleMoments

section RealEstimates
open Real intervalIntegral
theorem entropy_taylor_pointwise {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |(1 + u) * Real.log (1 + u) - u - (u ^ 2 / 2 - u ^ 3 / 6)| ≤ 7 / 4 * u ^ 4 := by
  have hx : |-u| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  set R := Real.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4) with hR
  have e : (∑ i ∈ Finset.range 4, (-u) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -u) = R := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hR, sub_neg_eq_add]
    push_cast
    ring
  rw [e, abs_neg] at h
  norm_num at h
  have hpos : 0 < 1 - |u| := by linarith
  have h0 : 0 ≤ |u| ^ 5 := by positivity
  have hR' : |R| ≤ 2 * |u| ^ 5 := by
    refine h.trans ?_
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hu)]
  have key : (1 + u) * Real.log (1 + u) - u - (u ^ 2 / 2 - u ^ 3 / 6)
      = u ^ 4 / 12 - u ^ 5 / 4 + (1 + u) * R := by
    rw [hR]; ring
  rw [key]
  have hu4 : |u| ^ 4 = u ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have h5 : |u| ^ 5 ≤ u ^ 4 / 2 := by
    have : |u| ^ 5 = |u| ^ 4 * |u| := by ring
    rw [this, hu4]; have : 0 ≤ u ^ 4 := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.2 hu)]
  have hu5 : |u ^ 5| = |u| ^ 5 := abs_pow _ _
  have h1u : |1 + u| ≤ 3 / 2 := by
    rw [abs_le] at hu ⊢; constructor <;> linarith [hu.1, hu.2]
  have h4 : 0 ≤ u ^ 4 := by positivity
  have hA : |u ^ 4 / 12 - u ^ 5 / 4 + (1 + u) * R|
      ≤ |u ^ 4 / 12| + |u ^ 5 / 4| + |(1 + u) * R| :=
    (abs_add_le _ _).trans (by gcongr; exact abs_sub _ _)
  rw [abs_of_nonneg (by positivity : 0 ≤ u ^ 4 / 12), abs_div, hu5, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 4)] at hA
  have hm : |1 + u| * |R| ≤ 3 / 2 * (2 * |u| ^ 5) :=
    mul_le_mul h1u hR' (abs_nonneg _) (by norm_num)
  nlinarith
theorem integral_sin_pow_mul_cos_odd_two_pi (m n : ℕ) :
    ∫ s in (0:ℝ)..1, Real.sin (2 * π * s) ^ m * Real.cos (2 * π * s) ^ (2 * n + 1) = 0 := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun x => Real.sin x ^ m * Real.cos x ^ (2 * n + 1)) (c := 2 * π) (by positivity)
  rw [h, integral_sin_pow_mul_cos_pow_odd]
  simp

theorem integral_cos_cube_two_pi : ∫ s in (0:ℝ)..1, Real.cos (2 * π * s) ^ 3 = 0 := by
  simpa using integral_sin_pow_mul_cos_odd_two_pi 0 1

theorem integral_sin_sq_mul_cos_two_pi :
    ∫ s in (0:ℝ)..1, Real.sin (2 * π * s) ^ 2 * Real.cos (2 * π * s) = 0 := by
  simpa using integral_sin_pow_mul_cos_odd_two_pi 2 0

theorem integral_cos_sq_two_pi : ∫ s in (0:ℝ)..1, Real.cos (2 * π * s) ^ 2 = 1 / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun x => Real.cos x ^ 2) (c := 2 * π) (by positivity)
  rw [h, integral_cos_sq]
  simp
  field_simp

theorem integral_sin_sq_two_pi : ∫ s in (0:ℝ)..1, Real.sin (2 * π * s) ^ 2 = 1 / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun x => Real.sin x ^ 2) (c := 2 * π) (by positivity)
  rw [h, integral_sin_sq]
  simp
  field_simp

theorem abs_cos_mul_le {t : ℝ} (ht : |t| ≤ 1 / 2) (s : ℝ) : |t * Real.cos (2 * π * s)| ≤ 1 / 2 := by
  rw [abs_mul]
  have := Real.abs_cos_le_one (2 * π * s)
  calc |t| * |Real.cos (2 * π * s)| ≤ 1 / 2 * 1 := mul_le_mul ht this (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := by norm_num

/-- Real entropy integral. -/
theorem entropy_integral_estimate {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(∫ s in (0:ℝ)..1, ((1 + t * Real.cos (2 * π * s)) * Real.log (1 + t * Real.cos (2 * π * s))
        - t * Real.cos (2 * π * s))) - t ^ 2 / 4| ≤ 7 / 8 * t ^ 4 := by
  set f : ℝ → ℝ := fun s => (1 + t * Real.cos (2 * π * s)) * Real.log (1 + t * Real.cos (2 * π * s))
        - t * Real.cos (2 * π * s) with hf
  set g : ℝ → ℝ := fun s => t ^ 2 / 2 * Real.cos (2 * π * s) ^ 2
        - t ^ 3 / 6 * Real.cos (2 * π * s) ^ 3 with hg
  have hfc : Continuous f := by
    have := Real.continuous_mul_log.comp (show Continuous fun s : ℝ => 1 + t * Real.cos (2 * π * s) by fun_prop)
    exact (this.sub (by fun_prop))
  have hgc : Continuous g := by fun_prop
  have hint : ∫ s in (0:ℝ)..1, g s = t ^ 2 / 4 := by
    simp only [hg]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_cos_sq_two_pi, integral_cos_cube_two_pi]
    · ring
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  have hsub : ∫ s in (0:ℝ)..1, (f s - g s) = (∫ s in (0:ℝ)..1, f s) - t ^ 2 / 4 := by
    rw [intervalIntegral.integral_sub (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _), hint]
  have hbound : ‖∫ s in (0:ℝ)..1, (f s - g s)‖ ≤ ∫ s in (0:ℝ)..1, 7 / 4 * t ^ 4 * Real.cos (2 * π * s) ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le (E := ℝ) (f := fun s => f s - g s)
      (g := fun s => 7 / 4 * t ^ 4 * Real.cos (2 * π * s) ^ 2) (μ := MeasureTheory.volume) zero_le_one ?_
      ((by fun_prop : Continuous fun s : ℝ => 7 / 4 * t ^ 4 * Real.cos (2 * π * s) ^ 2).intervalIntegrable _ _)
    refine Filter.Eventually.of_forall fun s _ => ?_
    have h := entropy_taylor_pointwise (abs_cos_mul_le ht s)
    have e : f s - g s = (1 + t * Real.cos (2 * π * s)) * Real.log (1 + t * Real.cos (2 * π * s))
        - t * Real.cos (2 * π * s) - ((t * Real.cos (2 * π * s)) ^ 2 / 2 - (t * Real.cos (2 * π * s)) ^ 3 / 6) := by
      simp only [hf, hg]; ring
    rw [Real.norm_eq_abs, e]
    refine h.trans ?_
    have hc : Real.cos (2 * π * s) ^ 4 ≤ Real.cos (2 * π * s) ^ 2 := by
      have h1 := Real.cos_sq_le_one (2 * π * s)
      have h2 := sq_nonneg (Real.cos (2 * π * s))
      nlinarith
    have : (t * Real.cos (2 * π * s)) ^ 4 = t ^ 4 * Real.cos (2 * π * s) ^ 4 := by ring
    rw [this]
    have ht4 : 0 ≤ t ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hc ht4]
  rw [intervalIntegral.integral_const_mul, integral_cos_sq_two_pi, hsub, Real.norm_eq_abs] at hbound
  linarith

theorem fisher_integral_estimate {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(∫ s in (0:ℝ)..1, 4 * π ^ 2 * t ^ 2 * Real.sin (2 * π * s) ^ 2 / (1 + t * Real.cos (2 * π * s)))
      - 2 * π ^ 2 * t ^ 2| ≤ 4 * π ^ 2 * t ^ 4 := by
  set F : ℝ → ℝ := fun s => 4 * π ^ 2 * t ^ 2 * Real.sin (2 * π * s) ^ 2 / (1 + t * Real.cos (2 * π * s)) with hF
  set h : ℝ → ℝ := fun s => 4 * π ^ 2 * t ^ 2 * Real.sin (2 * π * s) ^ 2
      - 4 * π ^ 2 * t ^ 3 * (Real.sin (2 * π * s) ^ 2 * Real.cos (2 * π * s)) with hh
  have hpos : ∀ s, 0 < 1 + t * Real.cos (2 * π * s) := fun s => by
    have := abs_le.1 (abs_cos_mul_le ht s); linarith [this.1]
  have hFc : Continuous F := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun s => (hpos s).ne'
  have hhc : Continuous h := by fun_prop
  have hint : ∫ s in (0:ℝ)..1, h s = 2 * π ^ 2 * t ^ 2 := by
    simp only [hh]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_sin_sq_two_pi, integral_sin_sq_mul_cos_two_pi]
    · ring
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  have hbound : ‖∫ s in (0:ℝ)..1, (F s - h s)‖ ≤ ∫ s in (0:ℝ)..1, 8 * π ^ 2 * t ^ 4 * Real.cos (2 * π * s) ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le (E := ℝ) (f := fun s => F s - h s)
      (g := fun s => 8 * π ^ 2 * t ^ 4 * Real.cos (2 * π * s) ^ 2) (μ := MeasureTheory.volume) zero_le_one ?_
      ((by fun_prop : Continuous fun s : ℝ => 8 * π ^ 2 * t ^ 4 * Real.cos (2 * π * s) ^ 2).intervalIntegrable _ _)
    refine Filter.Eventually.of_forall fun s _ => ?_
    set c := Real.cos (2 * π * s) with hc
    set sn := Real.sin (2 * π * s) with hsn
    have hp : 0 < 1 + t * c := hpos s
    have hv := abs_le.1 (abs_cos_mul_le ht s)
    have e : F s - h s = 4 * π ^ 2 * t ^ 2 * sn ^ 2 * (t * c) ^ 2 / (1 + t * c) := by
      have key : ∀ (sn c : ℝ), 0 < 1 + t * c →
          4 * π ^ 2 * t ^ 2 * sn ^ 2 / (1 + t * c) - (4 * π ^ 2 * t ^ 2 * sn ^ 2
            - 4 * π ^ 2 * t ^ 3 * (sn ^ 2 * c)) = 4 * π ^ 2 * t ^ 2 * sn ^ 2 * (t * c) ^ 2 / (1 + t * c) := by
        intro sn c hp
        field_simp
        ring
      exact key sn c hp
    have hs2 : sn ^ 2 ≤ 1 := by rw [hsn]; exact Real.sin_sq_le_one _
    have hq : sn ^ 2 * (t * c) ^ 2 / (1 + t * c) ≤ 2 * (t * c) ^ 2 := by
      rw [div_le_iff₀ hp]
      have h0 : 0 ≤ (t * c) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hs2 h0, mul_nonneg h0 (by linarith [hv.1] : (0:ℝ) ≤ 2 * (1 + t * c) - 1)]
    have hq0 : 0 ≤ sn ^ 2 * (t * c) ^ 2 / (1 + t * c) := by positivity
    have e2 : 4 * π ^ 2 * t ^ 2 * sn ^ 2 * (t * c) ^ 2 / (1 + t * c)
        = 4 * π ^ 2 * t ^ 2 * (sn ^ 2 * (t * c) ^ 2 / (1 + t * c)) := by ring
    rw [Real.norm_eq_abs, e, e2, abs_of_nonneg (by positivity)]
    have hπ : 0 ≤ 4 * π ^ 2 * t ^ 2 := by positivity
    calc 4 * π ^ 2 * t ^ 2 * (sn ^ 2 * (t * c) ^ 2 / (1 + t * c)) ≤ 4 * π ^ 2 * t ^ 2 * (2 * (t * c) ^ 2) :=
          mul_le_mul_of_nonneg_left hq hπ
      _ = 8 * π ^ 2 * t ^ 4 * c ^ 2 := by ring
  rw [intervalIntegral.integral_const_mul, integral_cos_sq_two_pi,
    intervalIntegral.integral_sub (hFc.intervalIntegrable _ _) (hhc.intervalIntegrable _ _), hint,
    Real.norm_eq_abs] at hbound
  linarith

end RealEstimates

theorem integral_haar_secT {G : (Fin 1 → ℝ) → ℝ} (hG : Measurable G) :
    ∫ x, G (SharpLSI.secT x) ∂haar 1 = ∫ s in (0:ℝ)..1, G (fun _ => s) := by
  rw [haar_eq_map_unitBox, integral_map (φ := torusLift) (f := fun x : Torus 1 => G (SharpLSI.secT x))
    (SharpLSI.measurable_liftT (ι := Fin 1)).aemeasurable
    (hG.comp SharpLSI.measurable_secT).aestronglyMeasurable]
  have h1 : ∫ y, G (SharpLSI.secT (torusLift y)) ∂((volume : Measure (Fin 1 → ℝ)).restrict
      (SharpLSI.unitBox (Fin 1))) = ∫ y in SharpLSI.unitBox (Fin 1), G y := by
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun y hy => ?_
    simp only [SharpLSI.secT_liftT hy]
  rw [h1, intervalIntegral.integral_of_le zero_le_one]
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  have := hmp.setIntegral_preimage_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
    (fun s => G (fun _ => s)) (Ioc 0 1)
  rw [← this]
  have hset : (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioc 0 1 = SharpLSI.unitBox (Fin 1) := by
    ext y
    simp [SharpLSI.unitBox, MeasurableEquiv.funUnique, Set.mem_pi, Fin.forall_fin_one]
  rw [hset]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) fun y _ => ?_
  have : (fun _ : Fin 1 => (MeasurableEquiv.funUnique (Fin 1) ℝ) y) = y := by
    funext i; simp [MeasurableEquiv.funUnique, Subsingleton.elim i default]
  simp only [this]


theorem integral_haar_eq {f : Torus 1 → ℝ} (hf : Continuous (f ∘ torusLift)) :
    ∫ x, f x ∂haar 1 = ∫ s in (0:ℝ)..1, f (torusLift fun _ => s) := by
  have := integral_haar_secT hf.measurable
  simpa [Function.comp_def, torusLift, SharpLSI.liftT_secT] using this

/-- The derivative of a function along the diagonal of `ℝ¹`. -/
theorem hasDerivAt_diag {F : (Fin 1 → ℝ) → ℝ} (hF : Differentiable ℝ F) (s : ℝ) :
    HasDerivAt (fun r : ℝ => F (fun _ => r)) (fderiv ℝ F (fun _ => s) (Pi.single 0 1)) s := by
  have h1 : HasDerivAt (fun r : ℝ => (fun _ : Fin 1 => r)) (Pi.single 0 1 : Fin 1 → ℝ) s := by
    rw [hasDerivAt_pi]
    intro i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    simpa using hasDerivAt_id' s
  exact (hF (fun _ => s)).hasFDerivAt.comp_hasDerivAt s h1

theorem lift_one_eq_zero : (torusLift (fun _ : Fin 1 => (1:ℝ))) = torusLift (fun _ : Fin 1 => (0:ℝ)) := by
  funext i
  simp [torusLift, SharpLSI.liftT]

/-- Integration by parts for smooth periodic functions on `𝕋¹`. -/
theorem ibp_smooth {u φ : Torus 1 → ℝ} (hu : IsSmoothPeriodic u) (hφ : IsSmoothPeriodic φ) :
    ∫ x, u x * coordPartial 0 φ x ∂haar 1 = -∫ x, coordPartial 0 u x * φ x ∂haar 1 := by
  set U : (Fin 1 → ℝ) → ℝ := u ∘ torusLift with hU
  set P : (Fin 1 → ℝ) → ℝ := φ ∘ torusLift with hP
  have hUd : ContDiff ℝ ∞ U := hu
  have hPd : ContDiff ℝ ∞ P := hφ
  have hU1 : ContDiff ℝ 1 U := hUd.of_le (by exact_mod_cast le_top)
  have hP1 : ContDiff ℝ 1 P := hPd.of_le (by exact_mod_cast le_top)
  have hUD : Differentiable ℝ U := hU1.differentiable one_ne_zero
  have hPD : Differentiable ℝ P := hP1.differentiable one_ne_zero
  have hUc : Continuous (fderiv ℝ U) := hU1.continuous_fderiv one_ne_zero
  have hPc : Continuous (fderiv ℝ P) := hP1.continuous_fderiv one_ne_zero
  have e1 : ∫ x, u x * coordPartial 0 φ x ∂haar 1
      = ∫ s in (0:ℝ)..1, U (fun _ => s) * fderiv ℝ P (fun _ => s) (Pi.single 0 1) := by
    have := integral_haar_secT (G := fun y => U y * fderiv ℝ P y (Pi.single 0 1))
      (by
        have : Continuous fun y => U y * fderiv ℝ P y (Pi.single 0 1) :=
          hU1.continuous.mul (hPc.clm_apply continuous_const)
        exact this.measurable)
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hU, Function.comp_def, torusLift, SharpLSI.liftT_secT, coordPartial]
    rfl
  have e2 : ∫ x, coordPartial 0 u x * φ x ∂haar 1
      = ∫ s in (0:ℝ)..1, fderiv ℝ U (fun _ => s) (Pi.single 0 1) * P (fun _ => s) := by
    have := integral_haar_secT (G := fun y => fderiv ℝ U y (Pi.single 0 1) * P y)
      (by
        have : Continuous fun y => fderiv ℝ U y (Pi.single 0 1) * P y :=
          (hUc.clm_apply continuous_const).mul hP1.continuous
        exact this.measurable)
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hP, Function.comp_def, torusLift, SharpLSI.liftT_secT, coordPartial]
    rfl
  rw [e1, e2]
  have hper : U (fun _ => 1) * P (fun _ => 1) - U (fun _ => 0) * P (fun _ => 0) = 0 := by
    simp only [hU, hP, Function.comp_def]
    rw [lift_one_eq_zero]; ring
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0:ℝ)) (b := 1)
    (u := fun r : ℝ => U (fun _ => r)) (v := fun r : ℝ => P (fun _ => r))
    (u' := fun r => fderiv ℝ U (fun _ => r) (Pi.single 0 1))
    (v' := fun r => fderiv ℝ P (fun _ => r) (Pi.single 0 1))
    (fun x _ => hasDerivAt_diag hUD x) (fun x _ => hasDerivAt_diag hPD x)
    (Continuous.intervalIntegrable (by
      exact (hUc.clm_apply continuous_const).comp (by fun_prop : Continuous fun r : ℝ => (fun _ : Fin 1 => r))) _ _)
    (Continuous.intervalIntegrable (by
      exact (hPc.clm_apply continuous_const).comp (by fun_prop : Continuous fun r : ℝ => (fun _ : Fin 1 => r))) _ _)
  rw [key]
  simp only at hper
  rw [hper]; ring


/-- The gradient of a smooth periodic function on `𝕋¹`, as a tangent-vector field. -/
noncomputable def smoothGrad (u : Torus 1 → ℝ) : Torus 1 → Tangent 1 :=
  fun x => coordPartial 0 u x • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

theorem smoothGrad_apply (u : Torus 1 → ℝ) (x : Torus 1) (j : Fin 1) :
    smoothGrad u x j = coordPartial 0 u x := by
  have : j = 0 := Subsingleton.elim _ _
  subst this
  simp [smoothGrad]

theorem norm_smoothGrad (u : Torus 1 → ℝ) (x : Torus 1) :
    ‖smoothGrad u x‖ = |coordPartial 0 u x| := by
  simp [smoothGrad, norm_smul]

theorem isWeakGradient_smooth {u : Torus 1 → ℝ} (hu : IsSmoothPeriodic u) :
    IsWeakGradient u (smoothGrad u) where
  memLp := (hu.memLp_top).mono_exponent le_top
  memLp_grad := by
    have h : MemLp (coordPartial 0 u) 2 (haar 1) :=
      (hu.memLp_top_coordPartial 0).mono_exponent le_top
    exact ((ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : ℝ →L[ℝ] Tangent 1).comp_memLp' h
  ibp := by
    intro φ hφ j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp only [smoothGrad_apply]
    exact ibp_smooth hu hφ


/-- The real first harmonic `cos (2π x)` on `𝕋¹`, as the real part of the Fourier mode. -/
noncomputable def cosMode (x : Torus 1) : ℝ :=
  (UnitAddTorus.mFourier (fun _ : Fin 1 => (1 : ℤ)) x).re

theorem cosMode_lift (y : Fin 1 → ℝ) : cosMode (torusLift y) = Real.cos (2 * Real.pi * y 0) := by
  unfold cosMode
  rw [mFourier_torusLift]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, Int.cast_one, mul_one]
  have : (2 * (Real.pi : ℂ) * Complex.I * y 0) = ((2 * Real.pi * y 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.ofReal_one, div_one, Complex.exp_ofReal_mul_I_re]

theorem isSmoothPeriodic_cosMode : IsSmoothPeriodic cosMode :=
  isSmoothPeriodic_re_mFourier _

theorem continuous_cosMode : Continuous cosMode :=
  Complex.continuous_re.comp (UnitAddTorus.mFourier _).continuous


open Real intervalIntegral in
theorem integral_cos_two_pi : ∫ s in (0:ℝ)..1, Real.cos (2 * π * s) = 0 := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun x => Real.cos x) (c := 2 * π) (by positivity)
  rw [h, integral_cos]
  simp

theorem abs_cosMode_le (x : Torus 1) : |cosMode x| ≤ 1 := by
  have := cosMode_lift (SharpLSI.secT x)
  have e : torusLift (SharpLSI.secT x) = x := SharpLSI.liftT_secT x
  rw [e] at this
  rw [this]
  exact Real.abs_cos_le_one _

/-- The density `1 + t cos (2π x)` on `𝕋¹`. -/
noncomputable def firstHarmonic (t : ℝ) (x : Torus 1) : ℝ := 1 + t * cosMode x

theorem firstHarmonic_lift (t : ℝ) (y : Fin 1 → ℝ) :
    firstHarmonic t (torusLift y) = 1 + t * Real.cos (2 * Real.pi * y 0) := by
  simp [firstHarmonic, cosMode_lift]

theorem firstHarmonic_pos {t : ℝ} (ht : |t| < 1) (x : Torus 1) : 0 < firstHarmonic t x := by
  have h1 := abs_cosMode_le x
  have : |t * cosMode x| < 1 := by
    rw [abs_mul]
    calc |t| * |cosMode x| ≤ |t| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ < 1 := by linarith
  have := (abs_lt.1 this).1
  unfold firstHarmonic; linarith

theorem continuous_firstHarmonic (t : ℝ) : Continuous (firstHarmonic t) :=
  continuous_const.add (continuous_const.mul continuous_cosMode)

theorem isSmoothPeriodic_firstHarmonic (t : ℝ) : IsSmoothPeriodic (firstHarmonic t) := by
  have h : ContDiff ℝ ∞ (cosMode ∘ torusLift) := isSmoothPeriodic_cosMode
  unfold IsSmoothPeriodic
  exact contDiff_const.add (contDiff_const.mul h)

/-- `√(1 + t cos (2π x))`. -/
noncomputable def firstSqrt (t : ℝ) (x : Torus 1) : ℝ := Real.sqrt (firstHarmonic t x)

theorem isSmoothPeriodic_firstSqrt {t : ℝ} (ht : |t| < 1) : IsSmoothPeriodic (firstSqrt t) := by
  have h : ContDiff ℝ ∞ (firstHarmonic t ∘ torusLift) := isSmoothPeriodic_firstHarmonic t
  unfold IsSmoothPeriodic firstSqrt
  exact h.sqrt fun y => (firstHarmonic_pos ht (torusLift y)).ne'

theorem integral_firstHarmonic (t : ℝ) : ∫ x, firstHarmonic t x ∂haar 1 = 1 := by
  rw [integral_haar_eq (isSmoothPeriodic_firstHarmonic t).continuous]
  simp_rw [firstHarmonic_lift]
  have hc : Continuous fun s : ℝ => Real.cos (2 * Real.pi * s) := by fun_prop
  have hi : IntervalIntegrable (fun s : ℝ => t * Real.cos (2 * Real.pi * s)) volume 0 1 :=
    (continuous_const.mul hc).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (f := fun _ => (1:ℝ)) (g := fun s : ℝ => t * Real.cos (2 * Real.pi * s))
    (by simp) hi]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, integral_cos_two_pi]
  simp

/-- The absolute-admissible density `ρ_t = 1 + t cos (2π x)`, `|t| < 1`. -/
noncomputable def firstHarmonicDensity (t : ℝ) (ht : |t| < 1) : AbsoluteDensity 1 where
  sqrt := firstSqrt t
  sqrt_mem := ⟨_, isWeakGradient_smooth (isSmoothPeriodic_firstSqrt ht)⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _
  mass_one := by
    have : ∀ x, firstSqrt t x ^ 2 = firstHarmonic t x := fun x =>
      Real.sq_sqrt (firstHarmonic_pos ht x).le
    simp_rw [this]
    exact integral_firstHarmonic t


theorem entropy_eq_ofReal {t : ℝ} (ht : |t| < 1) :
    relativeEntropy (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1)) (haar 1)
      = ENNReal.ofReal (∫ s in (0:ℝ)..1, ((1 + t * Real.cos (2 * Real.pi * s)) *
          Real.log (1 + t * Real.cos (2 * Real.pi * s)) - t * Real.cos (2 * Real.pi * s))) := by
  have hpos := firstHarmonic_pos ht
  have hsq : ∀ x, (firstHarmonicDensity t ht).sqrt x ^ 2 = firstHarmonic t x := fun x =>
    Real.sq_sqrt (hpos x).le
  rw [densityMeasure_coe]
  simp_rw [hsq]
  have hcont := continuous_firstHarmonic t
  rw [relativeEntropy_withDensity (Filter.Eventually.of_forall fun x => (hpos x).le)
    hcont.aemeasurable, entropy_mass_one (integral_firstHarmonic t)]
  set f : Torus 1 → ℝ := fun x => firstHarmonic t x * Real.log (firstHarmonic t x) - firstHarmonic t x + 1
    with hf
  have hfc : Continuous f := by
    refine ((hcont.mul (Continuous.log hcont fun x => (hpos x).ne')).sub hcont).add continuous_const
  have hfi : Integrable f (haar 1) := hfc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi
    (Filter.Eventually.of_forall fun x => self_mul_log_sub_add_one_nonneg (hpos x).le)]
  congr 1
  have hcl : Continuous (f ∘ torusLift) := by
    exact hfc.comp (by unfold torusLift SharpLSI.liftT; fun_prop)
  rw [integral_haar_eq hcl]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [hf, firstHarmonic_lift]
  ring


theorem fisher_eq {t : ℝ} (ht : |t| < 1) :
    4 * ∫ x, ‖weakGradient (firstHarmonicDensity t ht).sqrt (firstHarmonicDensity t ht).sqrt_mem x‖ ^ 2
        ∂haar 1
      = ∫ s in (0:ℝ)..1, 4 * Real.pi ^ 2 * t ^ 2 * Real.sin (2 * Real.pi * s) ^ 2
          / (1 + t * Real.cos (2 * Real.pi * s)) := by
  have hsm := isSmoothPeriodic_firstSqrt ht
  have hg := isWeakGradient_smooth hsm
  have hae := weakGradient_ae_eq hg
  have h1 : ∫ x, ‖weakGradient (firstHarmonicDensity t ht).sqrt (firstHarmonicDensity t ht).sqrt_mem x‖ ^ 2
        ∂haar 1 = ∫ x, coordPartial 0 (firstSqrt t) x ^ 2 ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have : weakGradient (firstHarmonicDensity t ht).sqrt (firstHarmonicDensity t ht).sqrt_mem x
        = smoothGrad (firstSqrt t) x := hx
    rw [this, norm_smoothGrad, sq_abs]
  rw [h1]
  set S : (Fin 1 → ℝ) → ℝ := firstSqrt t ∘ torusLift with hS
  have hSd : ContDiff ℝ ∞ S := hsm
  have hS1 : ContDiff ℝ 1 S := hSd.of_le (by exact_mod_cast le_top)
  have hSD : Differentiable ℝ S := hS1.differentiable one_ne_zero
  have hSc : Continuous (fderiv ℝ S) := hS1.continuous_fderiv one_ne_zero
  have e1 := integral_haar_secT (G := fun y => fderiv ℝ S y (Pi.single 0 1) ^ 2)
    (((hSc.clm_apply continuous_const).pow 2).measurable)
  have e2 : ∫ x, coordPartial 0 (firstSqrt t) x ^ 2 ∂haar 1
      = ∫ s in (0:ℝ)..1, fderiv ℝ S (fun _ => s) (Pi.single 0 1) ^ 2 := by
    rw [← e1]; rfl
  rw [e2, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hpos : 0 < 1 + t * Real.cos (2 * Real.pi * s) := by
    have := firstHarmonic_pos ht (torusLift fun _ => s)
    rwa [firstHarmonic_lift] at this
  have hfun : (fun r : ℝ => S (fun _ => r)) = fun r => Real.sqrt (1 + t * Real.cos (2 * Real.pi * r)) := by
    funext r
    simp [hS, firstSqrt, firstHarmonic_lift]
  have hd1 := hasDerivAt_diag hSD s
  rw [hfun] at hd1
  have hd2 : HasDerivAt (fun r : ℝ => 1 + t * Real.cos (2 * Real.pi * r))
      (t * (-Real.sin (2 * Real.pi * s) * (2 * Real.pi * 1))) s := by
    have := (((hasDerivAt_id s).const_mul (2 * Real.pi)).cos.const_mul t).const_add 1
    simpa using this
  have hd3 := hd2.sqrt hpos.ne'
  have hu := hd1.unique hd3
  rw [hu]
  have hsq : Real.sqrt (1 + t * Real.cos (2 * Real.pi * s)) ^ 2 = 1 + t * Real.cos (2 * Real.pi * s) :=
    Real.sq_sqrt hpos.le
  have hs0 : Real.sqrt (1 + t * Real.cos (2 * Real.pi * s)) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  rw [div_pow, mul_pow (2:ℝ), hsq]
  field_simp

/-! ### Total real-valued entropy and Fisher information -/

/-- The first-harmonic coefficient `a₀ = 4π²`. -/
noncomputable def a0 : ℝ := 4 * Real.pi ^ 2

/-- `H_t = H(ρ_t m | m)` as a real number (`0` outside `|t| < 1`, where `ρ_t` is not a density). -/
noncomputable def firstHarmonicEntropy (t : ℝ) : ℝ :=
  if ht : |t| < 1 then
    (relativeEntropy (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1)) (haar 1)).toReal
  else 0

/-- `I_t = 4 ∫ |(√ρ_t)'|² dm` with the Haar weak gradient (`0` outside `|t| < 1`). -/
noncomputable def firstHarmonicFisher (t : ℝ) : ℝ :=
  if ht : |t| < 1 then
    4 * ∫ x, ‖weakGradient (firstHarmonicDensity t ht).sqrt
      (firstHarmonicDensity t ht).sqrt_mem x‖ ^ 2 ∂haar 1
  else 0

theorem firstHarmonicEntropy_of_lt {t : ℝ} (ht : |t| < 1) :
    firstHarmonicEntropy t =
      (relativeEntropy (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1))
        (haar 1)).toReal := by
  simp [firstHarmonicEntropy, ht]

theorem firstHarmonicFisher_of_lt {t : ℝ} (ht : |t| < 1) :
    firstHarmonicFisher t =
      4 * ∫ x, ‖weakGradient (firstHarmonicDensity t ht).sqrt
        (firstHarmonicDensity t ht).sqrt_mem x‖ ^ 2 ∂haar 1 := by
  simp [firstHarmonicFisher, ht]

theorem firstHarmonicDensity_density {t : ℝ} (ht : |t| < 1) :
    (firstHarmonicDensity t ht).density = firstHarmonic t := by
  funext x
  exact Real.sq_sqrt (firstHarmonic_pos ht x).le

/-- Entropy estimate for `0 < |t| ≤ 1/2`. -/
theorem entropy_bounds {t : ℝ} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) (ht1 : |t| < 1) :
    0 < relativeEntropy (densityMeasure (firstHarmonicDensity t ht1) : Measure (Torus 1)) (haar 1) ∧
    relativeEntropy (densityMeasure (firstHarmonicDensity t ht1) : Measure (Torus 1)) (haar 1) ≠ ⊤ ∧
    |firstHarmonicEntropy t - t ^ 2 / 4| ≤ 7 / 8 * |t| ^ 4 := by
  have hE := entropy_integral_estimate ht
  have h4 : |t| ^ 4 = t ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h4]
  set J := ∫ s in (0:ℝ)..1, ((1 + t * Real.cos (2 * Real.pi * s)) *
          Real.log (1 + t * Real.cos (2 * Real.pi * s)) - t * Real.cos (2 * Real.pi * s)) with hJ
  have ht2 : 0 < t ^ 2 := by positivity
  have ht2' : t ^ 2 ≤ 1 / 4 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  have hJpos : 0 < J := by
    have := (abs_le.1 hE).1
    have h4' : t ^ 4 ≤ t ^ 2 / 4 := by nlinarith
    nlinarith
  rw [entropy_eq_ofReal ht1]
  refine ⟨ENNReal.ofReal_pos.2 hJpos, ENNReal.ofReal_ne_top, ?_⟩
  rw [firstHarmonicEntropy_of_lt ht1, entropy_eq_ofReal ht1, ENNReal.toReal_ofReal hJpos.le]
  exact hE

/-- Fisher information estimate for `|t| ≤ 1/2`. -/
theorem fisher_bounds {t : ℝ} (ht : |t| ≤ 1 / 2) (ht1 : |t| < 1) :
    |firstHarmonicFisher t - a0 * t ^ 2 / 2| ≤ 4 * Real.pi ^ 2 * |t| ^ 4 := by
  have hF := fisher_integral_estimate ht
  have h4 : |t| ^ 4 = t ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h4, firstHarmonicFisher_of_lt ht1, fisher_eq ht1]
  have : a0 * t ^ 2 / 2 = 2 * Real.pi ^ 2 * t ^ 2 := by unfold a0; ring
  rw [this]
  exact hF

/-- **H1044.** On the unit Haar circle, `ρ_t = 1 + t cos (2π x)` for `0 < |t| ≤ 1/2`:
`ρ_t` is smooth, positive, of mass one; `H_t > 0`; `|H_t - t²/4| ≤ C|t|⁴`;
`|I_t - a₀ t²/2| ≤ C|t|⁴` with `a₀ = 4π²` (one fixed `C = 4π²` on the whole range); and
`I_t / (2 H_t) → a₀` as `t → 0`. -/
theorem circle_first_harmonic_estimates :
    a0 = 4 * Real.pi ^ 2 ∧
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, ∀ ht : |t| < 1, t ≠ 0 → |t| ≤ 1 / 2 →
        IsSmoothPeriodic (firstHarmonic t) ∧
        (∀ x, 0 < firstHarmonic t x) ∧
        ∫ x, firstHarmonic t x ∂haar 1 = 1 ∧
        (firstHarmonicDensity t ht).density = firstHarmonic t ∧
        0 < relativeEntropy (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1))
          (haar 1) ∧
        relativeEntropy (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1))
          (haar 1) ≠ ⊤ ∧
        |firstHarmonicEntropy t - t ^ 2 / 4| ≤ C * |t| ^ 4 ∧
        |firstHarmonicFisher t - a0 * t ^ 2 / 2| ≤ C * |t| ^ 4) ∧
      Tendsto (fun t : ℝ => firstHarmonicFisher t / (2 * firstHarmonicEntropy t))
        (𝓝[≠] 0) (𝓝 a0) := by
  have hπ : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hC : (7:ℝ) / 8 ≤ 4 * Real.pi ^ 2 := by nlinarith
  refine ⟨rfl, 4 * Real.pi ^ 2, by positivity, ?_, ?_⟩
  · intro t ht ht0 hle
    obtain ⟨hp, hne, hb⟩ := entropy_bounds hle ht0 ht
    have hf := fisher_bounds hle ht
    have h4 : 0 ≤ |t| ^ 4 := by positivity
    refine ⟨isSmoothPeriodic_firstHarmonic t, firstHarmonic_pos ht, integral_firstHarmonic t,
      firstHarmonicDensity_density ht, hp, hne, hb.trans ?_, hf⟩
    nlinarith
  · -- the limit
    have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
      refine Filter.Eventually.and ?_ self_mem_nhdsWithin
      have : ∀ᶠ t in 𝓝 (0:ℝ), |t| < 1 / 2 := by
        have := (continuous_abs.tendsto (0:ℝ)).eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1 / 2))
        simpa using this
      exact nhdsWithin_le_nhds this
    set C : ℝ := 4 * Real.pi ^ 2 with hCdef
    have hsq : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
        (continuous_const.mul (continuous_pow 2)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    -- a(t) = I/t², b(t) = H/t²
    have ha : Tendsto (fun t : ℝ => firstHarmonicFisher t / t ^ 2) (𝓝[≠] 0) (𝓝 (a0 / 2)) := by
      have h0 : Tendsto (fun t : ℝ => firstHarmonicFisher t / t ^ 2 - a0 / 2) (𝓝[≠] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hsq
        filter_upwards [hev] with t ⟨hlt, ht0⟩
        have ht1 : |t| < 1 := by linarith
        have hf := fisher_bounds hlt.le ht1
        have h4 : |t| ^ 4 = t ^ 4 := by
          rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        rw [h4] at hf
        have ht2 : 0 < t ^ 2 := by positivity
        rw [Real.norm_eq_abs]
        have : firstHarmonicFisher t / t ^ 2 - a0 / 2 = (firstHarmonicFisher t - a0 * t ^ 2 / 2) / t ^ 2 := by
          field_simp
        rw [this, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
        calc |firstHarmonicFisher t - a0 * t ^ 2 / 2| ≤ 4 * Real.pi ^ 2 * t ^ 4 := hf
          _ = C * t ^ 2 * t ^ 2 := by rw [hCdef]; ring
      simpa using h0.add_const (a0 / 2)
    have hb : Tendsto (fun t : ℝ => firstHarmonicEntropy t / t ^ 2) (𝓝[≠] 0) (𝓝 (1 / 4)) := by
      have h0 : Tendsto (fun t : ℝ => firstHarmonicEntropy t / t ^ 2 - 1 / 4) (𝓝[≠] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hsq
        filter_upwards [hev] with t ⟨hlt, ht0⟩
        have ht1 : |t| < 1 := by linarith
        have hb := (entropy_bounds hlt.le ht0 ht1).2.2
        have h4 : |t| ^ 4 = t ^ 4 := by
          rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        rw [h4] at hb
        have ht2 : 0 < t ^ 2 := by positivity
        rw [Real.norm_eq_abs]
        have : firstHarmonicEntropy t / t ^ 2 - 1 / 4 = (firstHarmonicEntropy t - t ^ 2 / 4) / t ^ 2 := by
          field_simp
        rw [this, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
        have hC' : (7:ℝ) / 8 ≤ C := by rw [hCdef]; exact hC
        have h4' : 0 ≤ t ^ 4 := by positivity
        calc |firstHarmonicEntropy t - t ^ 2 / 4| ≤ 7 / 8 * t ^ 4 := hb
          _ ≤ C * t ^ 4 := mul_le_mul_of_nonneg_right hC' h4'
          _ = C * t ^ 2 * t ^ 2 := by ring
      have := h0.add_const (1 / 4)
      rw [zero_add] at this
      exact this.congr fun t => by ring
    have hq := ha.div (hb.const_mul 2) (by norm_num)
    have hlim : a0 / 2 / (2 * (1 / 4)) = a0 := by ring
    rw [hlim] at hq
    refine hq.congr' ?_
    filter_upwards [hev] with t ⟨hlt, ht0⟩
    have ht1 : |t| < 1 := by linarith
    have hpos : 0 < firstHarmonicEntropy t := by
      obtain ⟨hp, hne, -⟩ := entropy_bounds hlt.le ht0 ht1
      rw [firstHarmonicEntropy_of_lt ht1]
      exact ENNReal.toReal_pos hp.ne' hne
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    simp only [Pi.div_apply]
    field_simp

end DGPS.Analysis.CircleMoments
