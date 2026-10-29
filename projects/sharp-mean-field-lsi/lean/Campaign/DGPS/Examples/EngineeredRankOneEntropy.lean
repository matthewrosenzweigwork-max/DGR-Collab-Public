import DGPS.Examples.EngineeredRankOneGap
import DGPS.Examples.EngineeredRankOneNormalization
import DGPS.Analysis.ForceMultiplier
import DGPS.Circle.StationaryFlux
import DGPS.Foundations.Entropy
import DGPS.Foundations.RelativeEntropy

/-!
# Engineered rank-one model: the large-`T` entropy regime (EX041)

For `ρ = f² μ_h` on the engineered reference measure with `μ_h(f²) = 1`, set `E = μ_h((f')²)`,
`M = ρ(E_h)` and `T = E/h + M²`. If `T ≥ 1` and `h ≥ 2`, then `H(ρ | μ_h) ≤ C T` with `C`
independent of `h` and `ρ`.

The argument uses only elementary inequalities.
* The exact feature relation `exp (h U) = c_h + tanh h · E_h` and the tangent-line inequality for the
  logarithm give `ρ(hU) ≤ 3/2 + M²/2` (`feature_moment`).
* With the ground state `s = √q_h`, the function `w = f s` is an angular weak derivative whose
  energy is `≤ 2E + 16 h ρ(hU)` (`energy_bound`), using `(log q_h)'² ≤ 32 h (h U)`.
* The Agmon inequality bounds `f² q_h ≤ K` with `K = 1 + 2 √(a₀ ∫ (w')²)`.
* The entropy integrand is bounded pointwise by a linear expression in `ρ(hU)`, `log K`, `log Z_h`
  (`entropy_pointwise`), using `corr ≤ 3 h U` and `Z_h ≤ C₀ h^{-1/2}`.
* Since `T ≥ 1`, all logarithms are bounded by multiples of `T`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization
open DGPS.Circle.StationaryFlux

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models


theorem aH_le_three (h : ℝ) (hh : 2 ≤ h) : aH h ≤ 3 := by
  have hp : 0 < h := by linarith
  have hs : 0 < sinh h := Real.sinh_pos_iff.2 hp
  have h3 : (3:ℝ) ≤ exp h := by
    have := Real.add_one_le_exp h
    linarith
  have he : exp (-h) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hep : 0 < exp (-h) := exp_pos _
  have hc : cosh h ≤ 2 * sinh h := by
    rw [Real.cosh_eq, Real.sinh_eq]; nlinarith
  unfold aH
  have : cosh h / sinh h ≤ 2 := by
    rw [div_le_iff₀ hs]; exact hc
  linarith

theorem numer_le_two_sub_ent (h : ℝ) (hh : 0 < h) {v : ℝ} (hv : v ≤ 2) : numer h v ≤ 2 - v := by
  have h1 : exp (-h * 2) ≤ exp (-h * v) := by
    apply Real.exp_le_exp.2; nlinarith
  have h2 := aH_mul h hh
  have ha := aH_pos h hh
  unfold numer
  nlinarith

theorem numer_le_lin_ent (h : ℝ) (hh : 0 < h) (v : ℝ) (hv : 0 ≤ v) : numer h v ≤ aH h * h * v := by
  have h1 : 1 - exp (-h * v) ≤ h * v := by
    have := Real.add_one_le_exp (-h * v)
    linarith
  have ha := aH_pos h hh
  unfold numer
  nlinarith

theorem integrand_le_ent (h : ℝ) (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    integrand h u ≤ 3 * h := by
  have hp : 0 < h := by linarith
  have ha := aH_pos h hp
  have ha3 := aH_le_three h hh
  by_cases h0 : u = 0
  · subst h0
    have e : integrand h 0 = (aH h * h - 1) / 2 := by simp [integrand]
    rw [e]
    nlinarith
  by_cases h2 : u = 2
  · subst h2
    have e : integrand h 2 = -(aH h * h * exp (-h * 2) - 1) / 2 := by simp [integrand]
    rw [e]
    have : 0 ≤ aH h * h * exp (-h * 2) := by positivity
    nlinarith
  have hu0 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h0)
  have hu2 : u < 2 := lt_of_le_of_ne hu.2 h2
  rw [integrand_of_ne h h0 h2]
  have hd : 0 < u * (2 - u) := mul_pos hu0 (by linarith)
  rw [div_le_iff₀ hd]
  by_cases h1 : u ≤ 1
  · have := numer_le_lin_ent h hp u hu0.le
    have h4 : aH h * h * u ≤ 3 * h * u := by
      have : 0 ≤ h * u := by positivity
      nlinarith
    have h5 : 3 * h * u ≤ 3 * h * (u * (2 - u)) := by
      have : 0 ≤ 3 * h * u := by positivity
      nlinarith
    linarith
  · have h1 : 1 < u := not_le.1 h1
    have := numer_le_two_sub_ent h hp hu2.le
    nlinarith

theorem corr_le (h : ℝ) (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    corr h u ≤ 3 * h * u := by
  have hp : 0 < h := by linarith
  have hint : IntervalIntegrable (integrand h) volume 0 u :=
    ((contDiff_integrand h hp).continuous).intervalIntegrable _ _
  unfold corr
  have := intervalIntegral.integral_mono_on hu.1 hint
    (intervalIntegrable_const (c := 3 * h)) (fun v hv => integrand_le_ent h hh ⟨hv.1, hv.2.trans hu.2⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
  linarith

theorem dlogqAng_sq_le (h : ℝ) (hh : 2 ≤ h) (θ : AngCircle) :
    dlogqAng h θ ^ 2 ≤ 32 * h * (h * Uang θ) := by
  have hp : 0 < h := by linarith
  have hU := Uang_mem θ
  have h0 := integrand_nonneg h hp hU
  have h3 := integrand_le_ent h hh hU
  have hs : Real.Angle.sin θ ^ 2 ≤ 2 * Uang θ := by
    unfold Uang
    have := (by induction θ using Real.Angle.induction_on with
      | _ x => rw [Real.Angle.sin_coe, Real.Angle.cos_coe]; exact Real.sin_sq_add_cos_sq x :
      Real.Angle.sin θ ^ 2 + Real.Angle.cos θ ^ 2 = 1)
    have hc : Real.Angle.cos θ ≤ 1 := by
      induction θ using Real.Angle.induction_on with
      | _ x => rw [Real.Angle.cos_coe]; exact Real.cos_le_one x
    have hc' : -1 ≤ Real.Angle.cos θ := by
      induction θ using Real.Angle.induction_on with
      | _ x => rw [Real.Angle.cos_coe]; exact Real.neg_one_le_cos x
    nlinarith
  unfold dlogqAng
  rw [mul_pow, neg_sq]
  have hA : (h + integrand h (1 - Real.Angle.cos θ)) ^ 2 ≤ (4 * h) ^ 2 := by
    have e : 1 - Real.Angle.cos θ = Uang θ := rfl
    rw [e]
    apply pow_le_pow_left₀ (by linarith)
    linarith
  have hUn := hU.1
  calc (h + integrand h (1 - Real.Angle.cos θ)) ^ 2 * Real.Angle.sin θ ^ 2
      ≤ (4 * h) ^ 2 * (2 * Uang θ) :=
        mul_le_mul hA hs (sq_nonneg _) (by positivity)
    _ = 32 * h * (h * Uang θ) := by ring




theorem measurable_ofReal_qAng (h : ℝ) (hh : 0 < h) :
    Measurable (fun θ => ENNReal.ofReal (qAng h θ)) :=
  ENNReal.measurable_ofReal.comp (continuous_qAng h hh).measurable

theorem integral_ref_ent (h : ℝ) (hh : 0 < h) (F : AngCircle → ℝ) :
    ∫ x, F (angEquiv x) ∂engineeredReference h = ∫ θ, qAng h θ * F θ ∂angHaar := by
  unfold engineeredReference
  rw [integral_map_equiv angEquiv.symm]
  simp only [MeasurableEquiv.apply_symm_apply]
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_qAng h hh)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp [ENNReal.toReal_ofReal (qAng_pos h hh θ).le]

theorem lintegral_ref (h : ℝ) (hh : 0 < h) (G : AngCircle → ENNReal) :
    ∫⁻ x, G (angEquiv x) ∂engineeredReference h =
      ∫⁻ θ, ENNReal.ofReal (qAng h θ) * G θ ∂angHaar := by
  unfold engineeredReference
  rw [lintegral_map_equiv _ angEquiv.symm]
  simp only [MeasurableEquiv.apply_symm_apply]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_ofReal_qAng h hh)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

theorem aemeasurable_ref (h : ℝ) {v : AngCircle → ℝ} (hv : AEMeasurable v angHaar) :
    AEMeasurable (fun x => v (angEquiv x)) (engineeredReference h) := by
  unfold engineeredReference
  rw [angEquiv.symm.measurableEmbedding.aemeasurable_map_iff]
  simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply]
  exact hv.mono_ac (withDensity_absolutelyContinuous _ _)




theorem exists_bound_of_continuous {c : AngCircle → ℝ} (hc : Continuous c) :
    ∃ C : ℝ, ∀ θ, ‖c θ‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨C, fun θ => hC θ (mem_univ _)⟩

theorem memLp_mul_cont {u : AngCircle → ℝ} (hu : MemLp u 2 angHaar) {c : AngCircle → ℝ}
    (hc : Continuous c) : MemLp (fun θ => u θ * c θ) 2 angHaar := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hc
  refine hu.of_le_mul (c := C) (hu.aestronglyMeasurable.mul hc.aestronglyMeasurable) ?_
  refine Eventually.of_forall fun θ => ?_
  rw [norm_mul]
  nlinarith [hC θ, norm_nonneg (u θ), norm_nonneg (c θ)]

theorem integrable_cont_mul {u : AngCircle → ℝ} (hu : MemLp u 2 angHaar) {c : AngCircle → ℝ}
    (hc : Continuous c) : Integrable (fun θ => u θ * c θ) angHaar := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hc
  exact (hu.integrable (by norm_num)).mul_bdd hc.aestronglyMeasurable
    (Eventually.of_forall hC)

theorem isAngularWeakDeriv_mul_smooth {u g s : AngCircle → ℝ} (hu : IsAngularWeakDeriv u g)
    (hs : IsSmoothAngular s) :
    IsAngularWeakDeriv (fun θ => u θ * s θ)
      (fun θ => g θ * s θ + u θ * angDeriv s θ) where
  memLp := memLp_mul_cont hu.memLp (continuous_of_smooth hs)
  memLp_deriv :=
    (memLp_mul_cont hu.memLp_deriv (continuous_of_smooth hs)).add
      (memLp_mul_cont hu.memLp (continuous_of_smooth (smooth_angDeriv hs)))
  ibp := by
    intro ψ hψ
    have h1 := hu.ibp (fun θ => s θ * ψ θ) (smooth_mul hs hψ)
    rw [angDeriv_mul hs hψ] at h1
    have cs := continuous_of_smooth hs
    have cds := continuous_of_smooth (smooth_angDeriv hs)
    have cψ := continuous_of_smooth hψ
    have cdψ := continuous_of_smooth (smooth_angDeriv hψ)
    have i1 : Integrable (fun θ => u θ * (angDeriv s θ * ψ θ)) angHaar :=
      integrable_cont_mul hu.memLp (cds.mul cψ)
    have i2 : Integrable (fun θ => u θ * (s θ * angDeriv ψ θ)) angHaar :=
      integrable_cont_mul hu.memLp (cs.mul cdψ)
    have i3 : Integrable (fun θ => g θ * (s θ * ψ θ)) angHaar :=
      integrable_cont_mul hu.memLp_deriv (cs.mul cψ)
    have e1 : ∫ θ, u θ * (angDeriv s θ * ψ θ + s θ * angDeriv ψ θ) ∂angHaar =
        ∫ θ, u θ * (angDeriv s θ * ψ θ) ∂angHaar + ∫ θ, u θ * (s θ * angDeriv ψ θ) ∂angHaar := by
      rw [← integral_add i1 i2]
      exact integral_congr_ae (Eventually.of_forall fun θ => by simp only [mul_add])
    have e2 : ∫ θ, (g θ * s θ + u θ * angDeriv s θ) * ψ θ ∂angHaar =
        ∫ θ, g θ * (s θ * ψ θ) ∂angHaar + ∫ θ, u θ * (angDeriv s θ * ψ θ) ∂angHaar := by
      rw [← integral_add i3 i1]
      exact integral_congr_ae (Eventually.of_forall fun θ => by ring)
    have e3 : ∫ θ, u θ * s θ * angDeriv ψ θ ∂angHaar =
        ∫ θ, u θ * (s θ * angDeriv ψ θ) ∂angHaar :=
      integral_congr_ae (Eventually.of_forall fun θ => by ring)
    rw [e3, e2]
    rw [e1] at h1
    linarith

/-- The ground state `√q_h`. -/
noncomputable def sAng (h : ℝ) (θ : AngCircle) : ℝ :=
  (Real.sqrt (Zh h))⁻¹ * exp (logq h θ / 2)

theorem sAng_sq (h : ℝ) (hh : 0 < h) (θ : AngCircle) : sAng h θ ^ 2 = qAng h θ := by
  unfold sAng qAng
  rw [mul_pow, inv_pow, Real.sq_sqrt (Zh_pos h hh).le, ← Real.exp_nat_mul]
  congr 2
  push_cast; ring

theorem sAng_pos (h : ℝ) (hh : 0 < h) (θ : AngCircle) : 0 < sAng h θ := by
  unfold sAng
  exact mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Zh_pos h hh))) (exp_pos _)

theorem hasDerivAt_sAng (h : ℝ) (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sAng h (s : AngCircle))
      (sAng h (t : AngCircle) * (dlogqAng h (t : AngCircle) / 2)) t := by
  have h1 := ((hasDerivAt_logq h hh t).div_const 2).exp.const_mul ((Real.sqrt (Zh h))⁻¹)
  refine h1.congr_deriv ?_
  rw [dlogqAng_coe]
  have e : sAng h (t : AngCircle) = (Real.sqrt (Zh h))⁻¹ * exp (logq h (t : Real.Angle) / 2) := rfl
  rw [e]
  ring

theorem angDeriv_sAng (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    angDeriv (sAng h) θ = sAng h θ * (dlogqAng h θ / 2) :=
  angDeriv_of (G := fun θ => sAng h θ * (dlogqAng h θ / 2)) (hasDerivAt_sAng h hh) θ

theorem isSmoothAngular_sAng (h : ℝ) (hh : 0 < h) : IsSmoothAngular (sAng h) := by
  have hUs : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.cos t) :=
    contDiff_const.sub Real.contDiff_cos
  have hL : ContDiff ℝ ∞ (fun t : ℝ => logq h ((t : ℝ) : AngCircle)) := by
    have : (fun t : ℝ => logq h ((t : ℝ) : AngCircle)) =
        fun t => -(h * (1 - Real.cos t)) - corr h (1 - Real.cos t) := by
      funext t; unfold logq; rw [Uang_coe']
    rw [this]
    exact (contDiff_const.mul hUs).neg.sub ((contDiff_corr h hh).comp hUs)
  unfold IsSmoothAngular sAng
  exact contDiff_const.mul (Real.contDiff_exp.comp (hL.div_const 2))

theorem continuous_dlogqAng (h : ℝ) (hh : 0 < h) : Continuous (dlogqAng h) := by
  unfold dlogqAng
  exact ((continuous_const.add ((contDiff_integrand h hh).continuous.comp
    (continuous_const.sub Real.Angle.continuous_cos))).neg).mul Real.Angle.continuous_sin

theorem integrable_sq_mul_cont {f : AngCircle → ℝ} (hf : MemLp f 2 angHaar)
    {c : AngCircle → ℝ} (hc : Continuous c) :
    Integrable (fun θ => f θ ^ 2 * c θ) angHaar := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hc
  exact hf.integrable_sq.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall hC)

theorem integrable_q_sq_mul (h : ℝ) (hh : 0 < h) {f : AngCircle → ℝ} (hf : MemLp f 2 angHaar)
    {c : AngCircle → ℝ} (hc : Continuous c) :
    Integrable (fun θ => qAng h θ * f θ ^ 2 * c θ) angHaar := by
  have hc' : Continuous (fun θ => qAng h θ * c θ) := (continuous_qAng h hh).mul hc
  have := integrable_sq_mul_cont hf hc'
  refine this.congr (Eventually.of_forall fun θ => ?_)
  simp only
  ring

theorem integrable_q_sq (h : ℝ) (hh : 0 < h) {f : AngCircle → ℝ} (hf : MemLp f 2 angHaar) :
    Integrable (fun θ => qAng h θ * f θ ^ 2) angHaar := by
  have := integrable_q_sq_mul h hh hf (continuous_const (y := (1 : ℝ)))
  simpa using this

theorem q_sq_nonneg (h : ℝ) (hh : 0 < h) (f : AngCircle → ℝ) (θ : AngCircle) :
    0 ≤ qAng h θ * f θ ^ 2 :=
  mul_nonneg (qAng_pos h hh θ).le (sq_nonneg _)

theorem tanh_pos' {h : ℝ} (hh : 0 < h) : 0 < tanh h := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.2 hh) (Real.cosh_pos _)

theorem continuous_hU (h : ℝ) : Continuous (fun θ => h * Uang θ) :=
  continuous_const.mul continuous_Uang

theorem exp_hU_eq (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    exp (h * Uang θ) = cH h + tanh h * Eang h θ := by
  have ht : tanh h ≠ 0 := (tanh_pos' hh).ne'
  unfold Eang
  field_simp
  ring

theorem feature_X (h : ℝ) (hh : 0 < h) {f : AngCircle → ℝ} (hf : MemLp f 2 angHaar)
    (hnorm : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1) :
    ∫ θ, qAng h θ * f θ ^ 2 * exp (h * Uang θ) ∂angHaar =
      cH h + tanh h * ∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar := by
  have i1 := integrable_q_sq h hh hf
  have i2 := integrable_q_sq_mul h hh hf (continuous_Eang h)
  have e : ∀ θ, qAng h θ * f θ ^ 2 * exp (h * Uang θ) =
      cH h * (qAng h θ * f θ ^ 2) + tanh h * (qAng h θ * f θ ^ 2 * Eang h θ) := by
    intro θ
    rw [exp_hU_eq h hh θ]; ring
  simp_rw [e]
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    hnorm, mul_one]

theorem feature_moment (h : ℝ) (hh : 0 < h) {f : AngCircle → ℝ} (hf : MemLp f 2 angHaar)
    (hnorm : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1) :
    ∫ θ, qAng h θ * f θ ^ 2 * (h * Uang θ) ∂angHaar ≤
      3 / 2 + (∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar) ^ 2 / 2 := by
  have ht := tanh_pos' hh
  have ht1 := Real.tanh_lt_one h
  have hXeq := feature_X h hh hf hnorm
  have i0 := integrable_q_sq h hh hf
  have iE := integrable_q_sq_mul h hh hf (continuous_hU h)
  have iX := integrable_q_sq_mul h hh hf (continuous_hU h).rexp
  have hXge : 1 ≤ ∫ θ, qAng h θ * f θ ^ 2 * exp (h * Uang θ) ∂angHaar := by
    rw [← hnorm]
    refine integral_mono i0 iX fun θ => ?_
    have h1 : 1 ≤ exp (h * Uang θ) := Real.one_le_exp (mul_nonneg hh.le (Uang_mem θ).1)
    have := q_sq_nonneg h hh f θ
    nlinarith
  generalize hXd : ∫ θ, qAng h θ * f θ ^ 2 * exp (h * Uang θ) ∂angHaar = X at hXge hXeq
  generalize hMd : ∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar = M at hXeq
  have hXpos : 0 < X := by linarith
  have key : ∀ θ, qAng h θ * f θ ^ 2 * (h * Uang θ) ≤
      qAng h θ * f θ ^ 2 * (Real.log X - 1) + X⁻¹ * (qAng h θ * f θ ^ 2 * exp (h * Uang θ)) := by
    intro θ
    have hz : 0 < exp (h * Uang θ) / X := div_pos (exp_pos _) hXpos
    have h1 := Real.log_le_sub_one_of_pos hz
    rw [Real.log_div (exp_pos _).ne' hXpos.ne', Real.log_exp] at h1
    have h2 : exp (h * Uang θ) / X = X⁻¹ * exp (h * Uang θ) := by ring
    rw [h2] at h1
    have := q_sq_nonneg h hh f θ
    have h3 : h * Uang θ ≤ Real.log X - 1 + X⁻¹ * exp (h * Uang θ) := by linarith
    calc qAng h θ * f θ ^ 2 * (h * Uang θ)
        ≤ qAng h θ * f θ ^ 2 * (Real.log X - 1 + X⁻¹ * exp (h * Uang θ)) :=
          mul_le_mul_of_nonneg_left h3 this
      _ = _ := by ring
  have iR1 : Integrable (fun θ => qAng h θ * f θ ^ 2 * (Real.log X - 1)) angHaar :=
    i0.mul_const _
  have iR2 : Integrable (fun θ => X⁻¹ * (qAng h θ * f θ ^ 2 * exp (h * Uang θ))) angHaar :=
    iX.const_mul _
  have iS : Integrable (fun θ => qAng h θ * f θ ^ 2 * (Real.log X - 1) +
      X⁻¹ * (qAng h θ * f θ ^ 2 * exp (h * Uang θ))) angHaar := iR1.add iR2
  have iE' : Integrable (fun θ => qAng h θ * f θ ^ 2 * (h * Uang θ)) angHaar := iE
  have hint : ∫ θ, qAng h θ * f θ ^ 2 * (h * Uang θ) ∂angHaar ≤ Real.log X := by
    calc ∫ θ, qAng h θ * f θ ^ 2 * (h * Uang θ) ∂angHaar
        ≤ ∫ θ, (qAng h θ * f θ ^ 2 * (Real.log X - 1) +
            X⁻¹ * (qAng h θ * f θ ^ 2 * exp (h * Uang θ))) ∂angHaar :=
          integral_mono iE' iS key
      _ = Real.log X := by
          rw [integral_add iR1 iR2, integral_mul_const, integral_const_mul, hnorm, hXd]
          field_simp
          ring
  have hlog : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos hXpos
  have hM : X - 1 ≤ 1 + |M| := by
    rw [hXeq, cH]
    nlinarith [abs_nonneg M, le_abs_self M, neg_abs_le M]
  have hA : |M| ≤ (1 + M ^ 2) / 2 := by
    nlinarith [sq_abs M, sq_nonneg (|M| - 1)]
  linarith

theorem energy_bound (h : ℝ) (hh : 2 ≤ h) {f f' : AngCircle → ℝ} (hw : IsAngularWeakDeriv f f') :
    ∫ θ, (f' θ * sAng h θ + f θ * angDeriv (sAng h) θ) ^ 2 ∂angHaar ≤
      2 * ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar +
        16 * h * ∫ θ, qAng h θ * f θ ^ 2 * (h * Uang θ) ∂angHaar := by
  have hp : 0 < h := by linarith
  have hI := (isAngularWeakDeriv_mul_smooth hw (isSmoothAngular_sAng h hp)).memLp_deriv.integrable_sq
  have iA := integrable_q_sq h hp hw.memLp_deriv
  have iB := integrable_q_sq_mul h hp hw.memLp (continuous_hU h)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iA.const_mul _) (iB.const_mul _)]
  refine integral_mono hI ((iA.const_mul _).add (iB.const_mul _)) fun θ => ?_
  have hs := sAng_sq h hp θ
  have hq := qAng_pos h hp θ
  have hb := dlogqAng_sq_le h hh θ
  rw [angDeriv_sAng h hp]
  have hf2 := sq_nonneg (f θ)
  have e1 : (f' θ * sAng h θ + f θ * (sAng h θ * (dlogqAng h θ / 2))) ^ 2 ≤
      2 * (f' θ * sAng h θ) ^ 2 + 2 * (f θ * (sAng h θ * (dlogqAng h θ / 2))) ^ 2 := by
    nlinarith [sq_nonneg (f' θ * sAng h θ - f θ * (sAng h θ * (dlogqAng h θ / 2)))]
  have e2 : (f' θ * sAng h θ) ^ 2 = qAng h θ * f' θ ^ 2 := by
    rw [mul_pow, hs]; ring
  have e3 : (f θ * (sAng h θ * (dlogqAng h θ / 2))) ^ 2 =
      qAng h θ * f θ ^ 2 * (dlogqAng h θ ^ 2 / 4) := by
    have : (f θ * (sAng h θ * (dlogqAng h θ / 2))) ^ 2 =
        f θ ^ 2 * sAng h θ ^ 2 * (dlogqAng h θ ^ 2 / 4) := by ring
    rw [this, hs]; ring
  have e4 : qAng h θ * f θ ^ 2 * (dlogqAng h θ ^ 2 / 4) ≤
      qAng h θ * f θ ^ 2 * (8 * h * (h * Uang θ)) := by
    apply mul_le_mul_of_nonneg_left _ (q_sq_nonneg h hp f θ)
    linarith
  rw [e2, e3] at e1
  nlinarith


theorem agmon_ang {w w' : AngCircle → ℝ} (hw : IsAngularWeakDeriv w w')
    (hnorm : ∫ θ, w θ ^ 2 ∂angHaar = 1) :
    ∀ᵐ θ ∂angHaar, w θ ^ 2 ≤ 1 + 2 * Real.sqrt (a0 * ∫ θ, w' θ ^ 2 ∂angHaar) := by
  have hG := (isWeakGradient_comp_iff w w').1 hw
  have h1 := DGPS.Analysis.ForceMultiplier.circle_slice_sup_norm.1 (w ∘ angEquiv) (physGrad w') hG
  have e1 : ∫ t, (w ∘ angEquiv) t ^ 2 ∂haar 1 = 1 := by
    exact (integral_comp_angEquiv (fun θ => w θ ^ 2)).trans hnorm
  have e2 := integral_norm_sq_of_weakGradient hw hG
  rw [e1, e2] at h1
  refine (ae_comp_angEquiv_iff
    (p := fun θ => w θ ^ 2 ≤ 1 + 2 * Real.sqrt (a0 * ∫ θ, w' θ ^ 2 ∂angHaar))).1 ?_
  filter_upwards [h1] with x hx
  simpa using hx

theorem entropy_pointwise (h : ℝ) (hh : 2 ≤ h) {K : ℝ} (θ : AngCircle) {v : ℝ}
    (hv : 0 ≤ v) (hvK : qAng h θ * v ≤ K) :
    qAng h θ * (v * Real.log v - v + 1) ≤
      qAng h θ * v * (Real.log K + Real.log (Zh h) + 4 * (h * Uang θ) - 1) + qAng h θ := by
  have hp : 0 < h := by linarith
  have hq := qAng_pos h hp θ
  have hlogq : -Real.log (qAng h θ) ≤ Real.log (Zh h) + 4 * (h * Uang θ) := by
    rw [log_qAng h hp]
    unfold logq
    have := corr_le h hh (Uang_mem θ)
    linarith
  have hvl : v * Real.log v ≤ v * (Real.log K - Real.log (qAng h θ)) := by
    rcases hv.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · apply mul_le_mul_of_nonneg_left _ hv
      have := Real.log_le_log (mul_pos h0 hq) (by linarith : v * qAng h θ ≤ K)
      rw [Real.log_mul h0.ne' hq.ne'] at this
      linarith
  have hqv : 0 ≤ qAng h θ * v := mul_nonneg hq.le hv
  have h1 : qAng h θ * (v * Real.log v) ≤ qAng h θ * (v * (Real.log K - Real.log (qAng h θ))) :=
    mul_le_mul_of_nonneg_left hvl hq.le
  have h2 : qAng h θ * v * (Real.log K - Real.log (qAng h θ)) ≤
      qAng h θ * v * (Real.log K + Real.log (Zh h) + 4 * (h * Uang θ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hqv
  nlinarith

theorem entropy_lintegral_le (h : ℝ) (hh : 2 ≤ h) {f : AngCircle → ℝ} (hf : MemLp f 2 angHaar)
    (hnorm : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1) {K : ℝ}
    (hae : ∀ᵐ θ ∂angHaar, qAng h θ * f θ ^ 2 ≤ K) :
    ∫⁻ θ, ENNReal.ofReal (qAng h θ * (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) ∂angHaar ≤
      ENNReal.ofReal (Real.log K + Real.log (Zh h) +
        4 * ∫ θ, qAng h θ * f θ ^ 2 * (h * Uang θ) ∂angHaar) := by
  have hp : 0 < h := by linarith
  have iq : Integrable (qAng h) angHaar := integrable_angHaar_of_continuous (continuous_qAng h hp)
  have i0 := integrable_q_sq h hp hf
  have iU := integrable_q_sq_mul h hp hf (continuous_hU h)
  have iΨ : Integrable (fun θ => (Real.log K + Real.log (Zh h) - 1) * (qAng h θ * f θ ^ 2) +
      4 * (qAng h θ * f θ ^ 2 * (h * Uang θ)) + qAng h θ) angHaar :=
    ((i0.const_mul _).add (iU.const_mul _)).add iq
  have hΨ : ∀ θ, qAng h θ * f θ ^ 2 * (Real.log K + Real.log (Zh h) + 4 * (h * Uang θ) - 1) +
      qAng h θ = (Real.log K + Real.log (Zh h) - 1) * (qAng h θ * f θ ^ 2) +
      4 * (qAng h θ * f θ ^ 2 * (h * Uang θ)) + qAng h θ := fun θ => by ring
  have hnn : ∀ θ, 0 ≤ qAng h θ * (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1) := fun θ =>
    mul_nonneg (qAng_pos h hp θ).le (self_mul_log_sub_add_one_nonneg (sq_nonneg _))
  have hpt : ∀ᵐ θ ∂angHaar, qAng h θ * (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1) ≤
      (Real.log K + Real.log (Zh h) - 1) * (qAng h θ * f θ ^ 2) +
      4 * (qAng h θ * f θ ^ 2 * (h * Uang θ)) + qAng h θ := by
    filter_upwards [hae] with θ hθ
    rw [← hΨ θ]
    exact entropy_pointwise h hh θ (sq_nonneg _) hθ
  calc ∫⁻ θ, ENNReal.ofReal (qAng h θ * (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) ∂angHaar
      ≤ ∫⁻ θ, ENNReal.ofReal ((Real.log K + Real.log (Zh h) - 1) * (qAng h θ * f θ ^ 2) +
          4 * (qAng h θ * f θ ^ 2 * (h * Uang θ)) + qAng h θ) ∂angHaar :=
        lintegral_mono_ae (hpt.mono fun θ hθ => ENNReal.ofReal_le_ofReal hθ)
    _ = ENNReal.ofReal (∫ θ, (Real.log K + Real.log (Zh h) - 1) * (qAng h θ * f θ ^ 2) +
          4 * (qAng h θ * f θ ^ 2 * (h * Uang θ)) + qAng h θ ∂angHaar) := by
        refine (ofReal_integral_eq_lintegral_ofReal iΨ ?_).symm
        filter_upwards [hpt] with θ hθ
        exact (hnn θ).trans hθ
    _ = _ := by
        congr 1
        have iS : Integrable (fun θ => (Real.log K + Real.log (Zh h) - 1) * (qAng h θ * f θ ^ 2) +
            4 * (qAng h θ * f θ ^ 2 * (h * Uang θ))) angHaar :=
          (i0.const_mul _).add (iU.const_mul _)
        have iA : Integrable (fun θ => (Real.log K + Real.log (Zh h) - 1) *
            (qAng h θ * f θ ^ 2)) angHaar := i0.const_mul _
        have iB : Integrable (fun θ => 4 * (qAng h θ * f θ ^ 2 * (h * Uang θ))) angHaar :=
          iU.const_mul _
        rw [integral_add iS iq, integral_add iA iB, integral_const_mul, integral_const_mul,
          hnorm, integral_qAng h hp]
        ring

/-- The constant `c₀` in `Z_h ≤ c₀ h^{-1/2}`. -/
noncomputable def zhConst : ℝ := (2 * π)⁻¹ * √(π / (2 / π ^ 2))

theorem zhConst_nonneg : 0 ≤ zhConst := by
  unfold zhConst; positivity

theorem Zh_le_const (h : ℝ) (hh : 0 < h) : Zh h ≤ zhConst * (√h)⁻¹ := Zh_le h hh

/-- The explicit constant `C` of the large-`T` entropy bound, independent of `h` and `ρ`. -/
noncomputable def entropyConst : ℝ := zhConst * (2 + 34 * a0) + 8

theorem entropyConst_pos : 0 < entropyConst := by
  have h1 := zhConst_nonneg
  have h2 := a0_pos
  unfold entropyConst
  positivity

theorem entropy_core (h : ℝ) (hh : 2 ≤ h) {f f' : AngCircle → ℝ} (hw : IsAngularWeakDeriv f f')
    (hnorm : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1) {T : ℝ} (hT : 1 ≤ T)
    (hET : (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h +
      (∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar) ^ 2 ≤ T) :
    ∫⁻ θ, ENNReal.ofReal (qAng h θ * (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) ∂angHaar ≤
      ENNReal.ofReal (entropyConst * T) := by
  have hp : 0 < h := by linarith
  have ha0 := a0_pos
  have hc0 := zhConst_nonneg
  have hE0 : 0 ≤ ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar :=
    integral_nonneg fun θ => q_sq_nonneg h hp f' θ
  have hEdiv : 0 ≤ (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h := div_nonneg hE0 hp.le
  have hM2 : (∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar) ^ 2 ≤ T := by linarith
  have hEh : ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar ≤ h * T := by
    have h1 : (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h ≤ T := by
      nlinarith [sq_nonneg (∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar)]
    rw [div_le_iff₀ hp] at h1
    linarith
  have hPb : ∫ θ, qAng h θ * f θ ^ 2 * (h * Uang θ) ∂angHaar ≤ 2 * T := by
    have := feature_moment h hp hw.memLp hnorm
    linarith
  have hW := energy_bound h hh hw
  have hW' : ∫ θ, (f' θ * sAng h θ + f θ * angDeriv (sAng h) θ) ^ 2 ∂angHaar ≤ 34 * h * T := by
    have := mul_le_mul_of_nonneg_left hPb hp.le
    nlinarith
  have hwd := isAngularWeakDeriv_mul_smooth hw (isSmoothAngular_sAng h hp)
  have hwn : ∫ θ, (f θ * sAng h θ) ^ 2 ∂angHaar = 1 := by
    calc ∫ θ, (f θ * sAng h θ) ^ 2 ∂angHaar = ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar := by
          refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
          show (f θ * sAng h θ) ^ 2 = _
          rw [mul_pow, sAng_sq h hp]; ring
      _ = 1 := hnorm
  have hag := agmon_ang hwd hwn
  have hae : ∀ᵐ θ ∂angHaar, qAng h θ * f θ ^ 2 ≤ 1 + 2 * Real.sqrt (a0 * (34 * h * T)) := by
    filter_upwards [hag] with θ hθ
    have e : qAng h θ * f θ ^ 2 = (f θ * sAng h θ) ^ 2 := by
      rw [mul_pow, sAng_sq h hp]; ring
    rw [e]
    refine hθ.trans ?_
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hW' ha0.le)
    linarith
  have hent := entropy_lintegral_le h hh hw.memLp hnorm hae
  refine hent.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the scalar estimate
  set K : ℝ := 1 + 2 * Real.sqrt (a0 * (34 * h * T)) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hZpos := Zh_pos h hp
  have hsh : 1 ≤ √h := by
    rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hshpos : 0 < √h := by linarith
  have hy : 0 ≤ 34 * a0 * T := by positivity
  have hsq : Real.sqrt (a0 * (34 * h * T)) = Real.sqrt (34 * a0 * T) * √h := by
    rw [← Real.sqrt_mul hy]; congr 1; ring
  have hsy := Real.sq_sqrt hy
  have hKs : K * (√h)⁻¹ ≤ 2 + 34 * a0 * T := by
    have e : K * (√h)⁻¹ = (√h)⁻¹ + 2 * Real.sqrt (34 * a0 * T) := by
      rw [hKdef, hsq]; field_simp
    rw [e]
    have : (√h)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsh
    nlinarith [sq_nonneg (Real.sqrt (34 * a0 * T) - 1)]
  have hKZ : K * Zh h ≤ zhConst * (2 + 34 * a0) * T := by
    calc K * Zh h ≤ K * (zhConst * (√h)⁻¹) :=
          mul_le_mul_of_nonneg_left (Zh_le_const h hp) hKpos.le
      _ = zhConst * (K * (√h)⁻¹) := by ring
      _ ≤ zhConst * (2 + 34 * a0 * T) := mul_le_mul_of_nonneg_left hKs hc0
      _ ≤ zhConst * (2 + 34 * a0) * T := by
          have : 0 ≤ zhConst * (2 * (T - 1)) := by
            have : 0 ≤ T - 1 := by linarith
            positivity
          nlinarith
  have hlog : Real.log K + Real.log (Zh h) ≤ K * Zh h - 1 := by
    rw [← Real.log_mul hKpos.ne' hZpos.ne']
    exact Real.log_le_sub_one_of_pos (mul_pos hKpos hZpos)
  unfold entropyConst
  nlinarith

/-- The density measure `ρ = f² μ_h` on the torus. -/
noncomputable def densityRef (h : ℝ) (f : AngCircle → ℝ) : MeasureTheory.Measure (Torus 1) :=
  (engineeredReference h).withDensity fun x => ENNReal.ofReal (f (angEquiv x) ^ 2)

theorem entropy_regime_aux (h : ℝ) (hh : 2 ≤ h) {f f' : AngCircle → ℝ}
    (hw : IsAngularWeakDeriv f f')
    (hnorm : ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1) {T : ℝ} (hT : 1 ≤ T)
    (hET : (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
      (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 ≤ T) :
    relativeEntropy (densityRef h f) (engineeredReference h) ≤
      ENNReal.ofReal (entropyConst * T) := by
  have hp : 0 < h := by linarith
  have : IsProbabilityMeasure (engineeredReference h) :=
    DGPS.Examples.engineeredReference_isProbability h hp
  have hfm : AEMeasurable (fun θ => f θ ^ 2) angHaar :=
    (hw.memLp.aestronglyMeasurable.aemeasurable).pow_const 2
  have hvm : AEMeasurable (fun x => f (angEquiv x) ^ 2) (engineeredReference h) :=
    aemeasurable_ref h hfm
  have hnorm' : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1 :=
    (integral_ref_ent h hp (fun θ => f θ ^ 2)).symm.trans hnorm
  have hE : ∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h =
      ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar := integral_ref_ent h hp (fun θ => f' θ ^ 2)
  have hM : ∫ x, Eang h (angEquiv x) ∂densityRef h f =
      ∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar := by
    have hmo : AEMeasurable (fun x => ENNReal.ofReal (f (angEquiv x) ^ 2))
        (engineeredReference h) := ENNReal.measurable_ofReal.comp_aemeasurable hvm
    unfold densityRef
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmo
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have e : ∀ x, (ENNReal.ofReal (f (angEquiv x) ^ 2)).toReal • Eang h (angEquiv x) =
        (fun θ => f θ ^ 2 * Eang h θ) (angEquiv x) := fun x => by
      simp [ENNReal.toReal_ofReal (sq_nonneg _)]
    simp_rw [e]
    rw [integral_ref_ent h hp (fun θ => f θ ^ 2 * Eang h θ)]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only; ring
  rw [hE, hM] at hET
  have hcore := entropy_core h hh hw hnorm' hT hET
  have hre := relativeEntropy_withDensity (P := engineeredReference h)
    (v := fun x => f (angEquiv x) ^ 2) (Eventually.of_forall fun x => sq_nonneg _) hvm
  have hl := lintegral_ref h hp
    (fun θ => ENNReal.ofReal (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1))
  refine le_trans (le_of_eq ?_) hcore
  unfold densityRef
  rw [hre, entropy_mass_one hnorm]
  refine hl.trans (lintegral_congr fun θ => ?_)
  exact (ENNReal.ofReal_mul (qAng_pos h hp θ).le).symm

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Models DGPS.Circle.AngularNormalization

/-- EX041: engineered large-`T` entropy regime.  For `ρ = f² μ_h` with `f ≥ 0`, `μ_h(f²) = 1`
and angular weak derivative `f'`, put `E = μ_h((f')²)`, `M = ρ(E_h)` and `T = E/h + M²`.
There is `C > 0`, independent of `h ≥ 2` and `ρ`, with `H(ρ | μ_h) ≤ C T` whenever `T ≥ 1`. -/
theorem engineered_large_t_entropy_regime :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) →
      ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 →
      1 ≤ (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
        (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 →
      relativeEntropy (densityRef h f) (engineeredReference h) ≤
        ENNReal.ofReal (C * ((∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
          (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2)) :=
  ⟨entropyConst, entropyConst_pos, fun h hh _ _ hw _ hnorm hT =>
    entropy_regime_aux h hh hw hnorm hT le_rfl⟩

/-- Companion form with the physical gradient `2π f'`: the energy is `a₀ E` with `a₀ = 4π²`. -/
theorem engineered_large_t_entropy_regime_physical :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) →
      ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 →
      1 ≤ a0 * (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
        (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 →
      relativeEntropy (densityRef h f) (engineeredReference h) ≤
        ENNReal.ofReal (C * (a0 * (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
          (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2)) := by
  refine ⟨entropyConst, entropyConst_pos, fun h hh f f' hw _ hnorm hT => ?_⟩
  have hp : 0 < h := by linarith
  have ha : 1 ≤ a0 := by
    unfold a0; nlinarith [Real.pi_gt_three]
  have hE0 : 0 ≤ ∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h :=
    integral_nonneg fun x => sq_nonneg _
  refine entropy_regime_aux h hh hw hnorm hT ?_
  have : (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h ≤
      a0 * (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h :=
    div_le_div_of_nonneg_right (by nlinarith) hp.le
  linarith

end DGPS.Examples
