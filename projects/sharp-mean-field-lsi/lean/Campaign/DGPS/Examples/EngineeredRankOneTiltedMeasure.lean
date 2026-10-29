import DGPS.Examples.EngineeredRankOneEigen
import DGPS.Examples.EngineeredRankOneNormalization
import DGPS.Examples.EngineeredRankOneEX042

open MeasureTheory Real Set Filter Topology
open DGPS.Circle.AngularNormalization

/-!
# Engineered tilted-measure identity (EX043)

For `h ≥ 2` the probability measure `ν_h = c_h⁻¹ exp(hU) μ_h` (with `c_h = cH h`) satisfies
`ν_h(g²) = -2 ν_h(g) + (tanh h / c_h) M` for `g = f - 1`, where `M = ρ(E_h)` and `ρ = f² μ_h`,
and `ν_h(g²) ≤ C exp h h^{-1/2} √T` with `T = E/h + M²`.
Main output: `DGPS.Examples.engineered_tilted_measure_identity`.
-/

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models

/-- The tilted probability measure `ν_h = c_h⁻¹ exp(hU) μ_h` on the torus (EX043). -/
noncomputable def tiltedMeasure_ex043 (h : ℝ) : MeasureTheory.Measure (Torus 1) :=
  (engineeredReference h).withDensity fun x =>
    ENNReal.ofReal ((cH h)⁻¹ * exp (h * Uang (angEquiv x)))

theorem tanh_pos_ex043 {h : ℝ} (hp : 0 < h) : 0 < tanh h := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.2 hp) (Real.cosh_pos h)

theorem cH_pos_ex043 {h : ℝ} (hp : 0 < h) : 0 < cH h := by
  have := tanh_pos_ex043 hp
  unfold cH
  linarith

theorem one_le_cH_ex043 {h : ℝ} (hp : 0 < h) : 1 ≤ cH h := by
  have := tanh_pos_ex043 hp
  unfold cH
  linarith

theorem exp_le_ex043 {h : ℝ} (hp : 0 < h) (θ : AngCircle) :
    exp (h * Uang θ) ≤ exp (2 * h) := by
  apply Real.exp_le_exp.2
  have := (Uang_mem θ).2
  nlinarith

theorem abs_Eang_le_ex043 {h : ℝ} (hp : 0 < h) (θ : AngCircle) :
    |Eang h θ| ≤ (exp (2 * h) + cH h) / tanh h := by
  have ht0 := tanh_pos_ex043 hp
  have hc0 := cH_pos_ex043 hp
  have h1 := exp_le_ex043 hp θ
  have h2 := exp_pos (h * Uang θ)
  have h3 := exp_pos (2 * h)
  unfold Eang
  rw [abs_div, abs_of_pos ht0]
  refine div_le_div_of_nonneg_right ?_ ht0.le
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem exp_eq_ex043 {h : ℝ} (hp : 0 < h) (θ : AngCircle) :
    exp (h * Uang θ) = cH h + tanh h * Eang h θ := by
  have ht0 := tanh_pos_ex043 hp
  have hd : tanh h * ((exp (h * Uang θ) - cH h) / tanh h) = exp (h * Uang θ) - cH h := by
    field_simp
  unfold Eang
  rw [hd]
  ring

theorem continuous_expU_ex043 (h : ℝ) : Continuous (fun θ : AngCircle => exp (h * Uang θ)) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_Uang)

theorem continuous_qAng_ex043 {h : ℝ} (hp : 0 < h) : Continuous (qAng h) := by
  unfold qAng
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_logq h hp))

theorem integrable_mul_bdd_ex043 {F B : AngCircle → ℝ} (hF : Integrable F angHaar)
    (hB : AEStronglyMeasurable B angHaar) {K : ℝ} (hK : ∀ θ, |B θ| ≤ K) :
    Integrable (fun θ => F θ * B θ) angHaar :=
  hF.mul_bdd hB (Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact hK θ)

theorem integrable_qAng_ex043 {h : ℝ} (hp : 0 < h) : Integrable (qAng h) angHaar := by
  apply Integrable.of_integral_ne_zero
  rw [integral_qAng h hp]
  norm_num

theorem integrable_wf_ex043 {h : ℝ} (hp : 0 < h) {f : AngCircle → ℝ}
    (hfm : AEStronglyMeasurable f angHaar)
    (hwf2 : Integrable (fun θ => qAng h θ * f θ ^ 2) angHaar) :
    Integrable (fun θ => qAng h θ * f θ) angHaar := by
  have hbd : Integrable (fun θ => (qAng h θ + qAng h θ * f θ ^ 2) / 2) angHaar :=
    ((integrable_qAng_ex043 hp).add hwf2).div_const 2
  refine Integrable.mono' hbd ((continuous_qAng_ex043 hp).aestronglyMeasurable.mul hfm) ?_
  refine Eventually.of_forall fun θ => ?_
  have hq := qAng_pos h hp θ
  have h1 : qAng h θ * |f θ| ^ 2 = qAng h θ * f θ ^ 2 := by rw [sq_abs]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hq]
  nlinarith [mul_nonneg hq.le (sq_nonneg (|f θ| - 1))]

theorem integrable_setup_ex043 {h : ℝ} (hp : 0 < h) {f : AngCircle → ℝ}
    (hfm : AEStronglyMeasurable f angHaar) (hnorm : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1) :
    Integrable (qAng h) angHaar ∧ Integrable (fun θ => qAng h θ * f θ ^ 2) angHaar ∧
      Integrable (fun θ => qAng h θ * (f θ - 1)) angHaar ∧
      Integrable (fun θ => qAng h θ * (f θ - 1) ^ 2) angHaar := by
  have hw1 : Integrable (qAng h) angHaar := integrable_qAng_ex043 hp
  have hwf2 : Integrable (fun θ => qAng h θ * f θ ^ 2) angHaar := by
    apply Integrable.of_integral_ne_zero
    rw [hnorm]
    norm_num
  have hwf : Integrable (fun θ => qAng h θ * f θ) angHaar := integrable_wf_ex043 hp hfm hwf2
  have hwg : Integrable (fun θ => qAng h θ * (f θ - 1)) angHaar :=
    (hwf.sub hw1).congr (Eventually.of_forall fun θ => by simp only [Pi.sub_apply]; ring)
  have hwg2 : Integrable (fun θ => qAng h θ * (f θ - 1) ^ 2) angHaar :=
    ((hwf2.sub (hwf.const_mul 2)).add hw1).congr
      (Eventually.of_forall fun θ => by simp only [Pi.sub_apply, Pi.add_apply]; ring)
  exact ⟨hw1, hwf2, hwg, hwg2⟩

/-- Pushforward of the tilted measure to the angular circle. -/
theorem tilt_circle_ex043 {h : ℝ} (hp : 0 < h) (G : AngCircle → ℝ) :
    ∫ x, G (angEquiv x) ∂tiltedMeasure_ex043 h =
      ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * G θ) ∂angHaar := by
  have hc0 := cH_pos_ex043 hp
  have hnn : ∀ x : Torus 1, 0 ≤ (cH h)⁻¹ * exp (h * Uang (angEquiv x)) := fun x =>
    mul_nonneg (inv_nonneg.2 hc0.le) (exp_pos _).le
  have hc : Continuous (fun x : Torus 1 => (cH h)⁻¹ * exp (h * Uang (angEquiv x))) :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_Uang.comp continuous_angEquiv)))
  have hmo : AEMeasurable
      (fun x : Torus 1 => ENNReal.ofReal ((cH h)⁻¹ * exp (h * Uang (angEquiv x))))
      (engineeredReference h) :=
    (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
  have hsimp : ∀ x : Torus 1,
      (ENNReal.ofReal ((cH h)⁻¹ * exp (h * Uang (angEquiv x)))).toReal • G (angEquiv x) =
        (cH h)⁻¹ * exp (h * Uang (angEquiv x)) * G (angEquiv x) := fun x => by
    rw [ENNReal.toReal_ofReal (hnn x), smul_eq_mul]
  unfold tiltedMeasure_ex043
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmo
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_congr_ae (Eventually.of_forall hsimp)]
  exact integral_ref_ent h hp (fun θ => (cH h)⁻¹ * exp (h * Uang θ) * G θ)

/-- The tilted mass is one: `∫ qAng · c⁻¹ exp(hU) = c⁻¹ (c · 1 + tanh · 0) = 1`. -/
theorem tilt_mass_ex043 {h : ℝ} (hp : 0 < h) :
    ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ)) ∂angHaar = 1 := by
  have hc0 := cH_pos_ex043 hp
  have hcc : cH h * (cH h)⁻¹ = 1 := mul_inv_cancel₀ hc0.ne'
  have hw1 : Integrable (qAng h) angHaar := integrable_qAng_ex043 hp
  have hwE : Integrable (fun θ => qAng h θ * Eang h θ) angHaar :=
    integrable_mul_bdd_ex043 hw1 (continuous_Eang h).aestronglyMeasurable
      (fun θ => abs_Eang_le_ex043 hp θ)
  have hpt : ∀ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ)) =
      (cH h)⁻¹ * cH h * qAng h θ + (cH h)⁻¹ * tanh h * (qAng h θ * Eang h θ) := fun θ => by
    rw [exp_eq_ex043 hp θ]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (hw1.const_mul _) (hwE.const_mul _),
    integral_const_mul, integral_const_mul, integral_qAng h hp,
    integral_qAng_mul_Eang h hp]
  linear_combination hcc

/-- `ν_h` is a probability measure. -/
theorem tilt_prob_ex043 {h : ℝ} (hp : 0 < h) : IsProbabilityMeasure (tiltedMeasure_ex043 h) := by
  have hc0 := cH_pos_ex043 hp
  have hBnn : ∀ θ, 0 ≤ (cH h)⁻¹ * exp (h * Uang θ) := fun θ =>
    mul_nonneg (inv_nonneg.2 hc0.le) (exp_pos _).le
  have hBm : AEStronglyMeasurable (fun θ => (cH h)⁻¹ * exp (h * Uang θ)) angHaar :=
    ((continuous_expU_ex043 h).const_mul _).aestronglyMeasurable
  have hBb : ∀ θ, |(cH h)⁻¹ * exp (h * Uang θ)| ≤ (cH h)⁻¹ * exp (2 * h) := fun θ => by
    rw [abs_of_nonneg (hBnn θ)]
    exact mul_le_mul_of_nonneg_left (exp_le_ex043 hp θ) (inv_nonneg.2 hc0.le)
  have hint : Integrable (fun θ => qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ))) angHaar :=
    integrable_mul_bdd_ex043 (integrable_qAng_ex043 hp) hBm hBb
  refine ⟨?_⟩
  unfold tiltedMeasure_ex043
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have key : ∫⁻ x, ENNReal.ofReal ((cH h)⁻¹ * exp (h * Uang (angEquiv x)))
      ∂(engineeredReference h) =
      ∫⁻ θ, ENNReal.ofReal (qAng h θ) * ENNReal.ofReal ((cH h)⁻¹ * exp (h * Uang θ)) ∂angHaar :=
    lintegral_ref h hp (fun θ => ENNReal.ofReal ((cH h)⁻¹ * exp (h * Uang θ)))
  rw [key]
  have key2 : ∫⁻ θ, ENNReal.ofReal (qAng h θ) * ENNReal.ofReal ((cH h)⁻¹ * exp (h * Uang θ))
      ∂angHaar =
      ENNReal.ofReal (∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ)) ∂angHaar) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun θ => mul_nonneg (qAng_pos h hp θ).le (hBnn θ))]
    refine lintegral_congr fun θ => ?_
    rw [ENNReal.ofReal_mul (qAng_pos h hp θ).le]
  rw [key2, tilt_mass_ex043 hp, ENNReal.ofReal_one]

/-- Mean of `E_h` under `ρ = f² μ_h`, transported to the angular circle. -/
theorem M_conv_ex043 {h : ℝ} (hp : 0 < h) {f : AngCircle → ℝ}
    (hfm : AEStronglyMeasurable f angHaar) :
    ∫ x, Eang h (angEquiv x) ∂densityRef h f = ∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar := by
  have hfm2 : AEMeasurable (fun θ => f θ ^ 2) angHaar := hfm.aemeasurable.pow_const 2
  have hvm : AEMeasurable (fun x => f (angEquiv x) ^ 2) (engineeredReference h) :=
    aemeasurable_ref h hfm2
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
  simp only
  ring

/-- The circle-side tilted identity: `∫ w (c⁻¹ e g²) = -2 ∫ w (c⁻¹ e g) + (t/c) ∫ w f² E`. -/
theorem identity_circle_ex043 {h : ℝ} (hp : 0 < h) {f : AngCircle → ℝ}
    (hfm : AEStronglyMeasurable f angHaar) (hnorm : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1) :
    ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1) ^ 2) ∂angHaar =
      -2 * ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1)) ∂angHaar +
        tanh h / cH h * ∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar := by
  obtain ⟨hw1, hwf2, hwg, hwg2⟩ := integrable_setup_ex043 hp hfm hnorm
  have hc0 := cH_pos_ex043 hp
  have hcc : cH h * (cH h)⁻¹ = 1 := mul_inv_cancel₀ hc0.ne'
  have hwE : Integrable (fun θ => qAng h θ * Eang h θ) angHaar :=
    integrable_mul_bdd_ex043 hw1 (continuous_Eang h).aestronglyMeasurable
      (fun θ => abs_Eang_le_ex043 hp θ)
  have hwEf2 : Integrable (fun θ => qAng h θ * f θ ^ 2 * Eang h θ) angHaar :=
    integrable_mul_bdd_ex043 hwf2 (continuous_Eang h).aestronglyMeasurable
      (fun θ => abs_Eang_le_ex043 hp θ)
  have hBm : AEStronglyMeasurable (fun θ => (cH h)⁻¹ * exp (h * Uang θ)) angHaar :=
    ((continuous_expU_ex043 h).const_mul _).aestronglyMeasurable
  have hBb : ∀ θ, |(cH h)⁻¹ * exp (h * Uang θ)| ≤ (cH h)⁻¹ * exp (2 * h) := fun θ => by
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc0.le) (exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left (exp_le_ex043 hp θ) (inv_nonneg.2 hc0.le)
  have hΦ1 : Integrable
      (fun θ => qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1) ^ 2)) angHaar :=
    (integrable_mul_bdd_ex043 hwg2 hBm hBb).congr (Eventually.of_forall fun θ => by ring)
  have hΦ2 : Integrable
      (fun θ => qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1))) angHaar :=
    (integrable_mul_bdd_ex043 hwg hBm hBb).congr (Eventually.of_forall fun θ => by ring)
  have hpt : ∀ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1) ^ 2)
      + 2 * (qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1))) =
      (qAng h θ * f θ ^ 2 - qAng h θ) +
        (cH h)⁻¹ * tanh h * (qAng h θ * f θ ^ 2 * Eang h θ - qAng h θ * Eang h θ) := by
    intro θ
    rw [exp_eq_ex043 hp θ]
    linear_combination (qAng h θ * (f θ ^ 2 - 1)) * hcc
  have hr1 : Integrable (fun θ => qAng h θ * f θ ^ 2 - qAng h θ) angHaar := hwf2.sub hw1
  have hr2 : Integrable
      (fun θ => (cH h)⁻¹ * tanh h * (qAng h θ * f θ ^ 2 * Eang h θ - qAng h θ * Eang h θ))
      angHaar := (hwEf2.sub hwE).const_mul _
  have hfin : ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1) ^ 2) ∂angHaar
      + 2 * ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1)) ∂angHaar =
      (cH h)⁻¹ * tanh h * ∫ θ, qAng h θ * f θ ^ 2 * Eang h θ ∂angHaar := by
    rw [← integral_const_mul, ← integral_add hΦ1 (hΦ2.const_mul 2),
      integral_congr_ae (Eventually.of_forall hpt), integral_add hr1 hr2,
      integral_sub hwf2 hw1, integral_const_mul, integral_sub hwEf2 hwE, hnorm,
      integral_qAng h hp, integral_qAng_mul_Eang h hp]
    ring
  rw [div_eq_mul_inv]
  linear_combination hfin

/-- Discriminant-type bound: `|∫ w e g|² ≤ (∫ w e²)(∫ w g²)` (quadratic form nonnegative). -/
theorem abs_le_of_sq_ex043 {x Z : ℝ} (hZ : 0 ≤ Z) (hx : x ^ 2 ≤ Z ^ 2) : |x| ≤ Z := by
  nlinarith [sq_abs x, abs_nonneg x]

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Models DGPS.Circle.AngularNormalization

/-- EX043: engineered tilted-measure identity. For `h ≥ 2`, `f ≥ 0` with `μ_h(f²) = 1`, angular
weak derivative `f'`, and `T = E/h + M²` (with `E = μ_h((f')²)`, `M = ρ(E_h)`, `ρ = f² μ_h`), the
measure `ν_h = c_h⁻¹ exp(hU) μ_h` is a probability measure, `ν_h(g²) = -2 ν_h(g) + (tanh h / c_h) M`
for `g = f - 1`, and `ν_h(g²) ≤ C exp h h^{-1/2} √T` with `C` independent of `h`, `f`, `f'`. -/
theorem engineered_tilted_measure_identity :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) →
      ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 →
      ∀ T : ℝ,
      T = (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
        (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 →
      IsProbabilityMeasure (tiltedMeasure_ex043 h) ∧
      (∫ x, (f (angEquiv x) - 1) ^ 2 ∂tiltedMeasure_ex043 h =
        -2 * (∫ x, (f (angEquiv x) - 1) ∂tiltedMeasure_ex043 h) +
          tanh h / cH h * ∫ x, Eang h (angEquiv x) ∂densityRef h f) ∧
      (∫ x, (f (angEquiv x) - 1) ^ 2 ∂tiltedMeasure_ex043 h ≤
        C * exp h * h ^ (-(1 / 2 : ℝ)) * Real.sqrt T) := by
  obtain ⟨c0, C36, hc0, hC36, H36⟩ := engineered_normalization_and_rare_mass_bounds
  obtain ⟨C42, hC42, H42⟩ := engineered_small_t_l2_and_sup_controls
  obtain ⟨Kx, hKx⟩ : ∃ v : ℝ, v = Real.sqrt (C36 * max C42 4) := ⟨_, rfl⟩
  have hmaxpos : (0:ℝ) < max C42 4 := lt_max_of_lt_right (by norm_num)
  have hC36K : 0 ≤ C36 * max C42 4 := (mul_pos hC36 hmaxpos).le
  have hKx0 : 0 ≤ Kx := by rw [hKx]; exact Real.sqrt_nonneg _
  have hKx2 : Kx ^ 2 = C36 * max C42 4 := by rw [hKx, Real.sq_sqrt hC36K]
  refine ⟨2 * Kx + 1, by linarith, ?_⟩
  intro h hh f f' hw hf0 hnorm T hT
  have hp : 0 < h := by linarith
  have hfm : AEStronglyMeasurable f angHaar := hw.memLp.aestronglyMeasurable
  have hnorm' : ∫ θ, qAng h θ * f θ ^ 2 ∂angHaar = 1 :=
    (integral_ref_ent h hp (fun θ => f θ ^ 2)).symm.trans hnorm
  obtain ⟨hw1, hwf2, hwg, hwg2⟩ := integrable_setup_ex043 hp hfm hnorm'
  have hM := M_conv_ex043 hp hfm
  have hprob := tilt_prob_ex043 hp
  have hA : ∫ x, (f (angEquiv x) - 1) ^ 2 ∂tiltedMeasure_ex043 h =
      ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1) ^ 2) ∂angHaar :=
    tilt_circle_ex043 hp (fun θ => (f θ - 1) ^ 2)
  have hB : ∫ x, (f (angEquiv x) - 1) ∂tiltedMeasure_ex043 h =
      ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1)) ∂angHaar :=
    tilt_circle_ex043 hp (fun θ => f θ - 1)
  have hid := identity_circle_ex043 hp hfm hnorm'
  rw [← hM] at hid
  -- moment and energy bounds
  have hT0a : 0 ≤ (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h :=
    div_nonneg (integral_nonneg fun x => sq_nonneg _) hp.le
  have hM2 : (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 ≤ T := by linarith
  have hT0 : 0 ≤ T := le_trans (sq_nonneg _) hM2
  have hMabs : |∫ x, Eang h (angEquiv x) ∂densityRef h f| ≤ Real.sqrt T :=
    abs_le_of_sq_ex043 (Real.sqrt_nonneg T) (by rw [Real.sq_sqrt hT0]; exact hM2)
  -- the L² bound N ≤ max C42 4 * T
  have hN : ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar ≤ max C42 4 * T := by
    rcases le_total T 1 with hT1 | hT1
    · have h42 := (H42 h hh f f' hw hf0 hnorm T _ hT hT1 rfl).2.2.1
      have e1 : ∫ x, (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h =
          ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar :=
        integral_ref_ent h hp (fun θ => (f θ - 1) ^ 2)
      rw [e1] at h42
      have := mul_le_mul_of_nonneg_right (le_max_left C42 4) hT0
      linarith
    · have hle : ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar ≤
          ∫ θ, (2 * (qAng h θ * f θ ^ 2) + 2 * qAng h θ) ∂angHaar :=
        integral_mono hwg2 ((hwf2.const_mul 2).add (hw1.const_mul 2)) fun θ => by
          show qAng h θ * (f θ - 1) ^ 2 ≤ 2 * (qAng h θ * f θ ^ 2) + 2 * qAng h θ
          nlinarith [mul_nonneg (qAng_pos h hp θ).le (sq_nonneg (f θ + 1))]
      have e2 : ∫ θ, (2 * (qAng h θ * f θ ^ 2) + 2 * qAng h θ) ∂angHaar = 4 := by
        rw [integral_add (hwf2.const_mul 2) (hw1.const_mul 2), integral_const_mul,
          integral_const_mul, hnorm', integral_qAng h hp]
        norm_num
      have hmax1 := mul_le_mul_of_nonneg_left hT1 (le_trans (by norm_num) (le_max_right C42 4))
      have hK4 := le_max_right C42 4
      linarith
  -- the discriminant of the quadratic form in s
  obtain ⟨aI, haI⟩ : ∃ v : ℝ, v = ∫ θ, qAng h θ * exp (h * Uang θ) ^ 2 ∂angHaar := ⟨_, rfl⟩
  obtain ⟨xI, hxI⟩ : ∃ v : ℝ,
      v = ∫ θ, qAng h θ * (exp (h * Uang θ) * (f θ - 1)) ∂angHaar := ⟨_, rfl⟩
  obtain ⟨NI, hNI⟩ : ∃ v : ℝ, v = ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar := ⟨_, rfl⟩
  have hE2m : AEStronglyMeasurable (fun θ => exp (h * Uang θ) ^ 2) angHaar :=
    ((continuous_expU_ex043 h).pow 2).aestronglyMeasurable
  have hE2b : ∀ θ, |exp (h * Uang θ) ^ 2| ≤ exp (2 * h) ^ 2 := fun θ => by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [exp_le_ex043 hp θ, exp_pos (h * Uang θ)]
  have hw2e : Integrable (fun θ => qAng h θ * exp (h * Uang θ) ^ 2) angHaar :=
    integrable_mul_bdd_ex043 hw1 hE2m hE2b
  have hEm : AEStronglyMeasurable (fun θ => exp (h * Uang θ)) angHaar :=
    (continuous_expU_ex043 h).aestronglyMeasurable
  have hEb : ∀ θ, |exp (h * Uang θ)| ≤ exp (2 * h) := fun θ => by
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_ex043 hp θ
  have hwe_g : Integrable (fun θ => qAng h θ * (exp (h * Uang θ) * (f θ - 1))) angHaar :=
    (integrable_mul_bdd_ex043 hwg hEm hEb).congr (Eventually.of_forall fun θ => by ring)
  have hq : ∀ s : ℝ, 0 ≤ aI * (s * s) + (-2 * xI) * s + NI := by
    intro s
    have hnn : 0 ≤ ∫ θ, qAng h θ * (exp (h * Uang θ) * s - (f θ - 1)) ^ 2 ∂angHaar :=
      integral_nonneg fun θ => mul_nonneg (qAng_pos h hp θ).le (sq_nonneg _)
    have heq : ∫ θ, qAng h θ * (exp (h * Uang θ) * s - (f θ - 1)) ^ 2 ∂angHaar =
        aI * (s * s) + (-2 * xI) * s + NI := by
      have hA1 : Integrable (fun θ => (s * s) * (qAng h θ * exp (h * Uang θ) ^ 2)) angHaar :=
        hw2e.const_mul _
      have hA2 : Integrable
          (fun θ => (-2 * s) * (qAng h θ * (exp (h * Uang θ) * (f θ - 1)))) angHaar :=
        hwe_g.const_mul _
      have hpt2 : ∀ θ, qAng h θ * (exp (h * Uang θ) * s - (f θ - 1)) ^ 2 =
          (s * s) * (qAng h θ * exp (h * Uang θ) ^ 2)
            + (-2 * s) * (qAng h θ * (exp (h * Uang θ) * (f θ - 1)))
            + qAng h θ * (f θ - 1) ^ 2 := fun θ => by ring
      have i1 := integral_add (μ := angHaar) (hA1.add hA2) hwg2
      have i2 := integral_add (μ := angHaar) hA1 hA2
      simp only [Pi.add_apply] at i1 i2
      rw [integral_congr_ae (Eventually.of_forall hpt2), i1, i2, integral_const_mul,
        integral_const_mul, ← haI, ← hxI, ← hNI]
      ring
    linarith
  have hdisc := discrim_le_zero hq
  unfold discrim at hdisc
  have hx2 : xI ^ 2 ≤ aI * NI := by nlinarith [hdisc]
  have hN0 : 0 ≤ NI := by
    rw [hNI]
    exact integral_nonneg fun θ => mul_nonneg (qAng_pos h hp θ).le (sq_nonneg _)
  have hNIT : NI ≤ max C42 4 * T := by rw [hNI]; exact hN
  -- the L² bound on the exponential weight (EX036)
  have hpt3 : ∀ θ, qAng h θ * exp (h * Uang θ) ^ 2 = exp (2 * h * Uang θ) * qAng h θ := by
    intro θ
    rw [sq, ← Real.exp_add, show h * Uang θ + h * Uang θ = 2 * h * Uang θ by ring]
    ring
  have haI_le : aI ≤ C36 * exp (2 * h) / h := by
    rw [haI]
    rw [integral_congr_ae (Eventually.of_forall hpt3)]
    exact (H36 h hh).2.2
  -- the constant P = exp h * h^{-1/2}
  obtain ⟨P, hPdef⟩ : ∃ v : ℝ, v = exp h * h ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hr : (h ^ (-(1 / 2 : ℝ))) ^ 2 = h⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le,
      show -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have he2 : exp h ^ 2 = exp (2 * h) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hP2 : P ^ 2 = exp (2 * h) / h := by
    rw [hPdef, mul_pow, he2, hr, div_eq_mul_inv]
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (exp_pos _).le (Real.rpow_nonneg hp.le _)
  have hP1 : 1 ≤ P := by
    have hq1 : 1 ≤ P ^ 2 := by
      rw [hP2]
      exact (one_le_div hp).2 (by linarith [Real.add_one_le_exp (2 * h)])
    nlinarith
  have haI' : aI ≤ C36 * P ^ 2 := by
    rw [hP2, ← mul_div_assoc]
    exact haI_le
  have ha0 : 0 ≤ aI := by
    rw [haI]
    exact integral_nonneg fun θ => mul_nonneg (qAng_pos h hp θ).le (sq_nonneg _)
  -- |∫ w e g| ≤ P Kx √T
  have hsq_le : xI ^ 2 ≤ (P * Kx * Real.sqrt T) ^ 2 := by
    calc xI ^ 2 ≤ aI * NI := hx2
      _ ≤ (C36 * P ^ 2) * (max C42 4 * T) :=
          mul_le_mul haI' hNIT hN0 (mul_nonneg hC36.le (sq_nonneg _))
      _ = (P * Kx * Real.sqrt T) ^ 2 := by
          rw [mul_pow, mul_pow, hKx2, Real.sq_sqrt hT0]; ring
  have hx_le : |xI| ≤ P * Kx * Real.sqrt T :=
    abs_le_of_sq_ex043 (mul_nonneg (mul_nonneg hPnn hKx0) (Real.sqrt_nonneg T)) hsq_le
  -- the circle-side tilted identity in the form needed
  have hu0 : 0 < (cH h)⁻¹ := inv_pos.2 (cH_pos_ex043 hp)
  have hc1 := one_le_cH_ex043 hp
  have hcc : cH h * (cH h)⁻¹ = 1 := mul_inv_cancel₀ (cH_pos_ex043 hp).ne'
  have hu1 : (cH h)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
  have htu0 : 0 ≤ tanh h * (cH h)⁻¹ := mul_nonneg (tanh_pos_ex043 hp).le hu0.le
  have htu1 : tanh h * (cH h)⁻¹ ≤ 1 := by
    have hcm : tanh h ≤ cH h := by
      unfold cH
      linarith
    calc tanh h * (cH h)⁻¹ ≤ cH h * (cH h)⁻¹ := mul_le_mul_of_nonneg_right hcm hu0.le
      _ = 1 := hcc
  have hdiv : tanh h / cH h = tanh h * (cH h)⁻¹ := div_eq_mul_inv _ _
  have hq2pt : ∀ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1))
      = (cH h)⁻¹ * (qAng h θ * (exp (h * Uang θ) * (f θ - 1))) := fun θ => by ring
  have hQ2 : ∫ θ, qAng h θ * ((cH h)⁻¹ * exp (h * Uang θ) * (f θ - 1)) ∂angHaar
      = (cH h)⁻¹ * xI := by
    rw [hxI, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hq2pt)
  have hxu : -|xI| ≤ (cH h)⁻¹ * xI := by
    have h1 : (cH h)⁻¹ * (-|xI|) ≤ (cH h)⁻¹ * xI :=
      mul_le_mul_of_nonneg_left (neg_abs_le xI) hu0.le
    have h2 : -|xI| ≤ (cH h)⁻¹ * (-|xI|) := by
      have h3 := mul_le_mul_of_nonneg_right hu1 (abs_nonneg xI)
      rw [one_mul] at h3
      linarith
    exact h2.trans h1
  have hMu : tanh h * (cH h)⁻¹ * ∫ x, Eang h (angEquiv x) ∂densityRef h f ≤
      |∫ x, Eang h (angEquiv x) ∂densityRef h f| := by
    have := le_abs_self (tanh h * (cH h)⁻¹ * ∫ x, Eang h (angEquiv x) ∂densityRef h f)
    rw [abs_mul, abs_of_nonneg htu0] at this
    have h2 := mul_le_mul_of_nonneg_right htu1 (abs_nonneg (∫ x, Eang h (angEquiv x) ∂densityRef h f))
    rw [one_mul] at h2
    linarith
  have hPs : Real.sqrt T ≤ P * Real.sqrt T := le_mul_of_one_le_left (Real.sqrt_nonneg T) hP1
  have hR : (2 * Kx + 1) * exp h * h ^ (-(1 / 2 : ℝ)) * Real.sqrt T
      = (2 * Kx + 1) * P * Real.sqrt T := by
    rw [hPdef]
    ring
  have hfin1 : -2 * ((cH h)⁻¹ * xI) ≤ 2 * (P * Kx * Real.sqrt T) := by
    linarith [hxu, hx_le]
  have hfin2 : tanh h * (cH h)⁻¹ * (∫ x, Eang h (angEquiv x) ∂densityRef h f) ≤ P * Real.sqrt T := by
    linarith [hMu, hMabs, hPs]
  rw [hA, hid, hdiv, hB, hQ2, hR]
  exact ⟨hprob, rfl, by linarith [hfin1, hfin2]⟩

end DGPS.Examples
