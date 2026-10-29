import DGPS.Examples.EngineeredRankOneEntropy
import DGPS.Analysis.OneDimensionalHardy
import DGPS.Foundations.PeriodicSmoothing
import DGPS.Circle.StationaryFlux

/-!
# EX039: Hardy Poincare bound for the engineered rank-one reference

For the engineered angular density `q_h = qAng h` (`μ_h = q_h dθ/(2π)` on the circle) we prove:

* the tail-times-resistance bound
  `[∫_x^π q_h] [∫_0^x q_h⁻¹] ≤ 2 min(x, π-x)/(h sin x) ≤ π/h` for `0 < x < π` (and its mirror on
  the other half-circle), using that `q_h = Z⁻¹ exp(-Φ)` with `Φ(t) = h (1 - cos t) + R_h(1 - cos t)`
  satisfying `Φ(t) - Φ(x) ≥ h (cos x - cos t)` on `[0, π]` (monotone correction `R_h`);
* the FIN006 one-sided resistance constants of `q_h/(2π)` on `(-π, π)` anchored at `0` are at most
  `π/h`, hence the anchored Hardy constant is at most `4π/h`;
* the anchored weighted Hardy inequality for smooth angular functions and its extension to the
  weak angular form domain by smooth approximation in `H¹` (an `ε`-argument absorbing the
  `L²(μ_h)`-errors), giving `Var_{μ_h}(f) ≤ (4π/h) ∫ (f')² dμ_h`;
* `λ_P^angular(μ_h) ≥ c h` with `c = 1/(4π)` independent of `h ≥ 2`.

All helper declarations carry the suffix `_hardy`; they live in `DGPS.Examples.EngineeredHardy`.
The packaged result is `DGPS.Examples.engineered_hardy_poincare_bound`.
-/

open MeasureTheory Real Set Filter Topology
open DGPS DGPS.Circle.AngularNormalization DGPS.FiniteN
open scoped ENNReal

namespace DGPS.Examples.EngineeredHardy

lemma hasDerivAt_expcos_hardy (h s : ℝ) :
    HasDerivAt (fun s => Real.exp (h * Real.cos s))
      (Real.exp (h * Real.cos s) * (h * -Real.sin s)) s :=
  ((Real.hasDerivAt_cos s).const_mul h).exp

lemma continuous_expcos_hardy (h : ℝ) : Continuous (fun s => Real.exp (h * Real.cos s)) := by
  fun_prop

/-- Tail on `[π/2, π]`. -/
lemma tail_half_le_hardy {h : ℝ} (hh : 0 < h) :
    ∫ s in (π / 2)..π, Real.exp (h * Real.cos s) ≤ 2 / h := by
  have hπ := Real.pi_pos
  set a : ℝ := 2 * h / π with ha
  have ha0 : 0 < a := by positivity
  have h1 : ∫ s in (π / 2)..π, Real.exp (h * Real.cos s)
      = ∫ v in (0:ℝ)..(π / 2), Real.exp (h * Real.cos (π / 2 + v)) := by
    rw [intervalIntegral.integral_comp_add_left (fun s => Real.exp (h * Real.cos s)) (π / 2)]
    congr 1 <;> ring
  have h2 : ∫ v in (0:ℝ)..(π / 2), Real.exp (h * Real.cos (π / 2 + v))
      ≤ ∫ v in (0:ℝ)..(π / 2), Real.exp (-a * v) := by
    apply intervalIntegral.integral_mono_on (by positivity)
    · exact (by fun_prop : Continuous fun v : ℝ => Real.exp (h * Real.cos (π / 2 + v))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun v : ℝ => Real.exp (-a * v)).intervalIntegrable _ _
    · intro v hv
      apply Real.exp_le_exp.mpr
      have := Real.mul_le_sin hv.1 (by linarith [hv.2] : v ≤ π / 2)
      rw [add_comm, Real.cos_add_pi_div_two]
      have : -a * v = -(h * (2 / π * v)) := by rw [ha]; field_simp
      rw [this]
      nlinarith
  have h3 : ∫ v in (0:ℝ)..(π / 2), Real.exp (-a * v) ≤ 1 / a := by
    have hd : ∀ v ∈ Set.uIcc (0:ℝ) (π / 2),
        HasDerivAt (fun v => -(Real.exp (-a * v) / a)) (Real.exp (-a * v)) v := by
      intro v _
      have h1 := ((hasDerivAt_id v).const_mul (-a)).exp
      have h2 := (h1.div_const a).neg
      refine h2.congr_deriv ?_
      simp only [id]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun v : ℝ => Real.exp (-a * v)).intervalIntegrable _ _)]
    have : 0 ≤ Real.exp (-a * (π / 2)) / a := by positivity
    simp only [mul_zero, Real.exp_zero]
    rw [one_div]
    have : (1:ℝ) / a = a⁻¹ := one_div a
    nlinarith [this]
  have h4 : 1 / a = π / (2 * h) := by rw [ha]; field_simp
  have h5 : π / (2 * h) ≤ 2 / h := by
    rw [div_le_div_iff₀ (by positivity) hh]
    nlinarith [Real.pi_lt_four]
  linarith


/-- The key tail bound. -/
lemma tail_exp_cos_le_hardy {h y : ℝ} (hh : 0 < h) (hy0 : 0 < y) (hy : y ≤ π / 2) :
    ∫ s in y..π, Real.exp (h * Real.cos s) ≤
      2 * Real.exp (h * Real.cos y) / (h * Real.sin y) := by
  have hπ := Real.pi_pos
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy0 (by linarith)
  have hsplit : ∫ s in y..π, Real.exp (h * Real.cos s) =
      (∫ s in y..(π / 2), Real.exp (h * Real.cos s)) + ∫ s in (π / 2)..π, Real.exp (h * Real.cos s) :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((continuous_expcos_hardy h).intervalIntegrable _ _)
      ((continuous_expcos_hardy h).intervalIntegrable _ _)).symm
  have hB := tail_half_le_hardy hh
  -- FTC for E * sin
  have hd : ∀ s ∈ Set.uIcc y (π / 2),
      HasDerivAt (fun s => -(Real.exp (h * Real.cos s) / h))
        (Real.exp (h * Real.cos s) * Real.sin s) s := by
    intro s _
    have := ((hasDerivAt_expcos_hardy h s).div_const h).neg
    refine this.congr_deriv ?_
    field_simp
  have hF : ∫ s in y..(π / 2), Real.exp (h * Real.cos s) * Real.sin s =
      (Real.exp (h * Real.cos y) - 1) / h := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (((continuous_expcos_hardy h).mul Real.continuous_sin).intervalIntegrable _ _)]
    simp only [Real.cos_pi_div_two, mul_zero, Real.exp_zero]
    ring
  have hmono : ∫ s in y..(π / 2), Real.exp (h * Real.cos s) * Real.sin y ≤
      ∫ s in y..(π / 2), Real.exp (h * Real.cos s) * Real.sin s := by
    apply intervalIntegral.integral_mono_on hy
    · exact ((continuous_expcos_hardy h).mul continuous_const).intervalIntegrable _ _
    · exact ((continuous_expcos_hardy h).mul Real.continuous_sin).intervalIntegrable _ _
    · intro s hs'
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hs'.1]) (by linarith [hs'.2]) hs'.1
  rw [intervalIntegral.integral_mul_const, hF] at hmono
  have hA : ∫ s in y..(π / 2), Real.exp (h * Real.cos s) ≤
      (Real.exp (h * Real.cos y) - 1) / (h * Real.sin y) := by
    rw [le_div_iff₀ (by positivity)]
    have : (Real.exp (h * Real.cos y) - 1) / h * 1 = (Real.exp (h * Real.cos y) - 1) / h := by ring
    calc (∫ s in y..(π / 2), Real.exp (h * Real.cos s)) * (h * Real.sin y)
        = ((∫ s in y..(π / 2), Real.exp (h * Real.cos s)) * Real.sin y) * h := by ring
      _ ≤ (Real.exp (h * Real.cos y) - 1) / h * h := by gcongr
      _ = Real.exp (h * Real.cos y) - 1 := by field_simp
  have hE1 : 1 ≤ Real.exp (h * Real.cos y) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hy⟩
    positivity
  have hsin1 : Real.sin y ≤ 1 := Real.sin_le_one y
  have key : (Real.exp (h * Real.cos y) - 1) / (h * Real.sin y) + 2 / h
      = (Real.exp (h * Real.cos y) - 1 + 2 * Real.sin y) / (h * Real.sin y) := by
    field_simp
  have hfin : (Real.exp (h * Real.cos y) - 1 + 2 * Real.sin y) / (h * Real.sin y) ≤
      2 * Real.exp (h * Real.cos y) / (h * Real.sin y) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  linarith


/-- Abstract product bound, scale free. -/
lemma product_bound_hardy {h : ℝ} (hh : 0 < h) {Φ : ℝ → ℝ} (hΦc : Continuous Φ)
    (hΦ : ∀ x t, 0 ≤ x → x ≤ t → t ≤ π → h * (Real.cos x - Real.cos t) ≤ Φ t - Φ x)
    {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) :
    (∫ t in x..π, Real.exp (-Φ t)) * (∫ t in (0:ℝ)..x, Real.exp (Φ t)) ≤
      2 * min x (π - x) / (h * Real.sin x) := by
  have hπ := Real.pi_pos
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
  have hc1 : Continuous fun t => Real.exp (-Φ t) := by fun_prop
  have hc2 : Continuous fun t => Real.exp (Φ t) := by fun_prop
  have hI1 : 0 ≤ ∫ t in x..π, Real.exp (-Φ t) :=
    intervalIntegral.integral_nonneg hxπ.le (fun t _ => (Real.exp_pos _).le)
  have hI2 : 0 ≤ ∫ t in (0:ℝ)..x, Real.exp (Φ t) :=
    intervalIntegral.integral_nonneg hx0.le (fun t _ => (Real.exp_pos _).le)
  have hmono : ∀ t, 0 ≤ t → t ≤ π → ∀ u, t ≤ u → u ≤ π → Φ t ≤ Φ u := by
    intro t ht0 htπ u htu huπ
    have h1 : Real.cos u ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht0 huπ htu
    have := hΦ t u ht0 htu huπ
    nlinarith
  rcases le_or_gt x (π / 2) with hx | hx
  · -- case x ≤ π/2
    have hmin : min x (π - x) = x := min_eq_left (by linarith)
    rw [hmin]
    have hI2le : ∫ t in (0:ℝ)..x, Real.exp (Φ t) ≤ x * Real.exp (Φ x) := by
      calc ∫ t in (0:ℝ)..x, Real.exp (Φ t) ≤ ∫ t in (0:ℝ)..x, Real.exp (Φ x) := by
            apply intervalIntegral.integral_mono_on hx0.le
            · exact hc2.intervalIntegrable _ _
            · exact intervalIntegrable_const
            · intro t ht
              exact Real.exp_le_exp.mpr (hmono t ht.1 (by linarith [ht.2]) x ht.2 hxπ.le)
        _ = x * Real.exp (Φ x) := by simp
    have hI1le : ∫ t in x..π, Real.exp (-Φ t) ≤
        2 * Real.exp (-Φ x) / (h * Real.sin x) := by
      have hpt : ∫ t in x..π, Real.exp (-Φ t) ≤
          ∫ t in x..π, Real.exp (-Φ x - h * Real.cos x) * Real.exp (h * Real.cos t) := by
        apply intervalIntegral.integral_mono_on hxπ.le
        · exact hc1.intervalIntegrable _ _
        · exact (continuous_const.mul (continuous_expcos_hardy h)).intervalIntegrable _ _
        · intro t ht
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have := hΦ x t hx0.le ht.1 ht.2
          nlinarith
      rw [intervalIntegral.integral_const_mul] at hpt
      have hT := tail_exp_cos_le_hardy hh hx0 hx
      have hcpos : 0 < Real.exp (-Φ x - h * Real.cos x) := Real.exp_pos _
      calc ∫ t in x..π, Real.exp (-Φ t)
          ≤ Real.exp (-Φ x - h * Real.cos x) * ∫ t in x..π, Real.exp (h * Real.cos t) := hpt
        _ ≤ Real.exp (-Φ x - h * Real.cos x) *
              (2 * Real.exp (h * Real.cos x) / (h * Real.sin x)) :=
            mul_le_mul_of_nonneg_left hT hcpos.le
        _ = 2 * Real.exp (-Φ x) / (h * Real.sin x) := by
            have : Real.exp (-Φ x) = Real.exp (-Φ x - h * Real.cos x) * Real.exp (h * Real.cos x) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [this]; ring
    calc (∫ t in x..π, Real.exp (-Φ t)) * (∫ t in (0:ℝ)..x, Real.exp (Φ t))
        ≤ (2 * Real.exp (-Φ x) / (h * Real.sin x)) * (x * Real.exp (Φ x)) :=
          mul_le_mul hI1le hI2le hI2 (by positivity)
      _ = 2 * x / (h * Real.sin x) := by
          have : Real.exp (-Φ x) * Real.exp (Φ x) = 1 := by
            rw [← Real.exp_add]; simp
          calc (2 * Real.exp (-Φ x) / (h * Real.sin x)) * (x * Real.exp (Φ x))
              = 2 * x / (h * Real.sin x) * (Real.exp (-Φ x) * Real.exp (Φ x)) := by ring
            _ = 2 * x / (h * Real.sin x) := by rw [this, mul_one]
  · -- case x > π/2
    have hmin : min x (π - x) = π - x := min_eq_right (by linarith)
    rw [hmin]
    have hy0 : 0 < π - x := by linarith
    have hI1le : ∫ t in x..π, Real.exp (-Φ t) ≤ (π - x) * Real.exp (-Φ x) := by
      calc ∫ t in x..π, Real.exp (-Φ t) ≤ ∫ t in x..π, Real.exp (-Φ x) := by
            apply intervalIntegral.integral_mono_on hxπ.le
            · exact hc1.intervalIntegrable _ _
            · exact intervalIntegrable_const
            · intro t ht
              exact Real.exp_le_exp.mpr (by linarith [hmono x hx0.le hxπ.le t ht.1 ht.2])
        _ = (π - x) * Real.exp (-Φ x) := by simp
    have hI2le : ∫ t in (0:ℝ)..x, Real.exp (Φ t) ≤
        2 * Real.exp (Φ x) / (h * Real.sin x) := by
      have hpt : ∫ t in (0:ℝ)..x, Real.exp (Φ t) ≤
          ∫ t in (0:ℝ)..x, Real.exp (Φ x + h * Real.cos x) * Real.exp (h * Real.cos (π - t)) := by
        apply intervalIntegral.integral_mono_on hx0.le
        · exact hc2.intervalIntegrable _ _
        · exact (continuous_const.mul (by fun_prop : Continuous fun t : ℝ => Real.exp (h * Real.cos (π - t)))).intervalIntegrable _ _
        · intro t ht
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have := hΦ t x ht.1 ht.2 hxπ.le
          rw [Real.cos_pi_sub]
          nlinarith
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun s => Real.exp (h * Real.cos s)) π] at hpt
      have hT := tail_exp_cos_le_hardy hh hy0 (by linarith : π - x ≤ π / 2)
      have hsin : Real.sin (π - x) = Real.sin x := Real.sin_pi_sub x
      have hcos : Real.cos (π - x) = - Real.cos x := Real.cos_pi_sub x
      rw [hsin, hcos] at hT
      have hcpos : 0 < Real.exp (Φ x + h * Real.cos x) := Real.exp_pos _
      have hsub : π - x = π - x := rfl
      have hlim : ∫ s in (π - x)..(π - 0), Real.exp (h * Real.cos s) =
          ∫ s in (π - x)..π, Real.exp (h * Real.cos s) := by simp
      rw [hlim] at hpt
      calc ∫ t in (0:ℝ)..x, Real.exp (Φ t)
          ≤ Real.exp (Φ x + h * Real.cos x) * ∫ s in (π - x)..π, Real.exp (h * Real.cos s) := hpt
        _ ≤ Real.exp (Φ x + h * Real.cos x) *
              (2 * Real.exp (h * -Real.cos x) / (h * Real.sin x)) :=
            mul_le_mul_of_nonneg_left hT hcpos.le
        _ = 2 * Real.exp (Φ x) / (h * Real.sin x) := by
            have : Real.exp (Φ x) = Real.exp (Φ x + h * Real.cos x) * Real.exp (h * -Real.cos x) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [this]; ring
    calc (∫ t in x..π, Real.exp (-Φ t)) * (∫ t in (0:ℝ)..x, Real.exp (Φ t))
        ≤ ((π - x) * Real.exp (-Φ x)) * (2 * Real.exp (Φ x) / (h * Real.sin x)) :=
          mul_le_mul hI1le hI2le hI2 (by positivity)
      _ = 2 * (π - x) / (h * Real.sin x) := by
          have : Real.exp (-Φ x) * Real.exp (Φ x) = 1 := by
            rw [← Real.exp_add]; simp
          calc ((π - x) * Real.exp (-Φ x)) * (2 * Real.exp (Φ x) / (h * Real.sin x))
              = 2 * (π - x) / (h * Real.sin x) * (Real.exp (-Φ x) * Real.exp (Φ x)) := by ring
            _ = 2 * (π - x) / (h * Real.sin x) := by rw [this, mul_one]

/-- `2 min(x, π - x) / (h sin x) ≤ π / h`. -/
lemma min_div_sin_le_hardy {h x : ℝ} (hh : 0 < h) (hx0 : 0 < x) (hxπ : x < π) :
    2 * min x (π - x) / (h * Real.sin x) ≤ π / h := by
  have hπ := Real.pi_pos
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
  rw [div_le_div_iff₀ (by positivity) hh]
  have key : 2 * min x (π - x) ≤ π * Real.sin x := by
    rcases le_or_gt x (π / 2) with hx | hx
    · rw [min_eq_left (by linarith)]
      have := Real.mul_le_sin hx0.le hx
      have h2 : 2 / π * x * π = 2 * x := by field_simp
      nlinarith
    · rw [min_eq_right (by linarith)]
      have := Real.mul_le_sin (by linarith : 0 ≤ π - x) (by linarith : π - x ≤ π / 2)
      rw [Real.sin_pi_sub] at this
      have h2 : 2 / π * (π - x) * π = 2 * (π - x) := by field_simp
      nlinarith
  nlinarith


/-- The density on `(-π, π)` of an angular density `q` with respect to Lebesgue measure. -/
noncomputable def pOf (q : AngCircle → ℝ) : ℝ → ℝ := fun t => q (t : AngCircle) / (2 * π)

/-- The measure `q(t)/(2π) dt` on `(-π, π)`. -/
noncomputable abbrev muOf (q : AngCircle → ℝ) : Measure ℝ := DGPS.FiniteN.densityMeasure (Ioo (-π) π) (pOf q)

lemma continuous_pOf_hardy {q : AngCircle → ℝ} (hc : Continuous q) : Continuous (pOf q) := by
  unfold pOf
  exact (hc.comp Real.Angle.continuous_coe).div_const _

lemma pOf_nonneg_hardy {q : AngCircle → ℝ} (h0 : ∀ θ, 0 < q θ) (t : ℝ) : 0 ≤ pOf q t := by
  unfold pOf
  have := h0 (t : AngCircle)
  positivity

lemma integral_muOf_hardy {q : AngCircle → ℝ} (hc : Continuous q) (h0 : ∀ θ, 0 < q θ)
    (G : AngCircle → ℝ) :
    ∫ t, G (t : AngCircle) ∂(muOf q) = ∫ θ, q θ * G θ ∂angHaar := by
  have hpm : Measurable fun t => ENNReal.ofReal (pOf q t) :=
    ENNReal.measurable_ofReal.comp (continuous_pOf_hardy hc).measurable
  unfold muOf DGPS.FiniteN.densityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hpm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [DGPS.Examples.EngineeredRankOne.integral_angHaar_eq_interval (fun θ => q θ * G θ)]
  have h1 : ∀ t, (ENNReal.ofReal (pOf q t)).toReal • G (t : AngCircle) =
      (2 * π)⁻¹ * (q (t : AngCircle) * G (t : AngCircle)) := by
    intro t
    rw [ENNReal.toReal_ofReal (pOf_nonneg_hardy h0 t), smul_eq_mul]
    unfold pOf
    ring
  simp_rw [h1]
  rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]

lemma isProbabilityMeasure_muOf_hardy {q : AngCircle → ℝ} (hc : Continuous q)
    (h0 : ∀ θ, 0 < q θ) (h1 : ∫ θ, q θ ∂angHaar = 1) : IsProbabilityMeasure (muOf q) := by
  have h := integral_muOf_hardy hc h0 (fun _ => 1)
  simp only [mul_one, integral_const, smul_eq_mul] at h
  rw [h1] at h
  refine ⟨?_⟩
  have hr : (muOf q).real univ = 1 := h
  have : (muOf q univ).toReal = 1 := hr
  exact (ENNReal.toReal_eq_one_iff _).1 this


lemma muOf_Ici_hardy {q : AngCircle → ℝ} (hc : Continuous q) (h0 : ∀ θ, 0 < q θ) {x : ℝ}
    (hx : x ∈ Ioo (-π) π) :
    muOf q (Ici x) = ENNReal.ofReal (∫ t in x..π, pOf q t) := by
  have hp := continuous_pOf_hardy hc
  unfold muOf DGPS.FiniteN.densityMeasure
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici x ∩ Ioo (-π) π = Ico x π := by
    ext t; simp only [mem_inter_iff, mem_Ici, mem_Ioo, mem_Ico]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [hx.1], h3⟩
  rw [hset]
  have hint : IntegrableOn (pOf q) (Ico x π) volume :=
    (hp.continuousOn.integrableOn_Icc).mono_set Ico_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ico fun t _ => pOf_nonneg_hardy h0 t),
    intervalIntegral.integral_of_le hx.2.le, integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo]

lemma muOf_Iic_hardy {q : AngCircle → ℝ} (hc : Continuous q) (h0 : ∀ θ, 0 < q θ) {x : ℝ}
    (hx : x ∈ Ioo (-π) π) :
    muOf q (Iic x) = ENNReal.ofReal (∫ t in (-π)..x, pOf q t) := by
  have hp := continuous_pOf_hardy hc
  unfold muOf DGPS.FiniteN.densityMeasure
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic x ∩ Ioo (-π) π = Ioc (-π) x := by
    ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith [hx.2]⟩
  rw [hset]
  have hint : IntegrableOn (pOf q) (Ioc (-π) x) volume :=
    (hp.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t _ => pOf_nonneg_hardy h0 t),
    intervalIntegral.integral_of_le hx.1.le]

/-- Data needed for the one-dimensional Hardy argument: a positive continuous even probability
density on the circle with a uniform tail-times-resistance bound `B`. -/
structure HardyData (q : AngCircle → ℝ) (B : ℝ) : Prop where
  cont : Continuous q
  pos : ∀ θ, 0 < q θ
  int_one : ∫ θ, q θ ∂angHaar = 1
  even : ∀ t : ℝ, q ((-t : ℝ) : AngCircle) = q (t : AngCircle)
  nonneg : 0 ≤ B
  prod : ∀ x : ℝ, 0 < x → x < π →
    (∫ t in x..π, q (t : AngCircle)) * (∫ t in (0:ℝ)..x, (q (t : AngCircle))⁻¹) ≤ B

lemma right_term_hardy {q : AngCircle → ℝ} {B : ℝ} (hd : HardyData q B) {x : ℝ}
    (hx : x ∈ Ioo (-π) π) (hx0 : 0 < x) :
    (muOf q (Ici x)).toReal * ∫ t in (0:ℝ)..x, (pOf q t)⁻¹ ≤ B := by
  rw [muOf_Ici_hardy hd.cont hd.pos hx, ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg hx.2.le fun t _ => pOf_nonneg_hardy hd.pos t)]
  have h1 : ∫ t in x..π, pOf q t = (2 * π)⁻¹ * ∫ t in x..π, q (t : AngCircle) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; unfold pOf; ring
  have h2 : ∫ t in (0:ℝ)..x, (pOf q t)⁻¹ = (2 * π) * ∫ t in (0:ℝ)..x, (q (t : AngCircle))⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; unfold pOf; rw [inv_div, div_eq_mul_inv, mul_comm]
  rw [h1, h2]
  have := hd.prod x hx0 hx.2
  have hπ : (2 * π) ≠ 0 := by positivity
  calc (2 * π)⁻¹ * (∫ t in x..π, q (t : AngCircle)) *
        ((2 * π) * ∫ t in (0:ℝ)..x, (q (t : AngCircle))⁻¹)
      = ((2 * π)⁻¹ * (2 * π)) * ((∫ t in x..π, q (t : AngCircle)) *
          ∫ t in (0:ℝ)..x, (q (t : AngCircle))⁻¹) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hπ, one_mul]
    _ ≤ B := this

lemma left_term_hardy {q : AngCircle → ℝ} {B : ℝ} (hd : HardyData q B) {x : ℝ}
    (hx : x ∈ Ioo (-π) π) (hx0 : x < 0) :
    (muOf q (Iic x)).toReal * ∫ t in x..(0:ℝ), (pOf q t)⁻¹ ≤ B := by
  rw [muOf_Iic_hardy hd.cont hd.pos hx, ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg hx.1.le fun t _ => pOf_nonneg_hardy hd.pos t)]
  have hev : ∀ t, pOf q (-t) = pOf q t := by
    intro t; unfold pOf; rw [hd.even]
  have h1 : ∫ t in (-π)..x, pOf q t = (2 * π)⁻¹ * ∫ t in (-x)..π, q (t : AngCircle) := by
    have := intervalIntegral.integral_comp_neg (a := -π) (b := x) (pOf q)
    simp_rw [hev] at this
    rw [this, neg_neg, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; unfold pOf; ring
  have h2 : ∫ t in x..(0:ℝ), (pOf q t)⁻¹ =
      (2 * π) * ∫ t in (0:ℝ)..(-x), (q (t : AngCircle))⁻¹ := by
    have := intervalIntegral.integral_comp_neg (a := x) (b := 0) (fun t => (pOf q t)⁻¹)
    simp_rw [hev] at this
    rw [this, neg_zero, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; unfold pOf; rw [inv_div, div_eq_mul_inv, mul_comm]
  rw [h1, h2]
  have := hd.prod (-x) (by linarith) (by linarith [hx.1])
  have hπ : (2 * π) ≠ 0 := by positivity
  calc (2 * π)⁻¹ * (∫ t in (-x)..π, q (t : AngCircle)) *
        ((2 * π) * ∫ t in (0:ℝ)..(-x), (q (t : AngCircle))⁻¹)
      = ((2 * π)⁻¹ * (2 * π)) * ((∫ t in (-x)..π, q (t : AngCircle)) *
          ∫ t in (0:ℝ)..(-x), (q (t : AngCircle))⁻¹) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hπ, one_mul]
    _ ≤ B := this


lemma resistance_le_hardy {q : AngCircle → ℝ} {B : ℝ} (hd : HardyData q B) :
    max (rightResistanceConstant (Ioo (-π) π) (pOf q) 0)
      (leftResistanceConstant (Ioo (-π) π) (pOf q) 0) ≤ B := by
  refine max_le ?_ ?_
  · refine Real.sSup_le ?_ hd.nonneg
    rintro _ ⟨x, ⟨hxI, hx0⟩, rfl⟩
    exact right_term_hardy hd hxI hx0
  · refine Real.sSup_le ?_ hd.nonneg
    rintro _ ⟨x, ⟨hxI, hx0⟩, rfl⟩
    exact left_term_hardy hd hxI hx0

/-- Anchored Hardy inequality for smooth angular functions. -/
lemma smooth_hardy_hardy {q : AngCircle → ℝ} {B : ℝ} (hd : HardyData q B) {ψ : AngCircle → ℝ}
    (hψ : IsSmoothAngular ψ) :
    ∫ θ, q θ * (ψ θ - ψ ((0 : ℝ) : AngCircle)) ^ 2 ∂angHaar ≤
      4 * B * ∫ θ, q θ * (angDeriv ψ θ) ^ 2 ∂angHaar := by
  have := isProbabilityMeasure_muOf_hardy hd.cont hd.pos hd.int_one
  have hp := continuous_pOf_hardy hd.cont
  have hp0 : ∀ x ∈ Ioo (-π) π, 0 < pOf q x := by
    intro x _
    unfold pOf
    have := hd.pos (x : AngCircle)
    positivity
  have hdc : Continuous (angDeriv ψ) :=
    DGPS.Circle.StationaryFlux.continuous_of_smooth (DGPS.Circle.StationaryFlux.smooth_angDeriv hψ)
  have hf'c : Continuous fun t : ℝ => angDeriv ψ (t : AngCircle) :=
    hdc.comp Real.Angle.continuous_coe
  have hf : ∀ x ∈ Ioo (-π) π, ∀ y ∈ Ioo (-π) π,
      ψ (y : AngCircle) - ψ (x : AngCircle) = ∫ t in x..y, angDeriv ψ (t : AngCircle) := by
    intro x _ y _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => ψ (t : AngCircle))
      (fun t _ => DGPS.Circle.StationaryFlux.hasDerivAt_lift hψ t)
      (hf'c.intervalIntegrable _ _)]
  obtain ⟨C, hC⟩ := DGPS.Examples.EngineeredRankOne.exists_bound_of_continuous hdc
  have hE : Integrable (fun t : ℝ => (angDeriv ψ (t : AngCircle)) ^ 2) (muOf q) := by
    refine Integrable.of_bound (C := C ^ 2) (hf'c.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have := hC (t : AngCircle)
    rw [Real.norm_eq_abs] at this
    have h2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    rwa [sq_abs] at h2
  have key := anchored_half_line_resistance_poincare (I := Ioo (-π) π) (p := pOf q) (a := 0)
    (f := fun t : ℝ => ψ (t : AngCircle)) (f' := fun t : ℝ => angDeriv ψ (t : AngCircle))
    isOpen_Ioo ordConnected_Ioo ⟨by linarith [Real.pi_pos], Real.pi_pos⟩ hp.continuousOn hp0
    ⟨B, by rintro _ ⟨x, ⟨hxI, hx0⟩, rfl⟩; exact right_term_hardy hd hxI hx0⟩
    ⟨B, by rintro _ ⟨x, ⟨hxI, hx0⟩, rfl⟩; exact left_term_hardy hd hxI hx0⟩
    hf (hf'c.locallyIntegrable.locallyIntegrableOn _) hE
  have hk := key.2.2.1
  have hT1 := integral_muOf_hardy hd.cont hd.pos (fun θ => (ψ θ - ψ ((0 : ℝ) : AngCircle)) ^ 2)
  have hT2 := integral_muOf_hardy hd.cont hd.pos (fun θ => (angDeriv ψ θ) ^ 2)
  have hnn : 0 ≤ ∫ t : ℝ, (angDeriv ψ (t : AngCircle)) ^ 2 ∂(muOf q) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [← hT1, ← hT2]
  calc _ ≤ 4 * max (rightResistanceConstant (Ioo (-π) π) (pOf q) 0)
        (leftResistanceConstant (Ioo (-π) π) (pOf q) 0) *
        ∫ t : ℝ, (angDeriv ψ (t : AngCircle)) ^ 2 ∂(muOf q) := hk
    _ ≤ 4 * B * ∫ t : ℝ, (angDeriv ψ (t : AngCircle)) ^ 2 ∂(muOf q) := by
      have := resistance_le_hardy hd
      gcongr


lemma eLpNorm_angHaar_eq_hardy (w : AngCircle → ℝ) :
    eLpNorm w 2 angHaar = eLpNorm (fun x => w (angEquiv x)) 2 (haar 1) := by
  have := angEquiv.measurableEmbedding.eLpNorm_map_measure (g := w) (p := 2) (μ := haar 1)
  rw [measurePreserving_angEquiv.map_eq] at this
  exact this

lemma smooth_approx_hardy {u g : AngCircle → ℝ} (h : IsAngularWeakDeriv u g) :
    ∃ ψ : ℕ → AngCircle → ℝ, (∀ n, IsSmoothAngular (ψ n)) ∧
      Tendsto (fun n => eLpNorm (fun θ => ψ n θ - u θ) 2 angHaar) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun θ => angDeriv (ψ n) θ - g θ) 2 angHaar) atTop (𝓝 0) := by
  obtain ⟨v, hv, -, h1, h2⟩ := exists_smooth_tendsto_H1 ((isWeakGradient_comp_iff u g).1 h)
  have hcomp : ∀ n, (v n ∘ angEquiv.symm) ∘ angEquiv = v n := by
    intro n; funext x; simp
  have hs : ∀ n, IsSmoothAngular (v n ∘ angEquiv.symm) := by
    intro n
    rw [← isSmoothPeriodic_comp_iff, hcomp]; exact hv n
  refine ⟨fun n => v n ∘ angEquiv.symm, hs, ?_, ?_⟩
  · refine (h1.congr fun n => ?_)
    rw [eLpNorm_angHaar_eq_hardy]
    congr 1
    funext x
    simp
  · have h20 := h2 0
    have hc0 : ENNReal.ofReal (2 * π) ≠ 0 := by
      simp [Real.pi_pos]
    have hct : ENNReal.ofReal (2 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hA : ∀ n, eLpNorm (fun x => smoothGrad (v n) x 0 - physGrad g x 0) 2 (haar 1) =
        ENNReal.ofReal (2 * π) *
          eLpNorm (fun θ => angDeriv (v n ∘ angEquiv.symm) θ - g θ) 2 angHaar := by
      intro n
      rw [eLpNorm_angHaar_eq_hardy]
      have hpt : (fun x => smoothGrad (v n) x 0 - physGrad g x 0) =
          (2 * π) • (fun x => angDeriv (v n ∘ angEquiv.symm) (angEquiv x) - g (angEquiv x)) := by
        funext x
        rw [smoothGrad_apply, physGrad_apply]
        have := coordPartial_comp_angEquiv (hs n) x
        rw [hcomp] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [this]; ring
      rw [hpt, eLpNorm_const_smul]
      congr 1
      rw [Real.enorm_eq_ofReal (by positivity)]
    have hB : ∀ n, eLpNorm (fun θ => angDeriv (v n ∘ angEquiv.symm) θ - g θ) 2 angHaar =
        (ENNReal.ofReal (2 * π))⁻¹ * eLpNorm (fun x => smoothGrad (v n) x 0 - physGrad g x 0) 2 (haar 1) := by
      intro n
      rw [hA n, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    have := ENNReal.Tendsto.const_mul h20 (Or.inr (ENNReal.inv_ne_top.2 hc0))
    rw [mul_zero] at this
    exact this.congr fun n => (hB n).symm


lemma sq_add_le_hardy {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    (x + y) ^ 2 ≤ (1 + ε) * y ^ 2 + (1 + ε⁻¹) * x ^ 2 := by
  have h : (1 + ε) * y ^ 2 + (1 + ε⁻¹) * x ^ 2 - (x + y) ^ 2 = ε⁻¹ * (ε * y - x) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ ε⁻¹ * (ε * y - x) ^ 2 := by positivity
  linarith

lemma integral_sq_add_le_hardy {α : Type*} [MeasurableSpace α] {P : Measure α}
    {x y : α → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P) {ε : ℝ} (hε : 0 < ε) :
    ∫ a, (x a + y a) ^ 2 ∂P ≤ (1 + ε) * ∫ a, y a ^ 2 ∂P + (1 + ε⁻¹) * ∫ a, x a ^ 2 ∂P := by
  have hxs : Integrable (fun a => x a ^ 2) P := hx.integrable_sq
  have hys : Integrable (fun a => y a ^ 2) P := hy.integrable_sq
  have hxy : Integrable (fun a => (x a + y a) ^ 2) P := (hx.add hy).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hys.const_mul _) (hxs.const_mul _)]
  exact integral_mono hxy ((hys.const_mul _).add (hxs.const_mul _)) fun a => sq_add_le_hardy hε _ _

lemma variance_le_of_approx_hardy {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {u g : α → ℝ} (hu : MemLp u 2 P) (hg : MemLp g 2 P)
    {ψ d : ℕ → α → ℝ} (hψ : ∀ n, MemLp (ψ n) 2 P) (hd : ∀ n, MemLp (d n) 2 P)
    {c : ℕ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ n, ∫ a, (ψ n a - c n) ^ 2 ∂P ≤ K * ∫ a, d n a ^ 2 ∂P)
    (ha : Tendsto (fun n => ∫ a, (u a - ψ n a) ^ 2 ∂P) atTop (𝓝 0))
    (hb : Tendsto (fun n => ∫ a, (g a - d n a) ^ 2 ∂P) atTop (𝓝 0)) :
    ProbabilityTheory.variance u P ≤ K * ∫ a, g a ^ 2 ∂P := by
  set G := ∫ a, g a ^ 2 ∂P with hG
  have hvar : ∀ n, ProbabilityTheory.variance u P ≤ ∫ a, (u a - c n) ^ 2 ∂P := by
    intro n
    have h1 := ProbabilityTheory.variance_sub_const (μ := P) hu.aestronglyMeasurable (c n)
    have h2 := ProbabilityTheory.variance_le_expectation_sq (μ := P)
      (hu.aestronglyMeasurable.sub aestronglyMeasurable_const (β := ℝ) |>.congr
        (Eventually.of_forall fun _ => rfl) : AEStronglyMeasurable (fun a => u a - c n) P)
    rw [← h1]
    simpa [Pi.pow_apply] using h2
  have key : ∀ ε : ℝ, 0 < ε → ProbabilityTheory.variance u P ≤ (1 + ε) ^ 2 * (K * G) := by
    intro ε hε
    have hL : ∀ n, ProbabilityTheory.variance u P ≤
        (1 + ε) * (K * ((1 + ε) * G + (1 + ε⁻¹) * ∫ a, (g a - d n a) ^ 2 ∂P)) +
          (1 + ε⁻¹) * ∫ a, (u a - ψ n a) ^ 2 ∂P := by
      intro n
      refine (hvar n).trans ?_
      have e1 : ∀ a, (u a - c n) ^ 2 = ((u a - ψ n a) + (ψ n a - c n)) ^ 2 := fun a => by ring
      simp_rw [e1]
      have hx : MemLp (fun a => u a - ψ n a) 2 P := hu.sub (hψ n)
      have hy : MemLp (fun a => ψ n a - c n) 2 P := (hψ n).sub (memLp_const _)
      refine (integral_sq_add_le_hardy hx hy hε).trans ?_
      have hd1 : ∫ a, d n a ^ 2 ∂P ≤ (1 + ε) * G + (1 + ε⁻¹) * ∫ a, (g a - d n a) ^ 2 ∂P := by
        have e2 : ∀ a, d n a ^ 2 = ((d n a - g a) + g a) ^ 2 := fun a => by ring
        simp_rw [e2]
        have hx2 : MemLp (fun a => d n a - g a) 2 P := (hd n).sub hg
        refine (integral_sq_add_le_hardy hx2 hg hε).trans ?_
        have e3 : ∫ a, (d n a - g a) ^ 2 ∂P = ∫ a, (g a - d n a) ^ 2 ∂P := by
          congr 1; funext a; ring
        rw [e3]
      have hfac : (0 : ℝ) ≤ 1 + ε := by linarith
      have h3 := hK n
      have h4 : K * ∫ a, d n a ^ 2 ∂P ≤ K * ((1 + ε) * G + (1 + ε⁻¹) * ∫ a, (g a - d n a) ^ 2 ∂P) :=
        mul_le_mul_of_nonneg_left hd1 hK0
      have h5 := mul_le_mul_of_nonneg_left (h3.trans h4) hfac
      linarith
    have hlim : Tendsto (fun n => (1 + ε) * (K * ((1 + ε) * G + (1 + ε⁻¹) *
        ∫ a, (g a - d n a) ^ 2 ∂P)) + (1 + ε⁻¹) * ∫ a, (u a - ψ n a) ^ 2 ∂P) atTop
        (𝓝 ((1 + ε) * (K * ((1 + ε) * G + (1 + ε⁻¹) * 0)) + (1 + ε⁻¹) * 0)) := by
      refine Tendsto.add (Tendsto.const_mul _ (Tendsto.const_mul _ (Tendsto.const_add _
        (Tendsto.const_mul _ hb)))) (Tendsto.const_mul _ ha)
    have := ge_of_tendsto' hlim hL
    refine this.trans (le_of_eq ?_)
    ring
  have hlim2 : Tendsto (fun ε : ℝ => (1 + ε) ^ 2 * (K * G)) (𝓝[>] 0) (𝓝 ((1 + 0) ^ 2 * (K * G))) :=
    (((continuous_const.add continuous_id).pow 2).mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have := ge_of_tendsto hlim2 (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  simpa using this


lemma integral_sq_eq_hardy {α : Type*} [MeasurableSpace α] {P : Measure α} {w : α → ℝ}
    (hw : MemLp w 2 P) : ∫ a, w a ^ 2 ∂P = (eLpNorm w 2 P).toReal ^ 2 := by
  rw [hw.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ a, ‖w a‖ ^ (ENNReal.toReal 2) ∂P := integral_nonneg fun _ => by positivity
  rw [ENNReal.toReal_ofReal (by positivity)]
  have h1 : ∫ a, ‖w a‖ ^ (ENNReal.toReal 2) ∂P = ∫ a, w a ^ 2 ∂P := by
    congr 1; funext a
    simp
  rw [h1] at h0 ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  simp

lemma integral_nu_hardy {q : AngCircle → ℝ} (hc : Continuous q) (h0 : ∀ θ, 0 < q θ)
    (G : AngCircle → ℝ) :
    ∫ θ, G θ ∂(angHaar.withDensity fun θ => ENNReal.ofReal (q θ)) =
      ∫ θ, q θ * G θ ∂angHaar := by
  have hm : Measurable fun θ => ENNReal.ofReal (q θ) :=
    ENNReal.measurable_ofReal.comp hc.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp [ENNReal.toReal_ofReal (h0 θ).le]

lemma exists_bounds_hardy {q : AngCircle → ℝ} (hc : Continuous q) (h0 : ∀ θ, 0 < q θ) :
    ∃ m M : ℝ, 0 < m ∧ ∀ θ, m ≤ q θ ∧ q θ ≤ M := by
  obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  exact ⟨q a, q b, h0 a, fun θ => ⟨ha (mem_univ θ), hb (mem_univ θ)⟩⟩

lemma angHaar_le_hardy {q : AngCircle → ℝ} {m : ℝ} (hm : 0 < m)
    (hmq : ∀ θ, m ≤ q θ) :
    angHaar ≤ ENNReal.ofReal m⁻¹ • (angHaar.withDensity fun θ => ENNReal.ofReal (q θ)) := by
  rw [Measure.le_iff']
  intro s
  rw [Measure.smul_apply, withDensity_apply' _ s, smul_eq_mul]
  have h1 : ENNReal.ofReal m * angHaar s ≤ ∫⁻ a in s, ENNReal.ofReal (q a) ∂angHaar := by
    rw [← setLIntegral_const]
    exact lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hmq a)
  have hm0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.2 hm).ne'
  calc angHaar s = ENNReal.ofReal m⁻¹ * (ENNReal.ofReal m * angHaar s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hm.le), inv_mul_cancel₀ hm.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

lemma tendsto_integral_nu_hardy {q : AngCircle → ℝ} (hc : Continuous q) (h0 : ∀ θ, 0 < q θ)
    {M : ℝ} (hM : ∀ θ, q θ ≤ M) {w : ℕ → AngCircle → ℝ} (hw : ∀ n, MemLp (w n) 2 angHaar)
    (ht : Tendsto (fun n => eLpNorm (w n) 2 angHaar) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ θ, (w n θ) ^ 2 ∂(angHaar.withDensity fun θ => ENNReal.ofReal (q θ)))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => M * (eLpNorm (w n) 2 angHaar).toReal ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
    simp only [ENNReal.toReal_zero] at this
    have h2 := (this.pow 2).const_mul M
    simpa [Function.comp_def] using h2
  refine squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) (fun n => ?_) h1
  rw [integral_nu_hardy hc h0, ← integral_sq_eq_hardy (hw n)]
  have hi : Integrable (fun θ => w n θ ^ 2) angHaar := (hw n).integrable_sq
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun θ => ?_) (hi.const_mul M)
    (Eventually.of_forall fun θ => ?_)
  · exact mul_nonneg (h0 θ).le (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (hM θ) (sq_nonneg _)


/-- Anchored weighted Hardy inequality in the weak angular domain, with constant `4 B`. -/
lemma weak_hardy_hardy {q : AngCircle → ℝ} {B : ℝ} (hd : HardyData q B)
    (ν : ProbabilityMeasure AngCircle)
    (hν : (ν : Measure AngCircle) = angHaar.withDensity fun θ => ENNReal.ofReal (q θ))
    {u g : AngCircle → ℝ} (hw : IsAngMeasureWeakDeriv ν u g) :
    angVariance ν u ≤ 4 * B * ∫ θ, g θ ^ 2 ∂(ν : Measure AngCircle) := by
  obtain ⟨m, M, hm, hmM⟩ := exists_bounds_hardy hd.cont hd.pos
  have hle := angHaar_le_hardy (q := q) hm fun θ => (hmM θ).1
  rw [← hν] at hle
  have hcne : ENNReal.ofReal m⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hu1 : MemLp u 2 angHaar := hw.memLp.of_measure_le_smul hcne hle
  have hg1 : MemLp g 2 angHaar := hw.memLp_deriv.of_measure_le_smul hcne hle
  obtain ⟨ψ, hψs, hψ1, hψ2⟩ := smooth_approx_hardy (u := u) (g := g) ⟨hu1, hg1, hw.ibp⟩
  have hψc : ∀ n, Continuous (ψ n) := fun n => DGPS.Circle.StationaryFlux.continuous_of_smooth (hψs n)
  have hdc : ∀ n, Continuous (angDeriv (ψ n)) := fun n =>
    DGPS.Circle.StationaryFlux.continuous_of_smooth
      (DGPS.Circle.StationaryFlux.smooth_angDeriv (hψs n))
  have hbdd : ∀ {f : AngCircle → ℝ} (_ : Continuous f) (P : Measure AngCircle)
      [IsFiniteMeasure P], MemLp f 2 P := by
    intro f hf P _
    obtain ⟨C, hC⟩ := DGPS.Examples.EngineeredRankOne.exists_bound_of_continuous hf
    exact MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
  have hνp : IsProbabilityMeasure (ν : Measure AngCircle) := inferInstance
  have hψν : ∀ n, MemLp (ψ n) 2 (ν : Measure AngCircle) := fun n => hbdd (hψc n) _
  have hdν : ∀ n, MemLp (angDeriv (ψ n)) 2 (ν : Measure AngCircle) := fun n => hbdd (hdc n) _
  have hK : ∀ n, ∫ θ, (ψ n θ - ψ n ((0 : ℝ) : AngCircle)) ^ 2 ∂(ν : Measure AngCircle) ≤
      4 * B * ∫ θ, angDeriv (ψ n) θ ^ 2 ∂(ν : Measure AngCircle) := by
    intro n
    rw [hν, integral_nu_hardy hd.cont hd.pos, integral_nu_hardy hd.cont hd.pos]
    exact smooth_hardy_hardy hd (hψs n)
  have hwu : ∀ n, MemLp (fun θ => ψ n θ - u θ) 2 angHaar := fun n => (hbdd (hψc n) _).sub hu1
  have hwg : ∀ n, MemLp (fun θ => angDeriv (ψ n) θ - g θ) 2 angHaar := fun n =>
    (hbdd (hdc n) _).sub hg1
  have ha := tendsto_integral_nu_hardy hd.cont hd.pos (fun θ => (hmM θ).2) hwu hψ1
  have hb := tendsto_integral_nu_hardy hd.cont hd.pos (fun θ => (hmM θ).2) hwg hψ2
  rw [← hν] at ha hb
  have ha' : Tendsto (fun n => ∫ θ, (u θ - ψ n θ) ^ 2 ∂(ν : Measure AngCircle)) atTop (𝓝 0) := by
    refine ha.congr fun n => ?_
    congr 1; funext θ; ring
  have hb' : Tendsto (fun n => ∫ θ, (g θ - angDeriv (ψ n) θ) ^ 2 ∂(ν : Measure AngCircle))
      atTop (𝓝 0) := by
    refine hb.congr fun n => ?_
    congr 1; funext θ; ring
  have hvar := variance_le_of_approx_hardy (P := (ν : Measure AngCircle)) hw.memLp hw.memLp_deriv
    hψν hdν (c := fun n => ψ n ((0 : ℝ) : AngCircle)) (K := 4 * B)
    (by linarith [hd.nonneg]) hK ha' hb'
  rw [ProbabilityTheory.variance_eq_integral hw.memLp.aemeasurable] at hvar
  exact hvar


open DGPS.Examples.EngineeredRankOne DGPS.Models

lemma left_product_eq_hardy {q : AngCircle → ℝ} {B : ℝ} (hd : HardyData q B) {y : ℝ} :
    (∫ t in (-π)..(-y), q (t : AngCircle)) * (∫ t in (-y)..(0:ℝ), (q (t : AngCircle))⁻¹) =
      (∫ t in y..π, q (t : AngCircle)) * (∫ t in (0:ℝ)..y, (q (t : AngCircle))⁻¹) := by
  have h1 := intervalIntegral.integral_comp_neg (a := -π) (b := -y) (fun t => q (t : AngCircle))
  have h2 := intervalIntegral.integral_comp_neg (a := -y) (b := 0)
    (fun t => (q (t : AngCircle))⁻¹)
  simp_rw [hd.even, neg_neg, neg_zero] at h1 h2
  rw [h1, h2]

/-- Evaluation of the engineered density on a real parameter. -/
lemma qAng_coe_hardy (h t : ℝ) :
    qAng h (t : AngCircle) =
      (Zh h)⁻¹ * Real.exp (-(h * (1 - Real.cos t) + corr h (1 - Real.cos t))) := by
  unfold qAng logq
  rw [Uang_coe_eq]
  congr 2
  ring

lemma qAng_product_bound_hardy {h : ℝ} (hh : 0 < h) {x : ℝ} (hx0 : 0 < x) (hxπ : x < π) :
    (∫ t in x..π, qAng h (t : AngCircle)) * (∫ t in (0:ℝ)..x, (qAng h (t : AngCircle))⁻¹) ≤
      2 * min x (π - x) / (h * Real.sin x) := by
  set Φ : ℝ → ℝ := fun t => h * (1 - Real.cos t) + corr h (1 - Real.cos t) with hΦdef
  have hΦc : Continuous Φ := by
    have hc : Continuous (corr h) := (contDiff_corr h hh).continuous
    simp only [hΦdef]
    fun_prop
  have hmem : ∀ a : ℝ, 1 - Real.cos a ∈ Icc (0 : ℝ) 2 := fun a =>
    ⟨by linarith [Real.cos_le_one a], by linarith [Real.neg_one_le_cos a]⟩
  have hmono : ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ π →
      h * (Real.cos a - Real.cos t) ≤ Φ t - Φ a := by
    intro a t ha hat htπ
    have hcos : Real.cos t ≤ Real.cos a := Real.cos_le_cos_of_nonneg_of_le_pi ha htπ hat
    have hm := monotoneOn_corr h hh (hmem a) (hmem t) (by linarith)
    have e : Φ t - Φ a = h * (Real.cos a - Real.cos t) +
        (corr h (1 - Real.cos t) - corr h (1 - Real.cos a)) := by
      simp only [hΦdef]; ring
    linarith
  have e1 : ∀ t : ℝ, qAng h (t : AngCircle) = (Zh h)⁻¹ * Real.exp (-Φ t) := fun t =>
    qAng_coe_hardy h t
  have e2 : ∀ t : ℝ, (qAng h (t : AngCircle))⁻¹ = Zh h * Real.exp (Φ t) := by
    intro t
    rw [e1, mul_inv, inv_inv, ← Real.exp_neg, neg_neg]
  simp_rw [e2, e1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hZ := (Zh_pos h hh).ne'
  calc (Zh h)⁻¹ * (∫ t in x..π, Real.exp (-Φ t)) * (Zh h * ∫ t in (0:ℝ)..x, Real.exp (Φ t))
      = ((Zh h)⁻¹ * Zh h) * ((∫ t in x..π, Real.exp (-Φ t)) *
          ∫ t in (0:ℝ)..x, Real.exp (Φ t)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hZ, one_mul]
    _ ≤ _ := product_bound_hardy hh hΦc hmono hx0 hxπ

lemma hardyData_qAng {h : ℝ} (hh : 0 < h) : HardyData (qAng h) (π / h) where
  cont := by
    unfold qAng
    exact continuous_const.mul (continuous_exp.comp (continuous_logq h hh))
  pos := qAng_pos h hh
  int_one := integral_qAng h hh
  even := by
    intro t
    rw [qAng_coe_hardy, qAng_coe_hardy, Real.cos_neg]
  nonneg := by have := Real.pi_pos; positivity
  prod := fun _ hx0 hxπ =>
    (qAng_product_bound_hardy hh hx0 hxπ).trans (min_div_sin_le_hardy hh hx0 hxπ)

lemma angMap_engineered_hardy {h : ℝ} (hP : IsProbabilityMeasure (engineeredReference h)) :
    ((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) : Measure AngCircle) =
      angHaar.withDensity fun θ => ENNReal.ofReal (qAng h θ) := by
  refine (angMap_coe _).trans ?_
  show (engineeredReference h).map angEquiv = _
  unfold engineeredReference
  rw [Measure.map_map angEquiv.measurable angEquiv.symm.measurable]
  have : (angEquiv ∘ angEquiv.symm : AngCircle → AngCircle) = id := by
    funext θ; simp
  rw [this, Measure.map_id]

lemma lintegral_enorm_sq_hardy {α : Type*} [MeasurableSpace α] {P : Measure α} {g : α → ℝ}
    (hg : MemLp g 2 P) : ∫⁻ a, ‖g a‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ a, g a ^ 2 ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)]
  refine lintegral_congr fun a => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

end DGPS.Examples.EngineeredHardy

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Models DGPS.Examples.EngineeredHardy

/-- EX039: engineered Hardy Poincare bound.  For every `h ≥ 2` and with `q_h` the engineered
angular density (`qAng h`, so that `μ_h` is `q_h dθ/(2π)`):
* (half-circle product bound) for `0 < x < π`,
  `[∫_x^π q_h] [∫_0^x q_h⁻¹] ≤ 2 min(x, π-x)/(h sin x) ≤ π/h`, and the mirror statement on the
  other half-circle;
* the FIN006 one-sided resistance constants of the density `q_h/(2π)` on `(-π, π)` anchored at
  `0` are at most `π/h`, so the anchored Hardy constant `4 · max(R, L)` is at most `4π/h`;
* the anchored weighted Hardy inequality `∫ q_h (ψ - ψ(0))² ≤ (4π/h) ∫ q_h (ψ')²` for smooth
  angular `ψ`;
* every test function of the angular weak form domain of `μ_h` satisfies
  `Var ≤ (4π/h) ∫ (f')² dμ_h`;
* `λ_P^angular(μ_h) ≥ c h` with `c = 1/(4π)` independent of `h`. -/
theorem engineered_hardy_poincare_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℝ, 2 ≤ h →
      (∀ x : ℝ, 0 < x → x < π →
        (∫ t in x..π, qAng h (t : AngCircle)) * (∫ t in (0:ℝ)..x, (qAng h (t : AngCircle))⁻¹) ≤
            2 * min x (π - x) / (h * Real.sin x) ∧
          2 * min x (π - x) / (h * Real.sin x) ≤ π / h ∧
          (∫ t in (-π)..(-x), qAng h (t : AngCircle)) *
              (∫ t in (-x)..(0:ℝ), (qAng h (t : AngCircle))⁻¹) ≤
            2 * min x (π - x) / (h * Real.sin x)) ∧
      max (DGPS.FiniteN.rightResistanceConstant (Set.Ioo (-π) π)
            (fun t : ℝ => qAng h (t : AngCircle) / (2 * π)) 0)
          (DGPS.FiniteN.leftResistanceConstant (Set.Ioo (-π) π)
            (fun t : ℝ => qAng h (t : AngCircle) / (2 * π)) 0) ≤ π / h ∧
      (∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
        ∫ θ, qAng h θ * (ψ θ - ψ ((0 : ℝ) : AngCircle)) ^ 2 ∂angHaar ≤
          4 * (π / h) * ∫ θ, qAng h θ * (angDeriv ψ θ) ^ 2 ∂angHaar) ∧
      ∀ hP : IsProbabilityMeasure (engineeredReference h),
        (∀ f : AngWeakH1Test (angMap ⟨engineeredReference h, hP⟩),
          angVariance (angMap ⟨engineeredReference h, hP⟩) f.fn ≤
            4 * (π / h) * ∫ θ, f.grad θ ^ 2
              ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
                Measure AngCircle)) ∧
        ENNReal.ofReal (c * h) ≤ angPoincareRate (angMap ⟨engineeredReference h, hP⟩) := by
  have hπ := Real.pi_pos
  refine ⟨1 / (4 * π), by positivity, fun h h2 => ?_⟩
  have hh : 0 < h := by linarith
  have hd := hardyData_qAng hh
  refine ⟨fun x hx0 hxπ => ⟨qAng_product_bound_hardy hh hx0 hxπ, min_div_sin_le_hardy hh hx0 hxπ,
    ?_⟩, ?_, fun ψ hψ => smooth_hardy_hardy hd hψ, fun hP => ?_⟩
  · rw [left_product_eq_hardy hd]
    exact qAng_product_bound_hardy hh hx0 hxπ
  · have := resistance_le_hardy hd
    exact this
  · have hν := angMap_engineered_hardy hP
    have hweak : ∀ f : AngWeakH1Test (angMap ⟨engineeredReference h, hP⟩),
        angVariance (angMap ⟨engineeredReference h, hP⟩) f.fn ≤
          4 * (π / h) * ∫ θ, f.grad θ ^ 2
            ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
              Measure AngCircle) := fun f => weak_hardy_hardy hd _ hν f.isWeak
    refine ⟨hweak, ?_⟩
    unfold angPoincareRate
    refine le_iInf fun ⟨f, hv⟩ => ?_
    unfold angDirichletEnergy
    rw [lintegral_enorm_sq_hardy f.isWeak.memLp_deriv,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hv).ne')
        (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hweak f
    have hc : 0 ≤ 1 / (4 * π) * h := by positivity
    calc 1 / (4 * π) * h * angVariance (angMap ⟨engineeredReference h, hP⟩) f.fn
        ≤ 1 / (4 * π) * h * (4 * (π / h) * ∫ θ, f.grad θ ^ 2
            ∂((angMap ⟨engineeredReference h, hP⟩ : ProbabilityMeasure AngCircle) :
              Measure AngCircle)) := mul_le_mul_of_nonneg_left h1 hc
      _ = _ := by field_simp

end DGPS.Examples
