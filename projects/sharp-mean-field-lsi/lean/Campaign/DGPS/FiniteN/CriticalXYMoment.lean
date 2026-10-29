import DGPS.FiniteN.RotationalTools
import DGPS.FiniteN.Tools.StrongConvexityBobkovLedoux

/-!
# Critical scaled moment limit (FIN032)

Under the critical auxiliary law `η_N ∝ exp[-N ψ(|z|)] dz` on `ℝ²`, the rescaled variable
`N^{1/4} z` converges, together with all polynomial moments, to the probability measure on `ℝ²`
proportional to `exp(-|y|⁴/64)`.  In particular `√N ∫ g(|z|)² dη_N → 2/√π` and
`Var(F) / N^{3/2} → 1/√π`.

The proof writes `η_N` as the push-forward of the Gibbs measure of the scaled potential
`Φ_N(y) = N ψ(N^{-1/4}|y|)` (FIN029), bounds `Φ_N ≥ c min(|y|⁴, |y|²)` uniformly in `N` (FIN027),
uses the quartic Taylor expansion of `ψ` for the pointwise limit `Φ_N → |y|⁴/64`, and passes to
the limit in numerator and denominator by dominated convergence.
-/

open MeasureTheory Filter Topology Set
open DGPS.Circle.BesselMoments

namespace DGPS.FiniteN

/-- the limit law on `ℝ²`: the probability measure proportional to `exp(-|y|⁴/64)` -/
noncomputable def criticalScaledLimitLaw : Measure (EuclideanSpace ℝ (Fin 2)) :=
  Tools.StrongConvexityLSI.gibbs (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 4 / 64)

/-- the dominating function `(1 + |y|)^k exp(-c min(|y|⁴, |y|²))` -/
noncomputable def critMomDom (c : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (1 + ‖y‖) ^ k * Real.exp (-(c * min (‖y‖ ^ 4) (‖y‖ ^ 2)))

theorem critMom_pow_le (k : ℕ) (r : ℝ) (hr : 0 ≤ r) : (1 + r) ^ k ≤ 2 ^ k * (1 + r ^ k) := by
  rcases le_total r 1 with h | h
  · calc (1 + r) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + r ^ k) := by
        have : 0 ≤ r ^ k := pow_nonneg hr k
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k]
  · calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * r ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + r ^ k) := by
        have : 0 ≤ r ^ k := pow_nonneg hr k
        nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k]

theorem critMom_min_ge (r : ℝ) : r ^ 2 - 1 ≤ min (r ^ 4) (r ^ 2) := by
  refine le_min ?_ (by linarith)
  nlinarith [sq_nonneg (r ^ 2 - 1), sq_nonneg r]

theorem critMom_gauss_integrableOn (c : ℝ) (hc : 0 < c) (m : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ m * Real.exp (-c * r ^ 2)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_sq hc (s := (m : ℝ)) (by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  simpa [Real.rpow_natCast] using this

theorem critMom_integrable (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable (critMomDom c k) (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  have hfun : critMomDom c k = fun y : EuclideanSpace ℝ (Fin 2) =>
      (fun r : ℝ => (1 + r) ^ k * Real.exp (-(c * min (r ^ 4) (r ^ 2)))) ‖y‖ := rfl
  rw [hfun]
  refine (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (f := fun r : ℝ => (1 + r) ^ k * Real.exp (-(c * min (r ^ 4) (r ^ 2))))).2 ?_
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, pow_one, Nat.add_one_sub_one]
  have hb : IntegrableOn (fun r : ℝ => Real.exp c * 2 ^ k *
      (r ^ 1 * Real.exp (-c * r ^ 2) + r ^ (k + 1) * Real.exp (-c * r ^ 2))) (Ioi 0) :=
    ((critMom_gauss_integrableOn c hc 1).add (critMom_gauss_integrableOn c hc (k + 1))).const_mul _
  refine hb.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine measurable_id.mul ?_
    refine Measurable.mul (by fun_prop) ?_
    exact Real.measurable_exp.comp (Measurable.neg (measurable_const.mul
      (Measurable.min (by fun_prop) (by fun_prop))))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have h1 := critMom_pow_le k r hr0.le
    have h2 : Real.exp (-(c * min (r ^ 4) (r ^ 2))) ≤ Real.exp c * Real.exp (-c * r ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := critMom_min_ge r
      nlinarith
    have h3 : 0 ≤ Real.exp (-(c * min (r ^ 4) (r ^ 2))) := (Real.exp_pos _).le
    have h4 : 0 ≤ (1 + r) ^ k := pow_nonneg (by linarith) k
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc r * ((1 + r) ^ k * Real.exp (-(c * min (r ^ 4) (r ^ 2))))
        ≤ r * (2 ^ k * (1 + r ^ k) * (Real.exp c * Real.exp (-c * r ^ 2))) := by
          gcongr
      _ = Real.exp c * 2 ^ k * (r ^ 1 * Real.exp (-c * r ^ 2) +
            r ^ (k + 1) * Real.exp (-c * r ^ 2)) := by ring

/-! ### The scaling `a_N = N^{-1/4}` -/

theorem critScale_pos (N : ℝ) (hN : 1 ≤ N) : 0 < N ^ (-(1 / 4 : ℝ)) :=
  Real.rpow_pos_of_pos (by linarith) _

theorem critScale_pow4 (N : ℝ) (hN : 1 ≤ N) : N * (N ^ (-(1 / 4 : ℝ))) ^ 4 = 1 := by
  have hN0 : 0 < N := by linarith
  have : (N ^ (-(1 / 4 : ℝ))) ^ 4 = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    exact Real.rpow_neg_one N
  rw [this]
  field_simp

theorem critScale_sq_ge (N : ℝ) (hN : 1 ≤ N) : 1 ≤ N * (N ^ (-(1 / 4 : ℝ))) ^ 2 := by
  have h4 := critScale_pow4 N hN
  set a := N ^ (-(1 / 4 : ℝ))
  have ha : 0 < a := critScale_pos N hN
  have hsq : (N * a ^ 2) ^ 2 = N := by
    calc (N * a ^ 2) ^ 2 = N * (N * a ^ 4) := by ring
      _ = N := by rw [h4, mul_one]
  have : 0 < N * a ^ 2 := by positivity
  nlinarith

theorem critScale_tendsto {ι : Type*} {l : Filter ι} (N : ι → ℝ) (hN : Tendsto N l atTop) :
    Tendsto (fun n => N n ^ (-(1 / 4 : ℝ))) l (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hN

/-! ### Uniform lower bound and pointwise limit of the scaled potential -/

theorem critScaled_lower (N : ℝ) (hN : 1 ≤ N) (y : EuclideanSpace ℝ (Fin 2)) :
    criticalC0 / 12 * min (‖y‖ ^ 4) (‖y‖ ^ 2) ≤
      criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N y := by
  have hN0 : 0 < N := by linarith
  set a := N ^ (-(1 / 4 : ℝ)) with ha
  have ha0 : 0 < a := critScale_pos N hN
  have h4 := critScale_pow4 N hN
  have h2 := critScale_sq_ge N hN
  have hco := (critical_radial_hessian_coercivity (E := EuclideanSpace ℝ (Fin 2))).2.2.1
    (a * ‖y‖) (by positivity)
  have hc0 : (16 * Real.exp (1 / 4))⁻¹ = criticalC0 := rfl
  rw [hc0] at hco
  unfold criticalScaledPotential
  have hmin : min (‖y‖ ^ 4) (‖y‖ ^ 2) ≤ N * min ((a * ‖y‖) ^ 4) ((a * ‖y‖) ^ 2) := by
    rw [mul_min_of_nonneg _ _ hN0.le]
    refine min_le_min ?_ ?_
    · have : N * (a * ‖y‖) ^ 4 = ‖y‖ ^ 4 := by
        calc N * (a * ‖y‖) ^ 4 = (N * a ^ 4) * ‖y‖ ^ 4 := by ring
          _ = ‖y‖ ^ 4 := by rw [h4, one_mul]
      exact this.ge
    · have : N * (a * ‖y‖) ^ 2 = (N * a ^ 2) * ‖y‖ ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg ‖y‖]
  have hc := criticalC0_pos
  calc criticalC0 / 12 * min (‖y‖ ^ 4) (‖y‖ ^ 2)
      ≤ criticalC0 / 12 * (N * min ((a * ‖y‖) ^ 4) ((a * ‖y‖) ^ 2)) := by gcongr
    _ = N * (criticalC0 / 12 * min ((a * ‖y‖) ^ 4) ((a * ‖y‖) ^ 2)) := by ring
    _ ≤ N * criticalPsi (a * ‖y‖) := by gcongr

theorem critScaled_close (N : ℝ) (hN : 1 ≤ N) (y : EuclideanSpace ℝ (Fin 2))
    (hy : N ^ (-(1 / 4 : ℝ)) * ‖y‖ ≤ 1) :
    |criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N y - ‖y‖ ^ 4 / 64| ≤
      ‖y‖ ^ 6 * (N ^ (-(1 / 4 : ℝ))) ^ 2 / 96 := by
  have hN0 : 0 < N := by linarith
  set a := N ^ (-(1 / 4 : ℝ)) with ha
  have ha0 : 0 < a := critScale_pos N hN
  have h4 := critScale_pow4 N hN
  have hT := (critical_radial_hessian_coercivity (E := EuclideanSpace ℝ (Fin 2))).2.2.2.2.2
    (a * ‖y‖) (by positivity) hy
  unfold criticalScaledPotential
  have e1 : ‖y‖ ^ 4 / 64 = N * ((a * ‖y‖) ^ 4 / 64) := by
    calc ‖y‖ ^ 4 / 64 = (N * a ^ 4) * ‖y‖ ^ 4 / 64 := by rw [h4, one_mul]
      _ = N * ((a * ‖y‖) ^ 4 / 64) := by ring
  have e2 : ‖y‖ ^ 6 * a ^ 2 / 96 = N * ((a * ‖y‖) ^ 6 / 96) := by
    calc ‖y‖ ^ 6 * a ^ 2 / 96 = (N * a ^ 4) * ‖y‖ ^ 6 * a ^ 2 / 96 := by rw [h4, one_mul]
      _ = N * ((a * ‖y‖) ^ 6 / 96) := by ring
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos hN0]
  exact mul_le_mul_of_nonneg_left hT hN0.le

theorem critScaled_tendsto {ι : Type*} {l : Filter ι} (N : ι → ℝ) (hN : Tendsto N l atTop)
    (y : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n => criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) (N n) y) l
      (𝓝 (‖y‖ ^ 4 / 64)) := by
  have hN1 : ∀ᶠ n in l, 1 ≤ N n := hN.eventually_ge_atTop 1
  have ha := critScale_tendsto N hN
  have hay : ∀ᶠ n in l, N n ^ (-(1 / 4 : ℝ)) * ‖y‖ ≤ 1 := by
    have : Tendsto (fun n => N n ^ (-(1 / 4 : ℝ)) * ‖y‖) l (𝓝 (0 * ‖y‖)) := ha.mul_const _
    rw [zero_mul] at this
    exact this.eventually (eventually_le_nhds one_pos)
  have hb : Tendsto (fun n => ‖y‖ ^ 6 * (N n ^ (-(1 / 4 : ℝ))) ^ 2 / 96) l (𝓝 0) := by
    have := (((ha.pow 2).const_mul (‖y‖ ^ 6)).div_const 96)
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ hb
  filter_upwards [hN1, hay] with n h1 h2
  rw [Real.dist_eq]
  exact critScaled_close (N n) h1 y h2

/-! ### Dominated convergence for the Gibbs-normalised ratio -/

theorem critExp_integrable {U : EuclideanSpace ℝ (Fin 2) → ℝ} (hU : Continuous U) (c : ℝ)
    (hc : 0 < c) (hle : ∀ y, c * min (‖y‖ ^ 4) (‖y‖ ^ 2) ≤ U y) :
    Integrable (fun y => Real.exp (-U y)) (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  refine (critMom_integrable c hc 0).mono' ?_ ?_
  · exact (Real.continuous_exp.comp hU.neg).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    unfold critMomDom
    rw [pow_zero, one_mul]
    exact Real.exp_le_exp.2 (by linarith [hle y])

theorem critScaled_continuous (N : ℝ) (hN : 1 ≤ N) :
    Continuous (criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N) :=
  (criticalScaledPotential_contDiff N hN).continuous

theorem critLimit_continuous : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 4 / 64) := by
  fun_prop

theorem critLimit_lower (y : EuclideanSpace ℝ (Fin 2)) :
    (1 / 64 : ℝ) * min (‖y‖ ^ 4) (‖y‖ ^ 2) ≤ ‖y‖ ^ 4 / 64 := by
  have := min_le_left (‖y‖ ^ 4) (‖y‖ ^ 2)
  linarith

theorem critNum_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] (N : ι → ℝ)
    (hN : Tendsto N l atTop) (h : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (h0 : EuclideanSpace ℝ (Fin 2) → ℝ) (hm : ∀ n, Measurable (h n)) (C : ℝ) (k : ℕ)
    (hb : ∀ n y, |h n y| ≤ C * (1 + ‖y‖) ^ k)
    (hl : ∀ y, Tendsto (fun n => h n y) l (𝓝 (h0 y))) :
    Tendsto (fun n => ∫ y, Real.exp (-(criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2))
        (N n) y)) * h n y) l
      (𝓝 (∫ y, Real.exp (-(‖y‖ ^ 4 / 64)) * h0 y)) := by
  have hN1 : ∀ᶠ n in l, 1 ≤ N n := hN.eventually_ge_atTop 1
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => C * critMomDom (criticalC0 / 12) k y) ?_ ?_ ?_ ?_
  · filter_upwards [hN1] with n hn
    exact ((Real.continuous_exp.comp (critScaled_continuous (N n) hn).neg).measurable.mul
      (hm n)).aestronglyMeasurable
  · filter_upwards [hN1] with n hn
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-(criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) (N n) y)) ≤
        Real.exp (-(criticalC0 / 12 * min (‖y‖ ^ 4) (‖y‖ ^ 2))) :=
      Real.exp_le_exp.2 (by linarith [critScaled_lower (N n) hn y])
    calc Real.exp (-(criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) (N n) y)) *
          |h n y|
        ≤ Real.exp (-(criticalC0 / 12 * min (‖y‖ ^ 4) (‖y‖ ^ 2))) *
          (C * (1 + ‖y‖) ^ k) :=
          mul_le_mul h1 (hb n y) (abs_nonneg _) (Real.exp_pos _).le
      _ = C * critMomDom (criticalC0 / 12) k y := by unfold critMomDom; ring
  · exact (critMom_integrable (criticalC0 / 12) (by have := criticalC0_pos; positivity) k).const_mul C
  · refine Eventually.of_forall fun y => ?_
    have h1 := critScaled_tendsto N hN y
    exact ((Real.continuous_exp.tendsto _).comp h1.neg).mul (hl y)

theorem critGibbs_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] (N : ι → ℝ)
    (hN : Tendsto N l atTop) (h : ι → EuclideanSpace ℝ (Fin 2) → ℝ)
    (h0 : EuclideanSpace ℝ (Fin 2) → ℝ) (hm : ∀ n, Measurable (h n)) (C : ℝ) (k : ℕ)
    (hb : ∀ n y, |h n y| ≤ C * (1 + ‖y‖) ^ k)
    (hl : ∀ y, Tendsto (fun n => h n y) l (𝓝 (h0 y))) :
    Tendsto (fun n => ∫ y, h n y ∂Tools.StrongConvexityLSI.gibbs
        (criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) (N n))) l
      (𝓝 (∫ y, h0 y ∂criticalScaledLimitLaw)) := by
  have hN1 : ∀ᶠ n in l, 1 ≤ N n := hN.eventually_ge_atTop 1
  have hnum := critNum_tendsto N hN h h0 hm C k hb hl
  have hden := critNum_tendsto N hN (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    (fun _ => measurable_const) 1 0 (fun n y => by simp) (fun y => tendsto_const_nhds)
  simp only [mul_one] at hden
  have hq := Tools.StrongConvexityBobkovLedoux.integral_gibbs
    (critLimit_continuous.measurable) h0
  have hZ : 0 < ∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-(‖y‖ ^ 4 / 64)) :=
    Tools.StrongConvexityLSI.integral_exp_neg_pos
      (critExp_integrable critLimit_continuous (1 / 64) (by norm_num) critLimit_lower)
  unfold criticalScaledLimitLaw
  rw [hq]
  refine (hnum.div hden hZ.ne').congr' ?_
  filter_upwards [hN1] with n hn
  rw [Tools.StrongConvexityBobkovLedoux.integral_gibbs (critScaled_continuous (N n) hn).measurable]
  rfl

/-! ### Transfer from `η_N` to the Gibbs measure of the scaled potential -/

theorem critTransfer (N : ℝ) (hN : 1 ≤ N) (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ∫ z, f ((N ^ (1 / 4 : ℝ)) • z) ∂criticalAuxiliaryLaw N =
      ∫ y, f y ∂Tools.StrongConvexityLSI.gibbs
        (criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N) := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < N ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
  rw [criticalAuxiliaryLaw_eq_map N hN, integral_map_equiv]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hdil : (Tools.StrongConvexityLSI.dil (N ^ (1 / 4 : ℝ)) hs).symm y =
      (N ^ (1 / 4 : ℝ))⁻¹ • y := rfl
  simp only [hdil, smul_inv_smul₀ hs.ne']

/-! ### The radial integrals -/

theorem crit_radial_one :
    ∫ r in Ioi (0 : ℝ), r * Real.exp (-(r ^ 4 / 64)) = 2 * Real.sqrt Real.pi := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 4) (q := 1) (b := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∫ r in Ioi (0 : ℝ), r * Real.exp (-(r ^ 4 / 64)) =
      ∫ x in Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-(1 / 64 : ℝ) * x ^ (4 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have : x ^ (4 : ℝ) = x ^ 4 := by exact_mod_cast Real.rpow_natCast x 4
    rw [Real.rpow_one, this]
    congr 2
    ring
  rw [e, h]
  have e1 : (1 / 64 : ℝ) = (8 : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  have e2 : (1 / 64 : ℝ) ^ (-(1 + 1) / 4 : ℝ) = 8 := by
    rw [e1, ← Real.rpow_mul (by norm_num)]
    norm_num
  have e3 : ((1 : ℝ) + 1) / 4 = 1 / 2 := by norm_num
  rw [e2, e3, Real.Gamma_one_half_eq]
  ring

theorem crit_radial_three :
    ∫ r in Ioi (0 : ℝ), r * (Real.exp (-(r ^ 4 / 64)) * (r ^ 2 / 4)) = 4 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 4) (q := 3) (b := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∫ r in Ioi (0 : ℝ), r * (Real.exp (-(r ^ 4 / 64)) * (r ^ 2 / 4)) =
      (1 / 4) * ∫ x in Ioi (0 : ℝ), x ^ (3 : ℝ) * Real.exp (-(1 / 64 : ℝ) * x ^ (4 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have h4 : x ^ (4 : ℝ) = x ^ 4 := by exact_mod_cast Real.rpow_natCast x 4
    have h3 : x ^ (3 : ℝ) = x ^ 3 := by exact_mod_cast Real.rpow_natCast x 3
    simp only [h4, h3]
    have : -(1 / 64 : ℝ) * x ^ 4 = -(x ^ 4 / 64) := by ring
    rw [this]
    ring
  rw [e, h]
  have e2 : (1 / 64 : ℝ) ^ (-(3 + 1) / 4 : ℝ) = 64 := by
    have : (-(3 + 1) / 4 : ℝ) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
    norm_num
  have e3 : ((3 : ℝ) + 1) / 4 = 1 := by norm_num
  rw [e2, e3, Real.Gamma_one]
  norm_num

theorem crit_radial_means :
    (∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-(‖y‖ ^ 4 / 64)) * (‖y‖ ^ 2 / 4)) /
      ∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-(‖y‖ ^ 4 / 64)) = 2 / Real.sqrt Real.pi := by
  have hZ := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun r : ℝ => Real.exp (-(r ^ 4 / 64)))
  have hM := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun r : ℝ => Real.exp (-(r ^ 4 / 64)) * (r ^ 2 / 4))
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, pow_one, Nat.add_one_sub_one] at hZ hM
  have hV : 0 < (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [hM, hZ, crit_radial_one, crit_radial_three]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  field_simp
  norm_num

/-! ### The Bessel ratio through the series ratio `critR` -/

theorem critR_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ critR s := by
  have hA : 0 ≤ critA s := (hasSum_critA s hs).nonneg fun j => by positivity
  exact div_nonneg hA (critQ_pos s hs).le

theorem critR_le_one (s : ℝ) (hs : 0 ≤ s) : critR s ≤ 1 := by
  have h := critQ_sub_critA_ge s hs
  unfold critR
  rw [div_le_one (critQ_pos s hs)]
  linarith

theorem critR_zero : critR 0 = 1 := by
  have hQ : critQ 0 = 1 := by
    unfold critQ
    rw [tsum_eq_single 0]
    · simp
    · intro j hj
      simp [hj]
  have hA : critA 0 = 1 := by
    rw [(hasSum_critA 0 le_rfl).tsum_eq.symm, tsum_eq_single 0]
    · simp
    · intro j hj
      simp [hj]
  unfold critR
  rw [hQ, hA]
  norm_num

theorem critR_measurable : Measurable critR :=
  critA_contDiff.continuous.measurable.div critQ_contDiff.continuous.measurable

theorem critR_continuousAt_zero : ContinuousAt critR 0 :=
  (critR_differentiableAt 0 le_rfl).continuousAt

theorem besselRatio_eq (t : ℝ) (ht : 0 ≤ t) : besselRatio t = t / 2 * critR (t ^ 2 / 4) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have := DGPS.Circle.BesselMoments.besselRatio_neg 0
    rw [neg_zero] at this
    simp only [zero_div, zero_mul]
    linarith
  · have hs : 0 < t ^ 2 / 4 := by positivity
    have h := critR_ratio (t ^ 2 / 4) hs
    have hsq : Real.sqrt (t ^ 2 / 4) = t / 2 := by
      rw [show t ^ 2 / 4 = (t / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [hsq] at h
    have e : 2 * (t / 2) = t := by ring
    rw [e] at h
    field_simp at h ⊢
    linarith

/-- the scaled integrand `√N g(N^{-1/4}|y|)²` rewritten through `critR` -/
noncomputable def critBesselScaled (N : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖y‖ ^ 2 / 4 * critR ((N ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 / 4) ^ 2

theorem critBesselScaled_transfer (N : ℝ) (hN : 1 ≤ N) (z : EuclideanSpace ℝ (Fin 2)) :
    critBesselScaled N ((N ^ (1 / 4 : ℝ)) • z) =
      Real.sqrt N * besselRatio ‖z‖ ^ 2 := by
  have hN0 : 0 < N := by linarith
  set a := N ^ (-(1 / 4 : ℝ)) with ha
  set t := N ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have hat : a * t = 1 := by
    rw [ha, ht, ← Real.rpow_add hN0]
    norm_num
  have ht2 : t ^ 2 = Real.sqrt N := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow]
    norm_num
  unfold critBesselScaled
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, besselRatio_eq _ (norm_nonneg z)]
  have e : a ^ 2 * (t * ‖z‖) ^ 2 / 4 = ‖z‖ ^ 2 / 4 := by
    calc a ^ 2 * (t * ‖z‖) ^ 2 / 4 = (a * t) ^ 2 * ‖z‖ ^ 2 / 4 := by ring
      _ = ‖z‖ ^ 2 / 4 := by rw [hat]; ring
  rw [e, ← ht2]
  ring

theorem critBesselScaled_measurable (N : ℝ) : Measurable (critBesselScaled N) := by
  unfold critBesselScaled
  have : Measurable fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ := measurable_norm
  exact (this.pow_const 2 |>.div_const 4).mul
    ((critR_measurable.comp ((measurable_const.mul (this.pow_const 2)).div_const 4)).pow_const 2)

theorem critBesselScaled_bound (N : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    |critBesselScaled N y| ≤ 1 * (1 + ‖y‖) ^ 2 := by
  unfold critBesselScaled
  have hs : 0 ≤ (N ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 / 4 := by positivity
  have h1 := critR_nonneg _ hs
  have h2 := critR_le_one _ hs
  have h3 : critR ((N ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 / 4) ^ 2 ≤ 1 := by nlinarith
  have h4 : 0 ≤ critR ((N ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 / 4) ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (by positivity)]
  have hy := norm_nonneg y
  calc ‖y‖ ^ 2 / 4 * critR ((N ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 / 4) ^ 2
      ≤ ‖y‖ ^ 2 / 4 * 1 := by gcongr
    _ ≤ 1 * (1 + ‖y‖) ^ 2 := by nlinarith

theorem critBesselScaled_tendsto {ι : Type*} {l : Filter ι} (N : ι → ℝ)
    (hN : Tendsto N l atTop) (y : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n => critBesselScaled (N n) y) l (𝓝 (‖y‖ ^ 2 / 4)) := by
  have ha := critScale_tendsto N hN
  have h1 : Tendsto (fun n => (N n ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 / 4) l (𝓝 0) := by
    have := (((ha.pow 2).mul_const (‖y‖ ^ 2)).div_const 4)
    simpa using this
  have h2 : Tendsto (fun n => critR ((N n ^ (-(1 / 4 : ℝ))) ^ 2 * ‖y‖ ^ 2 / 4)) l (𝓝 1) := by
    have := critR_continuousAt_zero.tendsto.comp h1
    rwa [critR_zero] at this
  have := (h2.pow 2).const_mul (‖y‖ ^ 2 / 4)
  simpa [critBesselScaled] using this

theorem pnat_cast_tendsto : Tendsto (fun N : ℕ+ => (N : ℝ)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨⟨⌈b⌉₊ + 1, Nat.succ_pos _⟩, fun N hN => ?_⟩
  have h1 : ((⌈b⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    have : ⌈b⌉₊ + 1 ≤ (N : ℕ) := hN
    exact_mod_cast this
  have h2 : b ≤ ⌈b⌉₊ := Nat.le_ceil b
  push_cast at h1
  linarith

/-! ### Main limit statements -/

theorem critical_moment_convergence (f : EuclideanSpace ℝ (Fin 2) → ℝ) (hf : Continuous f)
    (C : ℝ) (k : ℕ) (hb : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) :
    Tendsto (fun N : ℕ+ =>
        ∫ z, f (((N : ℝ) ^ (1 / 4 : ℝ)) • z) ∂criticalAuxiliaryLaw (N : ℝ)) atTop
      (𝓝 (∫ y, f y ∂criticalScaledLimitLaw)) := by
  have hN := pnat_cast_tendsto
  have h := critGibbs_tendsto (fun N : ℕ+ => (N : ℝ)) hN (fun _ => f) f
    (fun _ => hf.measurable) C k (fun _ y => hb y) (fun y => tendsto_const_nhds)
  refine h.congr fun N => ?_
  exact (critTransfer (N : ℝ) (by exact_mod_cast N.pos) f).symm

theorem critical_bessel_limit :
    Tendsto (fun N : ℕ+ => Real.sqrt (N : ℝ) * ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ))
      atTop (𝓝 (2 / Real.sqrt Real.pi)) := by
  have hN := pnat_cast_tendsto
  have h := critGibbs_tendsto (fun N : ℕ+ => (N : ℝ)) hN (fun N => critBesselScaled (N : ℝ))
    (fun y => ‖y‖ ^ 2 / 4) (fun N => critBesselScaled_measurable _) 1 2
    (fun N y => critBesselScaled_bound _ y) (fun y => critBesselScaled_tendsto _ hN y)
  have hq := Tools.StrongConvexityBobkovLedoux.integral_gibbs
    (critLimit_continuous.measurable) (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2 / 4)
  have hlim : ∫ y, ‖y‖ ^ 2 / 4 ∂criticalScaledLimitLaw = 2 / Real.sqrt Real.pi := by
    unfold criticalScaledLimitLaw
    rw [hq]
    exact crit_radial_means
  rw [hlim] at h
  refine h.congr fun N => ?_
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  rw [← critTransfer (N : ℝ) hN1 (critBesselScaled (N : ℝ))]
  simp_rw [critBesselScaled_transfer (N : ℝ) hN1]
  rw [integral_const_mul]

theorem crit_variance_identity (x I : ℝ) (hx : 0 < x) :
    (x / 2 * (1 + (x - 1) * I)) / x ^ (3 / 2 : ℝ) =
      1 / (2 * Real.sqrt x) + (x - 1) / x / 2 * (Real.sqrt x * I) := by
  have h32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hsq := Real.sq_sqrt hx.le
  have hsp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  rw [h32]
  field_simp
  rw [hsq]
  ring

theorem critical_variance_limit :
    Tendsto (fun N : ℕ+ => ((N : ℝ) / 2 * (1 + ((N : ℝ) - 1) *
        ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ))) / (N : ℝ) ^ (3 / 2 : ℝ))
      atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
  have hN := pnat_cast_tendsto
  have hJ := critical_bessel_limit
  have hs : Tendsto (fun N : ℕ+ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have h1 : Tendsto (fun N : ℕ+ => 1 / (2 * Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (hs.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)))
    simpa [Function.comp_def, one_div] using this
  have h2 : Tendsto (fun N : ℕ+ => ((N : ℝ) - 1) / (N : ℝ) / 2) atTop (𝓝 (1 / 2)) := by
    have hinv : Tendsto (fun N : ℕ+ => (N : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).div_const 2
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hN.eventually_ge_atTop 1] with N hN1
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have h3 := h1.add (h2.mul hJ)
  have e : (0 : ℝ) + 1 / 2 * (2 / Real.sqrt Real.pi) = 1 / Real.sqrt Real.pi := by ring
  rw [e] at h3
  refine h3.congr fun N => ?_
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  exact (crit_variance_identity (N : ℝ) _ hN0).symm

theorem criticalScaledLimitLaw_isProbabilityMeasure : IsProbabilityMeasure criticalScaledLimitLaw :=
  Tools.StrongConvexityLSI.gibbs_isProbabilityMeasure
    (critExp_integrable critLimit_continuous (1 / 64) (by norm_num) critLimit_lower)

/-- **FIN032 (critical scaled moment limit).**  Under the critical auxiliary law `η_N`, the rescaled
variable `N^{1/4} z` converges, with all polynomial moments, to the probability measure on `ℝ²`
proportional to `exp(-|y|⁴/64)` (`criticalScaledLimitLaw`): for every continuous `f` of polynomial
growth, `∫ f(N^{1/4} z) dη_N → ∫ f dμ_∞`.  In particular `√N ∫ g(|z|)² dη_N → 2/√π`
(the limit law has mean `|y|²/4` equal to `2/√π`) and, for the critical XY model, the variance of
the first-harmonic magnetization satisfies `Var(F)/N^{3/2} → 1/√π`. -/
theorem critical_scaled_moment_limit :
    IsProbabilityMeasure criticalScaledLimitLaw ∧
    (∀ f : EuclideanSpace ℝ (Fin 2) → ℝ, Continuous f → ∀ (C : ℝ) (k : ℕ),
      (∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) →
      Tendsto (fun N : ℕ+ =>
          ∫ z, f (((N : ℝ) ^ (1 / 4 : ℝ)) • z) ∂criticalAuxiliaryLaw (N : ℝ)) atTop
        (𝓝 (∫ y, f y ∂criticalScaledLimitLaw))) ∧
    ∫ y, ‖y‖ ^ 2 / 4 ∂criticalScaledLimitLaw = 2 / Real.sqrt Real.pi ∧
    Tendsto (fun N : ℕ+ =>
        Real.sqrt (N : ℝ) * ∫ z, besselRatio ‖z‖ ^ 2 ∂criticalAuxiliaryLaw (N : ℝ)) atTop
      (𝓝 (2 / Real.sqrt Real.pi)) ∧
    (∀ {A : DGPS.InteractionData 1}, IsCriticalXY A → ∀ F : (N : ℕ+) → DGPS.ParticleH1 A N,
      (∀ N, (F N).1 = fun x : DGPS.ParticleSpace 1 N => ∑ i, (mode 1 (x i)).re) →
      Tendsto (fun N : ℕ+ =>
          ProbabilityTheory.variance (F N).1 (DGPS.particleLaw A N) / (N : ℝ) ^ (3 / 2 : ℝ))
        atTop (𝓝 (1 / Real.sqrt Real.pi))) := by
  refine ⟨criticalScaledLimitLaw_isProbabilityMeasure, ?_, ?_, critical_bessel_limit, ?_⟩
  · intro f hf C k hb
    exact critical_moment_convergence f hf C k hb
  · have hq := Tools.StrongConvexityBobkovLedoux.integral_gibbs
      (critLimit_continuous.measurable) (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2 / 4)
    unfold criticalScaledLimitLaw
    rw [hq]
    exact crit_radial_means
  · intro A hA F hF
    refine critical_variance_limit.congr fun N => ?_
    obtain ⟨f, hf1, -, -, -, -, hvar, -⟩ := rotational_symmetric_magnetization_variance_critical hA N
    rw [hF N, ← hf1, hvar]

end DGPS.FiniteN
