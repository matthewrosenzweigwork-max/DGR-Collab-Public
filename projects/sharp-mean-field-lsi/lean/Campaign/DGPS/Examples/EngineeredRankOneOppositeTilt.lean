import DGPS.Examples.EngineeredRankOneNormalization
import DGPS.Examples.EngineeredRankOneGap
import DGPS.Examples.EngineeredRankOneDrift
import DGPS.Examples.EngineeredRankOneEndpoints
import DGPS.Circle.BesselMoments
import DGPS.Structural.SmallRateCircle

/-!
# Engineered opposite-tilt one-site upper bound (EX048)

For the engineered rank-one reference `μ_h` and the opposite von Mises density
`ρ_h = exp(-h cos θ)/I₀(h)`, we prove `H(ρ_h | μ_h) = 2 h g(h) + O(log h)` and
`I(ρ_h | μ_h) / a0 = 4 h g(h) + O(1)` (with `g = I₁/I₀`), hence
`r_LS(μ_h) / a0 ≤ 1 + C log h / h` for large `h`.
-/

open MeasureTheory Real Set Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples.EngineeredRankOneOppositeTilt

theorem angCos_eq (θ : AngCircle) : angCos θ = Real.Angle.cos θ := by
  induction θ using Real.Angle.induction_on with
  | _ t => rw [Real.Angle.cos_coe]; exact (angMode_coe 1 t).trans (by simp)

theorem Uang_eq (θ : AngCircle) : Uang θ = 1 - angCos θ := by
  rw [angCos_eq]; rfl

/-- `∫ exp(-hU) dm`. -/
noncomputable def Sh (h : ℝ) : ℝ := ∫ θ, exp (-(h * Uang θ)) ∂angHaar

theorem besselI_zero_eq (h : ℝ) : besselI 0 h = exp h * Sh h := by
  rw [besselI_zero, Sh, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [pow_zero, mul_one, Uang_eq]
  rw [← Real.exp_add]; congr 1; ring

theorem besselI_zero_neg (h : ℝ) : besselI 0 (-h) = exp h * Sh h := by
  rw [besselI_neg]; simp [besselI_zero_eq]

theorem Sh_pos (h : ℝ) : 0 < Sh h := by
  have := besselI_zero_pos h
  rw [besselI_zero_eq] at this
  exact (mul_pos_iff_of_pos_left (exp_pos h)).1 this


theorem continuous_angCos : Continuous angCos := continuous_angMode 1

theorem integrable_of_cont {f : AngCircle → ℝ} (hf : Continuous f) : Integrable f angHaar :=
  integrable_angHaar_of_continuous hf

theorem integral_besselDensity (t : ℝ) : ∫ θ, besselDensity t θ ∂angHaar = 1 := by
  unfold besselDensity
  rw [integral_div]
  have : ∫ θ, exp (t * angCos θ) ∂angHaar = besselI 0 t := by
    rw [besselI_zero]; simp
  rw [this]
  exact div_self (besselI_zero_pos t).ne'

theorem integral_cos_density (h : ℝ) :
    ∫ θ, angCos θ * besselDensity (-h) θ ∂angHaar = -besselRatio h := by
  rw [← besselRatio_eq_mean, besselRatio_neg]

/-- Integration by parts: `t ∫ e^{t cos} (1 - cos²) = I₁(t)`. -/
theorem besselI_one_eq_ibp (t : ℝ) :
    besselI 1 t = t * ∫ θ, exp (t * angCos θ) * (1 - angCos θ ^ 2) ∂angHaar := by
  have h1 : besselI 1 t = (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, exp (t * Real.cos s) * Real.cos s := by
    rw [besselI_eq_interval]; simp
  have h2 : ∫ θ, exp (t * angCos θ) * (1 - angCos θ ^ 2) ∂angHaar =
      (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, exp (t * Real.cos s) * Real.sin s ^ 2 := by
    apply integral_ang
    intro s
    have : angCos (s : AngCircle) = Real.cos s := by
      exact (angMode_coe 1 s).trans (by simp)
    rw [this]
    have := Real.sin_sq_add_cos_sq s
    congr 1; linarith
  have hd : ∀ s : ℝ, HasDerivAt (fun s => Real.sin s * exp (t * Real.cos s))
      (Real.cos s * exp (t * Real.cos s) +
        Real.sin s * (exp (t * Real.cos s) * (t * -Real.sin s))) s := by
    intro s
    have h3 : HasDerivAt (fun s => exp (t * Real.cos s)) (exp (t * Real.cos s) * (t * -Real.sin s)) s :=
      ((Real.hasDerivAt_cos s).const_mul t).exp
    exact (Real.hasDerivAt_sin s).mul h3
  have hi : ∫ s in (0:ℝ)..2 * π, (Real.cos s * exp (t * Real.cos s) +
        Real.sin s * (exp (t * Real.cos s) * (t * -Real.sin s))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)]
    · simp
    · exact (by fun_prop : Continuous fun s : ℝ => Real.cos s * exp (t * Real.cos s) +
        Real.sin s * (exp (t * Real.cos s) * (t * -Real.sin s))).intervalIntegrable _ _
  have hsplit : ∫ s in (0:ℝ)..2 * π, (Real.cos s * exp (t * Real.cos s) +
        Real.sin s * (exp (t * Real.cos s) * (t * -Real.sin s))) =
      (∫ s in (0:ℝ)..2 * π, exp (t * Real.cos s) * Real.cos s) -
        t * ∫ s in (0:ℝ)..2 * π, exp (t * Real.cos s) * Real.sin s ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    · exact (by fun_prop : Continuous fun s : ℝ => exp (t * Real.cos s) * Real.cos s).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s : ℝ => t * (exp (t * Real.cos s) * Real.sin s ^ 2)).intervalIntegrable _ _
  rw [h1, h2]
  rw [hsplit] at hi
  have : ∫ s in (0:ℝ)..2 * π, exp (t * Real.cos s) * Real.cos s =
      t * ∫ s in (0:ℝ)..2 * π, exp (t * Real.cos s) * Real.sin s ^ 2 := by linarith
  rw [this]; ring

theorem integral_sin_sq_density (h : ℝ) (hh : 0 < h) :
    ∫ θ, (1 - angCos θ ^ 2) * besselDensity (-h) θ ∂angHaar = besselRatio h / h := by
  have h0 := besselI_zero_pos h
  have e : ∀ θ : AngCircle, (1 - angCos θ ^ 2) * besselDensity (-h) θ =
      (besselI 0 (-h))⁻¹ * (exp (-h * angCos θ) * (1 - angCos θ ^ 2)) := by
    intro θ; unfold besselDensity; field_simp
  simp_rw [e]
  rw [integral_const_mul]
  have := besselI_one_eq_ibp (-h)
  rw [besselI_neg] at this
  have hI : ∫ θ, exp (-h * angCos θ) * (1 - angCos θ ^ 2) ∂angHaar = besselI 1 h / h := by
    rw [eq_div_iff hh.ne']
    rw [pow_one] at this
    linarith
  rw [hI, besselI_neg]
  unfold besselRatio
  simp only [pow_zero, one_mul]
  field_simp

theorem continuous_Sh_integrand (h : ℝ) : Continuous fun θ : AngCircle => exp (-(h * Uang θ)) :=
  (continuous_const.mul continuous_Uang).neg.rexp

theorem one_sub_ratio (h : ℝ) :
    1 - besselRatio h = (∫ θ, exp (-(h * Uang θ)) * Uang θ ∂angHaar) / Sh h := by
  have hS := Sh_pos h
  have hc1 : Continuous fun θ : AngCircle => exp (-(h * Uang θ)) := continuous_Sh_integrand h
  have hc2 : Continuous fun θ : AngCircle => exp (-(h * Uang θ)) * Uang θ :=
    hc1.mul continuous_Uang
  have hI1 : besselI 1 h = exp h * (Sh h - ∫ θ, exp (-(h * Uang θ)) * Uang θ ∂angHaar) := by
    rw [besselI_one, Sh, ← integral_sub (integrable_of_cont hc1) (integrable_of_cont hc2),
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [pow_one, Uang_eq]
    rw [show exp (h * angCos θ) = exp h * exp (-(h * (1 - angCos θ))) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  unfold besselRatio
  rw [hI1, besselI_zero_eq]
  have := (exp_pos h).ne'
  field_simp
  ring

theorem exp_mul_Uang_le (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    exp (-(h * Uang θ)) * Uang θ ≤ (2 / h) * exp (-((h / 2) * Uang θ)) := by
  have hU := (Uang_mem θ).1
  set x : ℝ := (h / 2) * Uang θ with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : x * exp (-x) ≤ 1 := by
    have := Real.add_one_le_exp x
    calc x * exp (-x) ≤ exp x * exp (-x) := by
          gcongr; linarith
      _ = 1 := by rw [← Real.exp_add]; simp
  have e : exp (-(h * Uang θ)) = exp (-x) * exp (-x) := by
    rw [← Real.exp_add]; congr 1; rw [hx]; ring
  have e2 : Uang θ = (2 / h) * x := by rw [hx]; field_simp
  rw [e]
  calc exp (-x) * exp (-x) * Uang θ = (2 / h) * exp (-x) * (x * exp (-x)) := by rw [e2]; ring
    _ ≤ (2 / h) * exp (-x) * 1 := by gcongr
    _ = _ := by ring

theorem one_sub_ratio_le : ∃ K : ℝ, 0 < K ∧ ∀ h : ℝ, 2 ≤ h → 1 - besselRatio h ≤ K / h := by
  have hpi := Real.pi_pos
  set K0 : ℝ := (2 * π)⁻¹ * √(π / (2 / π ^ 2)) with hK0
  set cz : ℝ := exp (-16) / π with hcz
  have hK0p : 0 < K0 := by
    rw [hK0]; positivity
  have hczp : 0 < cz := by rw [hcz]; positivity
  refine ⟨2 * √2 * K0 / cz, by positivity, fun h hh => ?_⟩
  have hp : 0 < h := by linarith
  have hsh : 0 < √h := Real.sqrt_pos.2 hp
  set a : ℝ := (√h)⁻¹ with ha
  have hap : 0 < a := inv_pos.2 hsh
  have hS : cz * a ≤ Sh h := (Zh_ge h hh).trans (Zh_le_integral h hp)
  have hSp := Sh_pos h
  have hT : ∫ θ, exp (-(h * Uang θ)) * Uang θ ∂angHaar ≤ (2 / h) * (K0 * √2 * a) := by
    calc ∫ θ, exp (-(h * Uang θ)) * Uang θ ∂angHaar
        ≤ ∫ θ, (2 / h) * exp (-((h / 2) * Uang θ)) ∂angHaar :=
          integral_mono (integrable_of_cont ((continuous_Sh_integrand h).mul continuous_Uang))
            (integrable_of_cont (continuous_const.mul (continuous_Sh_integrand (h / 2))))
            (fun θ => exp_mul_Uang_le h hp θ)
      _ = (2 / h) * Sh (h / 2) := by rw [integral_const_mul]; rfl
      _ ≤ (2 / h) * (K0 * (√(h / 2))⁻¹) := by
          gcongr
          exact integral_exp_neg_Uang_le_sqrt (h / 2) (by linarith)
      _ = (2 / h) * (K0 * √2 * a) := by
          congr 1
          rw [Real.sqrt_div hp.le, ha]
          have : √2 ≠ 0 := by positivity
          field_simp
  have hTnn : 0 ≤ ∫ θ, exp (-(h * Uang θ)) * Uang θ ∂angHaar :=
    integral_nonneg fun θ => mul_nonneg (exp_pos _).le (Uang_mem θ).1
  rw [one_sub_ratio]
  calc (∫ θ, exp (-(h * Uang θ)) * Uang θ ∂angHaar) / Sh h
      ≤ ((2 / h) * (K0 * √2 * a)) / (cz * a) :=
        div_le_div₀ (by positivity) hT (by positivity) hS
    _ = 2 * √2 * K0 / cz / h := by field_simp


/-! ### The opposite von Mises density as an absolute-admissible density -/

theorem angCos_coe (t : ℝ) : angCos ((t : ℝ) : AngCircle) = Real.cos t :=
  (angMode_coe 1 t).trans (by simp)

theorem continuous_besselDensity (t : ℝ) : Continuous (besselDensity t) := by
  unfold besselDensity
  exact (continuous_const.mul continuous_angCos).rexp.div_const _

/-- Square root of the opposite von Mises density `exp(-h cos θ)/I₀(h)`. -/
noncomputable def uAng (h : ℝ) (θ : AngCircle) : ℝ :=
  exp (-(h / 2) * angCos θ) / √(besselI 0 (-h))

theorem uAng_pos (h : ℝ) (θ : AngCircle) : 0 < uAng h θ := by
  unfold uAng
  have := besselI_zero_pos (-h)
  positivity

theorem uAng_sq (h : ℝ) (θ : AngCircle) : uAng h θ ^ 2 = besselDensity (-h) θ := by
  unfold uAng besselDensity
  rw [div_pow, Real.sq_sqrt (besselI_zero_pos (-h)).le, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem uAng_coe (h t : ℝ) : uAng h ((t : ℝ) : AngCircle) =
    exp (-(h / 2) * Real.cos t) / √(besselI 0 (-h)) := by
  unfold uAng; rw [angCos_coe]

theorem isSmoothAngular_uAng (h : ℝ) : IsSmoothAngular (uAng h) := by
  unfold IsSmoothAngular
  have : (fun s : ℝ => uAng h (s : AngCircle)) =
      fun s => exp (-(h / 2) * Real.cos s) / √(besselI 0 (-h)) := funext (uAng_coe h)
  rw [this]
  exact (Real.contDiff_exp.comp (contDiff_const.mul Real.contDiff_cos)).div_const _

theorem hasDerivAt_uAng (h t : ℝ) :
    HasDerivAt (fun s : ℝ => uAng h (s : AngCircle))
      ((h / 2) * Real.Angle.sin ((t : ℝ) : AngCircle) * uAng h ((t : ℝ) : AngCircle)) t := by
  have : (fun s : ℝ => uAng h (s : AngCircle)) =
      fun s => exp (-(h / 2) * Real.cos s) / √(besselI 0 (-h)) := funext (uAng_coe h)
  rw [this, uAng_coe]
  have e : Real.Angle.sin ((t : ℝ) : AngCircle) = Real.sin t := Real.Angle.sin_coe t
  rw [e]
  have h1 : HasDerivAt (fun s : ℝ => exp (-(h / 2) * Real.cos s))
      (exp (-(h / 2) * Real.cos t) * (-(h / 2) * -Real.sin t)) t :=
    ((Real.hasDerivAt_cos t).const_mul (-(h / 2))).exp
  convert h1.div_const (√(besselI 0 (-h))) using 1
  ring

/-- The opposite von Mises density `ρ_h ∝ exp(-h cos θ)` as an absolute-admissible density on the
period-one torus. -/
noncomputable def oppositeDensity (h : ℝ) : AbsoluteDensity 1 where
  sqrt := fun x => uAng h (angEquiv x)
  sqrt_mem := ⟨_, ((isSmoothPeriodic_comp_iff (uAng h)).2 (isSmoothAngular_uAng h)).isWeakGradient⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun x => (uAng_pos h _).le
  mass_one := by
    refine (integral_comp_angEquiv (fun θ => uAng h θ ^ 2)).trans ?_
    simp only [uAng_sq]
    exact integral_besselDensity _

theorem oppositeDensity_density (h : ℝ) (x : Torus 1) :
    (oppositeDensity h).density x = besselDensity (-h) (angEquiv x) := uAng_sq h _

theorem integral_opposite (h : ℝ) (f : AngCircle → ℝ) :
    ∫ x, (oppositeDensity h).density x * f (angEquiv x) ∂haar 1 =
      ∫ θ, besselDensity (-h) θ * f θ ∂angHaar := by
  simp_rw [oppositeDensity_density]
  exact integral_comp_angEquiv (fun θ => besselDensity (-h) θ * f θ)

theorem besselDensity_neg_eq (h : ℝ) (θ : AngCircle) :
    besselDensity (-h) θ = exp (-(h * angCos θ)) / besselI 0 h := by
  unfold besselDensity
  rw [besselI_neg]; simp


/-! ### Elementary expectations against the opposite density -/

theorem integral_p_Uang (h : ℝ) :
    ∫ θ, besselDensity (-h) θ * Uang θ ∂angHaar = 1 + besselRatio h := by
  have e : ∀ θ, besselDensity (-h) θ * Uang θ =
      besselDensity (-h) θ - angCos θ * besselDensity (-h) θ := by
    intro θ; rw [Uang_eq]; ring
  simp_rw [e]
  have i1 : Integrable (fun θ => besselDensity (-h) θ) angHaar :=
    integrable_of_cont (continuous_besselDensity _)
  have i2 : Integrable (fun θ => angCos θ * besselDensity (-h) θ) angHaar :=
    integrable_of_cont (continuous_angCos.mul (continuous_besselDensity _))
  rw [integral_sub i1 i2, integral_besselDensity, integral_cos_density]
  ring

/-- `E_ρ[R_h(U)]`. -/
noncomputable def Ecorr (h : ℝ) : ℝ :=
  ∫ θ, besselDensity (-h) θ * corr h (Uang θ) ∂angHaar

theorem entropy_haar (h : ℝ) :
    (relativeEntropy (densityMeasure (oppositeDensity h) : Measure (Torus 1)) (haar 1)).toReal =
      h * besselRatio h - Real.log (besselI 0 h) := by
  rw [(absoluteDensity_entropy_finite (oppositeDensity h)).2.2.2]
  have e1 : ∫ x, (oppositeDensity h).density x * Real.log ((oppositeDensity h).density x) ∂haar 1 =
      ∫ x, (oppositeDensity h).density x * Real.log (besselDensity (-h) (angEquiv x)) ∂haar 1 := by
    simp only [oppositeDensity_density]
  rw [e1, integral_opposite h (fun θ => Real.log (besselDensity (-h) θ))]
  have hlog : ∀ θ, besselDensity (-h) θ * Real.log (besselDensity (-h) θ) =
      (-h) * (angCos θ * besselDensity (-h) θ) - Real.log (besselI 0 h) * besselDensity (-h) θ := by
    intro θ
    rw [besselDensity_neg_eq, Real.log_div (exp_pos _).ne' (besselI_zero_pos h).ne', Real.log_exp]
    ring
  simp_rw [hlog]
  have i1 : Integrable (fun θ => angCos θ * besselDensity (-h) θ) angHaar :=
    integrable_of_cont (continuous_angCos.mul (continuous_besselDensity _))
  have i2 : Integrable (fun θ => besselDensity (-h) θ) angHaar :=
    integrable_of_cont (continuous_besselDensity _)
  rw [integral_sub (i1.const_mul (-h)) (i2.const_mul (Real.log (besselI 0 h))), integral_const_mul,
    integral_const_mul, integral_besselDensity, integral_cos_density]
  ring

theorem entropy_formula (h : ℝ) (hh : 2 ≤ h) :
    relativeEntropy (densityMeasure (oppositeDensity h) : Measure (Torus 1))
        (DGPS.Models.engineeredModel h hh).ref.measure ≠ ⊤ ∧
    (relativeEntropy (densityMeasure (oppositeDensity h) : Measure (Torus 1))
        (DGPS.Models.engineeredModel h hh).ref.measure).toReal =
      2 * h * besselRatio h + Ecorr h + Real.log (Zh h) - Real.log (Sh h) := by
  have hp : 0 < h := by linarith
  have hfin := (absoluteDensity_entropy_finite (oppositeDensity h)).2.2.1
  refine ⟨((DGPS.Models.engineeredModel h hh).free_energy_identity _ hfin).1, ?_⟩
  rw [(DGPS.Models.engineeredModel h hh).entropy_ref_eq _ hfin, entropy_haar,
    DGPS.PositiveRankOne.RankOneModel.integral_densityMeasure]
  have e2 : ∫ x, (oppositeDensity h).density x * Real.log ((DGPS.Models.engineeredModel h hh).q x) ∂haar 1 =
      ∫ θ, besselDensity (-h) θ * Real.log (qAng h θ) ∂angHaar :=
    integral_opposite h (fun θ => Real.log (qAng h θ))
  rw [e2]
  have hlq : ∀ θ, besselDensity (-h) θ * Real.log (qAng h θ) =
      (-h) * (besselDensity (-h) θ * Uang θ) - besselDensity (-h) θ * corr h (Uang θ) -
        Real.log (Zh h) * besselDensity (-h) θ := by
    intro θ
    rw [log_qAng h hp]; unfold logq; ring
  simp_rw [hlq]
  have hc1 : Integrable (fun θ => besselDensity (-h) θ * Uang θ) angHaar :=
    integrable_of_cont ((continuous_besselDensity _).mul continuous_Uang)
  have hc2 : Integrable (fun θ => besselDensity (-h) θ * corr h (Uang θ)) angHaar :=
    integrable_of_cont ((continuous_besselDensity _).mul (continuous_corrU h hp))
  have hc3 : Integrable (fun θ => besselDensity (-h) θ) angHaar :=
    integrable_of_cont (continuous_besselDensity _)
  have hc12 : Integrable (fun θ => (-h) * (besselDensity (-h) θ * Uang θ) -
      besselDensity (-h) θ * corr h (Uang θ)) angHaar := (hc1.const_mul (-h)).sub hc2
  rw [integral_sub hc12 (hc3.const_mul (Real.log (Zh h))), integral_sub (hc1.const_mul (-h)) hc2,
    integral_const_mul, integral_const_mul, integral_p_Uang, integral_besselDensity]
  have hI : Real.log (besselI 0 h) = h + Real.log (Sh h) := by
    rw [besselI_zero_eq, Real.log_mul (exp_pos h).ne' (Sh_pos h).ne', Real.log_exp]
  rw [hI]
  unfold Ecorr
  ring


/-! ### Entropy bounds -/

theorem besselDensity_nonneg (t : ℝ) (θ : AngCircle) : 0 ≤ besselDensity t θ :=
  div_nonneg (exp_pos _).le (besselI_zero_pos _).le

theorem corr_le (h : ℝ) (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    corr h u ≤ 14 + Real.log (1 + 2 * h) := by
  have hb := (exp_corr_bounds hh hu).2
  have h1 : 1 + h * u ≤ 1 + 2 * h := by nlinarith [hu.2]
  have hpos : 0 < 1 + 2 * h := by linarith
  have : exp (corr h u) ≤ exp (14 + Real.log (1 + 2 * h)) := by
    rw [Real.exp_add, Real.exp_log hpos]
    calc exp (corr h u) ≤ exp 14 * (1 + h * u) := hb
      _ ≤ exp 14 * (1 + 2 * h) := by gcongr
  exact Real.exp_le_exp.1 this

theorem Ecorr_nonneg (h : ℝ) (hh : 2 ≤ h) : 0 ≤ Ecorr h :=
  integral_nonneg fun θ => mul_nonneg (besselDensity_nonneg _ _)
    (corr_nonneg h (by linarith) (Uang_mem θ))

theorem Ecorr_le (h : ℝ) (hh : 2 ≤ h) : Ecorr h ≤ 14 + Real.log (1 + 2 * h) := by
  have hp : 0 < h := by linarith
  calc Ecorr h ≤ ∫ θ, besselDensity (-h) θ * (14 + Real.log (1 + 2 * h)) ∂angHaar := by
        refine integral_mono (integrable_of_cont ((continuous_besselDensity _).mul
          (continuous_corrU h hp))) (integrable_of_cont ((continuous_besselDensity _).mul
          continuous_const)) fun θ => ?_
        exact mul_le_mul_of_nonneg_left (corr_le h hh (Uang_mem θ)) (besselDensity_nonneg _ _)
    _ = 14 + Real.log (1 + 2 * h) := by
        rw [integral_mul_const, integral_besselDensity, one_mul]

theorem logZ_sub_logS_le (h : ℝ) (hh : 2 ≤ h) : Real.log (Zh h) - Real.log (Sh h) ≤ 0 := by
  have hp : 0 < h := by linarith
  have := Real.log_le_log (Zh_pos h hp) (Zh_le_integral h hp)
  change Real.log (Zh h) ≤ Real.log (Sh h) at this
  linarith

theorem logZ_sub_logS_ge (h : ℝ) (hh : 2 ≤ h) :
    -(14 + Real.log (1 + 2 * h)) ≤ Real.log (Zh h) - Real.log (Sh h) := by
  have hp : 0 < h := by linarith
  set A : ℝ := 14 + Real.log (1 + 2 * h) with hA
  have hZ : Sh h * exp (-A) ≤ Zh h := by
    calc Sh h * exp (-A) = ∫ θ, exp (-(h * Uang θ)) * exp (-A) ∂angHaar := by
          rw [integral_mul_const]; rfl
      _ ≤ ∫ θ, exp (logq h θ) ∂angHaar := by
          refine integral_mono (integrable_of_cont ((continuous_Sh_integrand h).mul
            continuous_const)) (integrable_of_cont (continuous_logq h hp).rexp) fun θ => ?_
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          unfold logq
          have := corr_le h hh (Uang_mem θ)
          linarith
  have h2 := Real.log_le_log (mul_pos (Sh_pos h) (exp_pos _)) hZ
  rw [Real.log_mul (Sh_pos h).ne' (exp_pos _).ne', Real.log_exp] at h2
  linarith

theorem entropy_bound (h : ℝ) (hh : 2 ≤ h) :
    |(relativeEntropy (densityMeasure (oppositeDensity h) : Measure (Torus 1))
        (DGPS.Models.engineeredModel h hh).ref.measure).toReal - 2 * h * besselRatio h| ≤
      14 + Real.log (1 + 2 * h) := by
  rw [(entropy_formula h hh).2, abs_le]
  have h1 := Ecorr_nonneg h hh
  have h2 := Ecorr_le h hh
  have h3 := logZ_sub_logS_le h hh
  have h4 := logZ_sub_logS_ge h hh
  constructor <;> linarith


/-! ### Fisher information -/

theorem sin_sq_eq (θ : AngCircle) : Real.Angle.sin θ ^ 2 = 1 - angCos θ ^ 2 := by
  rw [angCos_eq]
  induction θ using Real.Angle.induction_on with
  | _ t =>
    rw [Real.Angle.sin_coe, Real.Angle.cos_coe]
    have := Real.sin_sq_add_cos_sq t; linarith

theorem one_sub_cos_sq (θ : AngCircle) : 1 - angCos θ ^ 2 = Uang θ * (2 - Uang θ) := by
  rw [Uang_eq]; ring

/-- The Fisher integrand `sin²θ (2h + R_h'(U))²`. -/
noncomputable def Fang (h : ℝ) (θ : AngCircle) : ℝ :=
  (1 - angCos θ ^ 2) * (2 * h + integrand h (Uang θ)) ^ 2

/-- `E_ρ[sin²θ (2h + R_h'(U))²]`. -/
noncomputable def Jh (h : ℝ) : ℝ := ∫ θ, besselDensity (-h) θ * Fang h θ ∂angHaar

theorem continuous_Fang (h : ℝ) (hp : 0 < h) : Continuous (Fang h) := by
  unfold Fang
  exact (continuous_const.sub (continuous_angCos.pow 2)).mul
    ((continuous_const.add ((contDiff_integrand h hp).continuous.comp continuous_Uang)).pow 2)

theorem weakGrad_ae (h : ℝ) :
    (fun x => (weakGradient (oppositeDensity h).sqrt (oppositeDensity h).sqrt_mem x) 0) =ᵐ[haar 1]
      fun x => 2 * π * ((h / 2) * Real.Angle.sin (angEquiv x) * uAng h (angEquiv x)) := by
  have hs : IsSmoothPeriodic (fun x => uAng h (angEquiv x)) :=
    (isSmoothPeriodic_comp_iff (uAng h)).2 (isSmoothAngular_uAng h)
  have hw := isWeakGradient_weakGradient (oppositeDensity h).sqrt_mem
  have := hw.ae_eq hs.isWeakGradient
  filter_upwards [this] with x hx
  rw [hx, smoothGrad_apply]
  exact coordPartial_of (ψ := uAng h) (G := fun θ => (h / 2) * Real.Angle.sin θ * uAng h θ)
    (isSmoothAngular_uAng h) (hasDerivAt_uAng h) x

theorem fisher_formula (h : ℝ) (hh : 2 ≤ h) :
    ordinaryRelativeFisher (densityMeasure (oppositeDensity h) : Measure (Torus 1))
        (DGPS.Models.engineeredModel h hh).ref = ENNReal.ofReal (a0 * Jh h) := by
  rw [(DGPS.Models.engineeredModel h hh).fisher_eq (oppositeDensity h)]
  congr 1
  have key : ∀ᵐ x ∂haar 1,
      (2 * (weakGradient (oppositeDensity h).sqrt (oppositeDensity h).sqrt_mem x) 0 -
        (oppositeDensity h).sqrt x * (DGPS.Models.engineeredModel h hh).dlogq x) ^ 2 =
      a0 * ((oppositeDensity h).density x * Fang h (angEquiv x)) := by
    filter_upwards [weakGrad_ae h] with x hx
    have hsq : (oppositeDensity h).sqrt x = uAng h (angEquiv x) := rfl
    have hd : dlogqAng h (angEquiv x) =
        -(h + integrand h (Uang (angEquiv x))) * Real.Angle.sin (angEquiv x) := rfl
    rw [hx, hsq, DGPS.Examples.EngineeredRankOne.engineeredModel_dlogq, oppositeDensity_density,
      ← uAng_sq, hd]
    unfold Fang
    rw [← sin_sq_eq (angEquiv x)]
    unfold a0
    ring
  rw [integral_congr_ae key, integral_const_mul, integral_opposite h (Fang h)]
  rfl


/-! ### Fisher bounds -/

theorem Fang_bounds (h : ℝ) (hh : 2 ≤ h) (θ : AngCircle) :
    4 * h ^ 2 * (1 - angCos θ ^ 2) ≤ Fang h θ ∧
      Fang h θ ≤ 4 * h ^ 2 * (1 - angCos θ ^ 2) + 8 * h * (2 - Uang θ) := by
  have hp : 0 < h := by linarith
  have hU := Uang_mem θ
  have hN0 := numer_nonneg h hp hU
  have hN1 := numer_le_two_sub h hp hU
  have hR0 := integrand_nonneg h hp hU
  have hR1 := integrand_le h hh hU
  have ha := aH_le_four h hh
  have hR1' : integrand h (Uang θ) ≤ 4 * h := hR1.trans (by nlinarith)
  have e : Fang h θ = 4 * h ^ 2 * (1 - angCos θ ^ 2) + 4 * h * numer h (Uang θ) +
      integrand h (Uang θ) * numer h (Uang θ) := by
    have := integrand_mul h hp (Uang θ)
    unfold Fang
    rw [← this, one_sub_cos_sq]
    ring
  rw [e]
  have h1 := mul_nonneg hR0 hN0
  have h2 := mul_nonneg hp.le hN0
  have h3 := mul_le_mul_of_nonneg_right hR1' hN0
  have h4 := mul_le_mul_of_nonneg_left hN1 (by linarith : (0:ℝ) ≤ 8 * h)
  constructor <;> nlinarith

theorem Jh_bounds (h : ℝ) (hh : 2 ≤ h) :
    4 * h * besselRatio h ≤ Jh h ∧ Jh h ≤ 4 * h * besselRatio h + 8 * h * (1 - besselRatio h) := by
  have hp : 0 < h := by linarith
  have i_p : Integrable (fun θ => besselDensity (-h) θ) angHaar :=
    integrable_of_cont (continuous_besselDensity _)
  have i_a : Integrable (fun θ => (1 - angCos θ ^ 2) * besselDensity (-h) θ) angHaar :=
    integrable_of_cont ((continuous_const.sub (continuous_angCos.pow 2)).mul
      (continuous_besselDensity _))
  have i_pU : Integrable (fun θ => besselDensity (-h) θ * Uang θ) angHaar :=
    integrable_of_cont ((continuous_besselDensity _).mul continuous_Uang)
  have i_F : Integrable (fun θ => besselDensity (-h) θ * Fang h θ) angHaar :=
    integrable_of_cont ((continuous_besselDensity _).mul (continuous_Fang h hp))
  have hA := integral_sin_sq_density h hp
  have hg : 4 * h ^ 2 * (besselRatio h / h) = 4 * h * besselRatio h := by field_simp
  constructor
  · calc 4 * h * besselRatio h = ∫ θ, 4 * h ^ 2 * ((1 - angCos θ ^ 2) * besselDensity (-h) θ) ∂angHaar := by
          rw [integral_const_mul, hA, hg]
      _ ≤ Jh h := by
          refine integral_mono (i_a.const_mul _) i_F fun θ => ?_
          have := (Fang_bounds h hh θ).1
          have h0 := besselDensity_nonneg (-h) θ
          calc 4 * h ^ 2 * ((1 - angCos θ ^ 2) * besselDensity (-h) θ)
              = besselDensity (-h) θ * (4 * h ^ 2 * (1 - angCos θ ^ 2)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left this h0
  · have i_b : Integrable (fun θ => 2 * besselDensity (-h) θ - besselDensity (-h) θ * Uang θ)
        angHaar := (i_p.const_mul 2).sub i_pU
    have hB : ∫ θ, (2 * besselDensity (-h) θ - besselDensity (-h) θ * Uang θ) ∂angHaar =
        1 - besselRatio h := by
      rw [integral_sub (i_p.const_mul 2) i_pU, integral_const_mul, integral_besselDensity,
        integral_p_Uang]
      ring
    calc Jh h ≤ ∫ θ, (4 * h ^ 2 * ((1 - angCos θ ^ 2) * besselDensity (-h) θ) +
          8 * h * (2 * besselDensity (-h) θ - besselDensity (-h) θ * Uang θ)) ∂angHaar := by
          refine integral_mono i_F ((i_a.const_mul _).add (i_b.const_mul _)) fun θ => ?_
          have := (Fang_bounds h hh θ).2
          have h0 := besselDensity_nonneg (-h) θ
          calc besselDensity (-h) θ * Fang h θ
              ≤ besselDensity (-h) θ * (4 * h ^ 2 * (1 - angCos θ ^ 2) + 8 * h * (2 - Uang θ)) :=
                mul_le_mul_of_nonneg_left this h0
            _ = _ := by ring
      _ = 4 * h * besselRatio h + 8 * h * (1 - besselRatio h) := by
          rw [integral_add (i_a.const_mul _) (i_b.const_mul _), integral_const_mul,
            integral_const_mul, hA, hB, hg]

theorem Jh_nonneg (h : ℝ) (_hh : 2 ≤ h) : 0 ≤ Jh h := by
  refine integral_nonneg fun θ => mul_nonneg (besselDensity_nonneg _ _) ?_
  have h1 : 0 ≤ 1 - angCos θ ^ 2 := by
    rw [one_sub_cos_sq]
    have := Uang_mem θ
    exact mul_nonneg this.1 (by linarith [this.2])
  exact mul_nonneg h1 (sq_nonneg _)

theorem fisher_ne_top (h : ℝ) (hh : 2 ≤ h) :
    ordinaryRelativeFisher (densityMeasure (oppositeDensity h) : Measure (Torus 1))
        (DGPS.Models.engineeredModel h hh).ref ≠ ⊤ := by
  rw [fisher_formula]; exact ENNReal.ofReal_ne_top

theorem fisher_toReal (h : ℝ) (hh : 2 ≤ h) :
    (ordinaryRelativeFisher (densityMeasure (oppositeDensity h) : Measure (Torus 1))
        (DGPS.Models.engineeredModel h hh).ref).toReal = a0 * Jh h := by
  have : 0 ≤ a0 := by unfold a0; positivity
  rw [fisher_formula, ENNReal.toReal_ofReal (mul_nonneg this (Jh_nonneg h hh))]


/-! ### Asymptotic assembly -/

theorem log_le_two_sqrt (h : ℝ) (hp : 0 < h) : Real.log h ≤ 2 * √h := by
  have hs : 0 < √h := Real.sqrt_pos.2 hp
  have h1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (√h) = Real.log h / 2 := Real.log_sqrt hp.le
  linarith

theorem log_ge_one (h : ℝ) (hh : 9216 ≤ h) : 1 ≤ Real.log h := by
  have h1 : exp 1 ≤ h := by
    have := Real.exp_one_lt_d9
    linarith
  have := Real.log_le_log (exp_pos 1) h1
  rwa [Real.log_exp] at this

theorem log_le_div (h : ℝ) (hh : 9216 ≤ h) : Real.log h ≤ h / 48 := by
  have hp : 0 < h := by linarith
  have h1 := log_le_two_sqrt h hp
  have hs : 96 ≤ √h := Real.le_sqrt_of_sq_le (by linarith)
  have h2 : √h * √h = h := Real.mul_self_sqrt hp.le
  nlinarith

theorem entropy_err_le (h : ℝ) (hh : 9216 ≤ h) :
    14 + Real.log (1 + 2 * h) ≤ 24 * Real.log h := by
  have hp : 0 < h := by linarith
  have h1 : Real.log (1 + 2 * h) ≤ Real.log 3 + Real.log h := by
    rw [← Real.log_mul (by norm_num) hp.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h3 := log_ge_one h hh
  linarith

theorem rate_bound (h : ℝ) (hh : 2 ≤ h) (hHpos : 0 < (relativeEntropy
    (densityMeasure (oppositeDensity h) : Measure (Torus 1))
      (DGPS.Models.engineeredModel h hh).ref.measure).toReal) :
    ordinaryLSRate (DGPS.Models.engineeredModel h hh).ref ≠ ⊤ ∧
    (ordinaryLSRate (DGPS.Models.engineeredModel h hh).ref).toReal *
      (2 * (relativeEntropy (densityMeasure (oppositeDensity h) : Measure (Torus 1))
        (DGPS.Models.engineeredModel h hh).ref.measure).toReal) ≤ a0 * Jh h := by
  have hfin := (entropy_formula h hh).1
  have hb := DGPS.Structural.budget_lsi_fisher (DGPS.Models.engineeredModel h hh).ref
    (densityMeasure (oppositeDensity h) : Measure (Torus 1)) hfin
  rw [fisher_formula] at hb
  set Hr := (relativeEntropy (densityMeasure (oppositeDensity h) : Measure (Torus 1))
    (DGPS.Models.engineeredModel h hh).ref.measure).toReal with hHr
  have hH : relativeEntropy (densityMeasure (oppositeDensity h) : Measure (Torus 1))
      (DGPS.Models.engineeredModel h hh).ref.measure = ENNReal.ofReal Hr :=
    (ENNReal.ofReal_toReal hfin).symm
  rw [hH] at hb
  set r := ordinaryLSRate (DGPS.Models.engineeredModel h hh).ref with hr
  have hrt : r ≠ ⊤ := by
    intro ht
    rw [ht] at hb
    have hne : ENNReal.ofReal Hr ≠ 0 := (ENNReal.ofReal_pos.2 hHpos).ne'
    have : 2 * (⊤ : ENNReal) * ENNReal.ofReal Hr = ⊤ := by
      rw [ENNReal.mul_top (by norm_num)]
      exact ENNReal.top_mul hne
    rw [this] at hb
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hb)
  refine ⟨hrt, ?_⟩
  rw [← ENNReal.ofReal_toReal hrt] at hb
  have h2 : (0:ℝ) ≤ 2 * r.toReal := mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  have : ENNReal.ofReal (2 * r.toReal * Hr) ≤ ENNReal.ofReal (a0 * Jh h) := by
    rw [ENNReal.ofReal_mul h2, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact hb
  have h0 : 0 ≤ a0 := by unfold a0; positivity
  have := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h0 (Jh_nonneg h hh))).1 this
  linarith

end DGPS.Examples.EngineeredRankOneOppositeTilt

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOneOppositeTilt DGPS.Circle.AngularNormalization
  DGPS.Circle.BesselMoments

/-- **EX048.** Engineered opposite-tilt one-site upper bound. For the opposite von Mises density
`ρ_h = exp(-h cos θ)/I₀(h)` (an absolute-admissible density on the circle) and the engineered
reference `μ_h`, for `h ≥ h0`: `H(ρ_h | μ_h) = 2 h g(h) + O(log h)` and
`I(ρ_h | μ_h) / a0 = 4 h g(h) + O(1)`, where `g = I₁/I₀` and `a0 = 4π²` is the physical-to-angular
scale. The ordinary logarithmic Sobolev rate satisfies `r_LS(μ_h) ≤ a0 (1 + C log h / h)`, i.e.
`a_h = r_LS / a0 ≤ 1 + C log h / h`. -/
theorem engineered_opposite_tilt_one_site_upper_bound :
    ∃ C h0 : ℝ, 0 < C ∧ 2 ≤ h0 ∧ ∀ (h : ℝ) (hh : 2 ≤ h), h0 ≤ h →
      (∀ x : DGPS.Torus 1, (oppositeDensity h).density x =
        Real.exp (-(h * angCos (angEquiv x))) / besselI 0 h) ∧
      relativeEntropy (densityMeasure (oppositeDensity h) : MeasureTheory.Measure (DGPS.Torus 1))
          (DGPS.Models.engineeredModel h hh).ref.measure ≠ ⊤ ∧
      |(relativeEntropy (densityMeasure (oppositeDensity h) : MeasureTheory.Measure (DGPS.Torus 1))
          (DGPS.Models.engineeredModel h hh).ref.measure).toReal - 2 * h * besselRatio h| ≤
        C * Real.log h ∧
      ordinaryRelativeFisher (densityMeasure (oppositeDensity h) : MeasureTheory.Measure (DGPS.Torus 1))
          (DGPS.Models.engineeredModel h hh).ref ≠ ⊤ ∧
      |(ordinaryRelativeFisher (densityMeasure (oppositeDensity h) :
          MeasureTheory.Measure (DGPS.Torus 1))
          (DGPS.Models.engineeredModel h hh).ref).toReal / a0 - 4 * h * besselRatio h| ≤ C ∧
      ordinaryLSRate (DGPS.Models.engineeredModel h hh).ref ≤
        ENNReal.ofReal (a0 * (1 + C * Real.log h / h)) := by
  obtain ⟨K, hK, hKb⟩ := one_sub_ratio_le
  refine ⟨48 + 8 * K, max 9216 (2 * K), by positivity,
    (by norm_num : (2:ℝ) ≤ 9216).trans (le_max_left _ _), fun h hh h0h => ?_⟩
  have h9 : 9216 ≤ h := (le_max_left _ _).trans h0h
  have h2K : 2 * K ≤ h := (le_max_right _ _).trans h0h
  have hp : 0 < h := by linarith
  have ha0 : 0 < a0 := by unfold a0; positivity
  have hg1 : 1 - besselRatio h ≤ K / h := hKb h hh
  have hKh : K / h ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
  have hg : 1 / 2 ≤ besselRatio h := by linarith
  have hlog1 := log_ge_one h h9
  have hlogd := log_le_div h h9
  have hL := entropy_err_le h h9
  have hEb := abs_le.1 (entropy_bound h hh)
  have hfin := (entropy_formula h hh).1
  set Hr := (relativeEntropy (densityMeasure (oppositeDensity h) : MeasureTheory.Measure (DGPS.Torus 1))
    (DGPS.Models.engineeredModel h hh).ref.measure).toReal with hHr
  have hhg : h ≤ 2 * h * besselRatio h := by nlinarith
  have hHlow : h / 2 ≤ Hr := by linarith [hEb.1]
  have hHpos : 0 < Hr := by linarith
  obtain ⟨hrt, hrb⟩ := rate_bound h hh hHpos
  have hJ := Jh_bounds h hh
  have hJ8 : 8 * h * (1 - besselRatio h) ≤ 8 * K := by
    have := (le_div_iff₀ hp).1 hg1
    nlinarith
  have hdens : ∀ x : DGPS.Torus 1, (oppositeDensity h).density x =
      Real.exp (-(h * angCos (angEquiv x))) / besselI 0 h := fun x => by
    rw [oppositeDensity_density, besselDensity_neg_eq]
  have hIJ : (ordinaryRelativeFisher (densityMeasure (oppositeDensity h) :
      MeasureTheory.Measure (DGPS.Torus 1)) (DGPS.Models.engineeredModel h hh).ref).toReal / a0 =
      Jh h := by
    rw [fisher_toReal, mul_div_cancel_left₀ _ ha0.ne']
  refine ⟨hdens, hfin, ?_, fisher_ne_top h hh, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith [hEb.1, hEb.2]
  · rw [hIJ, abs_le]
    constructor <;> nlinarith [hJ.1, hJ.2]
  · set rt := (ordinaryLSRate (DGPS.Models.engineeredModel h hh).ref).toReal with hrt'
    have hT : h ≤ 2 * Hr := by linarith
    have hTp : 0 < 2 * Hr := by linarith
    have hCl : 0 ≤ (48 + 8 * K) * Real.log h := by positivity
    have hJle : Jh h ≤ 2 * Hr + (48 + 8 * K) * Real.log h := by
      have h8 : 8 * K ≤ 8 * K * Real.log h := by nlinarith
      nlinarith [hEb.1, hJ.2]
    have h1 : rt * (2 * Hr) ≤ a0 * (2 * Hr + (48 + 8 * K) * Real.log h) :=
      hrb.trans (mul_le_mul_of_nonneg_left hJle ha0.le)
    have h2 : rt ≤ a0 * (2 * Hr + (48 + 8 * K) * Real.log h) / (2 * Hr) :=
      (le_div_iff₀ hTp).2 h1
    have h3 : a0 * (2 * Hr + (48 + 8 * K) * Real.log h) / (2 * Hr) =
        a0 * (1 + (48 + 8 * K) * Real.log h / (2 * Hr)) := by
      field_simp
    have h4 : (48 + 8 * K) * Real.log h / (2 * Hr) ≤ (48 + 8 * K) * Real.log h / h :=
      div_le_div_of_nonneg_left hCl hp hT
    have h5 : rt ≤ a0 * (1 + (48 + 8 * K) * Real.log h / h) := by
      rw [h3] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left (by linarith) ha0.le)
    rw [← ENNReal.ofReal_toReal hrt]
    exact ENNReal.ofReal_le_ofReal h5

end DGPS.Examples
