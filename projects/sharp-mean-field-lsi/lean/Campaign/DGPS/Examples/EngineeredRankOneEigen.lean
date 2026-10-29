import DGPS.Examples.EngineeredRankOneEndpoints

open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open DGPS.Circle.AngularNormalization

/-!
# Engineered feature exact eigenfunction (EX032)

For `h ≥ 2` and `L_h = ∂θ² + (log q_h)' ∂θ` (acting on the lifted angle `t : ℝ`), the feature
`E_h = (exp (h U) - c_h) / tanh h` (`DGPS.Examples.EngineeredRankOne.Eang`) satisfies
`-L_h E_h = Λ_h E_h` with `Λ_h = h coth h > 0`, `μ_h(E_h) = 0`, `E_h ≥ -1`, and `E_h` is smooth,
even and nonconstant. Main output: `DGPS.Examples.engineered_feature_exact_eigenfunction`.
-/

namespace DGPS.Examples.EngineeredRankOne

theorem integrand_mul (h : ℝ) (hh : 0 < h) (u : ℝ) :
    integrand h u * (u * (2 - u)) = numer h u := by
  by_cases h0 : u = 0
  · subst h0; simp [numer_zero]
  by_cases h2 : u = 2
  · subst h2; simp [numer_two h hh]
  rw [integrand_of_ne h h0 h2]
  have : u * (2 - u) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 (Ne.symm h2))
  field_simp

theorem Uang_coe (t : ℝ) : Uang (t : Real.Angle) = 1 - Real.cos t := by
  unfold Uang; rw [Real.Angle.cos_coe]

theorem hasDerivAt_Uang (t : ℝ) :
    HasDerivAt (fun s : ℝ => Uang (s : Real.Angle)) (Real.sin t) t := by
  have : (fun s : ℝ => Uang (s : Real.Angle)) = fun s => 1 - Real.cos s := funext Uang_coe
  rw [this]
  simpa using (Real.hasDerivAt_cos t).const_sub 1

/-- derivative of the lifted feature -/
noncomputable def dE (h t : ℝ) : ℝ := h * Real.sin t * exp (h * (1 - Real.cos t)) / tanh h

theorem hasDerivAt_Eang (h t : ℝ) :
    HasDerivAt (fun s : ℝ => Eang h (s : Real.Angle)) (dE h t) t := by
  have h1 := (hasDerivAt_Uang t).const_mul h
  have h2 := h1.exp
  have h3 := (h2.sub_const (cH h)).div_const (tanh h)
  have e : (fun s : ℝ => Eang h (s : Real.Angle)) =
      fun s : ℝ => (exp (h * Uang (s : Real.Angle)) - cH h) / tanh h := rfl
  rw [e]
  refine h3.congr_deriv ?_
  unfold dE; rw [Uang_coe]; ring

theorem hasDerivAt_dE (h t : ℝ) :
    HasDerivAt (dE h) (h / tanh h * exp (h * (1 - Real.cos t)) *
      (Real.cos t + h * Real.sin t ^ 2)) t := by
  have hc : HasDerivAt (fun s : ℝ => h * (1 - Real.cos s)) (h * Real.sin t) t := by
    simpa using ((Real.hasDerivAt_cos t).const_sub 1).const_mul h
  have h1 := ((Real.hasDerivAt_sin t).const_mul h).mul hc.exp
  have h2 := h1.div_const (tanh h)
  have e : dE h = fun s => h * Real.sin s * exp (h * (1 - Real.cos s)) / tanh h := rfl
  rw [e]
  refine h2.congr_deriv ?_
  ring

theorem hasDerivAt_logq (h : ℝ) (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => logq h (s : Real.Angle))
      (-(h + integrand h (1 - Real.cos t)) * Real.sin t) t := by
  have hc : HasDerivAt (corr h) (integrand h (Uang (t : Real.Angle))) (Uang (t : Real.Angle)) :=
    ((((contDiff_integrand h hh).continuous).integral_hasStrictDerivAt 0 _).hasDerivAt)
  have h1 := (hasDerivAt_Uang t).const_mul h
  have h2 := hc.comp t (hasDerivAt_Uang t)
  have h3 := (h1.neg).sub h2
  have e : (fun s : ℝ => logq h (s : Real.Angle)) =
      fun s : ℝ => -(h * Uang (s : Real.Angle)) - (corr h ∘ fun s : ℝ => Uang (s : Real.Angle)) s := rfl
  rw [e]
  refine h3.congr_deriv ?_
  rw [Uang_coe]; ring

theorem hasDerivAt_qlift (h : ℝ) (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => qAng h (s : Real.Angle))
      (qAng h (t : Real.Angle) * (-(h + integrand h (1 - Real.cos t)) * Real.sin t)) t := by
  have h1 := (hasDerivAt_logq h hh t).exp
  have h2 := h1.const_mul (Zh h)⁻¹
  have e : (fun s : ℝ => qAng h (s : Real.Angle)) = fun s : ℝ => (Zh h)⁻¹ * exp (logq h (s : Real.Angle)) :=
    rfl
  rw [e]
  refine h2.congr_deriv ?_
  unfold qAng; ring

/-- The eigen-equation, pointwise in the lifted angle, in explicit form. -/
theorem eigen_explicit (h : ℝ) (hh : 0 < h) (t : ℝ) :
    -(h / tanh h * exp (h * (1 - Real.cos t)) * (Real.cos t + h * Real.sin t ^ 2) +
      (-(h + integrand h (1 - Real.cos t)) * Real.sin t) * dE h t) =
    lamH h * Eang h (t : Real.Angle) := by
  have hn := integrand_mul h hh (1 - Real.cos t)
  have hs2 : Real.sin t ^ 2 = (1 - Real.cos t) * (2 - (1 - Real.cos t)) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  set U := 1 - Real.cos t with hUdef
  have hcos : Real.cos t = 1 - U := by rw [hUdef]; ring
  have hexp : exp (-h * U) * exp (h * U) = 1 := by rw [← Real.exp_add]; simp
  have hs : sinh h ≠ 0 := (Real.sinh_pos_iff.2 hh).ne'
  have hc : cosh h ≠ 0 := (Real.cosh_pos h).ne'
  have hcs : cosh h ^ 2 - sinh h ^ 2 = 1 := by
    have := Real.cosh_sq h; linarith
  unfold dE Eang cH lamH
  unfold numer aH at hn
  rw [Real.tanh_eq_sinh_div_cosh] at *
  have hI : integrand h U * (U * (2 - U)) = (1 + cosh h / sinh h) * (1 - exp (-h * U)) - U := hn
  set e := exp (h * U) with he
  set f := exp (-h * U) with hf
  have hepos : e ≠ 0 := (exp_pos _).ne'
  have hsin : Real.sin t ^ 2 = U * (2 - U) := hs2
  have key : integrand h U * Real.sin t ^ 2 = (1 + cosh h / sinh h) * (1 - f) - U := by
    rw [hsin]; exact hI
  have step1 : -(h / (sinh h / cosh h) * e * (Real.cos t + h * Real.sin t ^ 2) +
      (-(h + integrand h U) * Real.sin t) * (h * Real.sin t * e / (sinh h / cosh h))) =
      -(h / (sinh h / cosh h) * e * ((1 - U) - integrand h U * Real.sin t ^ 2)) := by
    rw [hcos]; ring
  rw [step1, key]
  have hsc : sinh h / cosh h ≠ 0 := div_ne_zero hs hc
  rw [Uang_coe]
  field_simp
  linear_combination (-(sinh h + cosh h)) * hexp

theorem continuous_qAng (h : ℝ) (hh : 0 < h) : Continuous (qAng h) := by
  unfold qAng
  exact continuous_const.mul (continuous_exp.comp (continuous_logq h hh))

theorem deriv_Eang_lift (h : ℝ) : deriv (fun s : ℝ => Eang h (s : Real.Angle)) = dE h :=
  funext fun t => (hasDerivAt_Eang h t).deriv

theorem deriv_dE_lift (h : ℝ) (t : ℝ) : deriv (deriv (fun s : ℝ => Eang h (s : Real.Angle))) t =
    h / tanh h * exp (h * (1 - Real.cos t)) * (Real.cos t + h * Real.sin t ^ 2) := by
  rw [deriv_Eang_lift]; exact (hasDerivAt_dE h t).deriv

theorem deriv_logq_lift (h : ℝ) (hh : 0 < h) (t : ℝ) :
    deriv (fun s : ℝ => logq h (s : Real.Angle)) t =
      -(h + integrand h (1 - Real.cos t)) * Real.sin t :=
  (hasDerivAt_logq h hh t).deriv

theorem eigen_equation (h : ℝ) (hh : 0 < h) (t : ℝ) :
    -(deriv (deriv (fun s : ℝ => Eang h (s : Real.Angle))) t +
      deriv (fun s : ℝ => logq h (s : Real.Angle)) t *
        deriv (fun s : ℝ => Eang h (s : Real.Angle)) t) = lamH h * Eang h (t : Real.Angle) := by
  rw [deriv_dE_lift, deriv_logq_lift h hh, deriv_Eang_lift]
  exact eigen_explicit h hh t

theorem lamH_pos (h : ℝ) (hh : 0 < h) : 0 < lamH h := by
  unfold lamH
  exact mul_pos hh (div_pos (Real.cosh_pos h) (Real.sinh_pos_iff.2 hh))

theorem integral_qAng_mul_Eang (h : ℝ) (hh : 0 < h) :
    ∫ θ, qAng h θ * Eang h θ ∂angHaar = 0 := by
  have hl := lamH_pos h hh
  let F : ℝ → ℝ := fun t => qAng h (t : Real.Angle) * dE h t
  have hF : ∀ t ∈ uIcc (0:ℝ) (0 + 2 * π),
      HasDerivAt F (-(lamH h * (qAng h (t : Real.Angle) * Eang h (t : Real.Angle)))) t := by
    intro t _
    have := (hasDerivAt_qlift h hh t).mul (hasDerivAt_dE h t)
    refine this.congr_deriv ?_
    have e := eigen_explicit h hh t
    linear_combination (qAng h (t : Real.Angle)) * (-e)
  have hcont : Continuous fun t : ℝ => -(lamH h * (qAng h (t : Real.Angle) * Eang h (t : Real.Angle))) :=
    (continuous_const.mul (((continuous_qAng h hh).comp Real.Angle.continuous_coe).mul
      ((continuous_Eang h).comp Real.Angle.continuous_coe))).neg
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)
  have hper : F (0 + 2 * π) = F 0 := by
    simp only [F, dE, zero_add]
    rw [Real.sin_two_pi, Real.cos_two_pi, Real.Angle.coe_two_pi]
    simp
  rw [hper, sub_self, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hint
  rw [AddCircle.integral_haarAddCircle]
  have h2 := AddCircle.intervalIntegral_preimage (2 * π) 0
    (fun θ : AngCircle => qAng h θ * Eang h θ)
  have h3 : ∫ t in (0:ℝ)..0 + 2 * π, qAng h (t : Real.Angle) * Eang h (t : Real.Angle) = 0 := by
    have : lamH h * ∫ t in (0:ℝ)..0 + 2 * π, qAng h (t : Real.Angle) * Eang h (t : Real.Angle) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h4 | h4
    · exact absurd h4 hl.ne'
    · exact h4
  rw [smul_eq_mul]
  have h5 : ∫ θ : AngCircle, qAng h θ * Eang h θ = 0 := by
    rw [← h2]; exact h3
  simp only [h5, mul_zero]

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne

/-- EX032: the engineered feature `E_h` is an exact eigenfunction of `-L_h`,
`L_h = ∂θ² + (log q_h)' ∂θ` (on the lifted angle `t : ℝ`), with eigenvalue `Λ_h = h coth h > 0`;
it is `μ_h`-centered (`μ_h = q_h dθ/(2π)`), bounded below by `-1` with equality at `θ = 0`, and
smooth, even and nonconstant. -/
theorem engineered_feature_exact_eigenfunction (h : ℝ) (hh : 2 ≤ h) :
    (∀ t : ℝ, -(deriv (deriv (fun s : ℝ => Eang h (s : Real.Angle))) t +
      deriv (fun s : ℝ => logq h (s : Real.Angle)) t *
        deriv (fun s : ℝ => Eang h (s : Real.Angle)) t) = lamH h * Eang h (t : Real.Angle)) ∧
    lamH h = h * (cosh h / sinh h) ∧ 0 < lamH h ∧
    ∫ θ, qAng h θ * Eang h θ ∂angHaar = 0 ∧
    (∀ θ : AngCircle, -1 ≤ Eang h θ) ∧ Eang h 0 = -1 ∧
    ContDiff ℝ ∞ (fun t : ℝ => Eang h (t : Real.Angle)) ∧
    (∀ θ : AngCircle, Eang h (-θ) = Eang h θ) ∧
    (∃ θ₁ θ₂ : AngCircle, Eang h θ₁ ≠ Eang h θ₂) := by
  have hp : 0 < h := by linarith
  have hT : 0 < tanh h := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 hp) (Real.cosh_pos h)
  have hT1 : 0 < tanh h := hT
  have hE0 : Eang h 0 = -1 := by
    have hU0 : Uang (0 : Real.Angle) = 0 := by
      unfold Uang; rw [Real.Angle.cos_zero]; norm_num
    unfold Eang cH
    rw [show Uang (0 : AngCircle) = 0 from hU0]
    simp
    field_simp
  refine ⟨eigen_equation h hp, rfl, lamH_pos h hp, integral_qAng_mul_Eang h hp, ?_, hE0,
    ?_, ?_, ?_⟩
  · intro θ
    have hU := (Uang_mem θ).1
    have : 1 ≤ exp (h * Uang θ) := Real.one_le_exp (by positivity)
    unfold Eang cH
    rw [le_div_iff₀ hT]
    linarith
  · have hUs : ContDiff ℝ ∞ (fun t : ℝ => Uang (t : Real.Angle)) := by
      have : (fun t : ℝ => Uang (t : Real.Angle)) = fun t => 1 - Real.cos t := funext Uang_coe
      rw [this]; exact contDiff_const.sub Real.contDiff_cos
    unfold Eang
    exact ((Real.contDiff_exp.comp (contDiff_const.mul hUs)).sub contDiff_const).div_const _
  · intro θ
    have : Uang (-θ) = Uang θ := by
      unfold Uang; rw [show Real.Angle.cos (-θ) = Real.Angle.cos θ from Real.Angle.cos_neg θ]
    unfold Eang
    rw [this]
  · refine ⟨0, (Real.pi : Real.Angle), ?_⟩
    rw [hE0]
    have hU : Uang (Real.pi : Real.Angle) = 2 := by
      unfold Uang; rw [Real.Angle.cos_coe, Real.cos_pi]; norm_num
    unfold Eang at *
    rw [hU]
    intro hc
    have h1 : exp (h * 2) - cH h = -tanh h := by
      field_simp at hc
      linarith
    have h2 : exp (h * 2) = 1 := by unfold cH at h1; linarith
    have h3 : 0 < h * 2 := by linarith
    have := Real.add_one_lt_exp h3.ne'
    linarith

end DGPS.Examples
