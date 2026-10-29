import FullLabeledLSI.Nonvacuity.Prop82.DBridge
import FullLabeledLSI.Nonvacuity.Prop82.DBessel
import FullLabeledLSI.Nonvacuity.Prop82.DGibbs
import FullLabeledLSI.Nonvacuity.Prop82.DMain

/-!
# Lane D: the oriented second-moment bound `β² ≤ H(σ)`

`β = alignedSecondMoment ρ` equals `∫₀¹ f(t) cos(4πt − 2φ) dt` for the phase `φ` of the first
Fourier moment; `cos(4πt − 2φ)` has period `1/2`, so `β` is also `∫ σ cos(4π· − 2φ)`; the Gibbs
inequality with the Bessel bound `∫ e^{s cos} ≤ e^{s²/4}` at `s = 2β` gives `β² ≤ H(σ)`.
-/

open MeasureTheory InformationTheory Filter Topology intervalIntegral
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

theorem gCos_lineT_D (t : Real) : gCos (lineT t) = Real.cos (2 * Real.pi * t) :=
  gCos_coe _ t rfl

theorem sCos_lineT_D (t : Real) : sCos (lineT t) = Real.sin (2 * Real.pi * t) :=
  expT_im_coe _ t rfl

theorem c2_lineT (t : Real) : c2 (lineT t) = Real.cos (4 * Real.pi * t) := by
  rw [c2_apply, gCos_lineT_D, show 4 * Real.pi * t = 2 * (2 * Real.pi * t) by ring,
    Real.cos_two_mul]

theorem cosMoment_eq {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    cosMoment rho = ∫ t in (0 : Real)..1, Real.cos (2 * Real.pi * t) * pf rho t := by
  unfold cosMoment
  refine (integral_torus_eq (g := fun x => gCos x * rho x)
    (continuous_gCos.mul (Sec8.continuous_of_smooth h.smooth))).trans ?_
  simp only [gCos_lineT_D, pf]

theorem sinMoment_eq {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    sinMoment rho = ∫ t in (0 : Real)..1, Real.sin (2 * Real.pi * t) * pf rho t := by
  unfold sinMoment
  refine (integral_torus_eq (g := fun x => sCos x * rho x)
    (continuous_sCos.mul (Sec8.continuous_of_smooth h.smooth))).trans ?_
  simp only [sCos_lineT_D, pf]

theorem firstMode_eq_moments_D {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    firstMode rho = cosMoment rho ^ 2 + sinMoment rho ^ 2 :=
  firstMode_eq (Sec8.integrable_of_smooth h.smooth)

/-- Polar form of the first Fourier moment. -/
theorem exists_phase (C S : Real) (hQ : 0 < C ^ 2 + S ^ 2) :
    ∃ r φ : Real, r ^ 2 = C ^ 2 + S ^ 2 ∧ C = r * Real.cos φ ∧ S = r * Real.sin φ := by
  refine ⟨‖Complex.mk C S‖, Complex.arg (Complex.mk C S), ?_, ?_, ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_apply]
    simp only
    ring
  · exact (Complex.norm_mul_cos_arg (Complex.mk C S)).symm
  · exact (Complex.norm_mul_sin_arg (Complex.mk C S)).symm

theorem aligned_second_moment_eq {rho : Torus 1 → Real} (h : SmoothProbability rho)
    (hQ : 0 < firstMode rho) :
    ∃ φ : Real, alignedSecondMoment rho =
      ∫ t in (0 : Real)..1, pf rho t * Real.cos (4 * Real.pi * t - 2 * φ) := by
  have hQ' := hQ
  rw [firstMode_eq_moments_D h] at hQ'
  obtain ⟨r, φ, hr, hC, hS⟩ := exists_phase (cosMoment rho) (sinMoment rho) hQ'
  refine ⟨φ, ?_⟩
  have hnum : (∫ x, rho x * ((cosMoment rho ^ 2 - sinMoment rho ^ 2) * c2 x +
      4 * cosMoment rho * sinMoment rho * gCos x * sCos x) ∂haar 1) =
      (cosMoment rho ^ 2 + sinMoment rho ^ 2) *
        ∫ t in (0 : Real)..1, pf rho t * Real.cos (4 * Real.pi * t - 2 * φ) := by
    have hc : Continuous (fun x => rho x * ((cosMoment rho ^ 2 - sinMoment rho ^ 2) * c2 x +
        4 * cosMoment rho * sinMoment rho * gCos x * sCos x)) :=
      (Sec8.continuous_of_smooth h.smooth).mul
        ((continuous_const.mul continuous_c2).add
          ((continuous_const.mul continuous_gCos).mul continuous_sCos))
    rw [integral_torus_eq hc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pf, c2_lineT, gCos_lineT_D, sCos_lineT_D]
    have e1 : (cosMoment rho ^ 2 - sinMoment rho ^ 2) * Real.cos (4 * Real.pi * t) +
        4 * cosMoment rho * sinMoment rho * Real.cos (2 * Real.pi * t) *
          Real.sin (2 * Real.pi * t) =
        (cosMoment rho ^ 2 + sinMoment rho ^ 2) * Real.cos (4 * Real.pi * t - 2 * φ) := by
      have hc4 : Real.cos (4 * Real.pi * t) =
          2 * Real.cos (2 * Real.pi * t) ^ 2 - 1 := by
        rw [show 4 * Real.pi * t = 2 * (2 * Real.pi * t) by ring, Real.cos_two_mul]
      have hs4 : Real.sin (4 * Real.pi * t) =
          2 * Real.sin (2 * Real.pi * t) * Real.cos (2 * Real.pi * t) := by
        rw [show 4 * Real.pi * t = 2 * (2 * Real.pi * t) by ring, Real.sin_two_mul]
      have hab := Real.sin_sq_add_cos_sq φ
      rw [Real.cos_sub, hc4, hs4, Real.cos_two_mul φ, Real.sin_two_mul φ, hC, hS]
      linear_combination (-(r ^ 2) * ((2 * Real.cos (2 * Real.pi * t) ^ 2 - 1) *
        (2 * Real.cos φ ^ 2) + 4 * Real.cos φ * Real.sin φ * Real.cos (2 * Real.pi * t) *
          Real.sin (2 * Real.pi * t))) * hab
    rw [e1]
    ring
  unfold alignedSecondMoment
  rw [hnum, firstMode_eq_moments_D h]
  field_simp

/-- Averaging over a half turn does not change integrals against half-periodic functions. -/
theorem integral_half_average {f g : Real → Real} (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ t, f (t + 1) = f t) (hgp : ∀ t, g (t + 1 / 2) = g t) :
    ∫ t in (0 : Real)..1, ((f t + f (t + 1 / 2)) / 2) * g t =
      ∫ t in (0 : Real)..1, f t * g t := by
  have hgp1 : ∀ t, g (t + 1) = g t := fun t => by
    rw [show t + 1 = (t + 1 / 2) + 1 / 2 by ring, hgp, hgp]
  have hP : Function.Periodic (fun t => f t * g t) 1 := fun t => by
    simp only [hfp, hgp1]
  have hshift : ∫ t in (0 : Real)..1, f (t + 1 / 2) * g t = ∫ t in (0 : Real)..1, f t * g t := by
    have : ∀ t, f (t + 1 / 2) * g t = (fun u => f u * g u) (t + 1 / 2) := fun t => by
      simp only [hgp]
    simp_rw [this]
    rw [intervalIntegral.integral_comp_add_right (fun u => f u * g u) (1 / 2)]
    have := hP.intervalIntegral_add_eq (0 + 1 / 2) 0
    simp only [zero_add] at this
    rw [show (1 : Real) + 1 / 2 = 1 / 2 + 1 by ring, zero_add]
    rw [this]
  have h1 : IntervalIntegrable (fun t => f t * g t) volume 0 1 :=
    (hf.mul hg).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => f (t + 1 / 2) * g t) volume 0 1 :=
    ((hf.comp (continuous_id.add continuous_const)).mul hg).intervalIntegrable _ _
  have : ∀ t, ((f t + f (t + 1 / 2)) / 2) * g t =
      (f t * g t + f (t + 1 / 2) * g t) / 2 := fun t => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add h1 h2, hshift]
  ring

theorem halfTurn_moment {rho : Torus 1 → Real} (h : SmoothProbability rho)
    (hQ : 0 < firstMode rho) :
    alignedSecondMoment rho ^ 2 ≤ entropy (halfSymmetrize rho) := by
  obtain ⟨φ, hφ⟩ := aligned_second_moment_eq h hQ
  have hs := halfSymmetrize_probability h
  set g : Real → Real := fun t => Real.cos (4 * Real.pi * t - 2 * φ) with hgdef
  have hgc : Continuous g := by
    simp only [hgdef]
    fun_prop
  have hgp : ∀ t, g (t + 1 / 2) = g t := fun t => by
    simp only [hgdef]
    rw [show 4 * Real.pi * (t + 1 / 2) - 2 * φ = (4 * Real.pi * t - 2 * φ) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  set b := alignedSecondMoment rho with hb
  have hbσ : b = ∫ t in (0 : Real)..1, pf (halfSymmetrize rho) t * g t := by
    have hfun : pf (halfSymmetrize rho) = fun u => (pf rho u + pf rho (u + 1 / 2)) / 2 :=
      funext (pf_halfSymmetrize rho)
    rw [hfun]
    exact hφ.trans
      (integral_half_average (pf_continuous h.smooth) hgc (pf_periodic rho) hgp).symm
  have hgibbs := gibbs_interval_paren (pf_continuous hs.smooth) (pf_pos hs.positive) hgc
    (integral_pf_eq_one hs) (2 * b)
  have hexp : ∫ t in (0 : Real)..1, Real.exp (2 * b * g t) ≤ Real.exp ((2 * b) ^ 2 / 4) := by
    have hG : Continuous (fun u : Real => Real.exp (2 * b * Real.cos (2 * Real.pi * u))) := by
      fun_prop
    have hGp : ∀ u, (fun u : Real => Real.exp (2 * b * Real.cos (2 * Real.pi * u))) (u + 1) =
        (fun u : Real => Real.exp (2 * b * Real.cos (2 * Real.pi * u))) u := fun u => by
      simp only
      rw [show 2 * Real.pi * (u + 1) = 2 * Real.pi * u + 2 * Real.pi by ring,
        Real.cos_add_two_pi]
    have hshift := integral_double_shift hG hGp (-(φ / Real.pi))
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have : ∀ t, Real.exp (2 * b * g t) =
        (fun u : Real => Real.exp (2 * b * Real.cos (2 * Real.pi * u))) (2 * t + -(φ / Real.pi)) :=
      fun t => by
        simp only [hgdef]
        congr 3
        field_simp
        ring
    simp_rw [this]
    rw [hshift]
    exact integral_exp_cos_le (2 * b)
  have hlog : Real.log (∫ t in (0 : Real)..1, Real.exp (2 * b * g t)) ≤ (2 * b) ^ 2 / 4 := by
    have hpos : 0 < ∫ t in (0 : Real)..1, Real.exp (2 * b * g t) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        ((by fun_prop : Continuous fun t => Real.exp (2 * b * g t)).intervalIntegrable _ _)
        (fun t _ => Real.exp_pos _) zero_lt_one
    calc Real.log _ ≤ Real.log (Real.exp ((2 * b) ^ 2 / 4)) :=
          Real.log_le_log hpos hexp
      _ = _ := Real.log_exp _
  rw [entropy_eq_interval hs]
  rw [← hbσ] at hgibbs
  nlinarith [hgibbs, hlog]

end SharpLSI.FL.Prop82
