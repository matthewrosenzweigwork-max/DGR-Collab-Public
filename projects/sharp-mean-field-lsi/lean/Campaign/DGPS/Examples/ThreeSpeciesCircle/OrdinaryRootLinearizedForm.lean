import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootWeakPairing

/-! The actual angular linearized gradient paired against the full weak-H1 domain. The
classical coefficient is C1; the arbitrary test is never required to have a continuous
representative. This is the weak Schur pairing, not a presumed root Poincare bound. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The explicit linearized ordinary gradient at a critical chart. -/
noncomputable def ordinaryRootLinearizedGradient (h γ : ℝ)
    (u v : PeriodicC2_STR02969) (t : ℝ) : ℝ :=
  rhoT_STR02901 h u.val t *
    (-2 * deriv (deriv v.val) t + 6 * h * Real.sin (3 * t) * deriv v.val t -
      2 * deriv u.val t * deriv v.val t - 2 * (1 + γ) *
        (v.val t - normInt_STR02933 (fun s => rhoT_STR02901 h u.val s * v.val s)))

/-- The linearized gradient is twice the covariance form, paired with every original
periodic weak-H1 tangent. Integration by parts uses the genuine C1 coefficient. -/
theorem ordinaryRoot_linearized_weak_pairing (h γ : ℝ)
    (u v : PeriodicC2_STR02969) (w g : ℝ → ℝ)
    (hw : IsPeriodicWeakDerivative_STR02933 w g) :
    normInt_STR02933 (fun t => ordinaryRootLinearizedGradient h γ u v t * w t) =
      2 * (normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * deriv v.val t * g t) -
        (1 + γ) * (normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * v.val t * w t) -
          normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * v.val t) *
            normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * w t))) := by
  let σ := rhoT_STR02901 h u.val
  let m := normInt_STR02933 (fun t => σ t * v.val t)
  let c : ℝ → ℝ := fun t => σ t * deriv v.val t
  have hσc : Continuous σ := continuous_rho_STR02950 h u.isC2.2.1.continuous
  have hDc : ∀ t, HasDerivAt c
      (σ t * deriv (deriv v.val) t + σ t *
        (-3 * h * Real.sin (3 * t) + deriv u.val t) * deriv v.val t) t := by
    intro t
    exact ((hasDerivAt_rho_STR02950 h u.isC2 t).mul
      (v.isC2.2.2.1 t).hasDerivAt).congr_deriv (by dsimp [σ]; ring)
  have hDcc : Continuous (deriv c) := by
    have he : deriv c = fun t => σ t * deriv (deriv v.val) t + σ t *
        (-3 * h * Real.sin (3 * t) + deriv u.val t) * deriv v.val t :=
      funext fun t => (hDc t).deriv
    rw [he]
    have := v.isC2.2.2.2.1
    have := v.isC2.2.2.1.continuous
    have := u.isC2.2.2.1.continuous
    fun_prop
  have hc : ContDiff ℝ 1 c :=
    contDiff_one_iff_deriv.mpr ⟨fun t => (hDc t).differentiableAt, hDcc⟩
  have hcp : Function.Periodic c (2 * π) :=
    (periodic_rho_STR02950 h u.isC2.1).mul (periodic_deriv_STR02901 v.isC2.1)
  have hIBP := ordinaryRoot_periodicWeak_ibp_c1 w g c hw hcp hc
  let I1 : ℝ → ℝ := fun t => w t * deriv c t
  let I2 : ℝ → ℝ := fun t => σ t * v.val t * w t
  let I3 : ℝ → ℝ := fun t => σ t * w t
  have hi1 : Integrable I1 (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [I1, mul_comm] using integrable_cmul_left_STR02935 hDcc hw.1.2
  have hi2 : Integrable I2 (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_cmul_left_STR02935 (hσc.mul v.isC2.2.1.continuous) hw.1.2
  have hi3 : Integrable I3 (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_cmul_left_STR02935 hσc hw.1.2
  have he : (fun t => ordinaryRootLinearizedGradient h γ u v t * w t) =
      fun t => (-2 : ℝ) * I1 t - (2 * (1 + γ)) * (I2 t - m * I3 t) := by
    funext t
    have hd := (hDc t).deriv
    dsimp only [ordinaryRootLinearizedGradient, I1, I2, I3, σ, m, c] at *
    rw [hd]
    ring
  have hkin : normInt_STR02933 (fun t => g t * c t) =
      normInt_STR02933 (fun t => σ t * deriv v.val t * g t) := by
    congr 1
    funext t
    dsimp [c]
    ring
  rw [he, normInt_sub_STR02902
      (f := fun t => -2 * I1 t)
      (h := fun t => (2 * (1 + γ)) * (I2 t - m * I3 t))
      (hi1.const_mul _) ((hi2.sub (hi3.const_mul m)).const_mul _),
    normInt_mul_const_STR02933, normInt_mul_const_STR02933,
    normInt_sub_STR02902 (f := I2) (h := fun t => m * I3 t)
      hi2 (hi3.const_mul m), normInt_mul_const_STR02933]
  change -2 * normInt_STR02933 (fun t => w t * deriv c t) -
    (2 * (1 + γ)) * (normInt_STR02933 I2 - m * normInt_STR02933 I3) = _
  rw [hIBP, hkin]
  dsimp only [I2, I3, σ, m]
  ring

/-- The genuine projected linearized equation implies orthogonality against every full
weak-H1 Haar complement tangent. No mixed-form conclusion is assumed. -/
theorem ordinaryRoot_linearized_complement_zero (h γ : ℝ)
    (u v : PeriodicC2_STR02969) (w g : ℝ → ℝ)
    (hw : IsPeriodicWeakDerivative_STR02933 w g)
    (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0)
    (hP : ∀ t, projP_STR02953 (ordinaryRootLinearizedGradient h γ u v) t = 0) :
    normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * deriv v.val t * g t) -
      (1 + γ) * (normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * v.val t * w t) -
        normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * v.val t) *
          normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * w t)) = 0 := by
  have hz := ordinaryRoot_complement_projection_pairing_zero
    (ordinaryRootLinearizedGradient h γ u v) w hw.1.2 h0 hc hs hP
  rw [ordinaryRoot_linearized_weak_pairing h γ u v w g hw] at hz
  linarith

end DGPS.Examples.ThreeSpeciesCircle
