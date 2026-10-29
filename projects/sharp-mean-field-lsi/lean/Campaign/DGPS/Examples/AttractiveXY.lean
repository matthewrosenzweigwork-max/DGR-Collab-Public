import DGPS.Analysis.RelativeFisher
import DGPS.Circle.AngularNormalization
import DGPS.Circle.BesselMoments
import DGPS.Model.Data
import DGPS.Model.ScalarRate
import DGPS.Model.SpeciesRate

/-!
# The attractive XY model and its frozen scores (EX018)

On the circle `𝕋¹` with `φ(x) = (cos 2πx, sin 2πx)`, the attractive XY model has
`V(x) = -h cos 2πx` and `W(x,y) = κ (1 - cos 2π(x-y))`, `κ, h ≥ 0`.  For a probability `ν` with mean
`z = ∫ φ dν`:

* the free energy is `F(ν) = H(ν | m) + κ/2 - h z₁ - κ |z|²/2`;
* `V + W * ν = -(h + κ z₁) cos - κ z₂ sin + κ`, so the force of `ρ` is `-∇ log p` a.e., where
  `p = exp((h e₁ + κ z) · φ) / Z` is the frozen law (a bounded positive Lipschitz reference);
* hence the scalar dissipation `D(ρ)` is the ordinary relative Fisher information `I(ρ m | p)`
  (DEF022), and for a species family `D_θ = ∑ θ_s I(ρ_s m | p)` with the common mean of the
  barycenter.

`DGPS.Models.attractiveXY κ h` and `DGPS.Models.attractiveXYDrift κ h` are the model and its
canonical absolute drift (the classical gradient of the smooth potential `V + W * ρ`).
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal ContDiff

namespace DGPS.Examples.AttractiveXY

/-- The first harmonic `e^{2πi x}` on the circle `𝕋^1`. -/
noncomputable def xyMode : DGPS.Torus 1 → ℂ := fun x => mFourier (fun _ : Fin 1 => (1 : ℤ)) x

theorem xyMode_apply (x : DGPS.Torus 1) : xyMode x = fourier 1 (x 0) := by
  simp [xyMode, mFourier]

theorem continuous_xyMode : Continuous xyMode := (mFourier _).continuous

theorem xyMode_sub (x y : DGPS.Torus 1) :
    xyMode (x - y) = xyMode x * (starRingEnd ℂ) (xyMode y) := by
  simp only [xyMode_apply, Pi.sub_apply]
  rw [sub_eq_add_neg, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul, smul_neg,
    ← fourier_apply, fourier_neg']

theorem xyMode_re_sub (x y : DGPS.Torus 1) :
    (xyMode (x - y)).re = (xyMode x).re * (xyMode y).re + (xyMode x).im * (xyMode y).im := by
  rw [xyMode_sub]; simp [Complex.mul_re]

theorem xyMode_lift (a : Fin 1 → ℝ) :
    xyMode (DGPS.torusLift a) = Complex.exp (2 * Real.pi * Complex.I * a 0) := by
  rw [xyMode_apply]
  show fourier 1 (((a 0 : ℝ)) : AddCircle (1 : ℝ)) = _
  rw [fourier_coe_apply]
  congr 1
  push_cast; ring

theorem xyMode_zero : xyMode 0 = 1 := by
  simp [xyMode_apply]

theorem xyMode_re_lift (a : Fin 1 → ℝ) :
    (xyMode (DGPS.torusLift a)).re = Real.cos (2 * Real.pi * a 0) := by
  have h2 : (2 * Real.pi * Complex.I * (a 0 : ℝ) : ℂ) = ((2 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [xyMode_lift, h2, Complex.exp_ofReal_mul_I_re]

theorem xyMode_im_lift (a : Fin 1 → ℝ) :
    (xyMode (DGPS.torusLift a)).im = Real.sin (2 * Real.pi * a 0) := by
  have h2 : (2 * Real.pi * Complex.I * (a 0 : ℝ) : ℂ) = ((2 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [xyMode_lift, h2, Complex.exp_ofReal_mul_I_im]

theorem xyMode_norm (x : DGPS.Torus 1) : ‖xyMode x‖ = 1 := by
  rw [xyMode_apply, fourier_apply]; simp

theorem abs_xyMode_re_le (x : DGPS.Torus 1) : |(xyMode x).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (xyMode_norm x).le

theorem abs_xyMode_im_le (x : DGPS.Torus 1) : |(xyMode x).im| ≤ 1 :=
  (Complex.abs_im_le_norm _).trans (xyMode_norm x).le

/-- `A cos 2πx + B sin 2πx + K` on the circle. -/
noncomputable def xyTrig (A B K : ℝ) : DGPS.Torus 1 → ℝ :=
  fun x => A * (xyMode x).re + B * (xyMode x).im + K

theorem xyTrig_lift (A B K : ℝ) (a : Fin 1 → ℝ) :
    xyTrig A B K (DGPS.torusLift a) =
      A * Real.cos (2 * Real.pi * a 0) + B * Real.sin (2 * Real.pi * a 0) + K := by
  simp only [xyTrig, xyMode_re_lift, xyMode_im_lift]

theorem isSmoothPeriodic_xyTrig (A B K : ℝ) : DGPS.IsSmoothPeriodic (xyTrig A B K) := by
  unfold DGPS.IsSmoothPeriodic
  have : (xyTrig A B K ∘ DGPS.torusLift) = fun a : Fin 1 → ℝ =>
      A * Real.cos (2 * Real.pi * a 0) + B * Real.sin (2 * Real.pi * a 0) + K := by
    funext a; exact xyTrig_lift A B K a
  rw [this]
  fun_prop

theorem coordPartial_re_xyMode (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (fun y => (xyMode y).re) x = -(2 * Real.pi) * (xyMode x).im := by
  have := DGPS.coordPartial_re_mFourier (d := 1) (fun _ => (1 : ℤ)) 0 x
  simp only [xyMode]
  rw [this]
  have e : (2 * (Real.pi : ℂ) * Complex.I * (((fun _ : Fin 1 => (1 : ℤ)) 0 : ℤ) : ℂ) *
      (mFourier fun _ : Fin 1 => (1 : ℤ)) x) =
      ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (mFourier fun _ : Fin 1 => (1 : ℤ)) x) := by
    push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

theorem coordPartial_im_xyMode (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (fun y => (xyMode y).im) x = (2 * Real.pi) * (xyMode x).re := by
  have := DGPS.coordPartial_im_mFourier (d := 1) (fun _ => (1 : ℤ)) 0 x
  simp only [xyMode]
  rw [this]
  have e : (2 * (Real.pi : ℂ) * Complex.I * (((fun _ : Fin 1 => (1 : ℤ)) 0 : ℤ) : ℂ) *
      (mFourier fun _ : Fin 1 => (1 : ℤ)) x) =
      ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (mFourier fun _ : Fin 1 => (1 : ℤ)) x) := by
    push_cast; ring
  rw [e, Complex.im_ofReal_mul, Complex.I_mul_im]

theorem isSmoothPeriodic_re_xyMode : DGPS.IsSmoothPeriodic (fun y => (xyMode y).re) := by
  have e : (fun y => (xyMode y).re) = xyTrig 1 0 0 := by
    funext y; simp [xyTrig]
  rw [e]; exact isSmoothPeriodic_xyTrig 1 0 0

theorem isSmoothPeriodic_im_xyMode : DGPS.IsSmoothPeriodic (fun y => (xyMode y).im) := by
  have e : (fun y => (xyMode y).im) = xyTrig 0 1 0 := by
    funext y; simp [xyTrig]
  rw [e]; exact isSmoothPeriodic_xyTrig 0 1 0

theorem coordPartial_xyTrig (A B K : ℝ) (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (xyTrig A B K) x = xyTrig (2 * Real.pi * B) (-(2 * Real.pi) * A) 0 x := by
  have h1 : DifferentiableAt ℝ ((fun y => (xyMode y).re) ∘ DGPS.torusLift) (SharpLSI.secT x) :=
    (isSmoothPeriodic_re_xyMode.differentiable (by simp)) _
  have h2 : DifferentiableAt ℝ ((fun y => (xyMode y).im) ∘ DGPS.torusLift) (SharpLSI.secT x) :=
    (isSmoothPeriodic_im_xyMode.differentiable (by simp)) _
  have e : (xyTrig A B K ∘ DGPS.torusLift) = fun a =>
      A * ((fun y => (xyMode y).re) ∘ DGPS.torusLift) a +
        B * ((fun y => (xyMode y).im) ∘ DGPS.torusLift) a + K := rfl
  have hc1 := coordPartial_re_xyMode x
  have hc2 := coordPartial_im_xyMode x
  unfold DGPS.coordPartial at hc1 hc2 ⊢
  rw [e, fderiv_add_const, fderiv_fun_add (h1.const_mul A) (h2.const_mul B),
    fderiv_const_mul h1, fderiv_const_mul h2]
  simp only [add_apply, smul_apply, smul_eq_mul, hc1, hc2,
    xyTrig]
  ring

theorem torusDist_one (x y : DGPS.Torus 1) : DGPS.torusDist x y = ‖x 0 - y 0‖ := by
  unfold DGPS.torusDist SharpLSI.flatDist
  simp [Real.sqrt_sq]

/-! ### Lipschitz estimates -/

theorem fourier_one_coe (a : ℝ) :
    fourier 1 (a : AddCircle (1 : ℝ)) = Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast; ring

theorem fourier_one_re_coe (a : ℝ) :
    (fourier 1 (a : AddCircle (1 : ℝ))).re = Real.cos (2 * Real.pi * a) := by
  rw [fourier_one_coe, Complex.exp_ofReal_mul_I_re]

theorem fourier_one_im_coe (a : ℝ) :
    (fourier 1 (a : AddCircle (1 : ℝ))).im = Real.sin (2 * Real.pi * a) := by
  rw [fourier_one_coe, Complex.exp_ofReal_mul_I_im]

theorem abs_periodic_sub_le (F : ℝ → ℝ) (hF : ∀ (a : ℝ) (n : ℤ), F (a + n) = F a)
    (hL : ∀ a b, |F a - F b| ≤ 2 * Real.pi * |a - b|) (a b : ℝ) :
    |F a - F b| ≤ 2 * Real.pi * ‖(a : AddCircle (1 : ℝ)) - (b : AddCircle (1 : ℝ))‖ := by
  rw [← QuotientAddGroup.mk_sub, AddCircle.norm_eq]
  set n : ℤ := round ((1 : ℝ)⁻¹ * (a - b)) with hn
  have h1 : F a = F (b + (a - b - n * 1)) := by
    have : b + (a - b - n * 1) = a + ((-n : ℤ) : ℝ) := by push_cast; ring
    rw [this, hF]
  rw [h1]
  refine (hL _ _).trans ?_
  have : b + (a - b - n * 1) - b = a - b - n * 1 := by ring
  rw [this]

theorem abs_fourier_re_sub_le (s t : AddCircle (1 : ℝ)) :
    |(fourier 1 s).re - (fourier 1 t).re| ≤ 2 * Real.pi * ‖s - t‖ := by
  induction s using QuotientAddGroup.induction_on with | _ a => ?_
  induction t using QuotientAddGroup.induction_on with | _ b => ?_
  simp only [fourier_one_re_coe]
  refine abs_periodic_sub_le (fun a => Real.cos (2 * Real.pi * a)) (fun a n => ?_)
    (fun a b => ?_) a b
  · have : 2 * Real.pi * (a + n) = 2 * Real.pi * a + (n : ℝ) * (2 * Real.pi) := by ring
    simp only [this, Real.cos_add_int_mul_two_pi]
  · refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem abs_fourier_im_sub_le (s t : AddCircle (1 : ℝ)) :
    |(fourier 1 s).im - (fourier 1 t).im| ≤ 2 * Real.pi * ‖s - t‖ := by
  induction s using QuotientAddGroup.induction_on with | _ a => ?_
  induction t using QuotientAddGroup.induction_on with | _ b => ?_
  simp only [fourier_one_im_coe]
  refine abs_periodic_sub_le (fun a => Real.sin (2 * Real.pi * a)) (fun a n => ?_)
    (fun a b => ?_) a b
  · have : 2 * Real.pi * (a + n) = 2 * Real.pi * a + (n : ℝ) * (2 * Real.pi) := by ring
    simp only [this, Real.sin_add_int_mul_two_pi]
  · refine (Real.abs_sin_sub_sin_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem abs_xyMode_re_sub_le (x y : DGPS.Torus 1) :
    |(xyMode x).re - (xyMode y).re| ≤ 2 * Real.pi * DGPS.torusDist x y := by
  rw [torusDist_one, xyMode_apply, xyMode_apply]
  exact abs_fourier_re_sub_le _ _

theorem abs_xyMode_im_sub_le (x y : DGPS.Torus 1) :
    |(xyMode x).im - (xyMode y).im| ≤ 2 * Real.pi * DGPS.torusDist x y := by
  rw [torusDist_one, xyMode_apply, xyMode_apply]
  exact abs_fourier_im_sub_le _ _

theorem abs_xyTrig_sub_le (A B K : ℝ) (x y : DGPS.Torus 1) :
    |xyTrig A B K x - xyTrig A B K y| ≤ (|A| + |B|) * (2 * Real.pi) * DGPS.torusDist x y := by
  have h1 := abs_xyMode_re_sub_le x y
  have h2 := abs_xyMode_im_sub_le x y
  have e : xyTrig A B K x - xyTrig A B K y =
      A * ((xyMode x).re - (xyMode y).re) + B * ((xyMode x).im - (xyMode y).im) := by
    simp only [xyTrig]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hA := mul_le_mul_of_nonneg_left h1 (abs_nonneg A)
  have hB := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
  nlinarith

/-- The first coordinate `z₁ = ∫ cos 2πx dν` of the mean of `ν` in the vector `(cos, sin)`. -/
noncomputable def xyZ1 (ν : Measure (DGPS.Torus 1)) : ℝ := ∫ y, (xyMode y).re ∂ν

/-- The second coordinate `z₂ = ∫ sin 2πx dν` of the mean of `ν` in the vector `(cos, sin)`. -/
noncomputable def xyZ2 (ν : Measure (DGPS.Torus 1)) : ℝ := ∫ y, (xyMode y).im ∂ν

theorem integrable_xyMode_re (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    Integrable (fun y => (xyMode y).re) ν :=
  (Complex.continuous_re.comp continuous_xyMode).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_xyMode_im (ν : Measure (DGPS.Torus 1)) [IsFiniteMeasure ν] :
    Integrable (fun y => (xyMode y).im) ν :=
  (Complex.continuous_im.comp continuous_xyMode).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end DGPS.Examples.AttractiveXY

namespace DGPS.Models

open DGPS.Examples.AttractiveXY

/-- The attractive XY model on the circle `𝕋^1`: `V(x) = -h cos 2πx` and
`W(x,y) = κ (1 - cos 2π(x-y))`. -/
noncomputable def attractiveXY (κ h : ℝ) : DGPS.InteractionData 1 where
  V := fun x => -h * (xyMode x).re
  W := fun x y => κ * (1 - (xyMode (x - y)).re)
  V_continuous := continuous_const.mul (Complex.continuous_re.comp continuous_xyMode)
  W_continuous :=
    continuous_const.mul (continuous_const.sub (Complex.continuous_re.comp
      (continuous_xyMode.comp (continuous_fst.sub continuous_snd))))
  W_symm := fun x y => by simp only [xyMode_re_sub]; ring
  W_diag := fun x => by simp [xyMode_zero]

end DGPS.Models

namespace DGPS.Examples.AttractiveXY

open DGPS.Models

theorem attractiveXY_V (κ h : ℝ) (x : DGPS.Torus 1) :
    (attractiveXY κ h).V x = -h * (xyMode x).re := rfl

theorem attractiveXY_W (κ h : ℝ) (x y : DGPS.Torus 1) :
    (attractiveXY κ h).W x y = κ * (1 - (xyMode (x - y)).re) := rfl

theorem attractiveXY_V_lift (κ h : ℝ) (a : Fin 1 → ℝ) :
    (attractiveXY κ h).V (DGPS.torusLift a) = -h * Real.cos (2 * Real.pi * a 0) := by
  rw [attractiveXY_V, xyMode_re_lift]

theorem torusLift_sub (a b : Fin 1 → ℝ) :
    DGPS.torusLift a - DGPS.torusLift b = DGPS.torusLift (a - b) := by
  ext i; simp [DGPS.torusLift, SharpLSI.liftT]

theorem attractiveXY_W_lift (κ h : ℝ) (a b : Fin 1 → ℝ) :
    (attractiveXY κ h).W (DGPS.torusLift a) (DGPS.torusLift b) =
      κ * (1 - Real.cos (2 * Real.pi * (a 0 - b 0))) := by
  rw [attractiveXY_W, torusLift_sub, xyMode_re_lift]
  simp

theorem lipschitzData_attractiveXY (κ h : ℝ) : DGPS.LipschitzData (attractiveXY κ h) := by
  refine ⟨⟨|h| * (2 * Real.pi), fun x y => ?_⟩, ?_⟩
  · rw [attractiveXY_V, attractiveXY_V]
    have e : -h * (xyMode x).re - -h * (xyMode y).re = -h * ((xyMode x).re - (xyMode y).re) := by
      ring
    rw [e, abs_mul, abs_neg]
    calc |h| * |(xyMode x).re - (xyMode y).re|
        ≤ |h| * (2 * Real.pi * DGPS.torusDist x y) :=
          mul_le_mul_of_nonneg_left (abs_xyMode_re_sub_le x y) (abs_nonneg _)
      _ = _ := by ring
  · rw [DGPS.LipschitzData.W_lipschitz_sum_iff]
    refine ⟨|κ| * (2 * Real.pi), fun x y x' y' => ?_⟩
    show |(attractiveXY κ h).W x y - (attractiveXY κ h).W x' y'| ≤ _
    rw [attractiveXY_W, attractiveXY_W, xyMode_apply, xyMode_apply]
    simp only [Pi.sub_apply]
    have h1 := abs_fourier_re_sub_le (x 0 - y 0) (x' 0 - y' 0)
    have h2 : ‖(x 0 - y 0) - (x' 0 - y' 0)‖ ≤ ‖x 0 - x' 0‖ + ‖y 0 - y' 0‖ := by
      have : (x 0 - y 0) - (x' 0 - y' 0) = (x 0 - x' 0) - (y 0 - y' 0) := by abel
      rw [this]; exact norm_sub_le _ _
    have h3 : κ * (1 - (fourier 1 (x 0 - y 0)).re) - κ * (1 - (fourier 1 (x' 0 - y' 0)).re) =
        -κ * ((fourier 1 (x 0 - y 0)).re - (fourier 1 (x' 0 - y' 0)).re) := by ring
    rw [h3, abs_mul, abs_neg, torusDist_one, torusDist_one]
    calc |κ| * |(fourier 1 (x 0 - y 0)).re - (fourier 1 (x' 0 - y' 0)).re|
        ≤ |κ| * (2 * Real.pi * ‖(x 0 - y 0) - (x' 0 - y' 0)‖) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |κ| * (2 * Real.pi * (‖x 0 - x' 0‖ + ‖y 0 - y' 0‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (abs_nonneg _)
      _ = _ := by ring

theorem integral_densityMeasure (ρ : DGPS.AbsoluteDensity 1) (f : DGPS.Torus 1 → ℝ) :
    ∫ x, f x ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) =
      ∫ x, ρ.density x * f x ∂DGPS.haar 1 := by
  rw [DGPS.densityMeasure_coe]
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [DGPS.AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]
  · exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem interactionPotential_attractiveXY (κ h : ℝ) (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.interactionPotential (attractiveXY κ h) ρ =
      xyTrig (-(h + κ * xyZ1 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))))
        (-(κ * xyZ2 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))) κ := by
  funext x
  unfold DGPS.interactionPotential
  have hW : ∀ y, (attractiveXY κ h).W x y =
      κ + (-(κ * (xyMode x).re)) * (xyMode y).re + (-(κ * (xyMode x).im)) * (xyMode y).im := by
    intro y
    rw [attractiveXY_W, xyMode_re_sub]; ring
  simp_rw [hW]
  set μ : Measure (DGPS.Torus 1) := (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) with hμ
  have i1 : Integrable (fun y => (-(κ * (xyMode x).re)) * (xyMode y).re) μ :=
    (integrable_xyMode_re μ).const_mul _
  have i2 : Integrable (fun y => (-(κ * (xyMode x).im)) * (xyMode y).im) μ :=
    (integrable_xyMode_im μ).const_mul _
  have i0 : Integrable (fun y : DGPS.Torus 1 => κ + (-(κ * (xyMode x).re)) * (xyMode y).re) μ :=
    (integrable_const κ).add i1
  rw [integral_add i0 i2, integral_add (integrable_const κ) i1,
    integral_const_mul, integral_const_mul]
  simp only [attractiveXY_V, xyTrig, xyZ1, xyZ2, integral_const]
  simp
  ring

theorem potentialEnergy_attractiveXY (κ h : ℝ) (ν : Measure (DGPS.Torus 1)) :
    DGPS.potentialEnergy (attractiveXY κ h) ν = -h * xyZ1 ν := by
  unfold DGPS.potentialEnergy xyZ1
  simp only [attractiveXY_V]
  rw [integral_const_mul]

theorem interactionEnergy_attractiveXY (κ h : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.interactionEnergy (attractiveXY κ h) ν =
      κ * (1 - (xyZ1 (ν : Measure (DGPS.Torus 1)) ^ 2 + xyZ2 (ν : Measure (DGPS.Torus 1)) ^ 2)) := by
  have hc : Continuous fun x => (xyMode x).re := Complex.continuous_re.comp continuous_xyMode
  have hs : Continuous fun x => (xyMode x).im := Complex.continuous_im.comp continuous_xyMode
  have hP : ∀ {f g : DGPS.Torus 1 → ℝ}, Continuous f → Continuous g →
      Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 => f p.1 * g p.2)
        ((ν : Measure (DGPS.Torus 1)).prod ν) := fun hf hg =>
    ((hf.comp continuous_fst).mul (hg.comp continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hform : ∀ p : DGPS.Torus 1 × DGPS.Torus 1,
      (attractiveXY κ h).W p.1 p.2 =
        κ - (κ * ((xyMode p.1).re * (xyMode p.2).re) +
          κ * ((xyMode p.1).im * (xyMode p.2).im)) := by
    intro p
    rw [attractiveXY_W, xyMode_re_sub]; ring
  unfold DGPS.interactionEnergy
  simp_rw [hform]
  have h1 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 =>
      κ * ((xyMode p.1).re * (xyMode p.2).re)) ((ν : Measure (DGPS.Torus 1)).prod ν) :=
    (hP hc hc).const_mul κ
  have h2 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 =>
      κ * ((xyMode p.1).im * (xyMode p.2).im)) ((ν : Measure (DGPS.Torus 1)).prod ν) :=
    (hP hs hs).const_mul κ
  have h12 : Integrable (fun p : DGPS.Torus 1 × DGPS.Torus 1 =>
      κ * ((xyMode p.1).re * (xyMode p.2).re) + κ * ((xyMode p.1).im * (xyMode p.2).im))
      ((ν : Measure (DGPS.Torus 1)).prod ν) := h1.add h2
  rw [integral_sub (integrable_const κ) h12, integral_add h1 h2,
    integral_const_mul, integral_const_mul,
    integral_prod_mul (fun x => (xyMode x).re) (fun x => (xyMode x).re),
    integral_prod_mul (fun x => (xyMode x).im) (fun x => (xyMode x).im)]
  simp only [xyZ1, xyZ2, integral_const]
  simp
  ring

theorem freeEnergy_attractiveXY (κ h : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.freeEnergy (attractiveXY κ h) ν =
      ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
        ((κ / 2 - h * xyZ1 (ν : Measure (DGPS.Torus 1)) -
          κ / 2 * (xyZ1 (ν : Measure (DGPS.Torus 1)) ^ 2 +
            xyZ2 (ν : Measure (DGPS.Torus 1)) ^ 2) : ℝ) : EReal) := by
  unfold DGPS.freeEnergy
  rw [potentialEnergy_attractiveXY, interactionEnergy_attractiveXY, add_assoc, ← EReal.coe_add]
  congr 2
  ring

theorem isSmoothPeriodic_interactionPotential (κ h : ℝ) (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.IsSmoothPeriodic (DGPS.interactionPotential (attractiveXY κ h) ρ) := by
  rw [interactionPotential_attractiveXY]; exact isSmoothPeriodic_xyTrig _ _ _

theorem isWeakGradientLp_one_of_smooth {φ : DGPS.Torus 1 → ℝ} (hφ : DGPS.IsSmoothPeriodic φ) :
    DGPS.IsWeakGradientLp 1 φ (DGPS.smoothGrad φ) := by
  have h := hφ.isWeakGradient
  exact ⟨h.memLp.mono_exponent (by norm_num), h.memLp_grad.mono_exponent (by norm_num), h.ibp⟩

end DGPS.Examples.AttractiveXY

namespace DGPS.Models

open DGPS.Examples.AttractiveXY

/-- The canonical absolute drift of the attractive XY model: the force of `ρ` is the classical
gradient of the smooth potential `V + W * (ρ m)`. -/
noncomputable def attractiveXYDrift (κ h : ℝ) : DGPS.AbsoluteDrift (attractiveXY κ h) where
  force := fun ρ => DGPS.smoothGrad (DGPS.interactionPotential (attractiveXY κ h) ρ)
  measurable_force := fun ρ =>
    (isSmoothPeriodic_interactionPotential κ h ρ).continuous_smoothGrad.measurable
  weak_gradient := fun ρ =>
    isWeakGradientLp_one_of_smooth (isSmoothPeriodic_interactionPotential κ h ρ)

end DGPS.Models

namespace DGPS.Examples.AttractiveXY

open DGPS.Models

theorem abs_xyTrig_zero_le (a b : ℝ) (x : DGPS.Torus 1) : |xyTrig a b 0 x| ≤ |a| + |b| := by
  unfold xyTrig
  rw [add_zero]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul_of_nonneg_left (abs_xyMode_re_le x) (abs_nonneg a)
  have h2 := mul_le_mul_of_nonneg_left (abs_xyMode_im_le x) (abs_nonneg b)
  linarith

theorem continuous_xyTrig (A B K : ℝ) : Continuous (xyTrig A B K) :=
  (isSmoothPeriodic_xyTrig A B K).continuous_torus

/-- The normalising constant `Z(a,b) = ∫ exp(a cos 2πx + b sin 2πx) dm`. -/
noncomputable def xyPartition (a b : ℝ) : ℝ :=
  ∫ x, Real.exp (xyTrig a b 0 x) ∂DGPS.haar 1

theorem integrable_exp_xyTrig (a b : ℝ) :
    Integrable (fun x => Real.exp (xyTrig a b 0 x)) (DGPS.haar 1) :=
  (Real.continuous_exp.comp (continuous_xyTrig a b 0)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem exp_neg_le_xyPartition (a b : ℝ) : Real.exp (-(|a| + |b|)) ≤ xyPartition a b := by
  have := integral_mono (integrable_const (Real.exp (-(|a| + |b|)))) (integrable_exp_xyTrig a b)
    (fun x => Real.exp_le_exp.2 (by linarith [neg_abs_le (xyTrig a b 0 x), abs_xyTrig_zero_le a b x]))
  unfold xyPartition
  simpa using this

theorem xyPartition_le_exp (a b : ℝ) : xyPartition a b ≤ Real.exp (|a| + |b|) := by
  have := integral_mono (integrable_exp_xyTrig a b) (integrable_const (Real.exp (|a| + |b|)))
    (fun x => Real.exp_le_exp.2 (by linarith [le_abs_self (xyTrig a b 0 x), abs_xyTrig_zero_le a b x]))
  unfold xyPartition
  simpa using this

theorem xyPartition_pos (a b : ℝ) : 0 < xyPartition a b :=
  lt_of_lt_of_le (Real.exp_pos _) (exp_neg_le_xyPartition a b)

theorem xyFrozen_lower (a b : ℝ) (x : DGPS.Torus 1) :
    Real.exp (-(|a| + |b|)) / Real.exp (|a| + |b|) ≤ Real.exp (xyTrig a b 0 x) / xyPartition a b :=
  div_le_div₀ (Real.exp_pos _).le
    (Real.exp_le_exp.2 (by linarith [neg_abs_le (xyTrig a b 0 x), abs_xyTrig_zero_le a b x]))
    (xyPartition_pos a b) (xyPartition_le_exp a b)

theorem xyFrozen_upper (a b : ℝ) (x : DGPS.Torus 1) :
    Real.exp (xyTrig a b 0 x) / xyPartition a b ≤ Real.exp (|a| + |b|) / Real.exp (-(|a| + |b|)) :=
  div_le_div₀ (Real.exp_pos _).le
    (Real.exp_le_exp.2 (by linarith [le_abs_self (xyTrig a b 0 x), abs_xyTrig_zero_le a b x]))
    (Real.exp_pos _) (exp_neg_le_xyPartition a b)

/-- The frozen reference law `p ∝ exp(a cos 2πx + b sin 2πx)` as a bounded positive reference. -/
noncomputable def xyFrozen (a b : ℝ) : DGPS.BoundedPositiveReference 1 where
  density := fun x => Real.exp (xyTrig a b 0 x) / xyPartition a b
  measurable_density :=
    ((Real.continuous_exp.comp (continuous_xyTrig a b 0)).div_const _).measurable
  lower := Real.exp (-(|a| + |b|)) / Real.exp (|a| + |b|)
  upper := Real.exp (|a| + |b|) / Real.exp (-(|a| + |b|))
  lower_pos := by positivity
  lower_le := Filter.Eventually.of_forall (xyFrozen_lower a b)
  le_upper := Filter.Eventually.of_forall (xyFrozen_upper a b)
  mass_one := by
    rw [integral_div]
    exact div_self (xyPartition_pos a b).ne'

theorem abs_exp_sub_le {s t B : ℝ} (hs : s ≤ B) (ht : t ≤ B) :
    |Real.exp s - Real.exp t| ≤ Real.exp B * |s - t| := by
  have key : ∀ {s t : ℝ}, t ≤ s → s ≤ B →
      Real.exp s - Real.exp t ≤ Real.exp B * (s - t) := by
    intro s t hts hsB
    have h1 := Real.add_one_le_exp (t - s)
    have h3 : Real.exp s * Real.exp (t - s) = Real.exp t := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp s - Real.exp t = Real.exp s * (1 - Real.exp (t - s)) := by
      rw [mul_sub, mul_one, h3]
    rw [h2]
    have h4 : 0 ≤ 1 - Real.exp (t - s) := by
      have : Real.exp (t - s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith
    exact mul_le_mul (Real.exp_le_exp.2 hsB) (by linarith) h4 (Real.exp_pos _).le
  rcases le_total t s with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact key h hs
  · rw [abs_sub_comm, abs_sub_comm s t, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)),
      abs_of_nonneg (sub_nonneg.2 h)]
    exact key h ht

theorem xyFrozen_hasPositiveLipschitzDensity (a b : ℝ) :
    (xyFrozen a b).hasPositiveLipschitzDensity := by
  refine ⟨Real.exp (|a| + |b|) / xyPartition a b * ((|a| + |b|) * (2 * Real.pi)),
    Real.exp (-(|a| + |b|)) / Real.exp (|a| + |b|), by positivity, xyFrozen_lower a b,
    fun x y => ?_⟩
  show |Real.exp (xyTrig a b 0 x) / xyPartition a b - Real.exp (xyTrig a b 0 y) / xyPartition a b|
    ≤ _
  have hZ := xyPartition_pos a b
  rw [← sub_div, abs_div, abs_of_pos hZ]
  have h1 := abs_exp_sub_le (abs_xyTrig_zero_le a b x |>.trans' (le_abs_self _))
    (abs_xyTrig_zero_le a b y |>.trans' (le_abs_self _))
  have h2 := abs_xyTrig_sub_le a b 0 x y
  rw [div_le_iff₀ hZ]
  calc _ ≤ Real.exp (|a| + |b|) * |xyTrig a b 0 x - xyTrig a b 0 y| := h1
    _ ≤ Real.exp (|a| + |b|) * ((|a| + |b|) * (2 * Real.pi) * DGPS.torusDist x y) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by field_simp

theorem log_xyFrozen_density (a b : ℝ) (x : DGPS.Torus 1) :
    Real.log ((xyFrozen a b).density x) = xyTrig a b (-Real.log (xyPartition a b)) x := by
  show Real.log (Real.exp (xyTrig a b 0 x) / xyPartition a b) = _
  rw [Real.log_div (Real.exp_pos _).ne' (xyPartition_pos a b).ne', Real.log_exp]
  simp only [xyTrig]; ring

theorem weakGradient_log_xyFrozen (a b : ℝ) :
    ∀ᵐ x ∂DGPS.haar 1,
      DGPS.weakGradient (fun x => Real.log ((xyFrozen a b).density x))
        ((xyFrozen a b).memH1_log (xyFrozen_hasPositiveLipschitzDensity a b)) x =
      DGPS.smoothGrad (xyTrig a b (-Real.log (xyPartition a b))) x := by
  have h1 := DGPS.isWeakGradient_weakGradient
    ((xyFrozen a b).memH1_log (xyFrozen_hasPositiveLipschitzDensity a b))
  have h2 : DGPS.IsWeakGradient (fun x => Real.log ((xyFrozen a b).density x))
      (DGPS.smoothGrad (xyTrig a b (-Real.log (xyPartition a b)))) := by
    have e : (fun x => Real.log ((xyFrozen a b).density x)) =
        xyTrig a b (-Real.log (xyPartition a b)) := funext (log_xyFrozen_density a b)
    rw [e]; exact (isSmoothPeriodic_xyTrig _ _ _).isWeakGradient
  exact h1.ae_eq h2

theorem smoothGrad_xyTrig_neg (A B K K' : ℝ) (x : DGPS.Torus 1) :
    DGPS.smoothGrad (xyTrig (-A) (-B) K) x = -DGPS.smoothGrad (xyTrig A B K') x := by
  ext j
  fin_cases j
  simp [DGPS.smoothGrad_apply, coordPartial_xyTrig, xyTrig]
  ring

end DGPS.Examples.AttractiveXY

namespace DGPS.Examples.AttractiveXY

open DGPS.Models

/-- The frozen law `p_{h,z} ∝ exp((h e₁ + κ z) · (cos 2πx, sin 2πx))` attached to a mean `z` of the
measure `ν`, as a bounded positive reference. -/
noncomputable abbrev xyFrozenLaw (κ h : ℝ) (ν : Measure (DGPS.Torus 1)) :
    DGPS.BoundedPositiveReference 1 :=
  xyFrozen (h + κ * xyZ1 ν) (κ * xyZ2 ν)

theorem force_ae_eq_neg_log (κ h : ℝ) (b : DGPS.AbsoluteDrift (attractiveXY κ h))
    (ρ : DGPS.AbsoluteDensity 1) :
    b.force ρ =ᵐ[DGPS.haar 1] fun x =>
      -DGPS.weakGradient
        (fun x => Real.log ((xyFrozenLaw κ h (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))).density x))
        ((xyFrozenLaw κ h (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))).memH1_log
          (xyFrozen_hasPositiveLipschitzDensity _ _)) x := by
  have hg := isWeakGradientLp_one_of_smooth (isSmoothPeriodic_interactionPotential κ h ρ)
  have h1 := b.ae_eq_of_isWeakGradient ρ hg
  have h2 := weakGradient_log_xyFrozen
    (h + κ * xyZ1 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))
    (κ * xyZ2 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, interactionPotential_attractiveXY]
  exact smoothGrad_xyTrig_neg _ _ _ _ x

theorem lintegral_score_attractiveXY (κ h : ℝ) (b : DGPS.AbsoluteDrift (attractiveXY κ h))
    (σ u : DGPS.AbsoluteDensity 1) :
    ∫⁻ x, ENNReal.ofReal
        (‖(2 : ℝ) • DGPS.weakGradient u.sqrt u.sqrt_mem x + u.sqrt x • b.force σ x‖ ^ 2)
        ∂DGPS.haar 1 =
      DGPS.ordinaryRelativeFisher (DGPS.densityMeasure u : Measure (DGPS.Torus 1))
        (xyFrozenLaw κ h (DGPS.densityMeasure σ : Measure (DGPS.Torus 1))) := by
  rw [DGPS.positiveReference_absolute_identity _ (xyFrozen_hasPositiveLipschitzDensity _ _) u]
  refine lintegral_congr_ae ?_
  filter_upwards [force_ae_eq_neg_log κ h b σ] with x hx
  rw [hx, smul_neg, ← sub_eq_add_neg, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end DGPS.Examples.AttractiveXY

namespace DGPS.Examples.AttractiveXY

open DGPS.Models

theorem scalarDissipation_attractiveXY (κ h : ℝ) (b : DGPS.AbsoluteDrift (attractiveXY κ h))
    (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.scalarDissipation (attractiveXY κ h) b ρ =
      DGPS.ordinaryRelativeFisher (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))
        (xyFrozenLaw κ h (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))) := by
  rw [← lintegral_score_attractiveXY κ h b ρ ρ]
  rfl

theorem speciesDissipation_attractiveXY (κ h : ℝ) (b : DGPS.AbsoluteDrift (attractiveXY κ h))
    (F : DGPS.SpeciesFamily 1) :
    DGPS.speciesDissipation (attractiveXY κ h) b F =
      ∑ s, ENNReal.ofReal (F.weight s) *
        DGPS.ordinaryRelativeFisher (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))
          (xyFrozenLaw κ h (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1))) := by
  unfold DGPS.speciesDissipation
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← lintegral_score_attractiveXY κ h b (DGPS.barycenter F) (F.density s)]
  rfl

theorem integral_barycenter (F : DGPS.SpeciesFamily 1) {f : DGPS.Torus 1 → ℝ} (hf : Continuous f)
    (hb : ∀ x, ‖f x‖ ≤ 1) :
    ∫ x, f x ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) =
      ∑ s, F.weight s * ∫ x, f x ∂(DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) := by
  simp_rw [integral_densityMeasure]
  have hi : ∀ s, Integrable (fun x => (F.density s).density x * f x) (DGPS.haar 1) := fun s =>
    (F.density s).integrable_density.mul_bdd hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  have e : ∀ x, (DGPS.barycenter F).density x * f x =
      ∑ s, F.weight s * ((F.density s).density x * f x) := by
    intro x
    rw [DGPS.SpeciesFamily.barycenter_density_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [DGPS.AbsoluteDensity.density]; ring
  simp_rw [e]
  rw [integral_finsetSum _ fun s _ => (hi s).const_mul _]
  simp_rw [integral_const_mul]

theorem xyZ1_barycenter (F : DGPS.SpeciesFamily 1) :
    xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) =
      ∑ s, F.weight s * xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) :=
  integral_barycenter F (Complex.continuous_re.comp continuous_xyMode)
    (fun x => by rw [Real.norm_eq_abs]; exact abs_xyMode_re_le x)

theorem xyZ2_barycenter (F : DGPS.SpeciesFamily 1) :
    xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) =
      ∑ s, F.weight s * xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) :=
  integral_barycenter F (Complex.continuous_im.comp continuous_xyMode)
    (fun x => by rw [Real.norm_eq_abs]; exact abs_xyMode_im_le x)

theorem xyFrozenLaw_density (κ h : ℝ) (ν : Measure (DGPS.Torus 1)) (x : DGPS.Torus 1) :
    (xyFrozenLaw κ h ν).density x =
      Real.exp ((h + κ * xyZ1 ν) * (xyMode x).re + (κ * xyZ2 ν) * (xyMode x).im) /
        ∫ y, Real.exp ((h + κ * xyZ1 ν) * (xyMode y).re + (κ * xyZ2 ν) * (xyMode y).im)
          ∂DGPS.haar 1 := by
  show Real.exp (xyTrig _ _ 0 x) / xyPartition _ _ = _
  simp [xyTrig, xyPartition]

end DGPS.Examples.AttractiveXY

namespace DGPS.Examples

open DGPS.Models DGPS.Examples.AttractiveXY

/-- EX018.  The attractive XY model on the circle `𝕋¹`, `V = -h cos θ`,
`W = κ (1 - cos(θ - φ))`, with `κ, h ≥ 0`, and its frozen scores.  Writing `z = ρ(cos, sin)`:

1. `V` and `W` are given by the displayed cosines and `W` vanishes on the diagonal;
2. `F(ν) = H(ν | Haar) + κ/2 - h z₁ - κ |z|² / 2` (in `EReal`);
3. the frozen law is `p_{h,z} = exp((h e₁ + κ z) · (cos, sin)) / Z`;
4. for every absolute drift of the model (e.g. `attractiveXYDrift κ h`) the scalar dissipation is the
   ordinary relative Fisher information `D(ρ) = I(ρ m | p_{h,z})` with `z` the mean of `ρ`;
5. for every species family `D_θ = ∑ θ_s I(ρ_s m | p_{h,z̄})` with the common mean `z̄` of the
   barycenter, `z̄ = ∑ θ_s z_s`. -/
theorem attractive_xy_model_and_frozen_scores (κ h : ℝ) (_hκ : 0 ≤ κ) (_hh : 0 ≤ h) :
    (∀ a b : Fin 1 → ℝ,
      (attractiveXY κ h).V (DGPS.torusLift a) = -h * Real.cos (2 * Real.pi * a 0) ∧
      (attractiveXY κ h).W (DGPS.torusLift a) (DGPS.torusLift b) =
        κ * (1 - Real.cos (2 * Real.pi * (a 0 - b 0)))) ∧
    (∀ x, (attractiveXY κ h).W x x = 0) ∧
    (∀ ν : MeasureTheory.ProbabilityMeasure (DGPS.Torus 1),
      DGPS.freeEnergy (attractiveXY κ h) ν =
        ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
          ((κ / 2 - h * xyZ1 (ν : Measure (DGPS.Torus 1)) -
            κ / 2 * (xyZ1 (ν : Measure (DGPS.Torus 1)) ^ 2 +
              xyZ2 (ν : Measure (DGPS.Torus 1)) ^ 2) : ℝ) : EReal)) ∧
    (∀ (ν : Measure (DGPS.Torus 1)) (x : DGPS.Torus 1),
      (xyFrozenLaw κ h ν).density x =
        Real.exp ((h + κ * xyZ1 ν) * (xyMode x).re + (κ * xyZ2 ν) * (xyMode x).im) /
          ∫ y, Real.exp ((h + κ * xyZ1 ν) * (xyMode y).re + (κ * xyZ2 ν) * (xyMode y).im)
            ∂DGPS.haar 1) ∧
    (∀ (b : DGPS.AbsoluteDrift (attractiveXY κ h)) (ρ : DGPS.AbsoluteDensity 1),
      DGPS.scalarDissipation (attractiveXY κ h) b ρ =
        DGPS.ordinaryRelativeFisher (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))
          (xyFrozenLaw κ h (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))) ∧
    (∀ (b : DGPS.AbsoluteDrift (attractiveXY κ h)) (F : DGPS.SpeciesFamily 1),
      DGPS.speciesDissipation (attractiveXY κ h) b F =
        ∑ s, ENNReal.ofReal (F.weight s) *
          DGPS.ordinaryRelativeFisher (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))
            (xyFrozenLaw κ h (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1))) ∧
      xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) =
        ∑ s, F.weight s * xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ∧
      xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) =
        ∑ s, F.weight s * xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))) :=
  ⟨fun a b => ⟨attractiveXY_V_lift κ h a, attractiveXY_W_lift κ h a b⟩,
    fun x => (attractiveXY κ h).W_diag x,
    freeEnergy_attractiveXY κ h,
    xyFrozenLaw_density κ h,
    fun b ρ => scalarDissipation_attractiveXY κ h b ρ,
    fun b F => ⟨speciesDissipation_attractiveXY κ h b F, xyZ1_barycenter F, xyZ2_barycenter F⟩⟩

end DGPS.Examples
