import DGPS.Examples.CriticalRecoveryEX021
import DGPS.FiniteN.SymmetricHarmonicTrial

/-!
# Exact first-harmonic Hessian range at criticality (EX021)
-/

open MeasureTheory

namespace DGPS.Examples.CriticalHessianKernelEX021

open DGPS.Examples.AttractiveXY
open DGPS.Examples.CriticalRecoveryEX021

theorem xyMode_neg_hessianEX021 (x : DGPS.Torus 1) :
    xyMode (-x) = star (xyMode x) := by
  simpa [xyMode_zero] using xyMode_sub (0 : DGPS.Torus 1) x

theorem integral_re_im_product_zero_EX021 :
    ∫ x, (xyMode x).re * (xyMode x).im ∂DGPS.haar 1 = 0 := by
  have : (DGPS.haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  have hodd : ∀ x : DGPS.Torus 1,
      (xyMode (-x)).re * (xyMode (-x)).im =
        -((xyMode x).re * (xyMode x).im) := by
    intro x
    rw [xyMode_neg_hessianEX021]
    simp
  have h := integral_neg_eq_self
    (fun x : DGPS.Torus 1 => (xyMode x).re * (xyMode x).im)
    (DGPS.haar 1)
  simp_rw [hodd] at h
  rw [integral_neg] at h
  linarith

theorem integral_xyMode_re_sq_EX021 :
    ∫ x, (xyMode x).re ^ 2 ∂DGPS.haar 1 = 1 / 2 := by
  simpa [xyMode, DGPS.FiniteN.mode] using DGPS.FiniteN.integral_re_mode_one_sq

theorem integral_xyMode_im_sq_EX021 :
    ∫ x, (xyMode x).im ^ 2 ∂DGPS.haar 1 = 1 / 2 := by
  simpa [xyMode, DGPS.FiniteN.mode] using DGPS.FiniteN.integral_im_mode_one_sq

noncomputable def firstHarmonicPartEX021
    (f : Lp ℝ 2 (DGPS.haar 1)) : Lp ℝ 2 (DGPS.haar 1) :=
  BoundedContinuousFunction.toLp 2 (DGPS.haar 1) ℝ
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x => 2 * ((xyMode x).re * ∫ y, (xyMode y).re * f y ∂DGPS.haar 1 +
        (xyMode x).im * ∫ y, (xyMode y).im * f y ∂DGPS.haar 1),
        ((continuous_const.mul (((Complex.continuous_re.comp continuous_xyMode).mul
          continuous_const).add ((Complex.continuous_im.comp continuous_xyMode).mul
          continuous_const))))⟩)

theorem firstHarmonicPart_ae_reprEX021 (f : Lp ℝ 2 (DGPS.haar 1)) :
    firstHarmonicPartEX021 f =ᵐ[DGPS.haar 1]
      (fun x => 2 * ((xyMode x).re * ∫ y, (xyMode y).re * f y ∂DGPS.haar 1 +
        (xyMode x).im * ∫ y, (xyMode y).im * f y ∂DGPS.haar 1)) := by
  unfold firstHarmonicPartEX021
  exact BoundedContinuousFunction.coeFn_toLp 2 (DGPS.haar 1) ℝ _

theorem kernelTransform_critical_formula_EX021
    (f : Lp ℝ 2 (DGPS.haar 1)) (x : DGPS.Torus 1) :
    DGPS.kernelTransform (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) f x =
      -2 * ((xyMode x).re * ∫ y, (xyMode y).re * f y ∂DGPS.haar 1 +
        (xyMode x).im * ∫ y, (xyMode y).im * f y ∂DGPS.haar 1) := by
  have hc : Continuous (fun y : DGPS.Torus 1 => (xyMode y).re) :=
    Complex.continuous_re.comp continuous_xyMode
  have hs : Continuous (fun y : DGPS.Torus 1 => (xyMode y).im) :=
    Complex.continuous_im.comp continuous_xyMode
  have hci : Integrable (fun y => (xyMode y).re * f y) (DGPS.haar 1) :=
    (DGPS.integrable_lp (DGPS.haarProbability 1) f).bdd_mul (c := 1)
      hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa using DGPS.Examples.AttractiveXY.abs_xyMode_re_le y)
  have hsi : Integrable (fun y => (xyMode y).im * f y) (DGPS.haar 1) :=
    (DGPS.integrable_lp (DGPS.haarProbability 1) f).bdd_mul (c := 1)
      hs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa using DGPS.Examples.AttractiveXY.abs_xyMode_im_le y)
  have hpoint : ∀ y,
      DGPS.centeredKernel (DGPS.Models.attractiveXY 2 0)
          (DGPS.haarProbability 1) x y * f y =
        -2 * ((xyMode x).re * ((xyMode y).re * f y) +
          (xyMode x).im * ((xyMode y).im * f y)) := by
    intro y
    rw [centeredKernel_critical_xy021, xyMode_re_sub]
    ring
  unfold DGPS.kernelTransform
  refine (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans ?_
  have hmeas : ((DGPS.haarProbability 1 : MeasureTheory.ProbabilityMeasure (DGPS.Torus 1)) :
      Measure (DGPS.Torus 1)) = DGPS.haar 1 := rfl
  rw [hmeas, integral_const_mul, integral_add (hci.const_mul _) (hsi.const_mul _),
    integral_const_mul, integral_const_mul]

theorem kernelOp_critical_range_EX021
    (f : Lp ℝ 2 (DGPS.haar 1)) :
    DGPS.kernelOp (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) f =
      -firstHarmonicPartEX021 f := by
  have hpart := firstHarmonicPart_ae_reprEX021 f
  have hneg := Lp.coeFn_neg (firstHarmonicPartEX021 f)
  apply Lp.ext
  filter_upwards [DGPS.kernelOp_ae (DGPS.Models.attractiveXY 2 0)
    (DGPS.haarProbability 1) f, hpart, hneg] with x hx hp hn
  refine hx.trans ((kernelTransform_critical_formula_EX021 f x).trans ?_)
  refine Eq.trans ?_ hn.symm
  rw [Pi.neg_apply, hp]
  ring

theorem exact_hessian_kernel_projection_EX021 :
    ∀ f : DGPS.centeredL2 (DGPS.haarProbability 1),
      DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
          (DGPS.haarProbability 1) f = 0 ↔
        f.1 = firstHarmonicPartEX021 f.1 := by
  intro f
  let G : Lp ℝ 2 ((DGPS.haarProbability 1 : MeasureTheory.ProbabilityMeasure (DGPS.Torus 1)) :
      Measure (DGPS.Torus 1)) := firstHarmonicPartEX021 f.1
  have hK : DGPS.kernelOp (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) f.1 = -G :=
    kernelOp_critical_range_EX021 f.1
  have hcoe :
      (DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
          (DGPS.haarProbability 1) f).1 = f.1 - G := by
    have h1 : (DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
          (DGPS.haarProbability 1) f).1 = f.1 +
        DGPS.kernelOp (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) f.1 := rfl
    rw [h1, hK]
    abel
  constructor
  · intro h
    have h' : (DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
          (DGPS.haarProbability 1) f).1 = 0 := by rw [h]; rfl
    rw [hcoe] at h'
    exact sub_eq_zero.mp h'
  · intro h
    apply Subtype.ext
    rw [hcoe]
    exact sub_eq_zero.mpr h

end DGPS.Examples.CriticalHessianKernelEX021
