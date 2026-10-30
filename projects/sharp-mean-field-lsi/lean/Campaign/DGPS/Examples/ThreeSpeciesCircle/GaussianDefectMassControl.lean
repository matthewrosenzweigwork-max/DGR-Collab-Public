import DGPS.Examples.ThreeSpeciesCircle.GaussianFirstProjection

/-! Quantitative full-native reference mass control by the actual Poincare
defect and the two actual first-feature moments. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private def nativeSum {h : ℝ} (hh : 0 < h) (f g : WeakH1Test (refProb hh)) :
    WeakH1Test (refProb hh) where
  fn x := f.fn x + g.fn x
  grad x := f.grad x + g.grad x
  isWeak := by
    apply (isMeasureWeakGradient_iff (ordinaryReference h)).mpr
    apply (isWeightedWeakGradient_iff (ordinaryReference h)).mpr
    exact ((isWeightedWeakGradient_iff (ordinaryReference h)).mp
      ((isMeasureWeakGradient_iff (ordinaryReference h)).mp f.isWeak)).add
      ((isWeightedWeakGradient_iff (ordinaryReference h)).mp
        ((isMeasureWeakGradient_iff (ordinaryReference h)).mp g.isWeak))

private theorem native_parallelogram {h : ℝ} (hh : 0 < h)
    (f p : WeakH1Test (refProb hh)) :
    gaussianReferenceMass hh (nativeSum hh f p) +
        gaussianReferenceMass hh (gaussianReferenceTestSubtract hh f p) =
      2 * (gaussianReferenceMass hh f + gaussianReferenceMass hh p) ∧
    gaussianReferenceRealEnergy hh (nativeSum hh f p) +
        gaussianReferenceRealEnergy hh (gaussianReferenceTestSubtract hh f p) =
      2 * (gaussianReferenceRealEnergy hh f + gaussianReferenceRealEnergy hh p) := by
  let z := nativeSum hh f p
  let w := gaussianReferenceTestSubtract hh f p
  constructor
  · unfold gaussianReferenceMass
    rw [← integral_add z.isWeak.memLp.integrable_sq w.isWeak.memLp.integrable_sq,
      ← integral_add f.isWeak.memLp.integrable_sq p.isWeak.memLp.integrable_sq,
      ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (f.fn x + p.fn x) ^ 2 + (f.fn x - p.fn x) ^ 2 = _
      ring
  · unfold gaussianReferenceRealEnergy
    rw [← integral_add z.isWeak.memLp_grad.norm.integrable_sq w.isWeak.memLp_grad.norm.integrable_sq,
      ← integral_add f.isWeak.memLp_grad.norm.integrable_sq p.isWeak.memLp_grad.norm.integrable_sq,
      ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => parallelogram_law_with_norm ℝ (f.grad x) (p.grad x)

private theorem centered_variance {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh))
    (hf : (∫ x, f.fn x ∂(refProb hh : Measure (Torus 1))) = 0) :
    weightedVariance (refProb hh) f.fn = gaussianReferenceMass hh f := by
  unfold weightedVariance gaussianReferenceMass
  rw [hf]
  simp only [sub_zero]

/-- The full native mass is controlled by its actual reference defect and
actual C/S coordinates. The physical Haar constant and h dependence are explicit. -/
theorem gaussianReference_mass_defect_first_moments {h : ℝ} (hh : 0 < h)
    (hhsmall : |h| ≤ 1 / 1000) (f : WeakH1Test (refProb hh))
    (hf : (∫ x, f.fn x ∂(refProb hh : Measure (Torus 1))) = 0) :
    a0 * gaussianReferenceMass hh f ≤
      2 * (gaussianReferenceRealEnergy hh f -
        (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh f) +
      6 * a0 * h ^ 2 *
        ((∫ x, featureC h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2 +
          (∫ x, featureS h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2) := by
  let P := (poincareRate (refProb hh)).toReal
  let p := gaussianReferenceFirstProjection hh f
  let w := gaussianReferenceTestSubtract hh f p
  let z := nativeSum hh f p
  obtain ⟨hpm, hwc, hws⟩ := gaussianReferenceFirstProjection_constraints hh f
  obtain ⟨hLp, hEp, hLf⟩ := gaussianReferenceFirstProjection_forms hh f
  have hwm : (∫ x, w.fn x ∂(refProb hh : Measure (Torus 1))) = 0 := by
    change (∫ x, f.fn x - p.fn x ∂(refProb hh : Measure (Torus 1))) = 0
    rw [integral_sub (f.isWeak.memLp.integrable (by norm_num))
      (p.isWeak.memLp.integrable (by norm_num)), hf, hpm, sub_self]
  have hzm : (∫ x, z.fn x ∂(refProb hh : Measure (Torus 1))) = 0 := by
    change (∫ x, f.fn x + p.fn x ∂(refProb hh : Measure (Torus 1))) = 0
    rw [integral_add (f.isWeak.memLp.integrable (by norm_num))
      (p.isWeak.memLp.integrable (by norm_num)), hf, hpm, zero_add]
  have hc : (∫ x, w.fn x * cosHarm 1 x ∂(refProb hh : Measure (Torus 1))) = 0 := by
    have he : (fun x => w.fn x * cosHarm 1 x) = fun x => h * (featureC h x * w.fn x) := by
      funext x; unfold featureC; field_simp [hh.ne'] <;> ring
    rw [he, integral_const_mul, hwc, mul_zero]
  have hs : (∫ x, w.fn x * sinHarm 1 x ∂(refProb hh : Measure (Torus 1))) = 0 := by
    have he : (fun x => w.fn x * sinHarm 1 x) = fun x => h * (featureS h x * w.fn x) := by
      funext x; unfold featureS; field_simp [hh.ne'] <;> ring
    rw [he, integral_const_mul, hws, mul_zero]
  have hg := threefold_reference_constrained_gap_native hh hhsmall w hc hs
  rw [gaussianReference_energy_eq_ofReal, centered_variance hh w hwm] at hg
  have hLw : 0 ≤ gaussianReferenceMass hh w := integral_nonneg fun _ => sq_nonneg _
  have hLp0 : 0 ≤ gaussianReferenceMass hh p := integral_nonneg fun _ => sq_nonneg _
  have hEw : 0 ≤ gaussianReferenceRealEnergy hh w := integral_nonneg fun _ => sq_nonneg _
  have hg' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  have h2Lw : 0 ≤ 2 * a0 * gaussianReferenceMass hh w :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) a0_pos.le) hLw
  rw [ENNReal.toReal_ofReal h2Lw,
    ENNReal.toReal_ofReal hEw] at hg'
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top (threefold_reference_poincare_upper hh)
  rw [ENNReal.toReal_ofReal a0_pos.le] at hu
  change P ≤ a0 at hu
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  have hz := gaussianReference_poincare_real hh z
  rw [centered_variance hh z hzm] at hz
  change P * gaussianReferenceMass hh z ≤ gaussianReferenceRealEnergy hh z at hz
  obtain ⟨hLpar, hEpar⟩ := native_parallelogram hh f p
  change gaussianReferenceMass hh z + gaussianReferenceMass hh w =
    2 * (gaussianReferenceMass hh f + gaussianReferenceMass hh p) at hLpar
  change gaussianReferenceRealEnergy hh z + gaussianReferenceRealEnergy hh w =
    2 * (gaussianReferenceRealEnergy hh f + gaussianReferenceRealEnergy hh p) at hEpar
  have hdw : gaussianReferenceRealEnergy hh w - P * gaussianReferenceMass hh w ≤
      2 * (gaussianReferenceRealEnergy hh f - P * gaussianReferenceMass hh f) +
        2 * (gaussianReferenceRealEnergy hh p - P * gaussianReferenceMass hh p) := by
    have hLparP := congrArg (fun t : ℝ => P * t) hLpar
    nlinarith only [hz, hLparP, hEpar]
  have hwlow : a0 * gaussianReferenceMass hh w ≤
      gaussianReferenceRealEnergy hh w - P * gaussianReferenceMass hh w := by
    nlinarith only [hg', mul_le_mul_of_nonneg_right hu hLw]
  have hscaled : a0 * gaussianReferenceMass hh f ≤
      2 * (gaussianReferenceRealEnergy hh f - P * gaussianReferenceMass hh f) +
        3 * a0 * gaussianReferenceMass hh p := by
    change gaussianReferenceRealEnergy hh p = a0 * gaussianReferenceMass hh p at hEp
    change gaussianReferenceMass hh f = gaussianReferenceMass hh p + gaussianReferenceMass hh w at hLf
    calc
      a0 * gaussianReferenceMass hh f =
          a0 * gaussianReferenceMass hh p + a0 * gaussianReferenceMass hh w := by
        rw [hLf]
        ring
      _ ≤ a0 * gaussianReferenceMass hh p +
          (gaussianReferenceRealEnergy hh w - P * gaussianReferenceMass hh w) :=
        add_le_add le_rfl hwlow
      _ ≤ a0 * gaussianReferenceMass hh p +
          (2 * (gaussianReferenceRealEnergy hh f - P * gaussianReferenceMass hh f) +
            2 * (gaussianReferenceRealEnergy hh p - P * gaussianReferenceMass hh p)) :=
        add_le_add le_rfl hdw
      _ ≤ 2 * (gaussianReferenceRealEnergy hh f - P * gaussianReferenceMass hh f) +
          3 * a0 * gaussianReferenceMass hh p := by
        rw [hEp]
        nlinarith only [mul_nonneg hP hLp0]
  rw [hLp] at hscaled
  convert hscaled using 1 <;> dsimp only [P] <;> ring

end DGPS.Examples.ThreeSpeciesCircle
