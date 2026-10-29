import LeanResearch.PeriodicAttractiveLogGas.RadialScaling
import LeanResearch.PeriodicAttractiveLogGas.RadialHarmonicReproduction
import LeanResearch.PeriodicAttractiveLogGas.QuadraticPotential

/-! Actual first and second moments and harmonic reproduction for the one
fixed scaled radial family used in source Lemma 2.2. -/

noncomputable section
open MeasureTheory Set Metric InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas

theorem integrable_scaledRadialMollifier_mul_continuous (ε : ℝ) (hε : 0 < ε)
    {f : PlanarSpace → ℝ} (hf : Continuous f) :
    Integrable (fun y ↦ scaledRadialMollifier ε y * f y) volume :=
  ((contDiff_scaledRadialMollifier ε).continuous.mul hf).integrable_of_hasCompactSupport
    (hasCompactSupport_scaledRadialMollifier ε hε).mul_right

theorem integral_scaledRadialMollifier_mul_linear (ε : ℝ)
    (L : PlanarSpace →L[ℝ] ℝ) :
    (∫ y, scaledRadialMollifier ε y * L y) = 0 := by
  have h := integral_neg_eq_self (fun y : PlanarSpace ↦
    scaledRadialMollifier ε y * L y) volume
  simp only [scaledRadialMollifier_neg, map_neg, mul_neg, integral_neg] at h
  linarith

theorem integral_scaledRadialMollifier_mul_norm_sq_le (ε : ℝ) (hε : 0 < ε) :
    (∫ y, scaledRadialMollifier ε y * ‖y‖ ^ 2) ≤ ε ^ 2 := by
  calc
    (∫ y, scaledRadialMollifier ε y * ‖y‖ ^ 2) ≤
        ∫ y, scaledRadialMollifier ε y * ε ^ 2 := by
      apply integral_mono
        (integrable_scaledRadialMollifier_mul_continuous ε hε
          (f := fun y : PlanarSpace ↦ ‖y‖ ^ 2) (continuous_norm.pow 2))
        ((integrable_scaledRadialMollifier ε hε).mul_const _)
      intro y
      by_cases hy : scaledRadialMollifier ε y = 0
      · simp only [hy, zero_mul, le_refl]
      · have hb := mem_ball_zero_iff.mp (support_scaledRadialMollifier_subset ε hε hy)
        apply mul_le_mul_of_nonneg_left _ (scaledRadialMollifier_nonneg ε y)
        nlinarith [norm_nonneg y]
    _ = ε ^ 2 := by rw [integral_mul_const, integral_scaledRadialMollifier ε hε, one_mul]

theorem integral_scaledRadialMollifier_mul_quadratic (ε : ℝ) (hε : 0 < ε)
    (x : PlanarSpace) :
    (∫ y, scaledRadialMollifier ε y * planarGreenQuadratic (x - y)) =
      planarGreenQuadratic x +
        (Real.pi / 2) * (∫ y, scaledRadialMollifier ε y * ‖y‖ ^ 2) := by
  have hconst := (integrable_scaledRadialMollifier ε hε).mul_const (planarGreenQuadratic x)
  have hlinear := (integrable_scaledRadialMollifier_mul_continuous ε hε
    (show Continuous (fun y : PlanarSpace ↦ inner ℝ x y) from (innerSL ℝ x).continuous)).const_mul Real.pi
  have hquad := (integrable_scaledRadialMollifier_mul_continuous ε hε
    (f := fun y : PlanarSpace ↦ ‖y‖ ^ 2) (continuous_norm.pow 2)).const_mul (Real.pi / 2)
  have hsub : Integrable (fun y ↦ scaledRadialMollifier ε y * planarGreenQuadratic x -
      Real.pi * (scaledRadialMollifier ε y * inner ℝ x y)) volume := hconst.sub hlinear
  have heq (y : PlanarSpace) :
      scaledRadialMollifier ε y * planarGreenQuadratic (x - y) =
        scaledRadialMollifier ε y * planarGreenQuadratic x -
          Real.pi * (scaledRadialMollifier ε y * inner ℝ x y) +
          (Real.pi / 2) * (scaledRadialMollifier ε y * ‖y‖ ^ 2) := by
    rw [planarGreenQuadratic, planarGreenQuadratic, norm_sub_sq_real]
    ring
  simp_rw [heq]
  rw [integral_add hsub hquad, integral_sub hconst hlinear,
    integral_mul_const, integral_scaledRadialMollifier ε hε, one_mul,
    integral_const_mul, integral_const_mul]
  have hz : (∫ y, scaledRadialMollifier ε y * inner ℝ x y) = 0 :=
    integral_scaledRadialMollifier_mul_linear ε (innerSL ℝ x)
  rw [hz, mul_zero, sub_zero]

theorem integral_scaledRadialMollifier_mul_quadratic_le (ε : ℝ) (hε : 0 < ε)
    (x : PlanarSpace) :
    (∫ y, scaledRadialMollifier ε y * planarGreenQuadratic (x - y)) ≤
      planarGreenQuadratic x + (Real.pi / 2) * ε ^ 2 := by
  rw [integral_scaledRadialMollifier_mul_quadratic ε hε x]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_scaledRadialMollifier_mul_norm_sq_le ε hε) (by positivity))

theorem integral_scaledRadialMollifier_mul_add_harmonic (ε : ℝ) (hε : 0 < ε)
    {h : PlanarSpace → ℝ} (hc : Continuous h) {x : PlanarSpace}
    (hh : HarmonicOnNhd h (closedBall x ε)) :
    (∫ y, scaledRadialMollifier ε y * h (x + y)) = h x := by
  let l : ℂ ≃ₗᵢ[ℝ] PlanarSpace := Complex.orthonormalBasisOneI.repr
  let c : ℂ := l.symm x
  have hhc : HarmonicOnNhd (h ∘ l) (closedBall c ε) := by
    intro z hz
    apply (harmonicAt_comp_linearIsometryEquiv_right_iff l).2
    apply hh
    change dist z c ≤ ε at hz
    change dist (l z) x ≤ ε
    calc
      dist (l z) x = dist z c := by
        change dist (l z) x = dist z (l.symm x)
        rw [← l.dist_map, l.apply_symm_apply]
      _ ≤ ε := hz
  have hmass : (∫ z : ℂ, scaledRadialMollifier ε (l z)) = 1 := by
    rw [l.measurePreserving.integral_comp l.toHomeomorph.measurableEmbedding]
    exact integral_scaledRadialMollifier ε hε
  have hrep := integral_complex_radial_mul_add
    (κ := fun z : ℂ ↦ scaledRadialMollifier ε (l z)) (h := h ∘ l) (c := c) ε
    ((contDiff_scaledRadialMollifier ε).continuous.comp l.continuous)
    (fun {z w} hzw ↦ scaledRadialMollifier_eq_of_norm_eq ε
      (by simpa only [l.norm_map] using hzw))
    (fun z hz ↦ scaledRadialMollifier_eq_zero_of_half_le_norm ε hε
      (by rw [l.norm_map]; linarith))
    (hc.comp l.continuous) hhc
  rw [hmass, one_mul] at hrep
  have hchange := l.measurePreserving.integral_comp l.toHomeomorph.measurableEmbedding
    (fun y ↦ scaledRadialMollifier ε y * h (x + y))
  rw [← hchange]
  simpa only [Function.comp_apply, c, map_add, l.apply_symm_apply] using hrep

theorem integral_scaledRadialMollifier_mul_sub_harmonic (ε : ℝ) (hε : 0 < ε)
    {h : PlanarSpace → ℝ} (hc : Continuous h) {x : PlanarSpace}
    (hh : HarmonicOnNhd h (closedBall x ε)) :
    (∫ y, scaledRadialMollifier ε y * h (x - y)) = h x := by
  have hneg := integral_neg_eq_self
    (fun y ↦ scaledRadialMollifier ε y * h (x - y)) volume
  have hplus : (∫ y, scaledRadialMollifier ε y * h (x + y)) =
      ∫ y, scaledRadialMollifier ε y * h (x - y) := by
    simpa only [scaledRadialMollifier_neg, sub_neg_eq_add] using hneg
  rw [← hplus]
  exact integral_scaledRadialMollifier_mul_add_harmonic ε hε hc hh

end PeriodicAttractiveLogGas
