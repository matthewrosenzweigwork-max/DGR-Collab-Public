import DGPS.Examples.ThreeSpeciesCircle.GaussianComparison
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFormIntegrals
import DGPS.Frontier.STR029.T35

/-! Exact finite-feature reference Gram data for the strict Gaussian lifting
argument. Only the genuine C3 reference symmetry is used; none of the model
features is asserted to be an eigenfunction of the weighted generator. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Native reference integration in the actual angular reference chart. -/
theorem threefoldReference_integral_angular (h : ℝ) (f : Torus 1 → ℝ) :
    (∫ x, f x ∂threefoldReference h) = normInt_STR02933
      (fun t => qT_STR02904 h t * f (angEquiv.symm (t : AngCircle))) := by
  rw [integral_threefoldReference]
  have he : (fun x => referenceDensity h x * f x) =
      fun x => (fun θ : AngCircle => qT_STR02904 h (angSec θ) *
        f (angEquiv.symm θ)) (angEquiv x) := by
    funext x
    have hq := qAng_eq_qT_STR02962 h (angEquiv x)
    change referenceDensity h (angEquiv.symm (angEquiv x)) =
      qT_STR02904 h (angSec (angEquiv x)) at hq
    simp only [angEquiv.symm_apply_apply] at hq ⊢
    rw [hq]
  rw [he, integral_comp_angEquiv (fun θ : AngCircle =>
    qT_STR02904 h (angSec θ) * f (angEquiv.symm θ))]
  have hs : (fun θ : AngCircle => qT_STR02904 h (angSec θ) * f (angEquiv.symm θ)) =
      fun θ => (fun t : ℝ => qT_STR02904 h t * f (angEquiv.symm (t : AngCircle))) (angSec θ) := by
    funext θ
    change qT_STR02904 h (angSec θ) * f (angEquiv.symm θ) =
      qT_STR02904 h (angSec θ) * f (angEquiv.symm ((angSec θ : ℝ) : AngCircle))
    rw [coe_angSec_STR02962]
  rw [hs, integral_angSec_STR02962 (fun t => qT_STR02904 h t * f (angEquiv.symm (t : AngCircle)))]
  exact (normInt_eq_meanT_STR02962 _).symm

private theorem angular_point (t : ℝ) :
    angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  congr 1
  field_simp

private theorem angular_cos (k : ℕ) (t : ℝ) :
    cosHarm k (angEquiv.symm (t : AngCircle)) = Real.cos ((k : ℝ) * t) := by
  rw [angular_point, cosHarm_pt]
  congr 1
  field_simp

private theorem angular_sin (k : ℕ) (t : ℝ) :
    sinHarm k (angEquiv.symm (t : AngCircle)) = Real.sin ((k : ℝ) * t) := by
  rw [angular_point, sinHarm_pt]
  congr 1
  field_simp

private theorem angular_gram (h : ℝ) :
    normInt_STR02904 (fun t => Real.cos t ^ 2 * qT_STR02904 h t) = 1 / 2 ∧
    normInt_STR02904 (fun t => Real.sin t ^ 2 * qT_STR02904 h t) = 1 / 2 ∧
    normInt_STR02904 (fun t => (Real.cos t * Real.sin t) * qT_STR02904 h t) = 0 := by
  have hmass : normInt_STR02904 (qT_STR02904 h) = 1 := by
    rw [← normInt_eq_STR02935]
    exact normInt_qT_STR02935 h
  have hq : Continuous (qT_STR02904 h) := continuous_qT_STR02904 h
  have hbase := harmonic_weight_STR02904 hq
    (periodic_STR02904 h) (shift_STR02904 h) hmass
  have hc := (hbase 1 0).2
  have hs := (hbase 0 1).2
  have hsum := (hbase 1 1).2
  norm_num only [one_mul, zero_mul, add_zero, zero_add, one_pow,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc hs hsum
  have he : (fun t => (Real.cos t + Real.sin t) ^ 2 * qT_STR02904 h t) =
      fun t => (Real.cos t ^ 2 * qT_STR02904 h t + Real.sin t ^ 2 * qT_STR02904 h t) +
        2 * ((Real.cos t * Real.sin t) * qT_STR02904 h t) := by funext t; ring
  rw [he, normInt_add_STR02904 (by fun_prop) (by fun_prop),
    normInt_add_STR02904 (by fun_prop) (by fun_prop), normInt_const_mul_STR02904,
    hc, hs] at hsum
  exact ⟨hc, hs, by linarith⟩

private theorem angular_invariant_first_zero (h : ℝ) :
    normInt_STR02904 (fun t => Real.cos t * ((Real.cos (3 * t) - referenceMean h) * qT_STR02904 h t)) = 0 ∧
    normInt_STR02904 (fun t => Real.sin t * ((Real.cos (3 * t) - referenceMean h) * qT_STR02904 h t)) = 0 := by
  let w : ℝ → ℝ := fun t => (Real.cos (3 * t) - referenceMean h) * qT_STR02904 h t
  have hq : Continuous (qT_STR02904 h) := continuous_qT_STR02904 h
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hp : Function.Periodic w (2 * Real.pi) := by
    intro t
    dsimp only [w]
    rw [periodic_STR02904 h t, show 3 * (t + 2 * Real.pi) = 3 * t + ((3 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring,
      Real.cos_add_nat_mul_two_pi]
  have hs : ∀ t, w (t + 2 * Real.pi / 3) = w t := by
    intro t
    dsimp only [w]
    rw [shift_STR02904 h t, show 3 * (t + 2 * Real.pi / 3) = 3 * t + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  have he := fourier_vanish_STR02904 hw hp hs 1
    (by rw [Nat.cast_one, one_mul, cos_two_pi_div_three_STR02904]; norm_num)
  simpa only [Nat.cast_one, one_mul, w] using he

/-- The actual C/S features are orthogonal and have equal exact reference norm;
the actual invariant B feature is orthogonal to both. -/
theorem elementaryReference_feature_gram {h : ℝ} (hh : 0 < h) :
    (∫ x, featureC h x ^ 2 ∂(refProb hh : Measure (Torus 1))) = 1 / (2 * h ^ 2) ∧
    (∫ x, featureS h x ^ 2 ∂(refProb hh : Measure (Torus 1))) = 1 / (2 * h ^ 2) ∧
    (∫ x, featureC h x * featureS h x ∂(refProb hh : Measure (Torus 1))) = 0 ∧
    (∫ x, featureB h x * featureC h x ∂(refProb hh : Measure (Torus 1))) = 0 ∧
    (∫ x, featureB h x * featureS h x ∂(refProb hh : Measure (Torus 1))) = 0 := by
  obtain ⟨hc, hs, hcs⟩ := angular_gram h
  obtain ⟨hbc, hbs⟩ := angular_invariant_first_zero h
  have pointC (t : ℝ) : featureC h (angEquiv.symm (t : AngCircle)) = Real.cos t / h := by
    simp only [featureC, angular_cos, Nat.cast_one, one_mul]
  have pointS (t : ℝ) : featureS h (angEquiv.symm (t : AngCircle)) = Real.sin t / h := by
    simp only [featureS, angular_sin, Nat.cast_one, one_mul]
  have pointB (t : ℝ) : featureB h (angEquiv.symm (t : AngCircle)) =
      15 * (Real.cos (3 * t) - referenceMean h) / (4 * h ^ 3) := by
    simp only [featureB, angular_cos, Nat.cast_ofNat]
  simp only [coe_refProb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [threefoldReference_integral_angular]
    have he : (fun t => qT_STR02904 h t * featureC h (angEquiv.symm (t : AngCircle)) ^ 2) =
        fun t => (h ^ 2)⁻¹ * (Real.cos t ^ 2 * qT_STR02904 h t) := by
      funext t
      rw [pointC]
      field_simp [hh.ne']
      <;> ring
    rw [he, normInt_mul_const_STR02933, normInt_eq_STR02935, hc]
    field_simp [hh.ne']
    <;> ring
  · rw [threefoldReference_integral_angular]
    have he : (fun t => qT_STR02904 h t * featureS h (angEquiv.symm (t : AngCircle)) ^ 2) =
        fun t => (h ^ 2)⁻¹ * (Real.sin t ^ 2 * qT_STR02904 h t) := by
      funext t
      rw [pointS]
      field_simp [hh.ne']
      <;> ring
    rw [he, normInt_mul_const_STR02933, normInt_eq_STR02935, hs]
    field_simp [hh.ne']
    <;> ring
  · rw [threefoldReference_integral_angular]
    have he : (fun t => qT_STR02904 h t * (featureC h (angEquiv.symm (t : AngCircle)) *
        featureS h (angEquiv.symm (t : AngCircle)))) =
        fun t => (h ^ 2)⁻¹ * ((Real.cos t * Real.sin t) * qT_STR02904 h t) := by
      funext t
      rw [pointC, pointS]
      field_simp [hh.ne']
      <;> ring
    rw [he, normInt_mul_const_STR02933, normInt_eq_STR02935, hcs, mul_zero]
  · rw [threefoldReference_integral_angular]
    have he : (fun t => qT_STR02904 h t * (featureB h (angEquiv.symm (t : AngCircle)) *
        featureC h (angEquiv.symm (t : AngCircle)))) =
        fun t => (15 / (4 * h ^ 4)) *
          (Real.cos t * ((Real.cos (3 * t) - referenceMean h) * qT_STR02904 h t)) := by
      funext t
      rw [pointB, pointC]
      field_simp [hh.ne']
      <;> ring
    rw [he, normInt_mul_const_STR02933, normInt_eq_STR02935, hbc, mul_zero]
  · rw [threefoldReference_integral_angular]
    have he : (fun t => qT_STR02904 h t * (featureB h (angEquiv.symm (t : AngCircle)) *
        featureS h (angEquiv.symm (t : AngCircle)))) =
        fun t => (15 / (4 * h ^ 4)) *
          (Real.sin t * ((Real.cos (3 * t) - referenceMean h) * qT_STR02904 h t)) := by
      funext t
      rw [pointB, pointS]
      field_simp [hh.ne']
      <;> ring
    rw [he, normInt_mul_const_STR02933, normInt_eq_STR02935, hbs, mul_zero]

end DGPS.Examples.ThreeSpeciesCircle
