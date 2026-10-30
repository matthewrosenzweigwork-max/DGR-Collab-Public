import DGPS.Examples.ThreeSpeciesCircle.GaussianRotationForms

/-! Actual reference moments of the full weak-domain C3 average. The
first-feature constraints follow from spatial rotation, without diagonalizing
the reference generator. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem cont_mul_integrable {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) {φ : Torus 1 → ℝ} (hφ : Continuous φ) :
    Integrable (fun x => φ x * f.fn x) (refProb hh : Measure (Torus 1)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact (f.isWeak.memLp.integrable (by norm_num)).bdd_mul (c := C)
    hφ.aestronglyMeasurable (Eventually.of_forall fun x => by
      simpa using hC x (Set.mem_univ _))

private theorem feature_turn (h : ℝ) (x : Torus 1) :
    featureC h (x + gaussianThirdTurn) =
      Real.cos (2 * Real.pi / 3) * featureC h x -
        Real.sin (2 * Real.pi / 3) * featureS h x ∧
    featureS h (x + gaussianThirdTurn) =
      Real.sin (2 * Real.pi / 3) * featureC h x +
        Real.cos (2 * Real.pi / 3) * featureS h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have he : pt t + gaussianThirdTurn = pt (t + 1 / 3) :=
    (SharpLSI.liftT_add (fun _ : Fin 1 => t) (fun _ : Fin 1 => 1 / 3)).symm
  rw [he]
  simp only [featureC, featureS, cosHarm_pt, sinHarm_pt, Nat.cast_one, mul_one]
  rw [show 2 * Real.pi * (t + 1 / 3) = 2 * Real.pi * t + 2 * Real.pi / 3 by ring,
    Real.cos_add, Real.sin_add]
  constructor <;> ring

private theorem featureB_invariant (h : ℝ) (x : Torus 1) :
    featureB h (x + gaussianThirdTurn) = featureB h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have he : pt t + gaussianThirdTurn = pt (t + 1 / 3) :=
    (SharpLSI.liftT_add (fun _ : Fin 1 => t) (fun _ : Fin 1 => 1 / 3)).symm
  rw [he]
  simp only [featureB, cosHarm_pt, Nat.cast_ofNat]
  rw [show 2 * Real.pi * 3 * (t + 1 / 3) = 2 * Real.pi * 3 * t + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

/-- The full native average preserves the actual reference mean. -/
theorem gaussianReferenceAverage_mean {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    (∫ x, (gaussianReferenceTestAverage hh f).fn x ∂(refProb hh : Measure (Torus 1))) =
      ∫ x, f.fn x ∂(refProb hh : Measure (Torus 1)) := by
  let R := gaussianReferenceTestTurn hh f
  let R2 := gaussianReferenceTestTurn hh R
  have h1 := threefoldReference_integral_thirdTurn h f.fn
  have h2 := threefoldReference_integral_thirdTurn h R.fn
  change (∫ x, R.fn x ∂(refProb hh : Measure (Torus 1))) =
    ∫ x, f.fn x ∂(refProb hh : Measure (Torus 1)) at h1
  change (∫ x, R2.fn x ∂(refProb hh : Measure (Torus 1))) =
    ∫ x, R.fn x ∂(refProb hh : Measure (Torus 1)) at h2
  change (∫ x, (1 / 3 : ℝ) * ((f.fn x + R.fn x) + R2.fn x)
    ∂(refProb hh : Measure (Torus 1))) = _
  have i0 := f.isWeak.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have i1 := R.isWeak.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have i2 := R2.isWeak.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have i01 : Integrable (fun x => f.fn x + R.fn x)
      (refProb hh : Measure (Torus 1)) := i0.add i1
  rw [integral_const_mul, integral_add i01 i2, integral_add i0 i1, h2, h1]
  ring

/-- Both genuine first-feature moments vanish on the actual C3 average of
every original native weak test. -/
theorem gaussianReferenceAverage_first_moments {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    (∫ x, featureC h x * (gaussianReferenceTestAverage hh f).fn x
      ∂(refProb hh : Measure (Torus 1))) = 0 ∧
    (∫ x, featureS h x * (gaussianReferenceTestAverage hh f).fn x
      ∂(refProb hh : Measure (Torus 1))) = 0 := by
  let P := gaussianReferenceTestAverage hh f
  let c := Real.cos (2 * Real.pi / 3)
  let s := Real.sin (2 * Real.pi / 3)
  let X := ∫ x, featureC h x * P.fn x ∂(refProb hh : Measure (Torus 1))
  let Y := ∫ x, featureS h x * P.fn x ∂(refProb hh : Measure (Torus 1))
  have ic := cont_mul_integrable hh P (featureC_continuous h)
  have is := cont_mul_integrable hh P (featureS_continuous h)
  have hc : c * X - s * Y = X := by
    have ht := threefoldReference_integral_thirdTurn h (fun x => featureC h x * P.fn x)
    have he : (fun x => featureC h (x + gaussianThirdTurn) * P.fn (x + gaussianThirdTurn)) =
        fun x => c * (featureC h x * P.fn x) - s * (featureS h x * P.fn x) := by
      funext x
      rw [(feature_turn h x).1, show P.fn (x + gaussianThirdTurn) = P.fn x from
        gaussianReferenceAverage_invariant f.fn x]
      dsimp [c, s]
      ring
    rw [he] at ht
    change (∫ x, c * (featureC h x * P.fn x) - s * (featureS h x * P.fn x)
      ∂(refProb hh : Measure (Torus 1))) =
      ∫ x, featureC h x * P.fn x ∂(refProb hh : Measure (Torus 1)) at ht
    rw [integral_sub (ic.const_mul c) (is.const_mul s), integral_const_mul,
      integral_const_mul] at ht
    exact ht
  have hs : s * X + c * Y = Y := by
    have ht := threefoldReference_integral_thirdTurn h (fun x => featureS h x * P.fn x)
    have he : (fun x => featureS h (x + gaussianThirdTurn) * P.fn (x + gaussianThirdTurn)) =
        fun x => s * (featureC h x * P.fn x) + c * (featureS h x * P.fn x) := by
      funext x
      rw [(feature_turn h x).2, show P.fn (x + gaussianThirdTurn) = P.fn x from
        gaussianReferenceAverage_invariant f.fn x]
      dsimp [c, s]
      ring
    rw [he] at ht
    change (∫ x, s * (featureC h x * P.fn x) + c * (featureS h x * P.fn x)
      ∂(refProb hh : Measure (Torus 1))) =
      ∫ x, featureS h x * P.fn x ∂(refProb hh : Measure (Torus 1)) at ht
    rw [integral_add (ic.const_mul s) (is.const_mul c), integral_const_mul,
      integral_const_mul] at ht
    exact ht
  have hcval : c = -(1 / 2 : ℝ) := DGPS.Frontier.STR029.cos_two_pi_div_three_STR02904
  have hzero : X ^ 2 + Y ^ 2 = 0 := by
    rw [hcval] at hc hs
    have hcx := congrArg (fun z : ℝ => z * X) hc
    have hsy := congrArg (fun z : ℝ => z * Y) hs
    nlinarith only [hcx, hsy]
  exact ⟨by change X = 0; nlinarith only [hzero, sq_nonneg Y],
    by change Y = 0; nlinarith only [hzero, sq_nonneg X]⟩

/-- Averaging preserves the actual invariant third-feature moment. -/
theorem gaussianReferenceAverage_third_moment {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    (∫ x, featureB h x * (gaussianReferenceTestAverage hh f).fn x
      ∂(refProb hh : Measure (Torus 1))) =
      ∫ x, featureB h x * f.fn x ∂(refProb hh : Measure (Torus 1)) := by
  let R := gaussianReferenceTestTurn hh f
  let R2 := gaussianReferenceTestTurn hh R
  have i0 := cont_mul_integrable hh f (featureB_continuous h)
  have i1 := cont_mul_integrable hh R (featureB_continuous h)
  have i2 := cont_mul_integrable hh R2 (featureB_continuous h)
  have h1 := threefoldReference_integral_thirdTurn h (fun x => featureB h x * f.fn x)
  simp only [featureB_invariant] at h1
  have h2 := threefoldReference_integral_thirdTurn h (fun x => featureB h x * R.fn x)
  simp only [featureB_invariant] at h2
  change (∫ x, featureB h x * R.fn x ∂(refProb hh : Measure (Torus 1))) =
    ∫ x, featureB h x * f.fn x ∂(refProb hh : Measure (Torus 1)) at h1
  change (∫ x, featureB h x * R2.fn x ∂(refProb hh : Measure (Torus 1))) =
    ∫ x, featureB h x * R.fn x ∂(refProb hh : Measure (Torus 1)) at h2
  have he : (fun x => featureB h x * (gaussianReferenceTestAverage hh f).fn x) =
      fun x => (1 / 3 : ℝ) * ((featureB h x * f.fn x + featureB h x * R.fn x) +
        featureB h x * R2.fn x) := by
    funext x
    change featureB h x * ((1 / 3 : ℝ) * _) = _
    dsimp only [R, R2, gaussianReferenceTestTurn]
    ring
  have i01 : Integrable (fun x => featureB h x * f.fn x + featureB h x * R.fn x)
      (refProb hh : Measure (Torus 1)) := i0.add i1
  rw [he, integral_const_mul, integral_add i01 i2, integral_add i0 i1, h2, h1]
  ring

end DGPS.Examples.ThreeSpeciesCircle
