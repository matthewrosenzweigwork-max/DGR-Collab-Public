import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceDefect
import DGPS.Foundations.PeriodicSmoothing

/-! The actual two-dimensional first-feature form domain. Its energy identity
is a Rayleigh-form identity after integration, not a generator eigenrelation. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem feature_partials {h : ℝ} (hh : 0 < h) (x : Torus 1) :
    coordPartial 0 (featureC h) x = -(2 * Real.pi) * featureS h x ∧
    coordPartial 0 (featureS h) x = (2 * Real.pi) * featureC h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have hc : (fun s : ℝ => featureC h (pt s)) = fun s => Real.cos (2 * Real.pi * s) / h := by
    funext s; simp only [featureC, cosHarm_pt, Nat.cast_one, mul_one]
  have hs : (fun s : ℝ => featureS h (pt s)) = fun s => Real.sin (2 * Real.pi * s) / h := by
    funext s; simp only [featureS, sinHarm_pt, Nat.cast_one, mul_one]
  have hdc := circ_coordPartial_pt (isSmooth_featureC h) t
  have hds := circ_coordPartial_pt (isSmooth_featureS h) t
  rw [hc] at hdc
  rw [hs] at hds
  have ec := hdc.unique (((hasDerivAt_id t).const_mul (2 * Real.pi)).cos.div_const h)
  have es := hds.unique (((hasDerivAt_id t).const_mul (2 * Real.pi)).sin.div_const h)
  simp only [id_eq] at ec es
  rw [ec, es]
  simp only [featureC, featureS, cosHarm_pt, sinHarm_pt, Nat.cast_one, mul_one]
  constructor <;> ring

/-- Every actual first-feature linear combination is an original native weak
test, carrying the genuine linear combination of its chosen smooth gradients. -/
def gaussianReferenceFirstCombination {h : ℝ} (hh : 0 < h) (c s : ℝ) :
    WeakH1Test (refProb hh) where
  fn x := c * featureC h x + s * featureS h x
  grad x := c • smoothGrad (featureC h) x + s • smoothGrad (featureS h) x
  isWeak := by
    apply (isMeasureWeakGradient_iff (ordinaryReference h)).mpr
    apply (isWeightedWeakGradient_iff (ordinaryReference h)).mpr
    exact ((isSmooth_featureC h).isWeakGradient.smul c).add
      ((isSmooth_featureS h).isWeakGradient.smul s)

private theorem linear_square_integral {h : ℝ} (hh : 0 < h) (c s : ℝ) :
    (∫ x, (c * featureC h x + s * featureS h x) ^ 2
      ∂(refProb hh : Measure (Torus 1))) = (c ^ 2 + s ^ 2) / (2 * h ^ 2) := by
  have hcL : MemLp (featureC h) 2 (refProb hh : Measure (Torus 1)) :=
    (featureC_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsL : MemLp (featureS h) 2 (refProb hh : Measure (Torus 1)) :=
    (featureS_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨hc, hs, hcs, _, _⟩ := elementaryReference_feature_gram hh
  have he : (fun x => (c * featureC h x + s * featureS h x) ^ 2) =
      fun x => (c ^ 2 * featureC h x ^ 2 + s ^ 2 * featureS h x ^ 2) +
        (2 * c * s) * (featureC h x * featureS h x) := by funext x; ring
  have iC : Integrable (fun x => c ^ 2 * featureC h x ^ 2)
      (refProb hh : Measure (Torus 1)) := hcL.integrable_sq.const_mul _
  have iS : Integrable (fun x => s ^ 2 * featureS h x ^ 2)
      (refProb hh : Measure (Torus 1)) := hsL.integrable_sq.const_mul _
  have iCS : Integrable (fun x => (2 * c * s) * (featureC h x * featureS h x))
      (refProb hh : Measure (Torus 1)) := (hcL.integrable_mul hsL).const_mul _
  have iSum : Integrable (fun x => c ^ 2 * featureC h x ^ 2 + s ^ 2 * featureS h x ^ 2)
      (refProb hh : Measure (Torus 1)) := iC.add iS
  rw [he, integral_add iSum iCS, integral_add iC iS,
    integral_const_mul, integral_const_mul, integral_const_mul, hc, hs, hcs]
  ring

/-- Exact native means and first-feature coordinates of the actual combination. -/
theorem gaussianReferenceFirstCombination_moments {h : ℝ} (hh : 0 < h) (c s : ℝ) :
    (∫ x, (gaussianReferenceFirstCombination hh c s).fn x
      ∂(refProb hh : Measure (Torus 1))) = 0 ∧
    (∫ x, featureC h x * (gaussianReferenceFirstCombination hh c s).fn x
      ∂(refProb hh : Measure (Torus 1))) = c / (2 * h ^ 2) ∧
    (∫ x, featureS h x * (gaussianReferenceFirstCombination hh c s).fn x
      ∂(refProb hh : Measure (Torus 1))) = s / (2 * h ^ 2) := by
  obtain ⟨hc0, hs0, _, _⟩ := elementaryFeatures_centered_independent hh
  change (∫ x, featureC h x ∂(refProb hh : Measure (Torus 1))) = 0 at hc0
  change (∫ x, featureS h x ∂(refProb hh : Measure (Torus 1))) = 0 at hs0
  obtain ⟨hc, hs, hcs, _, _⟩ := elementaryReference_feature_gram hh
  have hcL : MemLp (featureC h) 2 (refProb hh : Measure (Torus 1)) :=
    (featureC_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsL : MemLp (featureS h) 2 (refProb hh : Measure (Torus 1)) :=
    (featureS_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨?_, ?_, ?_⟩
  · change (∫ x, c * featureC h x + s * featureS h x ∂(refProb hh : Measure (Torus 1))) = 0
    rw [integral_add ((hcL.integrable (by norm_num)).const_mul c)
      ((hsL.integrable (by norm_num)).const_mul s), integral_const_mul, integral_const_mul, hc0, hs0]
    ring
  · have he : (fun x => featureC h x * (gaussianReferenceFirstCombination hh c s).fn x) =
        fun x => c * featureC h x ^ 2 + s * (featureC h x * featureS h x) := by
      funext x
      change featureC h x * (c * featureC h x + s * featureS h x) = _
      ring
    have iC : Integrable (fun x => c * featureC h x ^ 2)
        (refProb hh : Measure (Torus 1)) := hcL.integrable_sq.const_mul _
    have iCS : Integrable (fun x => s * (featureC h x * featureS h x))
        (refProb hh : Measure (Torus 1)) := (hcL.integrable_mul hsL).const_mul _
    rw [he, integral_add iC iCS,
      integral_const_mul, integral_const_mul, hc, hcs]
    ring
  · have he : (fun x => featureS h x * (gaussianReferenceFirstCombination hh c s).fn x) =
        fun x => s * featureS h x ^ 2 + c * (featureC h x * featureS h x) := by
      funext x; change featureS h x * (c * featureC h x + s * featureS h x) = _; ring
    have iS : Integrable (fun x => s * featureS h x ^ 2)
        (refProb hh : Measure (Torus 1)) := hsL.integrable_sq.const_mul _
    have iCS : Integrable (fun x => c * (featureC h x * featureS h x))
        (refProb hh : Measure (Torus 1)) := (hcL.integrable_mul hsL).const_mul _
    rw [he, integral_add iS iCS,
      integral_const_mul, integral_const_mul, hs, hcs]
    ring

/-- The original first-feature plane has exact integrated energy equal to the
physical Haar rate times its mass. No pointwise generator identity is asserted. -/
theorem gaussianReferenceFirstCombination_forms {h : ℝ} (hh : 0 < h) (c s : ℝ) :
    gaussianReferenceMass hh (gaussianReferenceFirstCombination hh c s) =
      (c ^ 2 + s ^ 2) / (2 * h ^ 2) ∧
    gaussianReferenceRealEnergy hh (gaussianReferenceFirstCombination hh c s) =
      a0 * gaussianReferenceMass hh (gaussianReferenceFirstCombination hh c s) := by
  have hmass : gaussianReferenceMass hh (gaussianReferenceFirstCombination hh c s) =
      (c ^ 2 + s ^ 2) / (2 * h ^ 2) := linear_square_integral hh c s
  refine ⟨hmass, ?_⟩
  have he (x : Torus 1) : ‖(gaussianReferenceFirstCombination hh c s).grad x‖ ^ 2 =
      a0 * (s * featureC h x + (-c) * featureS h x) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_one, gaussianReferenceFirstCombination, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, smoothGrad_apply, (feature_partials hh x).1,
      (feature_partials hh x).2, Real.norm_eq_abs, sq_abs]
    unfold a0
    ring
  unfold gaussianReferenceRealEnergy
  simp_rw [he]
  rw [integral_const_mul, linear_square_integral hh s (-c), hmass]
  ring

end DGPS.Examples.ThreeSpeciesCircle
