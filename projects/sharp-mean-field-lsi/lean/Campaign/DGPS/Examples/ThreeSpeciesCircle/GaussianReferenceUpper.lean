import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceGram
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers
import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorCentering
import DGPS.Foundations.PeriodicSmoothing

/-! An exact native reference Poincare upper bound from an actual smooth test.
No trigonometric weighted-generator eigenrelation is required. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem partial_featureC {h : ℝ} (hh : 0 < h) (x : Torus 1) :
    coordPartial 0 (featureC h) x = -(2 * Real.pi) * featureS h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have he : (fun s : ℝ => featureC h (pt s)) = fun s => Real.cos (2 * Real.pi * s) / h := by
    funext s
    simp only [featureC, cosHarm_pt, Nat.cast_one, mul_one]
  have hd := circ_coordPartial_pt (isSmooth_featureC h) t
  rw [he] at hd
  have hd' := (((hasDerivAt_id t).const_mul (2 * Real.pi)).cos.div_const h)
  have hh' := hd.unique hd'
  simp only [id_eq] at hh'
  change coordPartial 0 (featureC h) (pt t) = _
  rw [hh']
  simp only [featureS, sinHarm_pt, Nat.cast_one, mul_one]
  ring

/-- The canonical reference Poincare rate is finite and at most the physical
Haar rate, by the actual first-feature Rayleigh test on its native weak domain. -/
theorem threefold_reference_poincare_upper {h : ℝ} (hh : 0 < h) :
    poincareRate (refProb hh) ≤ ENNReal.ofReal a0 := by
  have hw : IsMeasureWeakGradient (refProb hh) (featureC h) (smoothGrad (featureC h)) :=
    (isMeasureWeakGradient_iff (ordinaryReference h)).mpr
      ((isWeightedWeakGradient_iff (ordinaryReference h)).mpr (isSmooth_featureC h).isWeakGradient)
  let f : WeakH1Test (refProb hh) := ⟨featureC h, smoothGrad (featureC h), hw⟩
  obtain ⟨hc, hs, _, _, _⟩ := elementaryReference_feature_gram hh
  have hm : (∫ x, f.fn x ∂(refProb hh : Measure (Torus 1))) = 0 :=
    (elementaryFeatures_centered_independent hh).1
  have hv : weightedVariance (refProb hh) f.fn = 1 / (2 * h ^ 2) := by
    unfold weightedVariance
    rw [hm]
    simp only [sub_zero]
    exact hc
  have hnorm (x : Torus 1) : ‖f.grad x‖ ^ 2 = a0 * featureS h x ^ 2 := by
    change ‖smoothGrad (featureC h) x‖ ^ 2 = _
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_one, smoothGrad_apply, partial_featureC hh,
      Real.norm_eq_abs, sq_abs]
    unfold a0
    ring
  have hi := f.isWeak.memLp_grad.norm.integrable_sq
  have he : dirichletEnergy (refProb hh) f = ENNReal.ofReal (a0 * (1 / (2 * h ^ 2))) := by
    have he0 : dirichletEnergy (refProb hh) f =
        ENNReal.ofReal (∫ x, ‖f.grad x‖ ^ 2 ∂(refProb hh : Measure (Torus 1))) := by
      unfold dirichletEnergy
      rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)]
      apply lintegral_congr
      intro x
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [he0]
    simp_rw [hnorm]
    rw [integral_const_mul, hs]
  have hn : (0 : ℝ) < 1 / (2 * h ^ 2) := by positivity
  have hvpos : 0 < weightedVariance (refProb hh) f.fn := by rw [hv]; exact hn
  refine (poincareRate_le_quotient (refProb hh) f hvpos).trans ?_
  unfold poincareQuotient
  rw [he, hv, ← ENNReal.ofReal_div_of_pos hn, mul_div_cancel_right₀ _ hn.ne']

/-- The exact original native reference rate is not infinite. -/
theorem threefold_reference_poincare_ne_top {h : ℝ} (hh : 0 < h) :
    poincareRate (refProb hh) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (threefold_reference_poincare_upper hh)

end DGPS.Examples.ThreeSpeciesCircle
