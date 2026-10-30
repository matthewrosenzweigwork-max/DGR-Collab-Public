import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceComplement
import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceUpper
import DGPS.Structural.AmplitudeComparison
import DGPS.Frontier.STR029.T26s2

/-! The reference first-feature constrained gap on the entire original native
weak H1 domain. Haar centering is performed internally and preserves variance
and energy; no extra regularity of a test or representative is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem haar_angular (f : Torus 1 → ℝ) :
    (∫ x, f x ∂haar 1) = normInt_STR02933 (fun t => f (angEquiv.symm (t : AngCircle))) := by
  calc
    _ = ∫ θ, f (angEquiv.symm θ) ∂angHaar := by
      simpa only [angEquiv.symm_apply_apply] using integral_comp_angEquiv (fun θ : AngCircle => f (angEquiv.symm θ))
    _ = _ := by
      have he : (fun θ : AngCircle => f (angEquiv.symm θ)) =
          fun θ => (fun t : ℝ => f (angEquiv.symm (t : AngCircle))) (angSec θ) := by
        funext θ
        change f (angEquiv.symm θ) = f (angEquiv.symm ((angSec θ : ℝ) : AngCircle))
        rw [coe_angSec_STR02962]
      rw [he, integral_angSec_STR02962 (fun t : ℝ => f (angEquiv.symm (t : AngCircle)))]
      exact (normInt_eq_meanT_STR02962 (fun t : ℝ => f (angEquiv.symm (t : AngCircle)))).symm

private theorem harmonic_angular (t : ℝ) :
    cosHarm 1 (angEquiv.symm (t : AngCircle)) = Real.cos t ∧
    sinHarm 1 (angEquiv.symm (t : AngCircle)) = Real.sin t := by
  have he : angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
    rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
    change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
    rw [angRescale_mk]
    congr 1
    field_simp
  rw [he, cosHarm_pt, sinHarm_pt]
  have ht : 2 * Real.pi * (1 : ℕ) * (t / (2 * Real.pi)) = t := by push_cast; field_simp
  rw [ht]
  exact ⟨rfl, rfl⟩

private theorem variance_shift (μ : ProbabilityMeasure (Torus 1)) (f : WeakH1Test μ) (c : ℝ) :
    weightedVariance μ (Structural.shiftTest μ f c).fn = weightedVariance μ f.fn := by
  have hm : (∫ x, (f.fn x - c) ∂(μ : Measure (Torus 1))) =
      (∫ x, f.fn x ∂(μ : Measure (Torus 1))) - c := by
    rw [integral_sub (f.isWeak.memLp.integrable (by norm_num)) (integrable_const c)]
    simp
  unfold weightedVariance
  change (∫ x, (f.fn x - c - ∫ y, (f.fn y - c) ∂(μ : Measure (Torus 1))) ^ 2
    ∂(μ : Measure (Torus 1))) = _
  rw [hm]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- A genuine native constrained Poincare bound with no additional Haar-mean
or smoothness assumption. Both constraints are actual reference moments. -/
theorem threefold_reference_constrained_gap_native {h : ℝ} (hh : 0 < h)
    (hhsmall : |h| ≤ 1 / 1000) (f : WeakH1Test (refProb hh))
    (hc : (∫ x, f.fn x * cosHarm 1 x ∂(refProb hh : Measure (Torus 1))) = 0)
    (hs : (∫ x, f.fn x * sinHarm 1 x ∂(refProb hh : Measure (Torus 1))) = 0) :
    ENNReal.ofReal (2 * a0 * weightedVariance (refProb hh) f.fn) ≤ dirichletEnergy (refProb hh) f := by
  let μ := refProb hh
  let c := ∫ x, f.fn x ∂haar 1
  let fc := Structural.shiftTest μ f c
  let F : AngCircle → ℝ := fun θ => fc.fn (angEquiv.symm θ)
  let G : AngCircle → ℝ := fun θ => (2 * Real.pi)⁻¹ * fc.grad (angEquiv.symm θ) 0
  have hHaar : IsWeakGradient fc.fn fc.grad :=
    (isWeightedWeakGradient_iff (ordinaryReference h)).mp
      ((isMeasureWeakGradient_iff (ordinaryReference h)).mp fc.isWeak)
  have hFG : IsWeakGradient (F ∘ angEquiv) (physGrad G) := by
    refine hHaar.congr_ae (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [Function.comp_apply, F, angEquiv.symm_apply_apply]
    · ext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rw [physGrad_apply]
      dsimp only [G]
      rw [angEquiv.symm_apply_apply]
      field_simp [Real.two_pi_pos.ne']
  have hweak := angularWD_to_periodicWD_STR02926 ((isWeakGradient_comp_iff F G).mpr hFG)
  have hmean : normInt_STR02933 (fun t : ℝ => F (t : AngCircle)) = 0 := by
    rw [← haar_angular fc.fn]
    change (∫ x, f.fn x - c ∂haar 1) = 0
    rw [integral_sub f.isWeak.integrable (integrable_const c)]
    simp [c]
  have hfi : Integrable f.fn (μ : Measure (Torus 1)) := f.isWeak.memLp.integrable (by norm_num)
  have iharm (φ : Torus 1 → ℝ) (hφ : Continuous φ) :
      Integrable (fun x => f.fn x * φ x) (μ : Measure (Torus 1)) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
    have ht := hfi.bdd_mul (c := C) hφ.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hC x (Set.mem_univ _))
    exact ht.congr (Eventually.of_forall fun x => by ring)
  have hc0 : (∫ x, cosHarm 1 x ∂(μ : Measure (Torus 1))) = 0 := by
    change (∫ x, cosHarm 1 x ∂threefoldReference h) = 0
    rw [integral_threefoldReference]
    exact (torusIntegral_density_first h).1
  have hs0 : (∫ x, sinHarm 1 x ∂(μ : Measure (Torus 1))) = 0 := by
    change (∫ x, sinHarm 1 x ∂threefoldReference h) = 0
    rw [integral_threefoldReference]
    exact (torusIntegral_density_first h).2
  have hshift (φ : Torus 1 → ℝ) (hφ : Continuous φ)
      (hφ0 : (∫ x, φ x ∂(μ : Measure (Torus 1))) = 0)
      (hfφ : (∫ x, f.fn x * φ x ∂(μ : Measure (Torus 1))) = 0) :
      (∫ x, fc.fn x * φ x ∂(μ : Measure (Torus 1))) = 0 := by
    change (∫ x, (f.fn x - c) * φ x ∂(μ : Measure (Torus 1))) = 0
    simp_rw [sub_mul]
    rw [integral_sub (iharm φ hφ)
      (hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) |>.const_mul c),
      integral_const_mul, hfφ, hφ0]
    ring
  have hcos := hshift _ (continuous_cosHarm 1) hc0 hc
  have hsin := hshift _ (continuous_sinHarm 1) hs0 hs
  have hcosA : normInt_STR02933 (fun t => F (t : AngCircle) * Real.cos t * qT_STR02904 h t) = 0 := by
    change (∫ x, fc.fn x * cosHarm 1 x ∂threefoldReference h) = 0 at hcos
    rw [threefoldReference_integral_angular] at hcos
    convert hcos using 1
    congr 1
    funext t
    rw [(harmonic_angular t).1]
    simp only [F]
    ring
  have hsinA : normInt_STR02933 (fun t => F (t : AngCircle) * Real.sin t * qT_STR02904 h t) = 0 := by
    change (∫ x, fc.fn x * sinHarm 1 x ∂threefoldReference h) = 0 at hsin
    rw [threefoldReference_integral_angular] at hsin
    convert hsin using 1
    congr 1
    funext t
    rw [(harmonic_angular t).2]
    simp only [F]
    ring
  have hp := threefold_reference_constrained_gap_angular h hhsmall _ _ hweak hmean hcosA hsinA
  have hv : weightedVariance μ fc.fn ≤
      normInt_STR02933 (fun t => F (t : AngCircle) ^ 2 * qT_STR02904 h t) := by
    have he := ProbabilityTheory.variance_eq_sub fc.isWeak.memLp
    have hv0 := ProbabilityTheory.variance_eq_integral fc.isWeak.memLp.aestronglyMeasurable.aemeasurable
    rw [hv0] at he
    change weightedVariance μ fc.fn = _ at he
    rw [he]
    change (∫ x, fc.fn x ^ 2 ∂threefoldReference h) -
      (∫ x, fc.fn x ∂threefoldReference h) ^ 2 ≤ _
    rw [threefoldReference_integral_angular]
    have hcomm : normInt_STR02933 (fun t => qT_STR02904 h t * fc.fn (angEquiv.symm (t : AngCircle)) ^ 2) =
        normInt_STR02933 (fun t => F (t : AngCircle) ^ 2 * qT_STR02904 h t) := by
      congr 1; funext t; dsimp [F]; ring
    rw [hcomm]
    exact sub_le_self _ (sq_nonneg _)
  have hgi := fc.isWeak.memLp_grad.norm.integrable_sq
  have hn : ∀ z : Tangent 1, ‖z‖ ^ 2 = (z 0) ^ 2 := by intro z; simp [EuclideanSpace.norm_sq_eq]
  have hE : dirichletEnergy μ fc = ENNReal.ofReal (a0 *
      normInt_STR02933 (fun t => G (t : AngCircle) ^ 2 * qT_STR02904 h t)) := by
    have hE0 : dirichletEnergy μ fc =
        ENNReal.ofReal (∫ x, ‖fc.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))) := by
      unfold dirichletEnergy
      rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun x => sq_nonneg _)]
      apply lintegral_congr
      intro x
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [hE0]
    congr 1
    simp_rw [hn]
    change (∫ x, fc.grad x 0 ^ 2 ∂threefoldReference h) = _
    rw [threefoldReference_integral_angular, ← normInt_mul_const_STR02933]
    congr 1
    funext t
    simp only [G]
    unfold a0
    field_simp [Real.two_pi_pos.ne']
    <;> ring
  have hEeq : dirichletEnergy μ fc = dirichletEnergy μ f := rfl
  have hvEq := variance_shift μ f c
  change weightedVariance μ fc.fn = weightedVariance μ f.fn at hvEq
  rw [← hEeq, hE]
  apply ENNReal.ofReal_le_ofReal
  have ha0 : 0 < a0 := a0_pos
  rw [hvEq] at hv
  nlinarith only [mul_le_mul_of_nonneg_left hp ha0.le, mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * a0)]

end DGPS.Examples.ThreeSpeciesCircle
