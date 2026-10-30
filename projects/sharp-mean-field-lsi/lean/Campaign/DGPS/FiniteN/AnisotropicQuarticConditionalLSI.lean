import DGPS.FiniteN.AnisotropicQuarticHubbard
import DGPS.FiniteN.TiltedXYPosteriorFIN050
import DGPS.FiniteN.Tools.UniformVonMises

/-!
# Uniform one-site LSI for the actual quartic Hubbard conditional law

The latent conditional law is the tensor product of these one-site laws. It is not
identified with a canonical coordinate conditional. The all-field von Mises estimate
is the genuine uniform Hardy estimate of FIN009; no field-oscillation bound is used.
-/

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
open DGPS DGPS.Models DGPS.Circle.AngularNormalization
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.UniformVonMises
open DGPS.FiniteN.Tools.ConditionalEntropyPinsker
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt

namespace DGPS.FiniteN

/-- The original physical feature is exactly the angular feature under the existing
measure-preserving angular coordinate map. -/
theorem quartic_hubbard_feature_angular (x : Torus 1) :
    quarticHubbardFeature x = phi (angEquiv x) := by
  change quarticHubbardFeature x = TiltedXY.Fin050.phiT x
  ext i
  fin_cases i
  · change scalarCos x = TiltedXY.Fin050.phiT x 0
    rw [scalarCos_eq_FIN066, TiltedXY.Fin050.phiT_zero_FIN050]
    change (xyMode x).re = (TiltedXY.Fin051.phase x).re
    rw [xyMode_apply]
    rfl
  · change scalarSin x = TiltedXY.Fin050.phiT x 1
    rw [scalarSin_eq_FIN066, TiltedXY.Fin050.phiT_one_FIN050]
    change (xyMode x).im = (TiltedXY.Fin051.phase x).im
    rw [xyMode_apply]
    rfl

private theorem quartic_site_exp (w : Fin 2 → ℝ) :
    expTerm quarticHubbardU quarticHubbardFeature w =
      (fun θ => Real.exp (vmPhase (WithLp.toLp 2 w) θ)) ∘ angEquiv := by
  funext x
  unfold expTerm quarticHubbardU
  rw [sub_zero, quartic_hubbard_feature_angular]
  congr 1
  exact dot_phi (WithLp.toLp 2 w) (angEquiv x)

private theorem quartic_site_partition (w : Fin 2 → ℝ) :
    auxPartition quarticHubbardU quarticHubbardFeature (haar 1) w =
      vmNorm (WithLp.toLp 2 w) := by
  unfold auxPartition vmNorm
  rw [quartic_site_exp]
  simpa only [Function.comp_apply] using integral_comp_angEquiv
    (fun θ => Real.exp (vmPhase (WithLp.toLp 2 w) θ))

/-- Exact pushforward of the actual physical Hubbard one-site law to the genuine
von Mises law, with every auxiliary field allowed. -/
theorem quartic_site_map_angEquiv (w : Fin 2 → ℝ) :
    (siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w).map angEquiv =
      vmLaw (WithLp.toLp 2 w) := by
  let q : AngCircle → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (Real.exp (vmPhase (WithLp.toLp 2 w) θ) / vmNorm (WithLp.toLp 2 w))
  have hq : Measurable q :=
    (((Real.continuous_exp.comp (continuous_vmPhase _)).div_const _).measurable).ennreal_ofReal
  have hden : ∀ x, ENNReal.ofReal (siteDensity quarticHubbardU quarticHubbardFeature (haar 1) w x) =
      q (angEquiv x) := by
    intro x
    unfold siteDensity q
    rw [quartic_site_exp, quartic_site_partition]
    rfl
  have hqm : Measurable (fun x => ENNReal.ofReal
      (siteDensity quarticHubbardU quarticHubbardFeature (haar 1) w x)) := by
    have hm : Measurable (fun x : Torus 1 => expTerm quarticHubbardU quarticHubbardFeature w x) :=
      (measurable_expTerm quartic_hubbard_hyp).comp (measurable_const.prodMk measurable_id)
    exact (hm.div_const _).ennreal_ofReal
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply angEquiv.measurable hs]
  unfold siteLaw vmLaw
  change ((haar 1).withDensity (fun x => ENNReal.ofReal
    (siteDensity quarticHubbardU quarticHubbardFeature (haar 1) w x))) (angEquiv ⁻¹' s) =
    (angHaar.withDensity q) s
  rw [withDensity_apply (fun x => ENNReal.ofReal
      (siteDensity quarticHubbardU quarticHubbardFeature (haar 1) w x))
      (hs.preimage angEquiv.measurable), withDensity_apply q hs,
    ← lintegral_indicator (hs.preimage angEquiv.measurable) (fun x => ENNReal.ofReal
      (siteDensity quarticHubbardU quarticHubbardFeature (haar 1) w x)),
    ← lintegral_indicator hs q]
  have he : (angEquiv ⁻¹' s).indicator (fun x => ENNReal.ofReal
      (siteDensity quarticHubbardU quarticHubbardFeature (haar 1) w x)) =
      (s.indicator q) ∘ angEquiv := by
    funext x
    change (angEquiv ⁻¹' s).indicator (fun x => ENNReal.ofReal
      (siteDensity quarticHubbardU quarticHubbardFeature (haar 1) w x)) x = s.indicator q (angEquiv x)
    by_cases hx : angEquiv x ∈ s
    · rw [Set.indicator_of_mem (show x ∈ angEquiv ⁻¹' s from hx), Set.indicator_of_mem hx]
      exact hden x
    · rw [Set.indicator_of_notMem (show x ∉ angEquiv ⁻¹' s from hx), Set.indicator_of_notMem hx]
  rw [he]
  exact lintegral_comp_angEquiv _

/-- A field-independent physical one-site LSI on exactly the smooth native test
class consumed by the conditional transfer. The physical factor is 4*pi squared. -/
theorem quartic_site_uniform_lsi :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Fin 2 → ℝ, ∀ f : Torus 1 → ℝ, IsSmoothPeriodic f →
      homogeneousEntropy (siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w)
        (fun x => f x ^ 2) ≤ ENNReal.ofReal (C *
          ∫ x, coordPartial 0 f x ^ 2
            ∂siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w) := by
  obtain ⟨K, hK, hLS⟩ := vm_h1_lsi
  have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by
    unfold DGPS.Circle.AngularNormalization.a0
    positivity
  refine ⟨K / DGPS.Circle.AngularNormalization.a0, div_pos hK ha0, fun w f hf => ?_⟩
  let F : AngCircle → ℝ := f ∘ angEquiv.symm
  have hcomp : F ∘ angEquiv = f := by
    funext x
    simp only [F, Function.comp_apply, angEquiv.symm_apply_apply]
  have hF : IsSmoothAngular F := (isSmoothPeriodic_comp_iff F).mp (by rw [hcomp]; exact hf)
  have hmp : MeasurePreserving angEquiv
      (siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w) (vmLaw (WithLp.toLp 2 w)) :=
    ⟨angEquiv.measurable, quartic_site_map_angEquiv w⟩
  have hEnt := Analysis.homogeneousEntropy_comp_measurePreserving hmp
    ((((hf.continuous_torus.measurable.comp angEquiv.symm.measurable).pow_const 2)).aestronglyMeasurable)
  have hL := hLS (WithLp.toLp 2 w) F (angDeriv F) (smooth_isWeakDeriv hF)
  have hI : (∫ θ, angDeriv F θ ^ 2 ∂vmLaw (WithLp.toLp 2 w)) =
      DGPS.Circle.AngularNormalization.a0⁻¹ * ∫ x, coordPartial 0 f x ^ 2
        ∂siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w := by
    rw [← quartic_site_map_angEquiv w, angEquiv.measurableEmbedding.integral_map]
    have hd : ∀ x, angDeriv F (angEquiv x) ^ 2 =
        DGPS.Circle.AngularNormalization.a0⁻¹ * coordPartial 0 f x ^ 2 := by
      intro x
      have hd := coordPartial_comp_angEquiv hF x
      rw [hcomp] at hd
      rw [hd]
      unfold DGPS.Circle.AngularNormalization.a0
      field_simp [Real.pi_ne_zero]
      ring
    simp_rw [hd]
    exact integral_const_mul _ _
  rw [hI] at hL
  have he : homogeneousEntropy (siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w)
      (fun x => f x ^ 2) = homogeneousEntropy (vmLaw (WithLp.toLp 2 w)) (fun θ => F θ ^ 2) := by
    simpa only [F, Function.comp_apply, angEquiv.symm_apply_apply] using hEnt
  rw [he]
  convert hL using 1 <;> congr 1 <;> ring

end DGPS.FiniteN
