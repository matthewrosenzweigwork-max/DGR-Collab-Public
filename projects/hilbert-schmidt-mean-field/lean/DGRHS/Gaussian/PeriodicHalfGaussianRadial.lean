import DGRHS.Gaussian.PeriodicHalfGaussianPair
import DGRHS.Gaussian.PeriodicBesselProper
import DGRHS.Gaussian.PeriodicBesselRadial
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Native actual planar Gaussian/polar law. The primary PolarCoord body
and exact pinned hash are recorded in native-reuse-release (Apache2).
This is an extended-integral identity: properness is a conclusion below,
not a hypothesis hidden in a totalized real integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DGRHS.Periodic

/-- Exact radial distribution of two independent variance-one-half Gaussians. -/
theorem periodic_halfGaussian_radial_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (Real.sqrt (p.1^2+p.2^2))
      ∂(gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))) =
      ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (2*r*Real.exp (-r^2))*F r := by
  rw [periodic_halfGaussian_pair_law,lintegral_withDensity_eq_lintegral_mul
    (g := fun p : ℝ × ℝ => F (Real.sqrt (p.1^2+p.2^2))) _ (by fun_prop)
    (hF.comp (by fun_prop))]
  rw [←lintegral_comp_polarCoord_symm]
  have he : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
      (ENNReal.ofReal (Real.pi⁻¹*Real.exp (-((polarCoord.symm p).1^2+
        (polarCoord.symm p).2^2)))*
        F (Real.sqrt ((polarCoord.symm p).1^2+(polarCoord.symm p).2^2))))
      =ᵐ[volume.restrict polarCoord.target]
    (fun p => (ENNReal.ofReal (p.1*Real.pi⁻¹*Real.exp (-p.1^2))*F p.1)*1) := by
    filter_upwards [ae_restrict_mem (polarCoord.open_target.measurableSet)] with p hp
    have hr : 0 < p.1 := hp.1
    have hs : (polarCoord.symm p).1^2+(polarCoord.symm p).2^2=p.1^2 := by
      change (p.1*Real.cos p.2)^2+(p.1*Real.sin p.2)^2=p.1^2
      nlinarith [Real.cos_sq_add_sin_sq p.2]
    rw [hs,Real.sqrt_sq hr.le,smul_eq_mul,←mul_assoc,←ENNReal.ofReal_mul hr.le]
    simp only [mul_one]
    congr 1
    congr 1
    ring
  change (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
    (ENNReal.ofReal (Real.pi⁻¹*Real.exp (-((polarCoord.symm p).1^2+
      (polarCoord.symm p).2^2)))*
      F (Real.sqrt ((polarCoord.symm p).1^2+(polarCoord.symm p).2^2)))) = _
  rw [lintegral_congr_ae he]
  change (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (p.1*Real.pi⁻¹*Real.exp (-p.1^2))*F p.1)*1
    ∂((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)) = _
  rw [←Measure.prod_restrict,lintegral_prod _ (by fun_prop)]
  simp only [mul_one]
  simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [Real.volume_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hpi := Real.pi_pos
  have hr' : 0 < r := hr
  dsimp only
  rw [show Real.pi-(-Real.pi)=2*Real.pi by ring]
  rw [mul_assoc,mul_comm (F r),←mul_assoc,←ENNReal.ofReal_mul (by positivity)]
  congr 1
  congr 1
  field_simp

/-- The genuine Gaussian Bessel factor equals the source radial factor. -/
theorem periodic_halfGaussian_Bessel_identity (N : ℕ) :
    (∫⁻ p, ENNReal.ofReal ((periodicBesselI0
      (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N)
      ∂(gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))) =
      periodicCriticalRadialIntegral N := by
  have hI : Measurable (fun r : ℝ => periodicBesselI0 (2*r/Real.sqrt (N:ℝ))) :=
    stronglyMeasurable_periodicBesselI0.measurable.comp (by fun_prop)
  have he := periodic_halfGaussian_radial_lintegral
    (fun r => ENNReal.ofReal (periodicBesselI0 (2*r/Real.sqrt (N:ℝ))^N))
    (ENNReal.measurable_ofReal.comp (hI.pow_const N))
  change _ = _ at he
  rw [he]
  unfold periodicCriticalRadialIntegral
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change ENNReal.ofReal (2*r*Real.exp (-r^2))*
    ENNReal.ofReal (periodicBesselI0 (2*r/Real.sqrt (N:ℝ))^N) = _
  have hr' : 0 < r := hr
  rw [←ENNReal.ofReal_mul (by positivity)]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_halfGaussian_radial_lintegral
#print axioms DGRHS.Periodic.periodic_halfGaussian_Bessel_identity
#check @DGRHS.Periodic.periodic_halfGaussian_radial_lintegral
#check @DGRHS.Periodic.periodic_halfGaussian_Bessel_identity
