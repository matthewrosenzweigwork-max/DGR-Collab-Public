import DGRHS.Commutator.SourceRieszAdjointPhysicalDrift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! UNCOMPILED source weak-evolution adapter. Absolute continuity and the
primitive differential mean-field equation for the selected time test imply
the terminal time-test identity. No endpoint identity is an assumption. This
records the weak well-posedness/time-test class; it does not derive differentiation
under an integral from a pointwise PDE without its properness hypotheses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

structure SourceRieszMeanFieldTestEvolution
    (s β T : ℝ) (ρ : ℝ→E→ℝ) (q : ℝ→E→ℝ) : Prop where
  absolute_continuity : AbsolutelyContinuousOnInterval
    (fun r=>∫ z,q r z ∂gaussianRieszDensityMeasure (ρ r)) 0 T
  differential_equation : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
    HasDerivAt (fun u=>∫ z,q u z ∂gaussianRieszDensityMeasure (ρ u))
      (sourceRieszMeanTestDrift s β (ρ r) q r) r

lemma SourceRieszMeanFieldTestEvolution.time_test_identity
    (s β T : ℝ) (hT : 0≤T) (ρ : ℝ→E→ℝ) (q : ℝ→E→ℝ)
    (h : SourceRieszMeanFieldTestEvolution s β T ρ q) :
    Integrable (fun r=>sourceRieszMeanTestDrift s β (ρ r) q r) (volume.restrict (Ioc 0 T)) ∧
      (∫ z,q T z ∂gaussianRieszDensityMeasure (ρ T))-
        (∫ z,q 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 T,sourceRieszMeanTestDrift s β (ρ r) q r := by
  let J := fun r=>∫ z,q r z ∂gaussianRieszDensityMeasure (ρ r)
  have he : deriv J=ᵐ[volume.restrict (Ioc 0 T)]
      (fun r=>sourceRieszMeanTestDrift s β (ρ r) q r) := by
    filter_upwards [h.differential_equation] with r hr
    exact hr.deriv
  have hi : Integrable (deriv J) (volume.restrict (Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp h.absolute_continuity.intervalIntegrable_deriv
  refine ⟨hi.congr he,?_⟩
  have ht := h.absolute_continuity.integral_deriv_eq_sub
  rw [intervalIntegral.integral_of_le hT] at ht
  change (∫ r in Ioc 0 T,deriv J r)=J T-J 0 at ht
  rw [integral_congr_ae he] at ht
  exact ht.symm

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszMeanFieldTestEvolution
#print axioms DGRHS.Commutator.SourceRieszMeanFieldTestEvolution
#check @DGRHS.Commutator.SourceRieszMeanFieldTestEvolution.time_test_identity
#print axioms DGRHS.Commutator.SourceRieszMeanFieldTestEvolution.time_test_identity
