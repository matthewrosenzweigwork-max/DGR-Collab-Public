import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Prod

/-! Spatial observables under an independent normalized velocity factor.
Native product integration, density tensorization and relative-entropy data
processing are reused from pinned Mathlib (Apache 2.0). These interfaces do
not assert kinetic dynamics or independence under a competing joint law. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Kinetic
variable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]

theorem spatial_partition_tensor (μ : Measure X) (η : Measure V)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] (u : X → ℝ) :
    (∫ z : X × V, Real.exp (u z.1) ∂μ.prod η) = ∫ x, Real.exp (u x) ∂μ := by
  simpa only [probReal_univ, one_smul] using
    (integral_fun_fst (μ := μ) (ν := η) (fun x => Real.exp (u x)))

theorem spatial_gibbs_tensor (μ : Measure X) (η : Measure V)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (u : X → ℝ) (hu : Measurable u) :
    (μ.prod η).tilted (fun z => u z.1) = (μ.tilted u).prod η := by
  unfold Measure.tilted
  rw [spatial_partition_tensor μ η u]
  have hm : Measurable (fun x => ENNReal.ofReal
      (Real.exp (u x) / ∫ y, Real.exp (u y) ∂μ)) :=
    ((Real.continuous_exp.measurable.comp hu).div_const _).ennreal_ofReal
  exact (prod_withDensity_left (μ := μ) (ν := η) hm).symm

theorem spatial_kl_marginal (Q : Measure X) (η : Measure V) (ν : Measure (X × V))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure η] [IsProbabilityMeasure ν] :
    klDiv (ν.map Prod.fst) Q ≤ klDiv ν (Q.prod η) := by
  simpa using klDiv_map_le ν (Q.prod η) measurable_fst

theorem spatial_kl_marginal_finite (Q : Measure X) (η : Measure V) (ν : Measure (X × V))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure η] [IsProbabilityMeasure ν]
    (hν : klDiv ν (Q.prod η) ≠ ∞) :
    klDiv (ν.map Prod.fst) Q ≠ ∞ :=
  ne_top_of_le_ne_top hν (spatial_kl_marginal Q η ν)

/-- A bound valid for all spatial laws transfers to every joint competitor,
with its full relative entropy; its position and velocity need not be independent. -/
theorem spatial_entropic_bound_tensor (Q : Measure X) (η : Measure V)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure η]
    (u : X → ℝ) (hu : StronglyMeasurable u) (a b : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ (σ : Measure X) [IsProbabilityMeasure σ], klDiv σ Q ≠ ∞ →
      Integrable u σ ∧ |∫ x, u x ∂σ| ≤ a * (klDiv σ Q).toReal + b)
    (ν : Measure (X × V)) [IsProbabilityMeasure ν] (hν : klDiv ν (Q.prod η) ≠ ∞) :
    Integrable (fun z => u z.1) ν ∧
      |∫ z, u z.1 ∂ν| ≤ a * (klDiv ν (Q.prod η)).toReal + b := by
  haveI : IsProbabilityMeasure (ν.map Prod.fst) := inferInstance
  obtain ⟨hi, hb⟩ := hbound (ν.map Prod.fst) (spatial_kl_marginal_finite Q η ν hν)
  have him := (integrable_map_measure hu.aestronglyMeasurable measurable_fst.aemeasurable).mp hi
  have he := integral_map (μ := ν) (φ := Prod.fst) measurable_fst.aemeasurable
    (f := u) hu.aestronglyMeasurable
  refine ⟨him, ?_⟩
  rw [he] at hb
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hν (spatial_kl_marginal Q η ν)) ha) le_rfl)

end DGRHS.Kinetic
#check @DGRHS.Kinetic.spatial_partition_tensor
#print axioms DGRHS.Kinetic.spatial_partition_tensor
#check @DGRHS.Kinetic.spatial_gibbs_tensor
#print axioms DGRHS.Kinetic.spatial_gibbs_tensor
#check @DGRHS.Kinetic.spatial_kl_marginal
#print axioms DGRHS.Kinetic.spatial_kl_marginal
#check @DGRHS.Kinetic.spatial_kl_marginal_finite
#print axioms DGRHS.Kinetic.spatial_kl_marginal_finite
#check @DGRHS.Kinetic.spatial_entropic_bound_tensor
#print axioms DGRHS.Kinetic.spatial_entropic_bound_tensor
