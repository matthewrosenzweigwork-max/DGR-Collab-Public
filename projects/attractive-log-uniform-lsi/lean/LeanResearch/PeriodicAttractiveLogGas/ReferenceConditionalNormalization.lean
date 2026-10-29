import LeanResearch.PeriodicAttractiveLogGas.ReferenceExponentialComparison
import LeanResearch.PeriodicAttractiveLogGas.OneCoordinateConditionals

/-! Actual residual sections and conditional normalization in source
lines 2645--2664. Fixed closed-cell placements and almost-everywhere
conditional-law statements are kept distinct. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.ReferenceConditionalNormalization

open MeshCells CellRestrictions LabelOccupations ReferenceResidual ReferenceSelfTerms
  ReferencePotentialBounds ReferenceDensityChange OneCoordinateConditionals

theorem integral_abs_green_le {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (μ : Measure Torus)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) (x : Torus) :
    (∫ y, |greenKernel x y| ∂μ) ≤ globalPotentialBound J := by
  have hd := reference_le_haar hJ a μ hμ
  have hi := (green_translate_integrable x).smul_measure
    (c := ENNReal.ofReal (Real.exp 1 * (J : ℝ) ^ 2)) ENNReal.ofReal_ne_top
  calc
    _ ≤ ∫ y, |greenKernel x y| ∂(ENNReal.ofReal (Real.exp 1 * (J : ℝ) ^ 2) • torusMeasure) :=
      integral_mono_measure hd (Eventually.of_forall fun y => abs_nonneg _) hi.abs
    _ = _ := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
        integral_abs_green_translate]
      rfl

theorem integrable_green_product {J : ℕ} (hJ : 0 < J) (b : MeshIndex J)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b) :
    Integrable (Function.uncurry greenKernel) (μ.prod ν) := by
  apply (integrable_prod_iff measurable_greenKernel.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (global_potential_bound hJ b ν hν x).1), ?_⟩
  have hm₀ : StronglyMeasurable (Function.uncurry (fun x y => ‖greenKernel x y‖)) :=
    measurable_greenKernel.norm.stronglyMeasurable
  have hm : AEStronglyMeasurable (fun x => ∫ y, ‖greenKernel x y‖ ∂ν) μ :=
    hm₀.integral_prod_right.aestronglyMeasurable
  apply (integrable_const (globalPotentialBound J)).mono' hm
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs] using integral_abs_green_le hJ b ν hν x

theorem pairAverage_symm {J : ℕ} (hJ : 0 < J) (b : MeshIndex J)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b) :
    pairAverage μ ν = pairAverage ν μ := by
  unfold pairAverage potential
  rw [integral_integral_swap (integrable_green_product hJ b μ ν hν)]
  simp_rw [greenKernel_symm]

theorem residual_symm {J : ℕ} (hJ : 0 < J) (b : MeshIndex J)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b) (x y : Torus) :
    residual μ ν x y = residual ν μ y x := by
  rw [residual_eq_source_order, residual_eq_source_order, greenKernel_symm x y,
    pairAverage_symm hJ b μ ν hν]
  ring

/-- Actual canonicality at every fixed pole, justified by global Green and
potential integrability. No AE canonical-section premise is used. -/
theorem residual_section_centered {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (μ ν : Measure Torus) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ b) (y : Torus) :
    Integrable (fun z => residual μ ν z y) μ ∧ (∫ z, residual μ ν z y ∂μ) = 0 := by
  have hi : Integrable (fun z => greenKernel z y) μ := by
    simpa only [greenKernel_symm] using (global_potential_bound hJ a μ hμ y).1
  have hp := (global_pairAverage_bound hJ b μ ν hν).1
  have hsub : Integrable (fun z => greenKernel z y - potential ν z) μ := hi.sub hp
  have hsub' : Integrable (fun z => greenKernel z y - potential ν z - potential μ y) μ :=
    hsub.sub (integrable_const _)
  constructor
  · have ht : Integrable (fun z => greenKernel z y - potential ν z - potential μ y +
        pairAverage μ ν) μ := hsub'.add (integrable_const _)
    simpa only [residual_eq_source_order] using! ht
  · simp_rw [residual_eq_source_order]
    rw [integral_add hsub' (integrable_const _), integral_sub hsub (integrable_const _),
      integral_sub hi hp]
    have he : (∫ z, greenKernel z y ∂μ) = potential μ y := by
      unfold potential
      simp_rw [greenKernel_symm]
    rw [he]
    simp only [integral_const, probReal_univ, one_smul, pairAverage]
    ring

/-- Literal source R_i on the existing deleted-coordinate configuration. -/
def residualSection {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) : ℝ :=
  (∑ j, residual (μ (η i)) (μ (η (i.succAbove j))) z (Y j)) / (n + 1 : ℕ)

def sectionWeight {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) (z : Torus) : ℝ :=
  Real.exp (β * residualSection μ η i Y z - (β / (n + 1 : ℕ)) * potential (μ (η i)) z)

def sectionNormalizer {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) : ℝ :=
  ∫ z, sectionWeight μ η i β Y z ∂μ (η i)

theorem measurable_residualSection {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (Y : Configuration n) : Measurable (residualSection μ η i Y) := by
  have hm (j : Fin n) : Measurable (fun z : Torus =>
      residual (μ (η i)) (μ (η (i.succAbove j))) z (Y j)) := by
    simp only [residual_eq_source_order]
    have hg : Measurable (fun z : Torus => greenKernel z (Y j)) :=
      measurable_greenKernel.comp (measurable_id.prodMk measurable_const)
    exact ((hg.sub (ReferenceDensityChange.measurable_potential _)).sub
      measurable_const).add measurable_const
  have hs : Measurable (fun z : Torus => ∑ j : Fin n,
      residual (μ (η i)) (μ (η (i.succAbove j))) z (Y j)) :=
    Finset.measurable_sum _ (fun j _ => hm j)
  exact hs.div_const _

theorem measurable_sectionWeight {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) : Measurable (sectionWeight μ η i β Y) :=
  (((measurable_residualSection μ η i Y).const_mul β).sub
    ((ReferenceDensityChange.measurable_potential (μ (η i))).const_mul _)).exp

theorem residualSection_centered {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (Y : Configuration n) :
    Integrable (residualSection μ η i Y) (μ (η i)) ∧
    (∫ z, residualSection μ η i Y z ∂μ (η i)) = 0 := by
  have hh (j : Fin n) := residual_section_centered hJ (η i) (η (i.succAbove j))
    (μ (η i)) (μ (η (i.succAbove j))) (hμ (η i)) (hμ (η (i.succAbove j))) (Y j)
  constructor
  · exact (integrable_finsetSum _ fun j _ => (hh j).1).div_const _
  · change (∫ z, (∑ j : Fin n, residual (μ (η i))
        (μ (η (i.succAbove j))) z (Y j)) / (n + 1 : ℕ) ∂μ (η i)) = 0
    rw [integral_div, integral_finsetSum _ (fun j _ => (hh j).1)]
    simp_rw [(hh _).2]
    simp

theorem sum_residualSection {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) (X : Configuration (n + 1)) :
    (∑ i, residualSection μ η i (removeSite i X) (X i)) =
      2 * ResidualExponential.residualSum μ η X := by
  classical
  let f (i j : Fin (n + 1)) := residual (μ (η i)) (μ (η j)) (X i) (X j)
  have hf (i j) : f j i = f i j := residual_symm hJ (η i) _ _ (hμ (η i)) _ _
  have hrow (i : Fin (n + 1)) : (∑ j : Fin n, f i (i.succAbove j)) =
      (∑ j, f i j) - f i i := by
    have hh := Fin.sum_univ_succAbove (f i) i
    linarith
  have hh := upper_pair_cross_sum f
  simp_rw [hf, Finset.sum_add_distrib] at hh
  simp only [residualSection, removeSite]
  change (∑ i, (∑ j : Fin n, f i (i.succAbove j)) / (n + 1 : ℕ)) = _
  simp_rw [hrow]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← hh,
    ResidualExponential.residualSum_eq_upper_pairs]
  dsimp only [f]
  ring

theorem section_exponent {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (β : ℝ)
    (Y : Configuration n) (z : Torus) :
    β * residualSection μ η i Y z - (β / (n + 1 : ℕ)) * potential (μ (η i)) z =
      (β / (n + 1 : ℕ)) * (∑ j, greenKernel z (Y j)) - β * averagePotential μ η z +
      (β / (n + 1 : ℕ)) * (∑ j, (pairAverage (μ (η i)) (μ (η (i.succAbove j))) -
        potential (μ (η i)) (Y j))) := by
  simp only [residualSection, residual_eq_source_order, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, averagePotential]
  rw [Fin.sum_univ_succAbove (fun j => potential (μ (η j)) z) i]
  ring

theorem density_mul_sectionWeight {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) (z : Torus) :
    (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β (η i)) *
      sectionWeight μ η i β Y z =
    (Real.exp ((β / (n + 1 : ℕ)) * (∑ j : Fin n,
      (pairAverage (μ (η i)) (μ (η (i.succAbove j))) - potential (μ (η i)) (Y j)))) /
        cellNormalizer hJ μ η β (η i)) * OneCoordinateConditionals.sourceWeight β Y z := by
  unfold sectionWeight
  rw [section_exponent]
  unfold OneCoordinateConditionals.sourceWeight GreenPointWeights.torusWeight
  simp only [← Finset.mul_sum]
  simp only [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  simp only [greenKernel]
  ring

/-- Source point-weight bounds imply finite normalization for every fixed
closed-cell placement, including coincident outside source positions. -/
theorem sectionWeight_integrable {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (hη : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    Integrable (sectionWeight μ η i β Y) (μ (η i)) ∧
      0 < sectionNormalizer μ η i β Y := by
  have hb := capped_source_bounds hJ hβ hβ₀
    ConditionalLawEstimates.kernelConstant_pos.le ConditionalLawEstimates.kernelConstant_pos.le
    ConditionalLawEstimates.kernel_log_bound ConditionalLawEstimates.kernel_gradient_bound
    hmesh η hη i Y hY (η i) GreenPointWeights.Patch.cell
  have hi : Integrable (sourceWeight β Y) (meshCellMeasure J hJ (η i)) := by
    simpa only [GreenPointWeights.patchMeasure] using hb.1
  have hz := cellNormalizer_pos_of_formula hJ μ η β (η i) (hformula (η i))
  have hd : Measurable (fun z => Real.exp (β * averagePotential μ η z) /
      cellNormalizer hJ μ η β (η i)) :=
    ((ReferenceDensityChange.measurable_averagePotential μ η).const_mul β).exp.div_const _
  have ht : Integrable (sectionWeight μ η i β Y) (μ (η i)) := by
    apply (RelativeEntropyVariational.integrable_density_iff (hformula (η i)) hd
      (Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hz.le)).mpr
    simp_rw [density_mul_sectionWeight]
    exact hi.const_mul _
  refine ⟨ht, ?_⟩
  exact integral_exp_pos ht

/-- Jensen's inequality in its tangent-line form, with both integrability
premises checked before integration. -/
theorem log_integral_exp_ge {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {F : α → ℝ} (hF : Integrable F ν)
    (he : Integrable (fun z => Real.exp (F z)) ν) :
    (∫ z, F z ∂ν) ≤ Real.log (∫ z, Real.exp (F z) ∂ν) := by
  let m := ∫ z, F z ∂ν
  have hi : Integrable (fun z => Real.exp m * (F z - m + 1)) ν :=
    ((hF.sub (integrable_const m)).add (integrable_const 1)).const_mul _
  have hb : ∀ z, Real.exp m * (F z - m + 1) ≤ Real.exp (F z) := by
    intro z
    calc
      _ ≤ Real.exp m * Real.exp (F z - m) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hh := integral_mono hi he hb
  have hsub : Integrable (fun z => F z - m) ν := hF.sub (integrable_const m)
  have hh₀ : (∫ z, Real.exp m * (F z - m + 1) ∂ν) = Real.exp m := by
    rw [integral_const_mul, integral_add hsub (integrable_const 1),
      integral_sub hF (integrable_const m)]
    simp [m]
  rw [hh₀] at hh
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos m) hh

theorem conditional_normalizer_lower {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (hη : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    Integrable (sectionWeight μ η i β Y) (μ (η i)) ∧
    0 < sectionNormalizer μ η i β Y ∧
    -(β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤
      Real.log (sectionNormalizer μ η i β Y) := by
  obtain ⟨he, hz⟩ := sectionWeight_integrable hJ μ η hβ hβ₀ hformula hmesh hη i Y hY
  obtain ⟨hr, hzero⟩ := residualSection_centered hJ μ hμ η i Y
  have hp := (global_pairAverage_bound hJ (η i) (μ (η i)) (μ (η i)) (hμ (η i))).1
  have hf : Integrable (fun z => β * residualSection μ η i Y z -
      (β / (n + 1 : ℕ)) * potential (μ (η i)) z) (μ (η i)) :=
    (hr.const_mul β).sub (hp.const_mul _)
  have hb := log_integral_exp_ge (μ (η i)) hf he
  rw [integral_sub (hr.const_mul _) (hp.const_mul _), integral_const_mul,
    integral_const_mul, hzero, mul_zero, zero_sub] at hb
  exact ⟨he, hz, by simpa only [neg_mul, pairAverage, sectionNormalizer, sectionWeight] using hb⟩

theorem referenceTilt_factor {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) :
    ∃ A : ℝ, 0 < A ∧ ∀ z,
      referenceTilt μ η β (insertSite i z Y) = A * sectionWeight μ η i β Y z := by
  classical
  let D := (β / (n + 1 : ℕ)) * (∑ j : Fin n,
    (pairAverage (μ (η i)) (μ (η (i.succAbove j))) - potential (μ (η i)) (Y j)))
  let C := β * (pairEnergy regularGreenRepresentative n Y / (n + 1 : ℕ) -
    (∑ j : Fin n, averagePotential μ η (Y j)) +
    (∑ ij ∈ ResidualNearExponential.upperPairs (n + 1),
      pairAverage (μ (η ij.1)) (μ (η ij.2))) / (n + 1 : ℕ))
  refine ⟨Real.exp (C - D), Real.exp_pos _, fun z => ?_⟩
  unfold referenceTilt sectionWeight
  rw [← Real.exp_add, section_exponent, centering_expansion]
  have hg : (∑ ij ∈ ResidualNearExponential.upperPairs (n + 1),
      greenKernel (insertSite i z Y ij.1) (insertSite i z Y ij.2)) =
      pairEnergy regularGreenRepresentative n Y + ∑ j : Fin n, greenKernel z (Y j) := by
    change (∑ ij ∈ planarOrderedPairs (n + 1),
      regularGreenRepresentative (insertSite i z Y ij.1 - insertSite i z Y ij.2)) = _
    rw [← pairEnergy_eq_sum_orderedPairs,
      pairEnergy_insertSite regularGreenRepresentative regularGreenRepresentative_even]
    rfl
  rw [hg, Fin.sum_univ_succAbove (fun k => averagePotential μ η (insertSite i z Y k)) i]
  simp only [insertSite_self, insertSite_succAbove]
  congr 1
  dsimp only [C, D]
  ring

/-- The actual normalized section of the reference tilt, for every admissible
fixed placement. It is not a hypothetical density comparison. -/
theorem conditionalKernel_eq_reference_density {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (hη : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y =
      (μ (η i)).withDensity (fun z =>
        ENNReal.ofReal (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y)) := by
  obtain ⟨A, hA, hf⟩ := referenceTilt_factor μ η i β Y
  obtain ⟨hi, hz⟩ := sectionWeight_integrable hJ μ η hβ hβ₀ hformula hmesh hη i Y hY
  exact PositiveProductConditionals.conditionalKernel_factor_eq_real_density _ _
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y hA
    (measurable_sectionWeight μ η i β Y) hf hi hz

theorem reference_productLaw_eq_labelGibbs {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a))) :
    PositiveProductConditionals.productLaw (fun i => μ (η i)) (referenceTilt μ η β) =
      labelGibbsMeasure hJ η β := by
  obtain ⟨hi, _, he⟩ := change_of_reference hJ hN μ η hβ hsub hformula
  rw [PositiveProductConditionals.productLaw_eq_real_density _
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) hi, he]
  rfl

theorem reference_lintegral_disintegrate {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (i : Fin (n + 1)) {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂labelGibbsMeasure hJ η β) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
        ∂PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
          (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y
        ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β) := by
  have hh := PositiveProductConditionals.lintegral_disintegrate_of_integrable
    (fun i => μ (η i)) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    (change_of_reference hJ hN μ η hβ hsub hformula).1 hF
  simpa only [reference_productLaw_eq_labelGibbs hJ hN μ η hβ hsub hformula] using hh

theorem normalizer_lower_of_integrable {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n)
    (he : Integrable (sectionWeight μ η i β Y) (μ (η i))) :
    -(β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤
      Real.log (sectionNormalizer μ η i β Y) := by
  obtain ⟨hr, hzero⟩ := residualSection_centered hJ μ hμ η i Y
  have hp := (global_pairAverage_bound hJ (η i) (μ (η i)) (μ (η i)) (hμ (η i))).1
  have hf : Integrable (fun z => β * residualSection μ η i Y z -
      (β / (n + 1 : ℕ)) * potential (μ (η i)) z) (μ (η i)) :=
    (hr.const_mul β).sub (hp.const_mul _)
  have hb := log_integral_exp_ge (μ (η i)) hf he
  rw [integral_sub (hr.const_mul _) (hp.const_mul _), integral_const_mul,
    integral_const_mul, hzero, mul_zero, zero_sub] at hb
  simpa only [neg_mul, pairAverage, sectionNormalizer, sectionWeight] using hb

/-- The exceptional set is null for the actual outside marginal of the
original prescribed-cell Gibbs law. No fixed-configuration integrability
assumption is introduced. -/
theorem ae_reference_conditional_normalization {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (i : Fin (n + 1)) :
    ∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β),
      Integrable (sectionWeight μ η i β Y) (μ (η i)) ∧
      0 < sectionNormalizer μ η i β Y ∧
      -(β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤
        Real.log (sectionNormalizer μ η i β Y) ∧
      PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y =
        (μ (η i)).withDensity (fun z =>
          ENNReal.ofReal (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y)) := by
  have ht := (change_of_reference hJ hN μ η hβ hsub hformula).1
  have hfin := (PositiveProductConditionals.normalizer_ne_top_iff_integrable
    (fun i => μ (η i)) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _)).mpr ht
  have hae := PositiveProductConditionals.ae_marginal_real_sections
    (fun i => μ (η i)) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i hfin
  change ∀ᵐ Y ∂Measure.map (removeSite i)
      (PositiveProductConditionals.productLaw (fun i => μ (η i)) (referenceTilt μ η β)), _ at hae
  rw [reference_productLaw_eq_labelGibbs hJ hN μ η hβ hsub hformula] at hae
  filter_upwards [hae] with Y hY
  obtain ⟨A, hA, hf⟩ := referenceTilt_factor μ η i β Y
  have hi : Integrable (sectionWeight μ η i β Y) (μ (η i)) := by
    have hh := hY.1.const_mul A⁻¹
    simp_rw [hf, ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] at hh
    exact hh
  have hz : 0 < sectionNormalizer μ η i β Y := integral_exp_pos hi
  exact ⟨hi, hz, normalizer_lower_of_integrable hJ μ hμ η i β Y hi,
    PositiveProductConditionals.conditionalKernel_factor_eq_real_density _ _
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y hA
      (measurable_sectionWeight μ η i β Y) hf hi hz⟩

/-- Disintegration against the literal normalized residual section density.
The marginal is the actual all-other-coordinate marginal, not a smaller Gibbs law. -/
theorem reference_lintegral_disintegrate_density {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (i : Fin (n + 1)) {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂labelGibbsMeasure hJ η β) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂(μ (η i)).withDensity (fun z =>
        ENNReal.ofReal (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y))
        ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β) := by
  rw [reference_lintegral_disintegrate hJ hN μ η hβ hsub hformula i hF]
  apply lintegral_congr_ae
  filter_upwards [ae_reference_conditional_normalization hJ hN μ hμ η hβ hsub hformula i]
    with Y hY
  rw [hY.2.2.2]

@[simp] theorem sectionWeight_zero {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) :
    sectionWeight μ η i 0 Y z = 1 := by simp [sectionWeight]

@[simp] theorem sectionNormalizer_zero {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (Y : Configuration n) : sectionNormalizer μ η i 0 Y = 1 := by
  simp [sectionNormalizer]

/-- Full source-family wrapper retaining both density bounds. The first
conclusion is valid for every admissible closed-cell placement; the second
is valid outside a null set under the actual Gibbs outside marginal. -/
theorem source_conditional_normalization {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (ht : t ≤ ConditionalLawEstimates.occupationBound β₀) (hη : OccupationCap t η)
    (i : Fin (n + 1)) :
    (∀ Y, PrescribedOutside hJ η i Y →
      Integrable (sectionWeight μ η i β Y) (μ (η i)) ∧
      0 < sectionNormalizer μ η i β Y ∧
      -(β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤
        Real.log (sectionNormalizer μ η i β Y) ∧
      PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y =
        (μ (η i)).withDensity (fun z =>
          ENNReal.ofReal (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y))) ∧
    (∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β),
      Integrable (sectionWeight μ η i β Y) (μ (η i)) ∧
      0 < sectionNormalizer μ η i β Y ∧
      -(β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤
        Real.log (sectionNormalizer μ η i β Y) ∧
      PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y =
        (μ (η i)).withDensity (fun z =>
          ENNReal.ofReal (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y))) := by
  have hμ := ReferenceExponentialComparison.source_reference_domination hJ μ η β hformula hdensity
  have hcap := hη.mono ht
  constructor
  · intro Y hY
    obtain ⟨hi, hz, hl⟩ := conditional_normalizer_lower hJ μ hμ η hβ hβ₀ hformula hmesh hcap i Y hY
    exact ⟨hi, hz, hl, conditionalKernel_eq_reference_density hJ μ η hβ hβ₀ hformula hmesh hcap i Y hY⟩
  · exact ae_reference_conditional_normalization hJ hN μ hμ η hβ (hβ₀.trans_lt hsub) hformula i

end PeriodicAttractiveLogGas.ReferenceConditionalNormalization
