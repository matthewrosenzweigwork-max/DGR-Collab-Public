import LeanResearch.PeriodicAttractiveLogGas.OccupationFieldL2
import LeanResearch.PeriodicAttractiveLogGas.OccupationFieldEstimates
import LeanResearch.PeriodicAttractiveLogGas.MovingPoleCalculus

/-! Actual exponential field errors and random cell normalizers in the
occupation-rates proof. All expectations retain the original labeled law.
The development note records the source correspondence and checked boundary. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.OccupationFieldApproximation

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions
  OneCoordinateConditionals ConditionalLawEstimates GreenConditionalInfluence
  OccupationPositiveExponential OccupationFieldL2

def fieldError {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (i : Fin (n + 1)) (z : Torus) (X : Configuration (n + 1)) : ℝ :=
  psi i z X - meanPotential hJ η β z

def potentialCellNormalizer {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (a : MeshIndex J) : ℝ :=
  ∫ z, Real.exp (β * meanPotential hJ η β z) ∂meshCellMeasure J hJ a

def potentialCellDensity {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (a : MeshIndex J) (z : Torus) : ℝ :=
  Real.exp (β * meanPotential hJ η β z) / potentialCellNormalizer hJ η β a

def fieldNormalizer {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J) (X : Configuration (n + 1)) : ℝ :=
  ∫ z, potentialCellDensity hJ η β a z * Real.exp (β * fieldError hJ η β i z X)
    ∂meshCellMeasure J hJ a

/-- Every constant is chosen before the particle number and labels. -/
def potentialBound (J : ℕ) (β₀ : ℝ) : ℝ := greenSecondMomentBound J β₀ + 1

def potentialDensityLower (J : ℕ) (β₀ : ℝ) : ℝ :=
  Real.exp (-2 * β₀ * potentialBound J β₀)

def potentialDensityUpper (J : ℕ) (β₀ : ℝ) : ℝ :=
  Real.exp (2 * β₀ * potentialBound J β₀)

def fieldLowerConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  MovingPoleCalculus.greenLowerConstant + potentialBound J β₀

def fieldNormalizerLower (J : ℕ) (β₀ : ℝ) : ℝ :=
  Real.exp (-β₀ * fieldLowerConstant J β₀)

def exponentialMomentBound (J : ℕ) (β₀ : ℝ) : ℝ :=
  Real.exp (2 * β₀ * (potentialBound J β₀ + densityNormBound β₀ * envelopeBound J))

def exponentialErrorConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  β₀ * Real.sqrt (2 * fieldL2Constant J β₀ * (1 + exponentialMomentBound J β₀))

def approximationConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  (J : ℝ) ^ 2 * potentialDensityUpper J β₀ *
    (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀)

def fieldThreshold (β₀ : ℝ) : ℕ := max 2 ⌈8 * β₀⌉₊

theorem fieldThreshold_bounds {N : ℕ} {β₀ : ℝ} (hN : fieldThreshold β₀ ≤ N) :
    2 ≤ N ∧ 8 * β₀ ≤ (N : ℝ) :=
  ⟨(le_max_left _ _).trans hN, Nat.ceil_le.mp ((le_max_right _ _).trans hN)⟩

theorem potentialBound_pos (J : ℕ) (β₀ : ℝ) : 0 < potentialBound J β₀ := by
  unfold potentialBound
  linarith [greenSecondMomentBound_nonneg J β₀]

theorem fieldLowerConstant_pos (J : ℕ) (β₀ : ℝ) : 0 < fieldLowerConstant J β₀ :=
  add_pos MovingPoleCalculus.greenLowerConstant_pos (potentialBound_pos J β₀)

theorem fieldNormalizerLower_pos (J : ℕ) (β₀ : ℝ) : 0 < fieldNormalizerLower J β₀ :=
  Real.exp_pos _

theorem exponentialErrorConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ exponentialErrorConstant J β₀ := mul_nonneg hβ₀ (Real.sqrt_nonneg _)

section Measurability

variable {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1)) (β : ℝ)
  [IsFiniteMeasure (labelGibbsMeasure hJ η β)]

theorem measurable_meanPotential : Measurable (meanPotential hJ η β) := by
  have hm : Measurable (fun p : Torus × Torus ↦
      greenRealRepresentative (p.1 - p.2) * averageDensity hJ η β p.2) :=
    (greenRealRepresentative_measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((measurable_averageDensity hJ η β).comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

omit [IsFiniteMeasure (labelGibbsMeasure hJ η β)] in
theorem measurable_psi_joint (i : Fin (n + 1)) :
    Measurable (fun p : Torus × Configuration (n + 1) ↦ psi i p.1 p.2) :=
  (Finset.measurable_sum _ fun j _ ↦ greenRealRepresentative_measurable.comp
    (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))).const_mul _

theorem measurable_fieldError_joint (i : Fin (n + 1)) :
    Measurable (fun p : Torus × Configuration (n + 1) ↦ fieldError hJ η β i p.1 p.2) :=
  (measurable_psi_joint i).sub ((measurable_meanPotential hJ η β).comp measurable_fst)

omit [IsFiniteMeasure (labelGibbsMeasure hJ η β)] in
theorem measurable_fieldError (i : Fin (n + 1)) (z : Torus) :
    Measurable (fieldError hJ η β i z) :=
  (psi_measurable i z).sub measurable_const

theorem measurable_potentialCellDensity (a : MeshIndex J) :
    Measurable (potentialCellDensity hJ η β a) :=
  (((measurable_meanPotential hJ η β).const_mul β).exp).div_const _

theorem measurable_fieldNormalizer (i : Fin (n + 1)) (a : MeshIndex J) :
    Measurable (fieldNormalizer hJ η β i a) := by
  have hm : Measurable (fun p : Torus × Configuration (n + 1) ↦
      potentialCellDensity hJ η β a p.1 * Real.exp (β * fieldError hJ η β i p.1 p.2)) :=
    ((measurable_potentialCellDensity hJ η β a).comp measurable_fst).mul
      (((measurable_fieldError_joint hJ η β i).const_mul β).exp)
  exact hm.stronglyMeasurable.integral_prod_left.measurable

theorem measurable_field_ratio (i : Fin (n + 1)) (a : MeshIndex J) (z : Torus) :
    Measurable (fun X ↦ Real.exp (β * fieldError hJ η β i z X) / fieldNormalizer hJ η β i a X) :=
  (((measurable_fieldError hJ η β i z).const_mul β).exp).div
    (measurable_fieldNormalizer hJ η β i a)

end Measurability

theorem psi_lower_of_summands {n : ℕ} (i : Fin (n + 1)) (z : Torus)
    (X : Configuration (n + 1))
    (hg : ∀ j, -MovingPoleCalculus.greenLowerConstant ≤ greenRealRepresentative (z - X j)) :
    -MovingPoleCalculus.greenLowerConstant ≤ psi i z X := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hs := Finset.sum_le_sum (s := Finset.univ.erase i) fun j _ ↦ hg j
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hc : ((Finset.univ.erase i).card : ℝ) = n := by simp
  rw [hc] at hs
  simp only [psi, Nat.cast_add, Nat.cast_one]
  calc
    _ = (n + 1 : ℝ)⁻¹ * ((n + 1 : ℝ) * (-MovingPoleCalculus.greenLowerConstant)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    _ ≤ (n + 1 : ℝ)⁻¹ * ((n : ℝ) * (-MovingPoleCalculus.greenLowerConstant)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [MovingPoleCalculus.greenLowerConstant_pos]) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Spatial almost-everywhere lower bound for every fixed tuple, without
asserting a pointwise equality between the two Green representatives. -/
theorem psi_lower_ae_torus {n : ℕ} (i : Fin (n + 1)) (X : Configuration (n + 1)) :
    ∀ᵐ z ∂torusMeasure, -MovingPoleCalculus.greenLowerConstant ≤ psi i z X := by
  have hg (j : Fin (n + 1)) : ∀ᵐ z ∂torusMeasure,
      -MovingPoleCalculus.greenLowerConstant ≤ greenRealRepresentative (z - X j) := by
    have hh := (measurePreserving_sub_right torusMeasure (X j)).quasiMeasurePreserving.ae_eq_comp
      regularGreenRepresentative_ae
    filter_upwards [hh] with z hz
    simp only [Function.comp_apply] at hz
    rw [← hz]
    exact MovingPoleCalculus.green_lower_bound _
  filter_upwards [ae_all_iff.mpr hg] with z hz
  exact psi_lower_of_summands i z X hz

section WeightedAverages

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  (τ : Measure A) (μ : Measure B) [IsProbabilityMeasure τ] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure τ] in
theorem integrable_pair_of_nonneg_bound (H : A × B → ℝ) (hH : Measurable H)
    (hH0 : ∀ Z, 0 ≤ H Z) (hI : ∀ z, Integrable (fun X ↦ H (z, X)) μ)
    {b : A → ℝ} (hb : Integrable b τ) (hbound : ∀ z, (∫ X, H (z, X) ∂μ) ≤ b z) :
    Integrable H (τ.prod μ) := by
  apply (integrable_prod_iff hH.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hI, ?_⟩
  have he : (fun z ↦ ∫ X, ‖H (z, X)‖ ∂μ) = fun z ↦ ∫ X, H (z, X) ∂μ := by
    funext z
    exact integral_congr_ae (Eventually.of_forall fun X ↦ Real.norm_of_nonneg (hH0 (z, X)))
  rw [he]
  have hm : StronglyMeasurable (Function.uncurry (fun z X ↦ H (z, X))) :=
    hH.stronglyMeasurable
  apply hb.mono' hm.integral_prod_right.aestronglyMeasurable
  exact Eventually.of_forall fun z ↦ by
    rw [Real.norm_of_nonneg (integral_nonneg fun X ↦ hH0 (z, X))]
    exact hbound z

/-- Genuine joint integrability makes the weighted random average and its
error integrable. The error bound is integrated with its density of mass one. -/
theorem weighted_normalizer_error (p : A → ℝ) (f : A → B → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hpI : Integrable p τ) (hp1 : (∫ z, p z ∂τ) = 1)
    (hI : Integrable (fun Z : A × B ↦ p Z.1 * f Z.1 Z.2) (τ.prod μ))
    {ε : ℝ} (herror : ∀ z, (∫ X, |f z X - 1| ∂μ) ≤ ε) :
    Integrable (fun X ↦ ∫ z, p z * f z X ∂τ) μ ∧
      Integrable (fun X ↦ |(∫ z, p z * f z X ∂τ) - 1|) μ ∧
      (∫ X, |(∫ z, p z * f z X ∂τ) - 1| ∂μ) ≤ ε := by
  have hab (z : A) (X : B) : ‖p z * f z X - p z‖ = p z * |f z X - 1| := by
    rw [Real.norm_eq_abs]
    calc
      _ = |p z * (f z X - 1)| := by congr 1; ring
      _ = _ := by rw [abs_mul, abs_of_nonneg (hp0 z)]
  have hG : Integrable (fun Z : A × B ↦ p Z.1 * |f Z.1 Z.2 - 1|) (τ.prod μ) := by
    have hh := (hI.sub (hpI.comp_fst μ)).norm
    simpa only [Pi.sub_apply, hab] using! hh
  have hWI : Integrable (fun X ↦ ∫ z, p z * f z X ∂τ) μ := hI.integral_prod_right
  have hWE : Integrable (fun X ↦ |(∫ z, p z * f z X ∂τ) - 1|) μ :=
    (hWI.sub (integrable_const 1)).abs
  refine ⟨hWI, hWE, ?_⟩
  have hpoint : ∀ᵐ X ∂μ, |(∫ z, p z * f z X ∂τ) - 1| ≤
      ∫ z, p z * |f z X - 1| ∂τ := by
    filter_upwards [hI.prod_left_ae] with X hX
    change Integrable (fun z ↦ p z * f z X) τ at hX
    have hh := norm_integral_le_integral_norm (μ := τ) (fun z ↦ p z * f z X - p z)
    rw [integral_sub hX hpI, hp1] at hh
    simp_rw [hab] at hh
    simpa only [Real.norm_eq_abs] using hh
  calc
    _ ≤ ∫ X, ∫ z, p z * |f z X - 1| ∂τ ∂μ := integral_mono_ae hWE hG.integral_prod_right hpoint
    _ = ∫ z, ∫ X, p z * |f z X - 1| ∂μ ∂τ := (integral_integral_swap hG).symm
    _ ≤ ∫ z, p z * ε ∂τ := by
      apply integral_mono_ae hG.integral_prod_left (hpI.mul_const ε)
      exact Eventually.of_forall fun z ↦ by
        change (∫ X, p z * |f z X - 1| ∂μ) ≤ p z * ε
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (herror z) (hp0 z)
    _ = ε := by rw [integral_mul_const, hp1, one_mul]

end WeightedAverages

section ExactConditionalAlgebra

theorem psi_eq_removeSite {n : ℕ} (i : Fin (n + 1)) (z : Torus)
    (X : Configuration (n + 1)) :
    psi i z X = (n + 1 : ℝ)⁻¹ * ∑ j : Fin n, greenRealRepresentative (z - removeSite i X j) := by
  classical
  simp only [psi, Nat.cast_add, Nat.cast_one]
  congr 1
  have h₁ := Finset.sum_erase_add Finset.univ
    (fun j ↦ greenRealRepresentative (z - X j)) (Finset.mem_univ i)
  have h₂ := Fin.sum_univ_succAbove (fun j ↦ greenRealRepresentative (z - X j)) i
  change (∑ j, greenRealRepresentative (z - X j)) =
    greenRealRepresentative (z - X i) + ∑ j : Fin n, greenRealRepresentative (z - removeSite i X j) at h₂
  linarith

theorem exp_psi_eq_rawSourceWeight {n : ℕ} (i : Fin (n + 1)) (β : ℝ)
    (z : Torus) (X : Configuration (n + 1)) :
    Real.exp (β * psi i z X) = rawSourceWeight β (removeSite i X) z := by
  rw [psi_eq_removeSite, rawSourceWeight, ← Finset.mul_sum]
  congr 1
  simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
  ring

@[simp] theorem psi_insertSite_removeSite {n : ℕ} (i : Fin (n + 1))
    (z u : Torus) (X : Configuration (n + 1)) :
    psi i z (insertSite i u (removeSite i X)) = psi i z X := by
  simp only [psi_eq_removeSite, removeSite_insertSite]

@[simp] theorem fieldError_insertSite_removeSite {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1))
    (z u : Torus) (X : Configuration (n + 1)) :
    fieldError hJ η β i z (insertSite i u (removeSite i X)) = fieldError hJ η β i z X := by
  simp only [fieldError, psi_insertSite_removeSite]

@[simp] theorem fieldNormalizer_insertSite_removeSite {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J)
    (u : Torus) (X : Configuration (n + 1)) :
    fieldNormalizer hJ η β i a (insertSite i u (removeSite i X)) = fieldNormalizer hJ η β i a X := by
  simp only [fieldNormalizer, fieldError_insertSite_removeSite]

theorem potential_mul_field_exponential {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1))
    (z : Torus) (X : Configuration (n + 1)) :
    Real.exp (β * meanPotential hJ η β z) * Real.exp (β * fieldError hJ η β i z X) =
      rawSourceWeight β (removeSite i X) z := by
  rw [← Real.exp_add, ← exp_psi_eq_rawSourceWeight]
  congr 1
  simp only [fieldError]
  ring

theorem weighted_field_exponential_eq_raw {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J)
    (z : Torus) (X : Configuration (n + 1)) :
    potentialCellDensity hJ η β a z * Real.exp (β * fieldError hJ η β i z X) =
      (potentialCellNormalizer hJ η β a)⁻¹ * rawSourceWeight β (removeSite i X) z := by
  calc
    _ = (Real.exp (β * meanPotential hJ η β z) *
        Real.exp (β * fieldError hJ η β i z X)) / potentialCellNormalizer hJ η β a := by
      simp only [potentialCellDensity]
      ring
    _ = _ := by rw [potential_mul_field_exponential]; ring

theorem fieldNormalizer_eq_raw_integral {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J)
    (X : Configuration (n + 1)) :
    fieldNormalizer hJ η β i a X = (potentialCellNormalizer hJ η β a)⁻¹ *
      ∫ z, rawSourceWeight β (removeSite i X) z ∂meshCellMeasure J hJ a := by
  unfold fieldNormalizer
  simp_rw [weighted_field_exponential_eq_raw]
  rw [integral_const_mul]

theorem potentialCellNormalizer_eq_haar {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (a : MeshIndex J) :
    potentialCellNormalizer hJ η β a = (J : ℝ) ^ 2 *
      ∫ z in meshCell J hJ a, Real.exp (β * meanPotential hJ η β z) ∂torusMeasure := by
  simp only [potentialCellNormalizer, meshCellMeasure, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]

/-- Exact algebra with the original particle count. The normalizer on the
right is a random function of the same outside coordinates as the numerator. -/
theorem rawDensity_eq_field_ratio_of_normalizer_ne_zero {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J)
    (hZ : potentialCellNormalizer hJ η β a ≠ 0) (z : Torus) (X : Configuration (n + 1)) :
    rawDensity (meshCellMeasure J hJ a) β (removeSite i X) z =
      potentialCellDensity hJ η β a z *
        (Real.exp (β * fieldError hJ η β i z X) / fieldNormalizer hJ η β i a X) := by
  rw [fieldNormalizer_eq_raw_integral, potentialCellDensity, rawDensity,
    ← potential_mul_field_exponential hJ η β i z X]
  by_cases hB : (∫ y, rawSourceWeight β (removeSite i X) y ∂meshCellMeasure J hJ a) = 0
  · simp only [hB, mul_zero, div_zero]
  · field_simp

/-- Transport to the actual omitted-coordinate marginal. The insertion is
only a way to evaluate a function independent of the removed coordinate. -/
theorem integral_removeSite_insertSite {n : ℕ} (μ : Measure (Configuration (n + 1)))
    (i : Fin (n + 1)) (F : Configuration (n + 1) → ℝ) (hF : Measurable F)
    (hinv : ∀ X, F (insertSite i 0 (removeSite i X)) = F X) :
    (∫ Y, F (insertSite i 0 Y) ∂Measure.map (removeSite i) μ) = ∫ X, F X ∂μ := by
  have hm : Measurable (fun Y ↦ F (insertSite i 0 Y)) :=
    hF.comp ((measurable_insertSite i).comp (measurable_const.prodMk measurable_id))
  rw [integral_map_of_stronglyMeasurable (μ := μ) (measurable_removeSite i) hm.stronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall hinv)

theorem integrable_removeSite_insertSite {n : ℕ} (μ : Measure (Configuration (n + 1)))
    (i : Fin (n + 1)) (F : Configuration (n + 1) → ℝ) (hF : Measurable F)
    (hinv : ∀ X, F (insertSite i 0 (removeSite i X)) = F X) (hi : Integrable F μ) :
    Integrable (fun Y ↦ F (insertSite i 0 Y)) (Measure.map (removeSite i) μ) := by
  have hm : Measurable (fun Y ↦ F (insertSite i 0 Y)) :=
    hF.comp ((measurable_insertSite i).comp (measurable_const.prodMk measurable_id))
  have hmp : MeasurePreserving (removeSite i) μ (Measure.map (removeSite i) μ) :=
    ⟨measurable_removeSite i, rfl⟩
  apply (hmp.integrable_comp hm.aestronglyMeasurable).mp
  simpa only [Function.comp_def, hinv] using! hi

/-- Finite grouping by the literal prescribed labels. No same-label
exchangeability assertion is needed for the subsequent error estimate. -/
theorem sum_label_values {N J : ℕ} (η : LabelVector J N) (f : MeshIndex J → ℝ) :
    (∑ i, f (η i)) = ∑ a, (occupation η a : ℝ) * f a := by
  classical
  calc
    _ = ∑ i, ∑ a, if η i = a then f a else 0 := by simp
    _ = ∑ a, ∑ i, if η i = a then f a else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, occupation]

theorem averageDensity_zero_on_empty_cell {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (a : MeshIndex J) (ha : occupation η a = 0)
    (z : Torus) (hz : z ∈ meshCell J hJ a) : averageDensity hJ η β z = 0 := by
  classical
  have he : Finset.univ.filter (fun i ↦ η i = a) = ∅ := Finset.card_eq_zero.mp ha
  have hh := congrFun (cellAverageDensity_eq_sum hJ η β a) z
  rw [cellAverageDensity, indicator_of_mem hz, he, Finset.sum_empty, mul_zero] at hh
  exact hh

theorem cell_sum_zero_on_empty_cell {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (a : MeshIndex J) (ha : occupation η a = 0)
    (f : MeshIndex J → Torus → ℝ) (z : Torus) (hz : z ∈ meshCell J hJ a) :
    (∑ b, ((occupation η b : ℝ) / (n + 1 : ℝ)) * (meshCell J hJ b).indicator (f b) z) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : b = a
  · subst b
    simp only [ha, Nat.cast_zero, zero_div, zero_mul]
  · have hzb : z ∉ meshCell J hJ b := fun h ↦ hb (h.symm.trans hz)
    rw [indicator_of_notMem hzb, mul_zero]

end ExactConditionalAlgebra

section ActualParameters

variable {n J : ℕ} (hN : 2 ≤ n + 1) {β₀ β δ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)

include hN hβ hβ₀ hsub hδ hη

theorem potential_exponential_bounds (z : Torus) :
    Real.exp (-β₀ * potentialBound J β₀) ≤
      Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∧
      Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ≤
        Real.exp (β₀ * potentialBound J β₀) := by
  have hu := meanPotential_abs_le hN hβ hβ₀ hsub hδ hmesh η hη z
  have hab : |β * meanPotential (mesh_pos hmesh) η β z| ≤ β₀ * potentialBound J β₀ := by
    rw [abs_mul, abs_of_nonneg hβ]
    exact (mul_le_mul_of_nonneg_left hu hβ).trans
      (mul_le_mul_of_nonneg_right hβ₀ (potentialBound_pos J β₀).le)
  exact ⟨Real.exp_le_exp.mpr (by simpa only [neg_mul] using (abs_le.mp hab).1),
    Real.exp_le_exp.mpr (abs_le.mp hab).2⟩

theorem potential_exponential_integrable (a : MeshIndex J) :
    Integrable (fun z ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β z))
      (meshCellMeasure J (mesh_pos hmesh) a) := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  apply Integrable.of_bound (((measurable_meanPotential (mesh_pos hmesh) η β).const_mul β).exp).aestronglyMeasurable
    (Real.exp (β₀ * potentialBound J β₀))
  exact Eventually.of_forall fun z ↦ by
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using
      (potential_exponential_bounds hN hβ hβ₀ hsub hδ hmesh η hη z).2

/-- Normalization bounds hold on every cell, whether or not it is occupied. -/
theorem potentialCellNormalizer_bounds (a : MeshIndex J) :
    Real.exp (-β₀ * potentialBound J β₀) ≤ potentialCellNormalizer (mesh_pos hmesh) η β a ∧
      potentialCellNormalizer (mesh_pos hmesh) η β a ≤ Real.exp (β₀ * potentialBound J β₀) := by
  have hi := potential_exponential_integrable hN hβ hβ₀ hsub hδ hmesh η hη a
  constructor
  · have hh := integral_mono_ae (integrable_const (Real.exp (-β₀ * potentialBound J β₀))) hi
      (Eventually.of_forall fun z ↦ (potential_exponential_bounds hN hβ hβ₀ hsub hδ hmesh η hη z).1)
    simpa only [potentialCellNormalizer, integral_const, probReal_univ, one_smul] using! hh
  · have hh := integral_mono_ae hi (integrable_const (Real.exp (β₀ * potentialBound J β₀)))
      (Eventually.of_forall fun z ↦ (potential_exponential_bounds hN hβ hβ₀ hsub hδ hmesh η hη z).2)
    simpa only [potentialCellNormalizer, integral_const, probReal_univ, one_smul] using! hh

theorem potentialCellNormalizer_pos (a : MeshIndex J) :
    0 < potentialCellNormalizer (mesh_pos hmesh) η β a :=
  (Real.exp_pos _).trans_le (potentialCellNormalizer_bounds hN hβ hβ₀ hsub hδ hmesh η hη a).1

theorem potentialCellDensity_pos (a : MeshIndex J) (z : Torus) :
    0 < potentialCellDensity (mesh_pos hmesh) η β a z :=
  div_pos (Real.exp_pos _) (potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη a)

theorem potentialCellDensity_integrable (a : MeshIndex J) :
    Integrable (potentialCellDensity (mesh_pos hmesh) η β a)
      (meshCellMeasure J (mesh_pos hmesh) a) :=
  (potential_exponential_integrable hN hβ hβ₀ hsub hδ hmesh η hη a).div_const _

theorem potentialCellDensity_integral_one (a : MeshIndex J) :
    (∫ z, potentialCellDensity (mesh_pos hmesh) η β a z
      ∂meshCellMeasure J (mesh_pos hmesh) a) = 1 := by
  change (∫ z, Real.exp (β * meanPotential (mesh_pos hmesh) η β z) /
    potentialCellNormalizer (mesh_pos hmesh) η β a ∂meshCellMeasure J (mesh_pos hmesh) a) = 1
  rw [integral_div]
  exact div_self (potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη a).ne'

theorem potentialCellDensity_bounds (a : MeshIndex J) (z : Torus) :
    potentialDensityLower J β₀ ≤ potentialCellDensity (mesh_pos hmesh) η β a z ∧
      potentialCellDensity (mesh_pos hmesh) η β a z ≤ potentialDensityUpper J β₀ := by
  have hZ := potentialCellNormalizer_bounds hN hβ hβ₀ hsub hδ hmesh η hη a
  have hZ0 := potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη a
  have he := potential_exponential_bounds hN hβ hβ₀ hsub hδ hmesh η hη z
  have hl : potentialDensityLower J β₀ =
      Real.exp (-β₀ * potentialBound J β₀) / Real.exp (β₀ * potentialBound J β₀) := by
    rw [potentialDensityLower, ← Real.exp_sub]
    congr 1
    ring
  have hu : potentialDensityUpper J β₀ =
      Real.exp (β₀ * potentialBound J β₀) / Real.exp (-β₀ * potentialBound J β₀) := by
    rw [potentialDensityUpper, ← Real.exp_sub]
    congr 1
    ring
  rw [hl, hu]
  constructor
  · apply (div_le_div_iff₀ (Real.exp_pos _) hZ0).mpr
    exact (mul_le_mul_of_nonneg_left hZ.2 (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right he.1 (Real.exp_pos _).le)
  · apply (div_le_div_iff₀ hZ0 (Real.exp_pos _)).mpr
    exact (mul_le_mul_of_nonneg_right he.2 (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left hZ.1 (Real.exp_pos _).le)

/-- For a fixed pole, the lower bound is transported through the true
Haar marginal of each particle and then the original joint law. -/
theorem psi_lower_ae (i : Fin (n + 1)) (z : Torus) :
    ∀ᵐ X ∂labelGibbsMeasure (mesh_pos hmesh) η β,
      -MovingPoleCalculus.greenLowerConstant ≤ psi i z X := by
  have hg (j : Fin (n + 1)) : ∀ᵐ X ∂labelGibbsMeasure (mesh_pos hmesh) η β,
      -MovingPoleCalculus.greenLowerConstant ≤ greenRealRepresentative (z - X j) := by
    have he := (torusMeasure.measurePreserving_sub_left z).quasiMeasurePreserving.ae_eq_comp
      regularGreenRepresentative_ae
    have hh : ∀ᵐ y ∂torusMeasure,
        -MovingPoleCalculus.greenLowerConstant ≤ greenRealRepresentative (z - y) := by
      filter_upwards [he] with y hy
      simp only [Function.comp_apply] at hy
      rw [← hy]
      exact MovingPoleCalculus.green_lower_bound _
    have hac : marginalLaw (mesh_pos hmesh) η β j ≪ torusMeasure := by
      rw [(marginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη j).1]
      exact withDensity_absolutelyContinuous _ _
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable (hac.ae_le hh)
  filter_upwards [ae_all_iff.mpr hg] with X hX
  exact psi_lower_of_summands i z X hX

theorem fieldError_lower_ae (i : Fin (n + 1)) (z : Torus) :
    ∀ᵐ X ∂labelGibbsMeasure (mesh_pos hmesh) η β,
      -fieldLowerConstant J β₀ ≤ fieldError (mesh_pos hmesh) η β i z X := by
  have hu := (abs_le.mp (meanPotential_abs_le hN hβ hβ₀ hsub hδ hmesh η hη z)).2
  filter_upwards [psi_lower_ae hN hβ hβ₀ hsub hδ hmesh η hη i z] with X hX
  dsimp only [fieldLowerConstant, fieldError, potentialBound]
  linarith

theorem fieldError_lower_ae_torus (i : Fin (n + 1)) (X : Configuration (n + 1)) :
    ∀ᵐ z ∂torusMeasure,
      -fieldLowerConstant J β₀ ≤ fieldError (mesh_pos hmesh) η β i z X := by
  filter_upwards [psi_lower_ae_torus i X] with z hz
  have hu := (abs_le.mp (meanPotential_abs_le hN hβ hβ₀ hsub hδ hmesh η hη z)).2
  dsimp only [fieldLowerConstant, fieldError, potentialBound]
  linarith

theorem fieldError_exponential_lower_ae_cell (i : Fin (n + 1)) (a : MeshIndex J)
    (X : Configuration (n + 1)) :
    ∀ᵐ z ∂meshCellMeasure J (mesh_pos hmesh) a,
      fieldNormalizerLower J β₀ ≤ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) := by
  have hh := (meshCellMeasure_absolutelyContinuous J (mesh_pos hmesh) a).ae_le
    (fieldError_lower_ae_torus hN hβ hβ₀ hsub hδ hmesh η hη i X)
  filter_upwards [hh] with z hz
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hz hβ
  have hb := mul_le_mul_of_nonneg_right hβ₀ (fieldLowerConstant_pos J β₀).le
  change -β₀ * fieldLowerConstant J β₀ ≤ _
  nlinarith

theorem fieldNormalizer_lower_of_integrable (i : Fin (n + 1)) (a : MeshIndex J)
    (X : Configuration (n + 1))
    (hi : Integrable (fun z ↦ potentialCellDensity (mesh_pos hmesh) η β a z *
      Real.exp (β * fieldError (mesh_pos hmesh) η β i z X))
        (meshCellMeasure J (mesh_pos hmesh) a)) :
    fieldNormalizerLower J β₀ ≤ fieldNormalizer (mesh_pos hmesh) η β i a X := by
  have hp := potentialCellDensity_integrable hN hβ hβ₀ hsub hδ hmesh η hη a
  have hl : ∀ᵐ z ∂meshCellMeasure J (mesh_pos hmesh) a,
      potentialCellDensity (mesh_pos hmesh) η β a z * fieldNormalizerLower J β₀ ≤
        potentialCellDensity (mesh_pos hmesh) η β a z *
          Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) := by
    filter_upwards [fieldError_exponential_lower_ae_cell hN hβ hβ₀ hsub hδ hmesh η hη i a X]
      with z hz
    exact mul_le_mul_of_nonneg_left hz (potentialCellDensity_pos hN hβ hβ₀ hsub hδ hmesh η hη a z).le
  have hh := integral_mono_ae (hp.mul_const (fieldNormalizerLower J β₀)) hi hl
  rw [integral_mul_const, potentialCellDensity_integral_one hN hβ hβ₀ hsub hδ hmesh η hη a, one_mul] at hh
  exact hh

/-- Every prescribed closed-cell outside placement has a genuine integrable
cell normalizer and the same positive lower bound, even with collisions. -/
theorem fieldNormalizer_prescribed_lower (i : Fin (n + 1)) (a : MeshIndex J)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    Integrable (fun z ↦ potentialCellDensity (mesh_pos hmesh) η β a z *
      Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y)))
        (meshCellMeasure J (mesh_pos hmesh) a) ∧
      fieldNormalizerLower J β₀ ≤ fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y) := by
  have hb := capped_patch_law (mesh_pos hmesh) hβ hβ₀ hδ hmesh η hη i Y hY a .cell
  have hr : Integrable (rawSourceWeight β Y) (meshCellMeasure J (mesh_pos hmesh) a) :=
    hb.raw_integrable
  have hi : Integrable (fun z ↦ potentialCellDensity (mesh_pos hmesh) η β a z *
      Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y)))
        (meshCellMeasure J (mesh_pos hmesh) a) := by
    have he : (fun z ↦ potentialCellDensity (mesh_pos hmesh) η β a z *
        Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y))) =
        fun z ↦ (potentialCellNormalizer (mesh_pos hmesh) η β a)⁻¹ * rawSourceWeight β Y z := by
      funext z
      simpa only [removeSite_insertSite] using
        weighted_field_exponential_eq_raw (mesh_pos hmesh) η β i a z (insertSite i 0 Y)
    rw [he]
    exact hr.const_mul _
  exact ⟨hi, fieldNormalizer_lower_of_integrable hN hβ hβ₀ hsub hδ hmesh η hη i a _ hi⟩

/-- The exact exponential shift of the already proved original-law moment. -/
theorem fieldError_exponential_moment {s : ℝ} (hs : 0 ≤ s) (hNs : 4 * s ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (z : Torus) :
    Integrable (fun X ↦ Real.exp (s * fieldError (mesh_pos hmesh) η β i z X))
      (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, Real.exp (s * fieldError (mesh_pos hmesh) η β i z X)
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
          Real.exp (s * (potentialBound J β₀ + densityNormBound β₀ * envelopeBound J)) := by
  obtain ⟨hi, hb⟩ := label_field_exponential_bound hN hβ hβ₀ hsub hδ hmesh η hη hs hNs i z
  have he : (fun X ↦ Real.exp (s * fieldError (mesh_pos hmesh) η β i z X)) =
      fun X ↦ Real.exp (-s * meanPotential (mesh_pos hmesh) η β z) * Real.exp (s * psi i z X) := by
    funext X
    rw [← Real.exp_add]
    congr 1
    dsimp only [fieldError]
    ring
  rw [he]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hu : Real.exp (-s * meanPotential (mesh_pos hmesh) η β z) ≤
      Real.exp (s * potentialBound J β₀) := by
    apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp (meanPotential_abs_le hN hβ hβ₀ hsub hδ hmesh η hη z)).1
    unfold potentialBound
    nlinarith
  calc
    _ ≤ Real.exp (s * potentialBound J β₀) * Real.exp (s * densityNormBound β₀ * envelopeBound J) :=
      mul_le_mul hu hb (integral_nonneg fun _ ↦ (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem fieldError_exponential_L2 (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (z : Torus) :
    MemLp (fun X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X)) 2
      (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, Real.exp (2 * (β * fieldError (mesh_pos hmesh) η β i z X))
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤ exponentialMomentBound J β₀ := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hs : 0 ≤ 2 * β := by positivity
  obtain ⟨hi, hb⟩ := fieldError_exponential_moment hN hβ hβ₀ hsub hδ hmesh η hη hs
    (by linarith : 4 * (2 * β) ≤ (n + 1 : ℕ)) i z
  have hm : AEStronglyMeasurable
      (fun X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X))
      (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    (((measurable_fieldError (mesh_pos hmesh) η β i z).const_mul β).exp).aestronglyMeasurable
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr ?_, ?_⟩
  · simpa only [mul_assoc, OccupationFieldEstimates.exp_twice] using! hi
  · have hsum : 0 ≤ potentialBound J β₀ + densityNormBound β₀ * envelopeBound J :=
      add_nonneg (potentialBound_pos J β₀).le
        (mul_nonneg (densityNormBound_pos β₀).le (envelopeBound_nonneg J))
    have hh := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ₀ (by norm_num : (0 : ℝ) ≤ 2)) hsum)
    have hb' : (∫ X, Real.exp (2 * (β * fieldError (mesh_pos hmesh) η β i z X))
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
        Real.exp (2 * β * (potentialBound J β₀ + densityNormBound β₀ * envelopeBound J)) := by
      simpa only [mul_assoc] using hb
    exact hb'.trans hh

/-- Source exponential-error estimate, including beta zero and every pole. -/
theorem field_exponential_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (z : Torus) :
    Integrable (fun X ↦ |Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) - 1|)
      (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, |Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) - 1|
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
          exponentialErrorConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  obtain ⟨hD, hD2⟩ := field_L2_bound hN hβ hβ₀ hsub hδ hmesh η hη i z
  obtain ⟨hE, hE2⟩ := fieldError_exponential_L2 hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z
  have hD2' : (∫ X, fieldError (mesh_pos hmesh) η β i z X ^ 2
      ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤ fieldL2Constant J β₀ / (n + 1 : ℝ) := by
    simpa only [fieldError, sq_abs] using! hD2
  refine ⟨OccupationFieldEstimates.integrable_exponential_error hE, ?_⟩
  have hh := OccupationFieldEstimates.exponential_error_le_of_moments hβ
    (fieldL2Constant_nonneg J β₀) (Real.exp_pos _).le (by positivity : (0 : ℝ) < n + 1)
    hD hE hD2' hE2
  refine hh.trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hβ₀ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem fieldError_exponential_L1 (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (z : Torus) :
    Integrable (fun X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X))
      (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, Real.exp (β * fieldError (mesh_pos hmesh) η β i z X)
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤ exponentialMomentBound J β₀ := by
  obtain ⟨hi, hb⟩ := fieldError_exponential_moment hN hβ hβ₀ hsub hδ hmesh η hη hβ
    (by linarith : 4 * β ≤ (n + 1 : ℕ)) i z
  refine ⟨hi, hb.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ potentialBound J β₀ + densityNormBound β₀ * envelopeBound J :=
    add_nonneg (potentialBound_pos J β₀).le
      (mul_nonneg (densityNormBound_pos β₀).le (envelopeBound_nonneg J))
  exact mul_le_mul_of_nonneg_right (by linarith : β ≤ 2 * β₀) hs

/-- Joint integrability is obtained from the actual original-law moments,
before integrating in the spatial variable to define the random denominator. -/
theorem fieldNormalizer_integrand_integrable (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a : MeshIndex J) :
    Integrable (fun P : Torus × Configuration (n + 1) ↦
      potentialCellDensity (mesh_pos hmesh) η β a P.1 *
        Real.exp (β * fieldError (mesh_pos hmesh) η β i P.1 P.2))
      ((meshCellMeasure J (mesh_pos hmesh) a).prod (labelGibbsMeasure (mesh_pos hmesh) η β)) := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let τ := meshCellMeasure J (mesh_pos hmesh) a
  let p := potentialCellDensity (mesh_pos hmesh) η β a
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hm : Measurable (fun P : Torus × Configuration (n + 1) ↦
      p P.1 * Real.exp (β * fieldError (mesh_pos hmesh) η β i P.1 P.2)) :=
    ((measurable_potentialCellDensity (mesh_pos hmesh) η β a).comp measurable_fst).mul
      (((measurable_fieldError_joint (mesh_pos hmesh) η β i).const_mul β).exp)
  apply integrable_pair_of_nonneg_bound τ μ _ hm
    (fun P ↦ mul_nonneg (potentialCellDensity_pos hN hβ hβ₀ hsub hδ hmesh η hη a P.1).le
      (Real.exp_pos _).le)
    (fun z ↦ (fieldError_exponential_L1 hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z).1.const_mul (p z))
    ((potentialCellDensity_integrable hN hβ hβ₀ hsub hδ hmesh η hη a).mul_const
      (exponentialMomentBound J β₀))
  intro z
  change (∫ X, p z * Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) ∂μ) ≤
    p z * exponentialMomentBound J β₀
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (fieldError_exponential_L1 hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z).2
    (potentialCellDensity_pos hN hβ hβ₀ hsub hδ hmesh η hη a z).le

theorem fieldNormalizer_integrable_and_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a : MeshIndex J) :
    Integrable (fieldNormalizer (mesh_pos hmesh) η β i a) (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∀ᵐ X ∂labelGibbsMeasure (mesh_pos hmesh) η β,
        fieldNormalizerLower J β₀ ≤ fieldNormalizer (mesh_pos hmesh) η β i a X) ∧
      Integrable (fun X ↦ |fieldNormalizer (mesh_pos hmesh) η β i a X - 1|)
        (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, |fieldNormalizer (mesh_pos hmesh) η β i a X - 1|
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
          exponentialErrorConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hI := fieldNormalizer_integrand_integrable hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a
  have hh := weighted_normalizer_error (meshCellMeasure J (mesh_pos hmesh) a)
    (labelGibbsMeasure (mesh_pos hmesh) η β)
    (potentialCellDensity (mesh_pos hmesh) η β a)
    (fun z X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X))
    (fun z ↦ (potentialCellDensity_pos hN hβ hβ₀ hsub hδ hmesh η hη a z).le)
    (potentialCellDensity_integrable hN hβ hβ₀ hsub hδ hmesh η hη a)
    (potentialCellDensity_integral_one hN hβ hβ₀ hsub hδ hmesh η hη a) hI
    (fun z ↦ (field_exponential_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z).2)
  refine ⟨hh.1, ?_, hh.2.1, hh.2.2⟩
  filter_upwards [hI.prod_left_ae] with X hX
  exact fieldNormalizer_lower_of_integrable hN hβ hβ₀ hsub hδ hmesh η hη i a X hX

/-- The actual denominator remains inside the original-law expectation. -/
theorem field_ratio_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a : MeshIndex J) (z : Torus) :
    Integrable (fun X ↦ |Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
      fieldNormalizer (mesh_pos hmesh) η β i a X - 1|)
        (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, |Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
        fieldNormalizer (mesh_pos hmesh) η β i a X - 1|
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
          (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) /
            Real.sqrt (n + 1 : ℝ) := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hA := (fieldError_exponential_L1 hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z).1
  have hW := fieldNormalizer_integrable_and_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a
  refine ⟨(OccupationFieldEstimates.integral_ratio_sub_one_le (fieldNormalizerLower_pos J β₀)
    hA hW.1 hW.2.1).1, ?_⟩
  have hh := OccupationFieldEstimates.integral_ratio_sub_one_le_of_errors
    (fieldNormalizerLower_pos J β₀) hA hW.1 hW.2.1
    (field_exponential_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z).2 hW.2.2.2
  convert hh using 1
  ring

/-- Integrability of the actual normalized conditional factor follows from
the already established integrable error; no totalized integral is substituted. -/
theorem field_ratio_integrable (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a : MeshIndex J) (z : Torus) :
    Integrable (fun X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
      fieldNormalizer (mesh_pos hmesh) η β i a X) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let q := fun X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
    fieldNormalizer (mesh_pos hmesh) η β i a X
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hm : Measurable q := measurable_field_ratio (mesh_pos hmesh) η β i a z
  have he : Integrable (fun X ↦ ‖q X - 1‖) μ := by
    simpa only [Real.norm_eq_abs] using!
      (field_ratio_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a z).1
  have hs : Integrable (fun X ↦ q X - 1) μ :=
    (integrable_norm_iff (hm.sub measurable_const).aestronglyMeasurable).mp he
  have hh : Integrable (fun X ↦ (q X - 1) + 1) μ := hs.add (integrable_const (1 : ℝ))
  simpa only [sub_add_cancel, q, μ] using! hh

theorem field_ratio_mean_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a : MeshIndex J) (z : Torus) :
    |(∫ X, Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
      fieldNormalizer (mesh_pos hmesh) η β i a X ∂labelGibbsMeasure (mesh_pos hmesh) η β) - 1| ≤
        (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) /
          Real.sqrt (n + 1 : ℝ) := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let q := fun X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
    fieldNormalizer (mesh_pos hmesh) η β i a X
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hi : Integrable q μ := field_ratio_integrable hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a z
  have hh := norm_integral_le_integral_norm (μ := μ) (fun X ↦ q X - 1)
  rw [integral_sub hi (integrable_const 1), integral_const, probReal_univ, one_smul] at hh
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans (field_ratio_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a z).2

/-- The same quantitative quotient is integrated under the genuine image
of the original joint law, not a Gibbs measure with fewer particles. -/
theorem field_ratio_outside_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a : MeshIndex J) (z : Torus) :
    Integrable (fun Y ↦ |Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y)) /
      fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y) - 1|)
        (Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) ∧
      (∫ Y, |Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y)) /
        fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y) - 1|
        ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) ≤
          (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) /
            Real.sqrt (n + 1 : ℝ) := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let F := fun X ↦ |Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
    fieldNormalizer (mesh_pos hmesh) η β i a X - 1|
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hsubm : Measurable (fun X ↦ Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
      fieldNormalizer (mesh_pos hmesh) η β i a X - 1) :=
    (measurable_field_ratio (mesh_pos hmesh) η β i a z).sub measurable_const
  have hm : Measurable F := continuous_abs.measurable.comp hsubm
  have hinv : ∀ X, F (insertSite i 0 (removeSite i X)) = F X := by
    intro X
    simp only [F, fieldError_insertSite_removeSite, fieldNormalizer_insertSite_removeSite]
  have hh := field_ratio_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a z
  refine ⟨integrable_removeSite_insertSite μ i F hm hinv hh.1, ?_⟩
  change (∫ Y, F (insertSite i 0 Y) ∂Measure.map (removeSite i) μ) ≤ _
  rw [integral_removeSite_insertSite μ i F hm hinv]
  exact hh.2

theorem conditionalKernel_eq_field_ratio (i : Fin (n + 1)) (a : MeshIndex J)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    conditionalKernel (meshCellMeasure J (mesh_pos hmesh) a) i β Y =
      (meshCellMeasure J (mesh_pos hmesh) a).withDensity (fun z ↦ ENNReal.ofReal
        (potentialCellDensity (mesh_pos hmesh) η β a z *
          (Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y)) /
            fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y)))) := by
  have hk := (capped_patch_law (mesh_pos hmesh) hβ hβ₀ hδ hmesh η hη i Y hY a .cell).kernel_eq_raw
  change conditionalKernel (meshCellMeasure J (mesh_pos hmesh) a) i β Y =
    (meshCellMeasure J (mesh_pos hmesh) a).withDensity
      (fun z ↦ ENNReal.ofReal (rawDensity (meshCellMeasure J (mesh_pos hmesh) a) β Y z)) at hk
  rw [hk]
  congr 1
  funext z
  congr 1
  simpa only [removeSite_insertSite] using
    rawDensity_eq_field_ratio_of_normalizer_ne_zero (mesh_pos hmesh) η β i a
      (potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη a).ne' z (insertSite i 0 Y)

/-- Literal source marginal identity under the actual outside law. This
version is pointwise for the already chosen density representative. -/
theorem cellMarginalDensity_eq_outside_ratio (i : Fin (n + 1)) (z : Torus) :
    cellMarginalDensity (mesh_pos hmesh) η β i z =
      potentialCellDensity (mesh_pos hmesh) η β (η i) z *
        ∫ Y, Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y)) /
          fieldNormalizer (mesh_pos hmesh) η β i (η i) (insertSite i 0 Y)
          ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  change (∫ Y, rawDensity (meshCellMeasure J (mesh_pos hmesh) (η i)) β Y z
    ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) = _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun Y ↦ by
    simpa only [removeSite_insertSite] using
      rawDensity_eq_field_ratio_of_normalizer_ne_zero (mesh_pos hmesh) η β i (η i)
        (potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη (η i)).ne' z (insertSite i 0 Y)

theorem cellMarginalDensity_eq_joint_ratio (i : Fin (n + 1)) (z : Torus) :
    cellMarginalDensity (mesh_pos hmesh) η β i z =
      potentialCellDensity (mesh_pos hmesh) η β (η i) z *
        ∫ X, Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
          fieldNormalizer (mesh_pos hmesh) η β i (η i) X
          ∂labelGibbsMeasure (mesh_pos hmesh) η β := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  rw [cellMarginalDensity_eq_outside_ratio hN hβ hβ₀ hsub hδ hmesh η hη i z]
  congr 1
  apply integral_removeSite_insertSite _ i _ (measurable_field_ratio (mesh_pos hmesh) η β i (η i) z)
  intro X
  simp only [fieldError_insertSite_removeSite, fieldNormalizer_insertSite_removeSite]

/-- The source normalization by J squared, with the true random denominator
still inside the outside expectation. -/
theorem marginalDensity_div_mesh_sq (i : Fin (n + 1)) (z : Torus)
    (hz : z ∈ meshCell J (mesh_pos hmesh) (η i)) :
    marginalDensity (mesh_pos hmesh) η β i z / (J : ℝ) ^ 2 =
      potentialCellDensity (mesh_pos hmesh) η β (η i) z *
        ∫ Y, Real.exp (β * fieldError (mesh_pos hmesh) η β i z (insertSite i 0 Y)) /
          fieldNormalizer (mesh_pos hmesh) η β i (η i) (insertSite i 0 Y)
          ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  rw [marginalDensity, haarCellDensity, indicator_of_mem hz]
  have hJ0 : (J : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (mesh_pos hmesh).ne')
  rw [mul_div_cancel_left₀ _ hJ0]
  exact cellMarginalDensity_eq_outside_ratio hN hβ hβ₀ hsub hδ hmesh η hη i z

/-- Genuine Haar-cell normalizers: every cell is included, independently
of its occupation. The upper and lower bounds keep the exact J squared factor. -/
theorem potential_haar_cell_normalizer (a : MeshIndex J) :
    Integrable (fun z ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β z))
      (torusMeasure.restrict (meshCell J (mesh_pos hmesh) a)) ∧
      0 < (∫ z in meshCell J (mesh_pos hmesh) a,
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure) ∧
      Real.exp (-β₀ * potentialBound J β₀) / (J : ℝ) ^ 2 ≤
        (∫ z in meshCell J (mesh_pos hmesh) a,
          Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure) ∧
      (∫ z in meshCell J (mesh_pos hmesh) a,
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure) ≤
          Real.exp (β₀ * potentialBound J β₀) / (J : ℝ) ^ 2 := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hi : Integrable (fun z ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β z)) torusMeasure := by
    apply Integrable.of_bound (((measurable_meanPotential (mesh_pos hmesh) η β).const_mul β).exp).aestronglyMeasurable
      (Real.exp (β₀ * potentialBound J β₀))
    exact Eventually.of_forall fun z ↦ by
      simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using
        (potential_exponential_bounds hN hβ hβ₀ hsub hδ hmesh η hη z).2
  have hZ := potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη a
  have hb := potentialCellNormalizer_bounds hN hβ hβ₀ hsub hδ hmesh η hη a
  rw [potentialCellNormalizer_eq_haar] at hZ hb
  have hJ2 : (0 : ℝ) < (J : ℝ) ^ 2 := pow_pos (by exact_mod_cast mesh_pos hmesh) _
  refine ⟨hi.restrict, ?_, ?_, ?_⟩
  · nlinarith
  · apply (div_le_iff₀ hJ2).mpr
    simpa only [mul_comm] using hb.1
  · apply (le_div_iff₀ hJ2).mpr
    simpa only [mul_comm] using hb.2

theorem haar_cell_density_identity (a : MeshIndex J) (z : Torus) :
    (J : ℝ) ^ 2 * (meshCell J (mesh_pos hmesh) a).indicator
      (potentialCellDensity (mesh_pos hmesh) η β a) z =
      (meshCell J (mesh_pos hmesh) a).indicator
        (fun y ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β y) /
          ∫ w in meshCell J (mesh_pos hmesh) a,
            Real.exp (β * meanPotential (mesh_pos hmesh) η β w) ∂torusMeasure) z := by
  classical
  by_cases hz : z ∈ meshCell J (mesh_pos hmesh) a
  · rw [indicator_of_mem hz, indicator_of_mem hz, potentialCellDensity, potentialCellNormalizer_eq_haar]
    have hJ0 : (J : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (mesh_pos hmesh).ne')
    have hJne : (J : ℝ) ≠ 0 := by exact_mod_cast (mesh_pos hmesh).ne'
    have hI0 := (potential_haar_cell_normalizer hN hβ hβ₀ hsub hδ hmesh η hη a).2.1.ne'
    field_simp [hJne]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]

theorem marginalDensity_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (z : Torus) :
    |marginalDensity (mesh_pos hmesh) η β i z - (J : ℝ) ^ 2 *
      (meshCell J (mesh_pos hmesh) (η i)).indicator
        (potentialCellDensity (mesh_pos hmesh) η β (η i)) z| ≤
          approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  classical
  have hc : 0 ≤ (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) /
      Real.sqrt (n + 1 : ℝ) := by
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num)
      (exponentialErrorConstant_nonneg J (hβ.trans hβ₀))) (fieldNormalizerLower_pos J β₀).le)
      (Real.sqrt_nonneg _)
  by_cases hz : z ∈ meshCell J (mesh_pos hmesh) (η i)
  · rw [marginalDensity, haarCellDensity, indicator_of_mem hz, indicator_of_mem hz,
      cellMarginalDensity_eq_joint_ratio hN hβ hβ₀ hsub hδ hmesh η hη i z]
    have he : (J : ℝ) ^ 2 * (potentialCellDensity (mesh_pos hmesh) η β (η i) z *
          ∫ X, Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
            fieldNormalizer (mesh_pos hmesh) η β i (η i) X
            ∂labelGibbsMeasure (mesh_pos hmesh) η β) -
        (J : ℝ) ^ 2 * potentialCellDensity (mesh_pos hmesh) η β (η i) z =
        ((J : ℝ) ^ 2 * potentialCellDensity (mesh_pos hmesh) η β (η i) z) *
          ((∫ X, Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) /
            fieldNormalizer (mesh_pos hmesh) η β i (η i) X
            ∂labelGibbsMeasure (mesh_pos hmesh) η β) - 1) := by ring
    rw [he, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (potentialCellDensity_pos hN hβ hβ₀ hsub hδ hmesh η hη (η i) z).le)]
    calc
      _ ≤ ((J : ℝ) ^ 2 * potentialCellDensity (mesh_pos hmesh) η β (η i) z) *
          ((2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) / Real.sqrt (n + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (field_ratio_mean_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i (η i) z)
          (mul_nonneg (sq_nonneg _) (potentialCellDensity_pos hN hβ hβ₀ hsub hδ hmesh η hη (η i) z).le)
      _ ≤ ((J : ℝ) ^ 2 * potentialDensityUpper J β₀) *
          ((2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) / Real.sqrt (n + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (potentialCellDensity_bounds hN hβ hβ₀ hsub hδ hmesh η hη (η i) z).2
            (sq_nonneg _)) hc
      _ = _ := by unfold approximationConstant; ring
  · rw [marginalDensity_eq_zero_of_not_mem (mesh_pos hmesh) η β i hz, indicator_of_notMem hz,
      mul_zero, sub_zero, abs_zero]
    calc
      0 ≤ ((J : ℝ) ^ 2 * potentialDensityUpper J β₀) *
          ((2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) / Real.sqrt (n + 1 : ℝ)) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hc
      _ = _ := by unfold approximationConstant; ring

/-- Exact finite averaging gives the source error without using equality
of two marginal densities carrying the same label. -/
theorem approximate_fixed_point_cells (hlarge : 8 * β₀ ≤ (n + 1 : ℕ)) (z : Torus) :
    |averageDensity (mesh_pos hmesh) η β z -
      ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) * (J : ℝ) ^ 2 *
        (meshCell J (mesh_pos hmesh) a).indicator (potentialCellDensity (mesh_pos hmesh) η β a) z| ≤
          approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  let r := fun a : MeshIndex J ↦ (J : ℝ) ^ 2 *
    (meshCell J (mesh_pos hmesh) a).indicator (potentialCellDensity (mesh_pos hmesh) η β a) z
  have hs : (∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) * (J : ℝ) ^ 2 *
      (meshCell J (mesh_pos hmesh) a).indicator (potentialCellDensity (mesh_pos hmesh) η β a) z) =
      (n + 1 : ℝ)⁻¹ * ∑ i, r (η i) := by
    rw [sum_label_values η r, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [r]
    ring
  rw [hs, OccupationFieldL2.averageDensity, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n + 1))]
  calc
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ i, |marginalDensity (mesh_pos hmesh) η β i z - r (η i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ _i : Fin (n + 1),
        approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ marginalDensity_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z)
        (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, ← mul_assoc, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_mul]

/-- The literal Haar-denominator cell map in the manuscript, pointwise for
the selected actual marginal density. Every denominator is finite and positive. -/
theorem approximate_fixed_point (hlarge : 8 * β₀ ≤ (n + 1 : ℕ)) (z : Torus) :
    |averageDensity (mesh_pos hmesh) η β z -
      ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) *
        (meshCell J (mesh_pos hmesh) a).indicator
          (fun y ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β y) /
            ∫ w in meshCell J (mesh_pos hmesh) a,
              Real.exp (β * meanPotential (mesh_pos hmesh) η β w) ∂torusMeasure) z| ≤
          approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  have he : (∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) *
      (meshCell J (mesh_pos hmesh) a).indicator
        (fun y ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β y) /
          ∫ w in meshCell J (mesh_pos hmesh) a,
            Real.exp (β * meanPotential (mesh_pos hmesh) η β w) ∂torusMeasure) z) =
      ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) * (J : ℝ) ^ 2 *
        (meshCell J (mesh_pos hmesh) a).indicator (potentialCellDensity (mesh_pos hmesh) η β a) z := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← haar_cell_density_identity hN hβ hβ₀ hsub hδ hmesh η hη a z]
    ring
  rw [he]
  exact approximate_fixed_point_cells hN hβ hβ₀ hsub hδ hmesh η hη hlarge z

/-- The manuscript's L-infinity estimate, for the exact Haar-denominator
cell sum and actual average marginal density. -/
theorem approximate_fixed_point_Linfty (hlarge : 8 * β₀ ≤ (n + 1 : ℕ)) :
    let T := fun z ↦ ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) *
      (meshCell J (mesh_pos hmesh) a).indicator
        (fun y ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β y) /
          ∫ w in meshCell J (mesh_pos hmesh) a,
            Real.exp (β * meanPotential (mesh_pos hmesh) η β w) ∂torusMeasure) z
    MemLp (fun z ↦ averageDensity (mesh_pos hmesh) η β z - T z) ∞ torusMeasure ∧
      lpNorm (fun z ↦ averageDensity (mesh_pos hmesh) η β z - T z) ∞ torusMeasure ≤
        approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  let T := fun z ↦ ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) *
    (meshCell J (mesh_pos hmesh) a).indicator
      (fun y ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β y) /
        ∫ w in meshCell J (mesh_pos hmesh) a,
          Real.exp (β * meanPotential (mesh_pos hmesh) η β w) ∂torusMeasure) z
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hT : Measurable T := by
    apply Finset.measurable_sum
    intro a _
    exact (((((measurable_meanPotential (mesh_pos hmesh) η β).const_mul β).exp).div_const _).indicator
      (measurableSet_meshCell J (mesh_pos hmesh) a)).const_mul _
  have hm : Measurable (fun z ↦ averageDensity (mesh_pos hmesh) η β z - T z) :=
    (measurable_averageDensity (mesh_pos hmesh) η β).sub hT
  have hc : 0 ≤ approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
    unfold approximationConstant
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (div_nonneg (mul_nonneg (by norm_num) (exponentialErrorConstant_nonneg J (hβ.trans hβ₀)))
        (fieldNormalizerLower_pos J β₀).le)) (Real.sqrt_nonneg _)
  have hp : ∀ z, ‖averageDensity (mesh_pos hmesh) η β z - T z‖ ≤
      approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
    intro z
    simpa only [Real.norm_eq_abs] using
      approximate_fixed_point hN hβ hβ₀ hsub hδ hmesh η hη hlarge z
  refine ⟨MemLp.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall hp), ?_⟩
  have hC : MemLp (fun _ : Torus ↦ approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ))
      ∞ torusMeasure := memLp_const _
  have hh := lpNorm_mono_real hC hp
  have hμ0 : torusMeasure ≠ 0 := by
    intro hzero
    have hprob : torusMeasure univ = 1 := measure_univ
    simp [hzero] at hprob
  rw [lpNorm_const (by simp : (∞ : ℝ≥0∞) ≠ 0) hμ0] at hh
  simpa only [probReal_univ, Real.one_rpow, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hc, T] using hh

omit hN hβ hβ₀ hsub hδ hη in
theorem empty_cell_densities (a : MeshIndex J) (ha : occupation η a = 0)
    (z : Torus) (hz : z ∈ meshCell J (mesh_pos hmesh) a) :
    averageDensity (mesh_pos hmesh) η β z = 0 ∧
      (∑ b, ((occupation η b : ℝ) / (n + 1 : ℝ)) *
        (meshCell J (mesh_pos hmesh) b).indicator
          (fun y ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β y) /
            ∫ w in meshCell J (mesh_pos hmesh) b,
              Real.exp (β * meanPotential (mesh_pos hmesh) η β w) ∂torusMeasure) z) = 0 :=
  ⟨averageDensity_zero_on_empty_cell (mesh_pos hmesh) η β a ha z hz,
    cell_sum_zero_on_empty_cell (mesh_pos hmesh) η a ha _ z hz⟩

/-- The actual normalizer-ratio error needed by the subsequent specified
label partition transport. Both cells are arbitrary and may be unoccupied. -/
theorem fieldNormalizer_ratio_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a b : MeshIndex J) :
    Integrable (fun X ↦ |fieldNormalizer (mesh_pos hmesh) η β i b X /
      fieldNormalizer (mesh_pos hmesh) η β i a X - 1|) (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, |fieldNormalizer (mesh_pos hmesh) η β i b X /
        fieldNormalizer (mesh_pos hmesh) η β i a X - 1|
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
          (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) / Real.sqrt (n + 1 : ℝ) := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have ha := fieldNormalizer_integrable_and_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a
  have hb := fieldNormalizer_integrable_and_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i b
  refine ⟨(OccupationFieldEstimates.integral_ratio_sub_one_le (fieldNormalizerLower_pos J β₀)
    hb.1 ha.1 ha.2.1).1, ?_⟩
  have hh := OccupationFieldEstimates.integral_ratio_sub_one_le_of_errors
    (fieldNormalizerLower_pos J β₀) hb.1 ha.1 ha.2.1 hb.2.2.2 ha.2.2.2
  convert hh using 1
  ring

end ActualParameters

/-- One fixed threshold discharges both the original N at least two gate
and the exponential-moment gate. No strictly positive beta is required. -/
theorem occupation_field_approximation {n J : ℕ} {β₀ β δ : ℝ}
    (hthreshold : fieldThreshold β₀ ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) :
    (∀ (i : Fin (n + 1)) (z : Torus),
      Integrable (fun X ↦ |Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) - 1|)
        (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, |Real.exp (β * fieldError (mesh_pos hmesh) η β i z X) - 1|
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤ exponentialErrorConstant J β₀ / Real.sqrt (n + 1 : ℝ)) ∧
    (let T := fun z ↦ ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) *
      (meshCell J (mesh_pos hmesh) a).indicator
        (fun y ↦ Real.exp (β * meanPotential (mesh_pos hmesh) η β y) /
          ∫ w in meshCell J (mesh_pos hmesh) a,
            Real.exp (β * meanPotential (mesh_pos hmesh) η β w) ∂torusMeasure) z
     MemLp (fun z ↦ averageDensity (mesh_pos hmesh) η β z - T z) ∞ torusMeasure ∧
       lpNorm (fun z ↦ averageDensity (mesh_pos hmesh) η β z - T z) ∞ torusMeasure ≤
         approximationConstant J β₀ / Real.sqrt (n + 1 : ℝ)) := by
  obtain ⟨hN, hlarge⟩ := fieldThreshold_bounds hthreshold
  exact ⟨fun i z ↦ field_exponential_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i z,
    approximate_fixed_point_Linfty hN hβ hβ₀ hsub hδ hmesh η hη hlarge⟩

end PeriodicAttractiveLogGas.OccupationFieldApproximation
