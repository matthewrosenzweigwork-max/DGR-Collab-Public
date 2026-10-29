import LeanResearch.PeriodicAttractiveLogGas.Ensemble

/-! Measure-theoretic consequences of a finite Gibbs normalizer and a lower
kernel bound. These hypotheses remain explicit until established for the actual
Green kernel. Source: prop:normalization and the closability argument in
prop:ambient. No estimate here is asserted uniform in particle number. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

theorem referenceMeasure_absolutelyContinuous_gibbsMeasure {g : Torus → ℝ}
    (hg : Measurable g) (N : ℕ) (β : ℝ) (hfin : partitionFunction g N β ≠ ⊤) :
    referenceMeasure N ≪ gibbsMeasure g N β := by
  apply Measure.AbsolutelyContinuous.smul_right
    (withDensity_absolutelyContinuous'
      (measurable_gibbsWeight hg N β).ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x ↦
        ne_of_gt (ENNReal.ofReal_pos.mpr (gibbsWeight_pos g N β x))))
  exact ENNReal.inv_ne_zero.mpr hfin

theorem gibbsMeasure_null_iff {g : Torus → ℝ} (hg : Measurable g)
    (N : ℕ) (β : ℝ) (hfin : partitionFunction g N β ≠ ⊤)
    (s : Set (Configuration N)) :
    gibbsMeasure g N β s = 0 ↔ referenceMeasure N s = 0 :=
  ⟨fun hs ↦ referenceMeasure_absolutelyContinuous_gibbsMeasure hg N β hfin hs,
    fun hs ↦ gibbsMeasure_absolutelyContinuous g N β hs⟩

def gibbsDensity (g : Torus → ℝ) (N : ℕ) (β : ℝ) (x : Configuration N) : ℝ≥0∞ :=
  (partitionFunction g N β)⁻¹ * ENNReal.ofReal (gibbsWeight g N β x)

theorem gibbsMeasure_eq_withDensity {g : Torus → ℝ} (hg : Measurable g)
    (N : ℕ) (β : ℝ) :
    gibbsMeasure g N β = (referenceMeasure N).withDensity (gibbsDensity g N β) := by
  exact (withDensity_smul _ (measurable_gibbsWeight hg N β).ennreal_ofReal).symm

def lowerWeight (N : ℕ) (β m : ℝ) : ℝ :=
  Real.exp ((β / (N : ℝ)) * (∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, m))

theorem lowerWeight_pos (N : ℕ) (β m : ℝ) : 0 < lowerWeight N β m := Real.exp_pos _

theorem lowerWeight_le_gibbsWeight {g : Torus → ℝ} {m : ℝ} (hgm : ∀ x, m ≤ g x)
    (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) (x : Configuration N) :
    lowerWeight N β m ≤ gibbsWeight g N β x := by
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hβ (Nat.cast_nonneg N))
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hgm (x i - x j)

theorem gibbsDensity_lower_bound {g : Torus → ℝ} {m : ℝ} (hgm : ∀ x, m ≤ g x)
    (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) (x : Configuration N) :
    (partitionFunction g N β)⁻¹ * ENNReal.ofReal (lowerWeight N β m) ≤
      gibbsDensity g N β x :=
  mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (lowerWeight_le_gibbsWeight hgm N hβ x)) zero_le zero_le

theorem gibbsMeasure_lower_bound {g : Torus → ℝ} (hg : Measurable g)
    {m : ℝ} (hgm : ∀ x, m ≤ g x) (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ((partitionFunction g N β)⁻¹ * ENNReal.ofReal (lowerWeight N β m)) •
      referenceMeasure N ≤ gibbsMeasure g N β := by
  rw [gibbsMeasure_eq_withDensity hg, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall (gibbsDensity_lower_bound hgm N hβ))

theorem gibbsMeasure_lower_coefficient_pos (g : Torus → ℝ)
    (N : ℕ) (β m : ℝ) (hfin : partitionFunction g N β ≠ ⊤) :
    0 < (partitionFunction g N β)⁻¹ * ENNReal.ofReal (lowerWeight N β m) := by
  exact pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.inv_ne_zero.mpr hfin)
    (ne_of_gt (ENNReal.ofReal_pos.mpr (lowerWeight_pos N β m))))

theorem gibbsMeasure_lower_coefficient_ne_top {g : Torus → ℝ} (hg : Measurable g)
    (N : ℕ) (β m : ℝ) :
    (partitionFunction g N β)⁻¹ * ENNReal.ofReal (lowerWeight N β m) ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (partitionFunction_ne_zero hg N β))
    ENNReal.ofReal_ne_top

theorem exists_referenceMeasure_le_finite_smul_gibbsMeasure {g : Torus → ℝ}
    (hg : Measurable g) {m : ℝ} (hgm : ∀ x, m ≤ g x)
    (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hfin : partitionFunction g N β ≠ ⊤) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ referenceMeasure N ≤ c • gibbsMeasure g N β := by
  let a := (partitionFunction g N β)⁻¹ * ENNReal.ofReal (lowerWeight N β m)
  have ha : a ≠ 0 := ne_of_gt (gibbsMeasure_lower_coefficient_pos g N β m hfin)
  have hatop : a ≠ ⊤ := gibbsMeasure_lower_coefficient_ne_top hg N β m
  refine ⟨a⁻¹, ENNReal.inv_ne_top.mpr ha, ?_⟩
  have h : a⁻¹ • (a • referenceMeasure N) ≤ a⁻¹ • gibbsMeasure g N β := by
    gcongr
    exact gibbsMeasure_lower_bound hg hgm N hβ
  simpa only [smul_smul, ENNReal.inv_mul_cancel ha hatop, one_smul] using h

end PeriodicAttractiveLogGas
