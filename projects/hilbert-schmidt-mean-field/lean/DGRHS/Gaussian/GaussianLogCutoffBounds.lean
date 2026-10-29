import DGRHS.Gaussian.GaussianLogAdaptiveBounds

/-! Supporting development: max-cutoff cap and actual essential norm, including zero-width bands. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma gaussianLog_max_cutoff_log_le (η α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    Real.log (δ/max η α) ≤ Real.log (δ/α) := by
  have hmax : 0 < max η α := hα.trans_le (le_max_right _ _)
  apply Real.log_le_log (div_pos hδ hmax)
  exact div_le_div_of_nonneg_left hδ.le hα (le_max_right _ _)

lemma gaussianLogCutoffAdaptive_cap_essential_bound (η δ A β n u : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : 0 < A) (hβ : 0 ≤ β) (hn : 1 ≤ n) (hu : 0 < u)
    (hd : 0 < (Fintype.card ι : ℝ))
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    let α := gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
    let ℓ := max η α
    (1+4*β*Real.log (δ/ℓ) ≤ 1+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)*(n/u)^(1/2 : ℝ)) ∧
    ((eLpNormEssSup (gaussianLogMasterBand ℓ δ (2*β) μ) (μ.prod μ)).toReal ≤
      1+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)*(n/u)^(1/2 : ℝ)) := by
  let α := gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
  have hp := gaussianLogAdaptiveScale_pos_le δ A β n u (Fintype.card ι : ℝ) hδ hA hβ (by linarith) hu
  have hℓ : 0 < max η α := hη.trans_le (le_max_left _ _)
  have hℓδ : max η α ≤ δ := max_le hηδ hp.2
  have hm : 0 ≤ Real.log (δ/α) := Real.log_nonneg (by rw [le_div_iff₀ hp.1];simpa using hp.2)
  have hl := gaussianLogAdaptiveScale_log_mass_le δ A β n u (Fintype.card ι : ℝ) hδ hδ1 hA hβ hn hu hd
  have hb := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 8*β)
  have he : (8*β)*((2/(Fintype.card ι : ℝ))*(A*(1+β))^(1/2 : ℝ)*(n/u)^(1/2 : ℝ)) =
      gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)*(n/u)^(1/2 : ℝ) := by
    unfold gaussianLogAdaptiveSizeConstant
    ring
  rw [he] at hb
  have hlog := gaussianLog_max_cutoff_log_le η α δ hp.1 hδ
  have hlog4 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4*β)
  have hlog8 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 8*β)
  have hess := essential_gaussianLogMasterBand_le (max η α) δ (2*β) hℓ hℓδ μ
  rw [abs_of_nonneg (by positivity : 0 ≤ 2*β)] at hess
  change (1+4*β*Real.log (δ/max η α) ≤ _) ∧ _
  constructor
  · nlinarith [mul_nonneg hβ hm]
  · nlinarith

lemma gaussianLogCutoffAdaptive_actual_size_bound (η δ A β n u₀ : ℝ)
    (hη : 0 < η) (hηδ : η ≤ δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : 0 < A) (hβ : 0 ≤ β) (hn : 1 ≤ n) (hu₀ : 1 ≤ u₀)
    (hd : 0 < (Fintype.card ι : ℝ))
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    let α := fun u => gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
    let q := fun u => gaussianLogMasterBand (max η (α u)) δ (2*β) μ
    let cap := fun u => 1+4*β*Real.log (δ/max η (α u))
    BddAbove (masterCutoffValues μ q cap u₀) ∧
      masterCutoffSize μ q cap u₀ ≤
        (2+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ))^2*n^(2/3 : ℝ) := by
  let α := fun u => gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
  let q := fun u => gaussianLogMasterBand (max η (α u)) δ (2*β) μ
  let cap := fun u => 1+4*β*Real.log (δ/max η (α u))
  have h := masterCutoffSize_le_adaptive_power μ q cap n u₀ (1/2 : ℝ) 1
    (gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)) hn hu₀
    (by norm_num) (by norm_num) (by norm_num)
    (gaussianLogAdaptiveSizeConstant_nonneg A β (Fintype.card ι : ℝ) hA hβ hd)
    (fun u hu => (gaussianLogCutoffAdaptive_cap_essential_bound η δ A β n u hη hηδ hδ hδ1 hA hβ hn (by linarith) hd μ).1)
    (fun u hu => (gaussianLogCutoffAdaptive_cap_essential_bound η δ A β n u hη hηδ hδ hδ1 hA hβ hn (by linarith) hd μ).2)
  norm_num only at h
  exact h

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLog_max_cutoff_log_le
#print axioms DGRHS.Gaussian.gaussianLog_max_cutoff_log_le
#check @DGRHS.Gaussian.gaussianLogCutoffAdaptive_cap_essential_bound
#print axioms DGRHS.Gaussian.gaussianLogCutoffAdaptive_cap_essential_bound
#check @DGRHS.Gaussian.gaussianLogCutoffAdaptive_actual_size_bound
#print axioms DGRHS.Gaussian.gaussianLogCutoffAdaptive_actual_size_bound
