import DGRHS.Gaussian.GaussianLogMasterBand
import DGRHS.Gaussian.GaussianLogAdaptiveScale

/-! Actual physical cap and essential norm yield a
common sublinear size envelope; finiteness of the size supremum is derived. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianLogAdaptiveSizeConstant (A β d : ℝ) : ℝ :=
  16*β/d*(A*(1+β))^(1/2 : ℝ)

lemma gaussianLogAdaptiveSizeConstant_nonneg (A β d : ℝ) (hA : 0 < A) (hβ : 0 ≤ β) (hd : 0 < d) :
    0 ≤ gaussianLogAdaptiveSizeConstant A β d := by
  unfold gaussianLogAdaptiveSizeConstant
  positivity

lemma gaussianLogAdaptive_cap_essential_bound (δ A β n u : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 < A) (hβ : 0 ≤ β)
    (hn : 1 ≤ n) (hu : 0 < u) (hd : 0 < (Fintype.card ι : ℝ))
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    let α := gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
    (1+4*β*Real.log (δ/α) ≤ 1+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)*(n/u)^(1/2 : ℝ)) ∧
    ((eLpNormEssSup (gaussianLogMasterBand α δ (2*β) μ) (μ.prod μ)).toReal ≤
      1+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)*(n/u)^(1/2 : ℝ)) := by
  let α := gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
  have hp := gaussianLogAdaptiveScale_pos_le δ A β n u (Fintype.card ι : ℝ) hδ hA hβ (by linarith) hu
  have hl := gaussianLogAdaptiveScale_log_mass_le δ A β n u (Fintype.card ι : ℝ) hδ hδ1 hA hβ hn hu hd
  have hm : 0 ≤ Real.log (δ/α) := Real.log_nonneg (by
    rw [le_div_iff₀ hp.1]
    simpa using hp.2)
  have hb := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 8*β)
  have he : (8*β)*((2/(Fintype.card ι : ℝ))*(A*(1+β))^(1/2 : ℝ)*(n/u)^(1/2 : ℝ)) =
      gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)*(n/u)^(1/2 : ℝ) := by
    unfold gaussianLogAdaptiveSizeConstant
    ring
  rw [he] at hb
  have hess := essential_gaussianLogMasterBand_le α δ (2*β) hp.1 hp.2 μ
  rw [abs_of_nonneg (by positivity : 0 ≤ 2*β)] at hess
  change (1+4*β*Real.log (δ/α) ≤ _) ∧ _
  constructor
  · nlinarith [mul_nonneg hβ hm]
  · nlinarith

lemma gaussianLogAdaptive_actual_size_bound (δ A β n u₀ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 < A) (hβ : 0 ≤ β)
    (hn : 1 ≤ n) (hu₀ : 1 ≤ u₀) (hd : 0 < (Fintype.card ι : ℝ))
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    let α := fun u => gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
    let q := fun u => gaussianLogMasterBand (α u) δ (2*β) μ
    let cap := fun u => 1+4*β*Real.log (δ/α u)
    BddAbove (masterCutoffValues μ q cap u₀) ∧
      masterCutoffSize μ q cap u₀ ≤
        (2+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ))^2*n^(2/3 : ℝ) := by
  let α := fun u => gaussianLogAdaptiveScale δ A β n u (Fintype.card ι : ℝ)
  let q := fun u => gaussianLogMasterBand (α u) δ (2*β) μ
  let cap := fun u => 1+4*β*Real.log (δ/α u)
  have h := masterCutoffSize_le_adaptive_power μ q cap n u₀ (1/2 : ℝ) 1
    (gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ)) hn hu₀
    (by norm_num) (by norm_num) (by norm_num)
    (gaussianLogAdaptiveSizeConstant_nonneg A β (Fintype.card ι : ℝ) hA hβ hd)
    (fun u hu => (gaussianLogAdaptive_cap_essential_bound δ A β n u hδ hδ1 hA hβ hn (by linarith) hd μ).1)
    (fun u hu => (gaussianLogAdaptive_cap_essential_bound δ A β n u hδ hδ1 hA hβ hn (by linarith) hd μ).2)
  norm_num only at h
  exact h

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogAdaptiveSizeConstant
#print axioms DGRHS.Gaussian.gaussianLogAdaptiveSizeConstant
#check DGRHS.Gaussian.gaussianLogAdaptiveSizeConstant_nonneg
#print axioms DGRHS.Gaussian.gaussianLogAdaptiveSizeConstant_nonneg
#check DGRHS.Gaussian.gaussianLogAdaptive_cap_essential_bound
#print axioms DGRHS.Gaussian.gaussianLogAdaptive_cap_essential_bound
#check DGRHS.Gaussian.gaussianLogAdaptive_actual_size_bound
#print axioms DGRHS.Gaussian.gaussianLogAdaptive_actual_size_bound
