import DGRHS.Gaussian.GaussianLogBandScaling
import DGRHS.Gaussian.PhysicalStatisticAlgebra

/-! The same scaled finite Gaussian logarithmic band
supplies actual measurable/canonical/bounded and deterministic-cap fields. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def gaussianLogMasterBand (η δ c : ℝ) (μ : Measure (EuclideanSpace ℝ ι)) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ :=
  c • hoeffdingCentered μ (gaussianLogBandPair η δ)

lemma measurable_gaussianLogMasterBand (η δ c : ℝ) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    Measurable (gaussianLogMasterBand η δ c μ) :=
  ((stronglyMeasurable_hoeffdingCentered _ _
    (stronglyMeasurable_gaussianLogBandPair η δ hη)).const_smul c).measurable

lemma memLp_infty_gaussianLogMasterBand (η δ c : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    MemLp (gaussianLogMasterBand η δ c μ) ∞ (μ.prod μ) :=
  (memLp_infty_gaussianLogCenteredBand η δ hη hηδ μ).const_smul c

lemma gaussianLogMasterBand_symmetric (η δ c : ℝ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x y : EuclideanSpace ℝ ι) :
    gaussianLogMasterBand η δ c μ (x,y) = gaussianLogMasterBand η δ c μ (y,x) := by
  unfold gaussianLogMasterBand
  simp only [Pi.smul_apply,smul_eq_mul,gaussianLogCenteredBand_symmetric η δ μ x y]

lemma gaussianLogMasterBand_canonical (η δ c : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ,∫ y,gaussianLogMasterBand η δ c μ (x,y) ∂μ = 0 := by
  filter_upwards [gaussianLogCenteredBand_canonical η δ hη hηδ μ] with x hx
  unfold gaussianLogMasterBand
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [integral_const_mul,hx,mul_zero]

lemma norm_gaussianLogMasterBand_le (η δ c : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ‖gaussianLogMasterBand η δ c μ p‖ ≤ 4*|c| *Real.log (δ/η) := by
  unfold gaussianLogMasterBand
  rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left (norm_gaussianLogCenteredBand_le η δ hη hηδ μ p) (abs_nonneg c)
  simpa only [mul_assoc,mul_left_comm] using h

lemma essential_gaussianLogMasterBand_le (η δ c : ℝ) (hη : 0 < η) (hηδ : η ≤ δ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    (eLpNormEssSup (gaussianLogMasterBand η δ c μ) (μ.prod μ)).toReal ≤ 4*|c| *Real.log (δ/η) := by
  have hmass : 0 ≤ Real.log (δ/η) := Real.log_nonneg (by
    rw [le_div_iff₀ hη]
    simpa using hηδ)
  have hC : 0 ≤ 4*|c| *Real.log (δ/η) := by positivity
  have h := eLpNormEssSup_le_of_ae_bound (μ := μ.prod μ)
    (Filter.Eventually.of_forall (norm_gaussianLogMasterBand_le η δ c hη hηδ μ))
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

lemma gaussianLogMasterBand_particle_cap (η δ c : ℝ) (hη : 0 < η) (hηδ : η ≤ δ) (hc : 0 ≤ c)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ ι) :
    iidNegativeStatistic n (gaussianLogMasterBand η δ c μ) ω ≤ 2*c*Real.log (δ/η) := by
  have hb := gaussianLogCenteredBand_particle_cap η δ hη hηδ μ n hn ω
  unfold gaussianLogMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  nlinarith [mul_le_mul_of_nonneg_left hb hc]

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogMasterBand
#print axioms DGRHS.Gaussian.gaussianLogMasterBand
#check DGRHS.Gaussian.measurable_gaussianLogMasterBand
#print axioms DGRHS.Gaussian.measurable_gaussianLogMasterBand
#check DGRHS.Gaussian.memLp_infty_gaussianLogMasterBand
#print axioms DGRHS.Gaussian.memLp_infty_gaussianLogMasterBand
#check DGRHS.Gaussian.gaussianLogMasterBand_symmetric
#print axioms DGRHS.Gaussian.gaussianLogMasterBand_symmetric
#check DGRHS.Gaussian.gaussianLogMasterBand_canonical
#print axioms DGRHS.Gaussian.gaussianLogMasterBand_canonical
#check DGRHS.Gaussian.norm_gaussianLogMasterBand_le
#print axioms DGRHS.Gaussian.norm_gaussianLogMasterBand_le
#check DGRHS.Gaussian.essential_gaussianLogMasterBand_le
#print axioms DGRHS.Gaussian.essential_gaussianLogMasterBand_le
#check DGRHS.Gaussian.gaussianLogMasterBand_particle_cap
#print axioms DGRHS.Gaussian.gaussianLogMasterBand_particle_cap
