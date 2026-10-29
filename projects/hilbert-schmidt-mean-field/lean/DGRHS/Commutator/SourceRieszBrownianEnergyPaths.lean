import DGRHS.Commutator.SourceRieszBrownianCompensatedSquare
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Regularity of the actual squared-integrand time energy. Continuity follows
from dominated convergence and the verified atomless Lebesgue time measure;
path integrability follows from the actual product L2 estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator

instance sourceRieszBrownianTime_nullSingleton : NullSingletonClass sourceRieszBrownianTime := by
  constructor
  intro r
  have hm : MeasurableEmbedding ((↑) : ℝ≥0→ℝ) := NNReal.isClosedEmbedding_coe.measurableEmbedding
  rw [sourceRieszBrownianTime,hm.comap_apply]
  simp

lemma sourceRiesz_integral_Ioc_continuous (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (f : ℝ≥0→ℝ) (hf : Integrable f μ) :
    Continuous (fun t=>∫ r in Ioc 0 t,f r ∂μ) := by
  simp_rw [←integral_indicator measurableSet_Ioc]
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (fun r=>‖f r‖)
  · exact Filter.Eventually.of_forall (fun _=>hf.aestronglyMeasurable.indicator measurableSet_Ioc)
  · exact Filter.Eventually.of_forall (fun u=>ae_of_all _ fun r=>by
      by_cases hr : r∈Ioc 0 u <;> simp [hr])
  · exact hf.norm
  · filter_upwards [μ.ae_ne t] with r hrt
    by_cases h0 : 0<r
    · rcases lt_or_gt_of_ne hrt with hr | hr
      · apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_nhds hr] with u hu
        change r<u at hu
        simp [mem_Ioc,h0,hr.le,hu.le]
      · apply tendsto_const_nhds.congr'
        filter_upwards [Iio_mem_nhds hr] with u hu
        change u<r at hu
        simp [mem_Ioc,h0,not_le_of_gt hr,not_le_of_gt hu]
    · have he : (fun u=>(Ioc 0 u).indicator f r)=(fun _=>0) := by
        funext u
        simp [mem_Ioc,h0]
      simp only [he]
      simpa [mem_Ioc,h0] using (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0=>(0:ℝ)) (𝓝 t) (𝓝 0))

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

lemma sourceRieszBrownianEnergy_zero
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (ω : Ω) :
    sourceRieszBrownianEnergy P F T g 0 ω=0 := by
  simp [sourceRieszBrownianEnergy]

lemma sourceRieszBrownianEnergy_nonneg
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) (ω : Ω) :
    0≤sourceRieszBrownianEnergy P F T g t ω := integral_nonneg (fun r=>sq_nonneg _)

lemma sourceRieszBrownianEnergy_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,Continuous (fun t=>sourceRieszBrownianEnergy P F T g t ω) := by
  letI : NullSingletonClass (sourceRieszBrownianTimeOn T) := by
    unfold sourceRieszBrownianTimeOn
    infer_instance
  filter_upwards [(sourceRieszBrownianEnergy_product_integrable P F T g).prod_left_ae] with ω hω
  exact sourceRiesz_integral_Ioc_continuous (sourceRieszBrownianTimeOn T) (fun r=>(g (r,ω))^2) hω

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianTime_nullSingleton
#print axioms DGRHS.Commutator.sourceRieszBrownianTime_nullSingleton
#check @DGRHS.Commutator.sourceRiesz_integral_Ioc_continuous
#print axioms DGRHS.Commutator.sourceRiesz_integral_Ioc_continuous
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_zero
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_nonneg
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_nonneg
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_ae_continuous
