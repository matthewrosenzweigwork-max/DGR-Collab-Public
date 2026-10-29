import DGRHS.Commutator.SourceLogTransportLocal
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def positiveLocalLog (z : EuclideanSpace ℝ ι) : ℝ := max (-Real.log ‖z‖) 0

lemma measurable_positiveLocalLog : Measurable (positiveLocalLog (ι := ι)) := by
  unfold positiveLocalLog
  fun_prop

lemma positiveLocalLog_eq_indicator : positiveLocalLog (ι := ι) =
    (Metric.closedBall (0 : EuclideanSpace ℝ ι) 1).indicator (fun z => -Real.log ‖z‖) := by
  funext z
  by_cases hz : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) 1
  · have hn : ‖z‖ ≤ 1 := by simpa using hz
    rw [Set.indicator_of_mem hz]
    exact max_eq_left (by linarith [Real.log_nonpos (norm_nonneg z) hn])
  · have hn : 1 < ‖z‖ := by simpa using hz
    rw [Set.indicator_of_notMem hz]
    exact max_eq_right (by linarith [Real.log_nonneg hn.le])

/-- The actual source local logarithmic integral is proper in every positive dimension. -/
lemma integrable_positiveLocalLog (hd : 0 < (Fintype.card ι : ℝ)) :
    Integrable (positiveLocalLog (ι := ι)) volume := by
  let q := (Fintype.card ι : ℝ) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hdim : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ ι) := by
    simp only [finrank_euclideanSpace]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hd.ne')
  have hqDim : q < (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) := by
    simp only [finrank_euclideanSpace]
    dsimp [q]
    linarith
  have hBound (z : EuclideanSpace ℝ ι) : ‖positiveLocalLog z‖ ≤ (1/q) * ‖z‖^(-q) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · exact (neg_log_le_power_majorant ‖z‖ q (norm_nonneg z) hq).trans_eq (by ring)
    · positivity
  have hi : IntegrableOn (positiveLocalLog (ι := ι)) (Metric.ball 0 2) volume :=
    integrableOn_ball_of_norm_le_rpow hdim hqDim
      (Filter.Eventually.of_forall hBound) measurable_positiveLocalLog.aestronglyMeasurable
  have he : (Metric.ball (0 : EuclideanSpace ℝ ι) 2).indicator positiveLocalLog = positiveLocalLog := by
    funext z
    by_cases hz : z ∈ Metric.ball (0 : EuclideanSpace ℝ ι) 2
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz]
      have hn : 2 ≤ ‖z‖ := by simpa using hz
      symm
      exact max_eq_right (by linarith [Real.log_nonneg (show 1 ≤ ‖z‖ by linarith)])
  rw [← he]
  exact hi.integrable_indicator measurableSet_ball

lemma integral_positiveLocalLog_eq_source :
    (∫ z : EuclideanSpace ℝ ι, positiveLocalLog z ∂volume) =
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) 1, -Real.log ‖z‖ ∂volume := by
  rw [positiveLocalLog_eq_indicator, integral_indicator measurableSet_closedBall]

/-- Density domination and translation invariance give the exact local positive-part bound. -/
lemma positiveLocalLog_section_bound (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => positiveLocalLog (x-y)) (gaussianRieszDensityMeasure ρ) ∧
      (∫ y, positiveLocalLog (x-y) ∂gaussianRieszDensityMeasure ρ) ≤
        M * ∫ z : EuclideanSpace ℝ ι, positiveLocalLog z ∂volume := by
  have hi : Integrable (fun y => positiveLocalLog (x-y)) (ENNReal.ofReal M • volume) :=
    ((integrable_positiveLocalLog hd).comp_sub_left x).smul_measure ENNReal.ofReal_ne_top
  refine ⟨hi.mono_measure (gaussianRieszDensityMeasure_le ρ M hρ), ?_⟩
  calc
    _ ≤ ∫ y, positiveLocalLog (x-y) ∂(ENNReal.ofReal M • volume) :=
      integral_mono_measure (gaussianRieszDensityMeasure_le ρ M hρ)
        (Filter.Eventually.of_forall fun y => le_max_right _ _) hi
    _ = _ := by
      rw [integral_smul_measure, integral_sub_left_eq_self positiveLocalLog volume x,
        ENNReal.toReal_ofReal hM]
      rfl

/-- Exact Appendix absolute pair-log control; no origin-tail assumption is introduced. -/
theorem source_log_family_absolute_pair_control (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M J : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (hI : -J ≤ DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b => logPhysicalPair (a,b))) :
    (∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, |Real.log ‖p.1-p.2‖|
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
      2 * M * (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) 1, -Real.log ‖z‖ ∂volume) + 2 * J := by
  let μ := gaussianRieszDensityMeasure ρ
  have hp : Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (logPhysicalPair p)⁺) (μ.prod μ) := by
    change Integrable (fun p => max (logPhysicalPair p) 0) (μ.prod μ)
    fun_prop
  have hpos : (∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      (logPhysicalPair p)⁺ ∂μ.prod μ) ≤ M * ∫ z : EuclideanSpace ℝ ι, positiveLocalLog z ∂volume := by
    rw [integral_prod _ hp]
    calc
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, (M * ∫ z : EuclideanSpace ℝ ι, positiveLocalLog z ∂volume) ∂μ :=
        integral_mono_ae hp.integral_prod_left (integrable_const _)
          (Filter.Eventually.of_forall fun x => (positiveLocalLog_section_bound hd ρ M hM hρ x).2)
      _ = _ := by simp
  have hid : (∫ p, |logPhysicalPair p| ∂μ.prod μ) =
      2 * (∫ p, (logPhysicalPair p)⁺ ∂μ.prod μ) - (∫ p, logPhysicalPair p ∂μ.prod μ) :=
    integral_abs_eq_two_mul_integral_posPart_sub_integral hpair
  have hmean : -2 * J ≤ ∫ p, logPhysicalPair p ∂μ.prod μ := by
    dsimp [DGRHS.interactionEnergy] at hI
    change -J ≤ (1/2 : ℝ) * (∫ p, logPhysicalPair p ∂μ.prod μ) at hI
    linarith
  rw [integral_positiveLocalLog_eq_source] at hpos
  have hres : (∫ p, |logPhysicalPair p| ∂μ.prod μ) ≤
      2 * M * (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) 1, -Real.log ‖z‖ ∂volume) + 2 * J := by linarith
  simpa [μ, logPhysicalPair] using hres

end DGRHS.Commutator
#print axioms DGRHS.Commutator.integrable_positiveLocalLog
#print axioms DGRHS.Commutator.positiveLocalLog_section_bound
#print axioms DGRHS.Commutator.source_log_family_absolute_pair_control
#check @DGRHS.Commutator.source_log_family_absolute_pair_control
