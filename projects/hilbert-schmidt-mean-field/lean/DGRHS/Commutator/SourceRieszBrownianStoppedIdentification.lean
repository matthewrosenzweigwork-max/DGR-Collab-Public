import DGRHS.Commutator.SourceRieszBrownianFamily

/-! Deterministic stopping from the actual integrand support, with one common
probability-one event for all times. The proof uses the proved interval isometry,
then the AE-continuous representative. No stopping theorem or desired bracket
identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)

lemma sourceRieszBrownianProcessL2_stopped_support
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (a : ℝ≥0)
    (hs : ∀ᵐ p ∂sourceRieszBrownianPredictableMeasure P F T,a<p.1 → g p=0) (t : ℝ≥0) :
    sourceRieszBrownianProcessL2 P F T B hB hBa hind g t=
      sourceRieszBrownianProcessL2 P F T B hB hBa hind g (min t a) := by
  by_cases hta : t≤a
  · rw [min_eq_left hta]
  · have hat : a≤t := le_of_not_ge hta
    rw [min_eq_right hat]
    have hid (u : Lp ℝ 2 P) : sourceRieszL2Indicator P univ MeasurableSet.univ u=u := by
      apply Lp.ext
      filter_upwards [sourceRieszL2Indicator_coe P univ MeasurableSet.univ u] with ω hω
      simpa only [indicator_univ] using hω
    have hi := sourceRieszBrownianProcessL2_conditional_isometry_no_continuity
      P F T B hB hBa hind g a t hat univ MeasurableSet.univ
    rw [hid] at hi
    have hz : (∫ p in Ioc a t ×ˢ (univ:Set Ω),(g p)^2
        ∂sourceRieszBrownianPredictableMeasure P F T)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_of_ae hs,
        ae_restrict_mem (measurableSet_predictable_Ioc_prod a t MeasurableSet.univ)] with p hp hmem
      rw [hp hmem.1.1]
      norm_num
    rw [hz] at hi
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hi))

variable (hBc : ∀ᵐ ω ∂P,Continuous (fun r=>B r ω))
include hB hBa hind hBc in
lemma sourceRieszBrownianContinuousProcess_stopped_support
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (a : ℝ≥0)
    (hs : ∀ᵐ p ∂sourceRieszBrownianPredictableMeasure P F T,a<p.1 → g p=0) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianContinuousProcess P F T B g t ω=
      sourceRieszBrownianContinuousProcess P F T B g (min t a) ω := by
  apply sourceRiesz_ae_continuous_indistinguishable P
  · exact sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous P F T B hB hBa hind hBc g
  · filter_upwards [sourceRieszBrownianContinuousProcess_continuous_of_ae_continuous P F T B hB hBa hind hBc g] with ω hω
    exact hω.comp (continuous_id.min continuous_const)
  · intro t
    have he := sourceRieszBrownianProcessL2_stopped_support P F T B hB hBa hind g a hs t
    filter_upwards [sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc g t,
      sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc g (min t a)]
      with ω ht ha
    exact ht.trans ((congrArg (fun u:Lp ℝ 2 P=>u ω) he).trans ha.symm)

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_finite_stopped_sum
    {α : Type*} [Fintype α] (a : α→ℝ≥0) (θ : α→ℝ)
    (g : α→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (hs : ∀ i,∀ᵐ p ∂sourceRieszBrownianPredictableMeasure P F T,a i<p.1 → g i p=0) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianContinuousProcess P F T B (∑ i,θ i • g i) t ω=
      ∑ i,θ i*sourceRieszBrownianContinuousProcess P F T B (g i) (min t (a i)) ω := by
  filter_upwards [sourceRieszBrownianContinuousProcess_finsetSum P F T B hB hBa hind hBc Finset.univ (fun i=>θ i • g i),
    ae_all_iff.2 (fun i=>sourceRieszBrownianContinuousProcess_smul P F T B hB hBa hind hBc (θ i) (g i)),
    ae_all_iff.2 (fun i=>sourceRieszBrownianContinuousProcess_stopped_support P F T B hB hBa hind hBc (g i) (a i) (hs i))]
      with ω hsum hsmul hstop
  intro t
  rw [hsum t]
  exact Finset.sum_congr rfl (fun i _=>by rw [hsmul i t,hstop i t])

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_stopped_support
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_stopped_support
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_stopped_support
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_stopped_support
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_finite_stopped_sum
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_finite_stopped_sum
