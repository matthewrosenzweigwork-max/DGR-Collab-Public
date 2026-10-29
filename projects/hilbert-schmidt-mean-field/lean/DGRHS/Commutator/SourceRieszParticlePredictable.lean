import DGRHS.Commutator.SourceRieszPredictableContinuous
import DGRHS.Commutator.SourceRieszFiniteCovariance
import Mathlib.Order.Interval.Set.ProjIcc

/-! Actual deterministically stopped particle-gradient integrands. Classical
joint gradient regularity on its own horizon, bounded gradient, and a supplied
continuous adapted particle version imply predictability and proper product L2.
The time measure may be any finite measure, in particular restricted Lebesgue.
No stochastic integral, martingale or bracket identity is an input or conclusion.
The indicator left-continuity argument follows the Apache-2.0 BrownianMotion
Predictable.lean proof at revision 0d5b6eb928e616d3b1f774ad7d233c167d9f42c9;
original source and license are preserved in own reassessment records. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_predictable_le_product (F : Filtration ℝ≥0 mΩ) :
    F.predictable≤Prod.instMeasurableSpace := by
  unfold Filtration.predictable
  apply MeasurableSpace.generateFrom_le
  rintro s (⟨A,hA,rfl⟩ | ⟨i,A,hA,rfl⟩)
  · exact (measurableSet_singleton _).prod (F.le _ _ hA)
  · exact measurableSet_Ioi.prod (F.le _ _ hA)

lemma sourceRiesz_cutoff_leftContinuous (T : ℝ≥0) (r : ℝ≥0) :
    ContinuousWithinAt (fun u : ℝ≥0=>if u≤T then (1:ℝ) else 0) (Iio r) r := by
  by_cases hr : r≤T
  · refine (continuousWithinAt_const (b:=(1:ℝ))).congr (fun u hu=>?_) ?_
    · simp only [if_pos ((mem_Iio.mp hu).le.trans hr)]
    · simp only [if_pos hr]
  · have hopen : IsOpen {u : ℝ≥0 | T<u} := isOpen_Ioi
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_const (y:=(0:ℝ))).congr
    filter_upwards [hopen.mem_nhds (lt_of_not_ge hr)] with u hu
    simp only [if_neg (not_le.mpr hu)]

theorem sourceRiesz_particle_stopped_gradient_predictable
    (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ]
    (T : ℝ≥0) (f : ℝ→E→ℝ)
    (hgrad : ContinuousOn (fun p : ℝ×E=>gradient (f p.1) p.2) (Icc 0 (T:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ r∈Icc 0 (T:ℝ),∀ z,‖gradient (f r) z‖≤(G:ℝ))
    (X : ℝ≥0→Ω→E) (hXa : StronglyAdapted F X)
    (hXc : ∀ ω,Continuous (fun r=>X r ω)) :
    let U := fun (r : ℝ≥0) ω=>sourceRieszStoppedGradient (T:ℝ) f (r:ℝ) (X r ω)
    IsStronglyPredictable F U ∧
      StronglyMeasurable (Function.uncurry U) ∧
      MemLp (Function.uncurry U) 2 (τ.prod P) ∧
      (∀ r ω,‖U r ω‖≤(G:ℝ)) := by
  let ge := fun p : ℝ×E=>gradient (f (projIcc 0 (T:ℝ) T.coe_nonneg p.1)) p.2
  have hge : Continuous ge := by
    have hc : Continuous (fun p : ℝ×E=>
        ((projIcc 0 (T:ℝ) T.coe_nonneg p.1 : ℝ),p.2)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
    exact hgrad.comp_continuous hc (fun p=>
      ⟨(projIcc 0 (T:ℝ) T.coe_nonneg p.1).property,mem_univ _⟩)
  let Y := fun (r : ℝ≥0) ω=>ge ((r:ℝ),X r ω)
  have hYa : StronglyAdapted F Y := by
    intro r
    exact hge.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk (hXa r))
  have hYc (ω) : Continuous (fun r=>Y r ω) :=
    hge.comp (NNReal.continuous_coe.prodMk (hXc ω))
  let U := fun (r : ℝ≥0) ω=>sourceRieszStoppedGradient (T:ℝ) f (r:ℝ) (X r ω)
  have he : U=fun r ω=>(if r≤T then (1:ℝ) else 0) • Y r ω := by
    funext r ω
    by_cases hr : r≤T
    · have hr' : (r:ℝ)∈Icc 0 (T:ℝ) := ⟨r.coe_nonneg,hr⟩
      simp only [U,sourceRieszStoppedGradient,if_pos hr',if_pos hr,one_smul,Y,ge,
        projIcc_of_mem T.coe_nonneg hr']
    · have hr' : ¬(r:ℝ)∈Icc 0 (T:ℝ) := fun hh=>hr hh.2
      simp only [U,sourceRieszStoppedGradient,if_neg hr',if_neg hr,zero_smul]
  have hUa : StronglyAdapted F U := by
    rw [he]
    intro r
    have hs : StronglyMeasurable[F r] (fun _ : Ω=>if r≤T then (1:ℝ) else 0) :=
      stronglyMeasurable_const
    exact hs.smul (hYa r)
  have hUc (ω) (r) : ContinuousWithinAt (fun u=>U u ω) (Iio r) r := by
    rw [he]
    exact (sourceRiesz_cutoff_leftContinuous T r).smul (hYc ω).continuousAt.continuousWithinAt
  have hp : IsStronglyPredictable F U :=
    sourceRiesz_adapted_predictable_of_leftContinuous hUa hUc
  have hm : StronglyMeasurable (Function.uncurry U) := hp.mono (sourceRiesz_predictable_le_product F)
  have hUb (r) (ω) : ‖U r ω‖≤(G:ℝ) := by
    dsimp only [U,sourceRieszStoppedGradient]
    split_ifs with hr
    · exact hb _ hr _
    · simpa only [norm_zero] using G.coe_nonneg
  exact ⟨hp,hm,MemLp.of_bound hm.aestronglyMeasurable G (ae_of_all _ fun p=>hUb p.1 p.2),hUb⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_particle_stopped_gradient_predictable
#print axioms DGRHS.Commutator.sourceRiesz_particle_stopped_gradient_predictable

#check @DGRHS.Commutator.sourceRiesz_predictable_le_product
#print axioms DGRHS.Commutator.sourceRiesz_predictable_le_product

#check @DGRHS.Commutator.sourceRiesz_cutoff_leftContinuous
#print axioms DGRHS.Commutator.sourceRiesz_cutoff_leftContinuous
