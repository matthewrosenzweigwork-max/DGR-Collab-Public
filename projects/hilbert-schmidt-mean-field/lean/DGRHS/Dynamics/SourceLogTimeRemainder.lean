/- Original finiteNAdjointDuality remainder: actual moving density,
actual path marginal laws and actual physical commutator.  Its rate is
DERIVED from the two-sided Gibbs moment/entropy factory and proper Fubini;
no expected-commutator estimate or proper time integral is an input. -/
import DGRHS.Dynamics.SourceLogDynamicCommutator
import DGRHS.Dynamics.SourceLogTimeMeasurable
import DGRHS.Dynamics.SourceDensityKernel
import DGRHS.Dynamics.AbsoluteTimeIntegralAE
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]

theorem exists_sourceLog_time_commutator_remainder
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K : ℝ≥0) (hK : 0<(K:ℝ)) (M : ℝ) (hM : 0≤M) (J H : ℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→EuclideanSpace ℝ ι→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ x ∂volume,ρ r x≤M) →
      (∀ r∈Icc 0 T,Integrable logPhysicalPair
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) →
      (∀ r∈Icc 0 T,-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
        (fun x y=>logPhysicalPair (x,y))) →
      ∀ (v : ℝ→EuclideanSpace ℝ ι→EuclideanSpace ℝ ι),Measurable (Function.uncurry v) →
      (∀ r∈Icc 0 T,LipschitzWith K (v r)) →
      ∀ (X : ℝ→Ω→Fin N→EuclideanSpace ℝ ι),Measurable (Function.uncurry X) →
      (∀ r∈Icc 0 T,klDiv (ν.map (X r)) (sourceLogSingularGibbs β (ρ r) N)≠∞) →
      (∀ r∈Icc 0 T,(klDiv (ν.map (X r)) (sourceLogSingularGibbs β (ρ r) N)).toReal≤H) →
      let A := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
        (sourceLogTransportKernel 1 (v r)) N (X r ω)
      Integrable (Function.uncurry A) ((volume.restrict (Ioc 0 T)).prod ν) ∧
      Integrable (fun ω=>(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)) ν ∧
      (∫ ω,|(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)| ∂ν)≤T*D/(2*Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceLog_dynamic_commutator_absolute_bound β hβ hd K hK M hM J H
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ hpair hI v hvm hv X hXm hKL hH
  let η := volume.restrict (Ioc 0 T)
  let κ := sourceDensityKernel volume ρ
  let A := fun r ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
    (sourceLogTransportKernel 1 (v r)) N (X r ω)
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρ r) :=
    sourceDensityKernel_apply volume ρ hρm r
  have hAm : Measurable (Function.uncurry A) := by
    have ht := measurable_sourceLogTransportEnergy_time κ v hvm N (by omega) (Function.uncurry X) hXm
    change Measurable (fun p : ℝ×Ω=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ p.1))
      (sourceLogTransportKernel 1 (v p.1)) N (X p.1 p.2))
    simpa only [hκ, Function.uncurry] using ht
  have hcap : ∀ᵐ z ∂η.prod ν,|A z.1 z.2|≤4*(K:ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le (continuous_abs.measurable.comp hAm) measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hprob r hr'
    apply Filter.Eventually.of_forall
    intro ω
    exact abs_sourceTransportEnergy_le (gaussianRieszDensityMeasure (ρ r)) _
      (measurable_sourceLogTransportKernel_one (hv r hr')) (K:ℝ)
      (abs_sourceLogTransportKernel_one_le (hv r hr'))
      (fun a b=>(sourceLogTransportKernel_swap 1 (v r) (a,b)).symm)
      (fun a=>by simp [sourceLogTransportKernel]) N (by omega) (X r ω)
  have hslice : ∀ᵐ r ∂η,(∫ ω,|A r ω| ∂ν)≤D/(N:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hprob r hr'
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨hai,hb⟩ := hfactory (v r) (hv r hr') (ρ r) (hρ r hr') (hpair r hr') (hI r hr')
      N hN (ν.map (X r)) (hKL r hr') (hH r hr')
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    exact hb
  obtain ⟨hi,hiT,hb⟩ := absolute_time_integral_bound_ae η ν A hAm.aestronglyMeasurable
    (4*(K:ℝ)) (D/(N:ℝ)) hcap hslice
  have hmass : η.real univ=T := by
    rw [measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hT,sub_zero]
  rw [hmass] at hb
  refine ⟨hi,hiT.const_mul _,?_⟩
  have hn : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hsq : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt hn.le
  calc
    (∫ ω,|(Real.sqrt N/2)*(∫ r,A r ω ∂η)| ∂ν)=
        (Real.sqrt N/2)*(∫ ω,|∫ r,A r ω ∂η| ∂ν) := by
      simp_rw [abs_mul,abs_of_nonneg (div_nonneg hs.le (by norm_num : (0:ℝ)≤2))]
      exact integral_const_mul _ _
    _ ≤ (Real.sqrt N/2)*(T*(D/(N:ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg hs.le (by norm_num))
    _ = T*D/(2*Real.sqrt N) := by
      field_simp
      rw [hsq]
      ring
end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.exists_sourceLog_time_commutator_remainder
#print axioms DGRHS.Dynamics.exists_sourceLog_time_commutator_remainder
