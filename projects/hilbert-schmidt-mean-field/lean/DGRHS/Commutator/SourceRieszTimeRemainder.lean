import DGRHS.Commutator.SourceRieszTimeMeasurable
import DGRHS.Commutator.SourceRieszDynamicTransfers
import DGRHS.Dynamics.AbsoluteTimeIntegralAE
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual finite-horizon positive-Riesz commutator remainder. Singularity
precludes a global pointwise cap. Product properness instead follows from
proved physical slice integrability and original Gronwall/Gibbs expectation
bounds through native integrable_prod_iff. Probability/density/Lip controls
are required only on Icc0T; no desired expected-A/time-integral premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Singular-kernel Fubini from proper slices and their integrable mean norm.
The physical endpoint below derives BOTH hypotheses from original data. -/
theorem sourceRiesz_time_integral_from_slices
    {τ Ω : Type*} [MeasurableSpace τ] [MeasurableSpace Ω]
    (η : Measure τ) [IsFiniteMeasure η] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : τ→Ω→ℝ) (hA : Measurable (Function.uncurry A)) (C : ℝ)
    (hiSlice : ∀ᵐ t ∂η,Integrable (A t) ν)
    (hbound : ∀ᵐ t ∂η,(∫ ω,|A t ω| ∂ν)≤C) :
    Integrable (Function.uncurry A) (η.prod ν) ∧
    Integrable (fun ω=>∫ t,A t ω ∂η) ν ∧
    (∫ ω,|∫ t,A t ω ∂η| ∂ν)≤η.real Set.univ*C := by
  have hiNorm : Integrable (fun t=>∫ ω,‖A t ω‖ ∂ν) η := by
    apply (integrable_const C).mono'
      hA.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hbound] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun ω=>norm_nonneg (A t ω)))]
    simpa only [Real.norm_eq_abs,Function.uncurry_apply_pair] using ht
  have hi : Integrable (Function.uncurry A) (η.prod ν) :=
    (integrable_prod_iff hA.aestronglyMeasurable).2 ⟨hiSlice,hiNorm⟩
  have ha := hi.abs
  refine ⟨hi,hi.integral_prod_right,?_⟩
  calc
    (∫ ω,|∫ t,A t ω ∂η| ∂ν)≤∫ ω,∫ t,|A t ω| ∂η ∂ν :=
      integral_mono hi.integral_prod_right.abs ha.integral_prod_right
        (fun ω=>abs_integral_le_integral_abs)
    _ = ∫ t,∫ ω,|A t ω| ∂ν ∂η := (integral_integral_swap ha).symm
    _ ≤ ∫ _ : τ,C ∂η := integral_mono_ae ha.integral_prod_left (integrable_const C) hbound
    _ = η.real Set.univ*C := by simp only [integral_const,smul_eq_mul]

 theorem exists_sourceRiesz_time_commutator_remainder
    (s β M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      ∀ (v : ℝ→E→E),Measurable (Function.uncurry v) →
      (∀ r∈Icc 0 T,LipschitzWith K (v r)) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (Function.uncurry X) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ r∈Icc 0 T,sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N (ν.map (X r))≤
        (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
          (sourceRieszSingularGibbs s β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      let A := fun r ω=>sourceRieszLocalTransportEnergy (ρ r) s 1 (v r) N (X r ω)
      Measurable (Function.uncurry A) ∧
      Integrable (Function.uncurry A) ((volume.restrict (Ioc 0 T)).prod ν) ∧
      (∀ᵐ ω ∂ν,Integrable (fun r=>A r ω) (volume.restrict (Ioc 0 T))) ∧
      Integrable (fun ω=>(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)) ν ∧
      (∫ ω,|(Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω)| ∂ν)≤T*D/(2*Real.sqrt N) := by
  obtain ⟨H,D,Dl,hH,hD,hDl,hfactory⟩ := sourceRieszDynamic_entropy_transfers
    (ι:=ι) s β M Bmax 0 hs hβ hd hM hBmax (by norm_num) K
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ v hvm hv X hXm G B hG hB hE
  let η := volume.restrict (Ioc 0 T)
  let A := fun r ω=>sourceRieszLocalTransportEnergy (ρ r) s 1 (v r) N (X r ω)
  have hAm : Measurable (Function.uncurry A) :=
    measurable_sourceRieszTransportEnergy_time s hs ρ hρm v hvm N (by omega) (Function.uncurry X) hXm
  have h0 : (0:ℝ)∈Icc 0 T := ⟨le_rfl,hT⟩
  letI := hprob 0 h0
  have hslice : ∀ᵐ r ∂η,Integrable (A r) ν ∧ (∫ ω,|A r ω| ∂ν)≤D/(N:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hprob r hr'
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨_,_,_,_,_,_,hcomm,_⟩ := hfactory N hN (ρ 0) (ρ r) (hρ 0 h0) (hρ r hr')
      (ν.map (X r)) (G r) (B r) (hG r hr') (hB r hr') (hE r hr')
    obtain ⟨hai,hb⟩ := hcomm (v r) (hv r hr')
    have hi : Integrable (A r) ν :=
      (integrable_map_measure hai.aestronglyMeasurable hXr.aemeasurable).mp hai
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    exact ⟨hi,hb⟩
  obtain ⟨hi,hiT,hb⟩ := sourceRiesz_time_integral_from_slices η ν A hAm
    (D/(N:ℝ)) (hslice.mono fun r hr=>hr.1) (hslice.mono fun r hr=>hr.2)
  have hmass : η.real univ=T := by
    rw [measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hT,sub_zero]
  rw [hmass] at hb
  refine ⟨hAm,hi,hi.prod_left_ae,hiT.const_mul _,?_⟩
  have hn : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hsq : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt hn.le
  calc
    (∫ ω,|(Real.sqrt N/2)*(∫ r,A r ω ∂η)| ∂ν)=
        (Real.sqrt N/2)*(∫ ω,|∫ r,A r ω ∂η| ∂ν) := by
      simp_rw [abs_mul,abs_of_nonneg (div_nonneg hsqrt.le (by norm_num : (0:ℝ)≤2))]
      exact integral_const_mul _ _
    _ ≤ (Real.sqrt N/2)*(T*(D/(N:ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg hsqrt.le (by norm_num))
    _ = T*D/(2*Real.sqrt N) := by
      field_simp
      rw [hsq]
      ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_time_integral_from_slices
#print axioms DGRHS.Commutator.sourceRiesz_time_integral_from_slices
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceRiesz_time_commutator_remainder
#print axioms DGRHS.Commutator.exists_sourceRiesz_time_commutator_remainder
