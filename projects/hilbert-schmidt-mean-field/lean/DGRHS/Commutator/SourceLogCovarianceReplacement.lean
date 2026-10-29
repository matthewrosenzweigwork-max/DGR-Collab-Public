/- Physical finite-horizon cross-gradient covariance replacement from original
logarithmic entropy/free-energy controls. Actual native gradients and their sup bounds
derive test measurability, bounded range and all proper integrals. This is a
covariance-expression estimate, not a stochastic bracket realization. -/
import DGRHS.Commutator.SourceRieszTimeCovarianceTest
import DGRHS.Commutator.SourceRieszTimeRemainder
import DGRHS.Dynamics.SourceLogDynamicTransfers
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual logarithmic empirical difference; the finite atomic law agrees
by definition with the already checked generic covariance support. -/
def sourceLogDynamicEmpiricalDifference (ρ q : E→ℝ) (N : ℕ) (ω : Fin N→E) : ℝ :=
  (∫ x,q x ∂transportEmpiricalLaw N ω)-∫ x,q x ∂gaussianRieszDensityMeasure ρ

/-- Actual logarithmic covariance expression replacement; no stochastic bracket claimed. -/
theorem exists_sourceLog_cross_gradient_covariance_replacement
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (M : ℝ) (hM : 0≤M) (J c C C₂ Amax Bmax : ℝ)
    (hc₀ : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) (Gf Gg : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (ta tb : ℝ),ta∈Icc 0 T → tb∈Icc 0 T →
      ∀ (N : ℕ),1≤N → ∀ (Ω : Type u),∀ [MeasurableSpace Ω],
      ∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      (∀ r∈Icc 0 T,Integrable logPhysicalPair
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) →
      (∀ r∈Icc 0 T,-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
        (fun x y=>logPhysicalPair (x,y))) →
      ∀ (f g : ℝ→E→ℝ),
      (∀ r∈Icc 0 ta,ContDiff ℝ 2 (f r)) → (∀ r∈Icc 0 tb,ContDiff ℝ 2 (g r)) →
      ContinuousOn (fun p : ℝ×E=>gradient (f p.1) p.2) (Icc 0 ta ×ˢ univ) →
      ContinuousOn (fun p : ℝ×E=>gradient (g p.1) p.2) (Icc 0 tb ×ˢ univ) →
      (∀ r∈Icc 0 ta,∀ z,‖gradient (f r) z‖≤(Gf:ℝ)) →
      (∀ r∈Icc 0 tb,∀ z,‖gradient (g r) z‖≤(Gg:ℝ)) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (Function.uncurry X) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) →
      (∀ r∈Icc 0 T,G r≤Amax) → (∀ r∈Icc 0 T,B r≤Bmax) →
      c≤(sourceLogSingularPartition β (ρ 0) N).toReal →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition β (ρ r) N).toReal≤C) →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition
        (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) (ρ r) N).toReal≤C₂) →
      (∀ r∈Icc 0 T,sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      let U := min ta tb
      let η := volume.restrict (Ioc 0 U)
      let q := fun r z=>⟪gradient (f r) z,gradient (g r) z⟫
      let A := fun r ω=>sourceLogDynamicEmpiricalDifference (ρ r) (q r) N (X r ω)
      (∀ r∈Icc 0 U,Integrable (q r) (gaussianRieszDensityMeasure (ρ r)) ∧
        ∀ x,Integrable (q r) (transportEmpiricalLaw N x)) ∧
      Integrable (fun p : ℝ×Ω=>∫ z,q p.1 z ∂gaussianRieszDensityMeasure (ρ p.1)) (η.prod ν) ∧
      Integrable (fun p : ℝ×Ω=>∫ z,q p.1 z ∂transportEmpiricalLaw N (X p.1 p.2)) (η.prod ν) ∧
      Integrable (Function.uncurry A) (η.prod ν) ∧
      (∀ᵐ ω ∂ν,Integrable (fun r=>A r ω) η) ∧
      Integrable (fun ω=>(2/(β:ℝ))*(∫ r,A r ω ∂η)) ν ∧
      (∫ ω,|(2/(β:ℝ))*(∫ r,A r ω ∂η)| ∂ν)≤U*D/Real.sqrt N := by
  obtain ⟨H,Dc,Dl,hH,hDc,hDl,hfactory⟩ := exists_sourceLog_dynamic_entropy_transfers
    (ι:=ι) β hβ hd 1 (by norm_num) M hM J c C C₂ Amax Bmax
    (2*(Gf:ℝ)*(Gg:ℝ)) hc₀ hAmax hBmax (by positivity)
  have hc : 0<(2:ℝ)/β := div_pos (by norm_num) hβ
  refine ⟨(2/(β:ℝ))*Dl,mul_nonneg hc.le hDl,?_⟩
  intro T hT ta tb hta htb N hN Ω _ ν _ ρ hρm hprob hρ hp hI f g hfreg hgreg hf hg hfB hgB X hXm G B hG hGA hB hlow hcap hcap₂ hE
  let U := min ta tb
  let η := volume.restrict (Ioc 0 U)
  have hU : 0≤U := le_min hta.1 htb.1
  have hUT : U≤T := (min_le_left ta tb).trans hta.2
  have hUa (r : ℝ) (hr : r∈Icc 0 U) : r∈Icc 0 ta := ⟨hr.1,hr.2.trans (min_le_left _ _)⟩
  have hUb (r : ℝ) (hr : r∈Icc 0 U) : r∈Icc 0 tb := ⟨hr.1,hr.2.trans (min_le_right _ _)⟩
  have hUr (r : ℝ) (hr : r∈Icc 0 U) : r∈Icc 0 T := ⟨hr.1,hr.2.trans hUT⟩
  let Q := sourceRieszCrossGradientCut U f g
  have hQ : Measurable Q := measurable_sourceRieszCrossGradientCut U f g
    (hf.mono (by intro p hp;exact ⟨hUa p.1 hp.1,hp.2⟩))
    (hg.mono (by intro p hp;exact ⟨hUb p.1 hp.1,hp.2⟩))
  let P := fun r ω=>sourceLogDynamicEmpiricalDifference (ρ r) (fun z=>Q (r,z)) N (X r ω)
  let q := fun r z=>⟪gradient (f r) z,gradient (g r) z⟫
  let A := fun r ω=>sourceLogDynamicEmpiricalDifference (ρ r) (q r) N (X r ω)
  have hPm : Measurable (Function.uncurry P) :=
    measurable_sourceRieszEmpiricalDifference_time ρ hρm Q hQ N (Function.uncurry X) hXm
  have hQeq (r : ℝ) (hr : r∈Icc 0 U) : (fun z=>Q (r,z))=q r :=
    funext fun z=>sourceRieszCrossGradientCut_eq U f g r hr z
  have h0 : (0:ℝ)∈Icc 0 T := ⟨le_rfl,hT⟩
  letI := hprob 0 h0
  have hphys (r : ℝ) (hr : r∈Icc 0 U) :
      Integrable (q r) (gaussianRieszDensityMeasure (ρ r)) ∧
      (∀ x,Integrable (q r) (transportEmpiricalLaw N x)) ∧
      Integrable (P r) ν ∧ (∫ ω,|P r ω| ∂ν)≤Dl/Real.sqrt N := by
    have hrT := hUr r hr
    letI := hprob r hrT
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨_,_,_,hlinear⟩ := hfactory N hN (ρ 0) (ρ r) (hρ 0 h0) (hρ r hrT)
      (hp 0 h0) (hp r hrT) (hI r hrT) (ν.map (X r)) (G r) (B r)
      (hG r hrT) (hGA r hrT) (hB r hrT) hlow (hcap r hrT) (hcap₂ r hrT) (hE r hrT)
    have hqr : Measurable (fun z=>Q (r,z)) := hQ.comp (measurable_const.prodMk measurable_id)
    obtain ⟨hlo,hup,hosc⟩ := sourceRieszCrossGradient_range U f g Gf Gg
      (fun r hr=>hfB r (hUa r hr)) (fun r hr=>hgB r (hUb r hr)) r hr
    obtain ⟨hiq,hiemp,hai,hb⟩ := hlinear (fun z=>Q (r,z)) hqr hlo hup hosc
    have hi : Integrable (P r) ν := (integrable_map_measure hai.aestronglyMeasurable hXr.aemeasurable).mp hai
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    rw [hQeq r hr] at hiq hiemp
    exact ⟨hiq,hiemp,hi,hb⟩
  have hslice : ∀ᵐ r ∂η,Integrable (P r) ν ∧ (∫ ω,|P r ω| ∂ν)≤Dl/Real.sqrt N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨(hphys r ⟨hr.1.le,hr.2⟩).2.2.1,(hphys r ⟨hr.1.le,hr.2⟩).2.2.2⟩
  obtain ⟨hi,hiT,hb⟩ := sourceRiesz_time_integral_from_slices η ν P hPm (Dl/Real.sqrt N)
    (hslice.mono fun r hr=>hr.1) (hslice.mono fun r hr=>hr.2)
  have htime : ∀ᵐ p : ℝ×Ω ∂η.prod ν,p.1∈Ioc 0 U := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Filter.Eventually.of_forall fun _=>hr
  have heq : Function.uncurry P =ᵐ[η.prod ν] Function.uncurry A := htime.mono fun p hp=>by
    simp only [P,A,hQeq p.1 ⟨hp.1.le,hp.2⟩,Function.uncurry]
  have hAi := hi.congr heq
  have hIntEq (ω : Ω) : (∫ r,P r ω ∂η)=(∫ r,A r ω ∂η) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [P,A,hQeq r ⟨hr.1.le,hr.2⟩]
  let κ := sourceDensityKernel volume ρ
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρ r) := sourceDensityKernel_apply volume ρ hρm r
  have hMean : Measurable (fun r=>∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)) := by
    simpa only [hκ] using (hQ.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  have hm : Integrable (fun r=>∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)) η := by
    apply (integrable_const ((Gf:ℝ)*(Gg:ℝ))).mono' hMean.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 U := ⟨hr.1.le,hr.2⟩
    letI := hprob r (hUr r hr')
    change |∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)|≤_
    have hb : ∀ᵐ z ∂gaussianRieszDensityMeasure (ρ r),‖Q (r,z)‖≤(Gf:ℝ)*(Gg:ℝ) :=
      Filter.Eventually.of_forall fun z=>by
        rw [Real.norm_eq_abs,congrFun (hQeq r hr') z]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (hfB r (hUa r hr') z) (hgB r (hUb r hr') z) (norm_nonneg _) Gf.coe_nonneg)
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
      (norm_integral_le_of_norm_le_const hb)
  have hmProd : Integrable (fun p : ℝ×Ω=>∫ z,q p.1 z ∂gaussianRieszDensityMeasure (ρ p.1)) (η.prod ν) := by
    apply (hm.comp_fst ν).congr
    filter_upwards [htime] with p hp
    rw [hQeq p.1 ⟨hp.1.le,hp.2⟩]
  have heProd : Integrable (fun p : ℝ×Ω=>∫ z,q p.1 z ∂transportEmpiricalLaw N (X p.1 p.2)) (η.prod ν) := by
    apply (hAi.add hmProd).congr
    exact Filter.Eventually.of_forall fun p=>by simp [A,sourceLogDynamicEmpiricalDifference,Function.uncurry]
  have hmass : η.real univ=U := by
    rw [measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hU,sub_zero]
  rw [hmass] at hb
  simp_rw [hIntEq] at hiT hb
  refine ⟨fun r hr=>⟨(hphys r hr).1,(hphys r hr).2.1⟩,hmProd,heProd,hAi,hAi.prod_left_ae,hiT.const_mul _,?_⟩
  calc
    (∫ ω,|(2/(β:ℝ))*(∫ r,A r ω ∂η)| ∂ν)=(2/(β:ℝ))*(∫ ω,|∫ r,A r ω ∂η| ∂ν) := by
      simp_rw [abs_mul,abs_of_pos hc]
      exact integral_const_mul _ _
    _ ≤ (2/(β:ℝ))*(U*(Dl/Real.sqrt N)) := mul_le_mul_of_nonneg_left hb hc.le
    _ = U*((2/(β:ℝ))*Dl)/Real.sqrt N := by ring
end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_cross_gradient_covariance_replacement
#print axioms DGRHS.Commutator.exists_sourceLog_cross_gradient_covariance_replacement

#check @DGRHS.Commutator.sourceLogDynamicEmpiricalDifference
#print axioms DGRHS.Commutator.sourceLogDynamicEmpiricalDifference
