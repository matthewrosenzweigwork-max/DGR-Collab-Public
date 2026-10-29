import DGRHS.Commutator.SourceRieszStoppedCovariance
import DGRHS.Commutator.SourceLogCovarianceReplacement

/-! Actual logarithmic strong product-L1 covariance replacement for the literal finite Volterra
Ito comparison. All physical rate hypotheses are original Gr/initial Gibbs;
no desired bracket error or stochastic identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceLog_stopped_square_product_replacement
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (M : ℝ) (hM : 0≤M) (J c C C₂ Amax Bmax : ℝ)
    (hc₀ : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) (Gmax : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (k : ℕ) (t θ : Fin k→ℝ),
      (∀ a,t a∈Icc 0 T) → ∀ (N : ℕ),1≤N → ∀ (Ω : Type u),∀ [MeasurableSpace Ω],
      ∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      (∀ r∈Icc 0 T,Integrable logPhysicalPair
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) →
      (∀ r∈Icc 0 T,-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
        (fun x y=>logPhysicalPair (x,y))) →
      ∀ (f : Fin k→ℝ→E→ℝ),
      (∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r)) →
      (∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ)) →
      (∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ)) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (Function.uncurry X) →
      ∀ (A B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤A r) →
      (∀ r∈Icc 0 T,A r≤Amax) → (∀ r∈Icc 0 T,B r≤Bmax) →
      c≤(sourceLogSingularPartition β (ρ 0) N).toReal →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition β (ρ r) N).toReal≤C) →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition
        (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) (ρ r) N).toReal≤C₂) →
      (∀ r∈Icc 0 T,sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (A r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      let J := fun r ω=>(2/(β:ℝ))*sourceLogDynamicEmpiricalDifference (ρ r) (S r) N (X r ω)
      Measurable (Function.uncurry J) ∧
      (∀ r∈Icc 0 T,Integrable (J r) ν ∧
        (∫ ω,|J r ω| ∂ν)≤D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N) ∧
      Integrable (Function.uncurry J) ((volume.restrict (Ioc 0 T)).prod ν) ∧
      Integrable (fun r=>∫ ω,|J r ω| ∂ν) (volume.restrict (Ioc 0 T)) ∧
      (∫ r in Ioc 0 T,∫ ω,|J r ω| ∂ν)≤T*D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N := by
  obtain ⟨H,Dc,Dl,hH,hDc,hDl,hfactory⟩ := exists_sourceLog_dynamic_entropy_transfers
    (ι:=ι) β hβ hd 1 (by norm_num) M hM J c C C₂ Amax Bmax
    (2*(Gmax:ℝ)^2) hc₀ hAmax hBmax (by positivity)
  have hc : 0<(2:ℝ)/β := div_pos (by norm_num) hβ
  refine ⟨(2/(β:ℝ))*Dl,mul_nonneg hc.le hDl,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hp hI f hfreg hf hfB X hXm A B hA hAA hB hlow hcap hcap₂ hE
  let Q := fun a b (p : ℝ×E)=>⟪sourceRieszStoppedGradient (t a) (f a) p.1 p.2,
    sourceRieszStoppedGradient (t b) (f b) p.1 p.2⟫
  have hQm (a b : Fin k) : Measurable (Q a b) :=
    (measurable_sourceRieszStoppedGradient (t a) (f a) (hf a)).inner
      (measurable_sourceRieszStoppedGradient (t b) (f b) (hf b))
  have hQb (a b : Fin k) (r : ℝ) (z : E) : |Q a b (r,z)|≤(Gmax:ℝ)^2 := by
    apply (abs_real_inner_le_norm _ _).trans
    simpa only [pow_two] using mul_le_mul
      (norm_sourceRieszStoppedGradient_le (t a) (f a) Gmax (hfB a) r z)
      (norm_sourceRieszStoppedGradient_le (t b) (f b) Gmax (hfB b) r z)
      (norm_nonneg _) Gmax.coe_nonneg
  let P := fun a b r ω=>sourceLogDynamicEmpiricalDifference (ρ r) (fun z=>Q a b (r,z)) N (X r ω)
  have h0 : (0:ℝ)∈Icc 0 T := ⟨le_rfl,hT⟩
  letI := hprob 0 h0
  have hpair (r : ℝ) (hr : r∈Icc 0 T) (a b : Fin k) :
      Integrable (fun z=>Q a b (r,z)) (gaussianRieszDensityMeasure (ρ r)) ∧
      Integrable (P a b r) ν ∧ (∫ ω,|P a b r ω| ∂ν)≤Dl/Real.sqrt N := by
    letI := hprob r hr
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨_,_,_,hlinear⟩ := hfactory N hN (ρ 0) (ρ r) (hρ 0 h0) (hρ r hr)
      (hp 0 h0) (hp r hr) (hI r hr) (ν.map (X r)) (A r) (B r)
      (hA r hr) (hAA r hr) (hB r hr) hlow (hcap r hr) (hcap₂ r hr) (hE r hr)
    let q := fun z=>Q a b (r,z)
    have hlo : BddBelow (range q) := ⟨-((Gmax:ℝ)^2),by
      rintro y ⟨z,rfl⟩;exact (abs_le.mp (hQb a b r z)).1⟩
    have hup : BddAbove (range q) := ⟨(Gmax:ℝ)^2,by
      rintro y ⟨z,rfl⟩;exact (abs_le.mp (hQb a b r z)).2⟩
    have hsup := csSup_le (range_nonempty q) (fun y hy=>by
      rcases hy with ⟨z,rfl⟩;exact (abs_le.mp (hQb a b r z)).2)
    have hinf := le_csInf (range_nonempty q) (fun y hy=>by
      rcases hy with ⟨z,rfl⟩;exact (abs_le.mp (hQb a b r z)).1)
    have hosc : sSup (range q)-sInf (range q)≤2*(Gmax:ℝ)^2 := by linarith
    have hqm : Measurable q := (hQm a b).comp (measurable_const.prodMk measurable_id)
    obtain ⟨hiq,_,hai,hb⟩ := hlinear q hqm hlo hup hosc
    have hi : Integrable (P a b r) ν :=
      (integrable_map_measure hai.aestronglyMeasurable hXr.aemeasurable).mp hai
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    exact ⟨hiq,hi,hb⟩
  let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
  let J := fun r ω=>(2/(β:ℝ))*sourceLogDynamicEmpiricalDifference (ρ r) (S r) N (X r ω)
  have hSm : Measurable (fun p : ℝ×E=>S p.1 p.2) := by
    have heq : (fun p : ℝ×E=>S p.1 p.2)=
        (fun p=>∑ a,∑ b,(θ a*θ b)*Q a b p) :=
      funext fun p=>sourceRieszStoppedGradientNormSq k t θ f p.1 p.2
    rw [heq]
    exact Finset.measurable_sum _ fun a _=>Finset.measurable_sum _ fun b _=>
      (hQm a b).const_mul _
  have hJm : Measurable (Function.uncurry J) :=
    (measurable_sourceRieszEmpiricalDifference_time ρ hρm _ hSm N (Function.uncurry X) hXm).const_mul _
  have hslice (r : ℝ) (hr : r∈Icc 0 T) : Integrable (J r) ν ∧
      (∫ ω,|J r ω| ∂ν)≤((2/(β:ℝ))*Dl)*(∑ a : Fin k,|θ a|)^2/Real.sqrt N := by
    obtain ⟨hi,hb⟩ := sourceRiesz_weighted_finite_L1 ν k θ (fun a b=>P a b r) (Dl/Real.sqrt N)
      (fun a b=>(hpair r hr a b).2.1) (fun a b=>(hpair r hr a b).2.2)
    have heq (ω : Ω) : sourceLogDynamicEmpiricalDifference (ρ r) (S r) N (X r ω)=
        ∑ a,∑ b,(θ a*θ b)*P a b r ω :=
      sourceRieszStopped_square_difference k t θ f r (gaussianRieszDensityMeasure (ρ r))
        N (X r ω) (fun a b=>(hpair r hr a b).1)
    have hdi : Integrable (fun ω=>sourceLogDynamicEmpiricalDifference (ρ r) (S r) N (X r ω)) ν :=
      hi.congr (Filter.Eventually.of_forall fun ω=>(heq ω).symm)
    refine ⟨hdi.const_mul _,?_⟩
    calc
      (∫ ω,|J r ω| ∂ν)=(2/(β:ℝ))*(∫ ω,|∑ a,∑ b,(θ a*θ b)*P a b r ω| ∂ν) := by
        simp only [J,abs_mul,abs_of_pos hc,heq]
        exact integral_const_mul _ _
      _ ≤ (2/(β:ℝ))*((Dl/Real.sqrt N)*(∑ a : Fin k,|θ a|)^2) := mul_le_mul_of_nonneg_left hb hc.le
      _ = _ := by ring
  let η := volume.restrict (Ioc 0 T)
  have hslices : ∀ᵐ r ∂η,Integrable (J r) ν ∧
      (∫ ω,|J r ω| ∂ν)≤((2/(β:ℝ))*Dl)*(∑ a : Fin k,|θ a|)^2/Real.sqrt N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hslice r ⟨hr.1.le,hr.2⟩
  obtain ⟨hi,_,_⟩ := sourceRiesz_time_integral_from_slices η ν J hJm
    (((2/(β:ℝ))*Dl)*(∑ a : Fin k,|θ a|)^2/Real.sqrt N)
    (hslices.mono fun r hr=>hr.1) (hslices.mono fun r hr=>hr.2)
  refine ⟨hJm,hslice,hi,hi.abs.integral_prod_left,?_⟩
  calc
    (∫ r in Ioc 0 T,∫ ω,|J r ω| ∂ν)≤
        ∫ _ : ℝ,((2/(β:ℝ))*Dl)*(∑ a : Fin k,|θ a|)^2/Real.sqrt N ∂η :=
      integral_mono_ae hi.abs.integral_prod_left (integrable_const _) (hslices.mono fun r hr=>hr.2)
    _ = _ := by
      rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hT,sub_zero]
      ring

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_stopped_square_product_replacement
#print axioms DGRHS.Commutator.exists_sourceLog_stopped_square_product_replacement
