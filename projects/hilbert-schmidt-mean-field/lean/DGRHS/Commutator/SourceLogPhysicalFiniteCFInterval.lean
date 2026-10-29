import DGRHS.Commutator.SourceLogPhysicalFiniteCF
import Mathlib.Topology.Order.ProjIcc

/-! The physical logarithmic finite characteristic comparison on its original
closed horizon. Only measurable density, paths and phase are extended; the
native tests and their derivatives remain unchanged. The primitive finite
phase Ito identity transfers by equality on every integration interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
set_option maxHeartbeats 1000000 in
theorem exists_sourceLog_interval_physical_finite_Ito_comparison
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (M : ℝ) (hM : 0≤M) (J c C C₂ Amax Bmax : ℝ)
    (hc₀ : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) (Gmax : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (k : ℕ) (t θ : Fin k→ℝ),
      (∀ a,t a∈Icc 0 T) → ∀ (N : ℕ),1≤N → ∀ (Ω : Type u),∀ [MeasurableSpace Ω],
      ∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2) →
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
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (fun p : Icc (0:ℝ) T×Ω=>X p.1 p.2) →
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
      let H := fun r ω=>∫ z,S r z ∂sourceRieszLocalEmpiricalLaw N (X r ω)
      let m := fun r=>∫ z,S r z ∂gaussianRieszDensityMeasure (ρ r)
      ∀ (A₀ : Ω→ℝ),Measurable A₀ → ∀ (M₀ : ℝ→Ω→ℝ),
      Measurable (fun p : Icc (0:ℝ) T×Ω=>M₀ p.1 p.2) →
      let Φ := fun r ω=>sourceRieszFinitePhase (A₀ ω+M₀ r ω)
      let chi := fun r=>∫ ω,Φ r ω ∂ν
      (∀ r∈Icc 0 T,chi r=chi 0-(1/(β:ℝ):ℝ) •
        (∫ u in 0..r,∫ ω,Φ u ω*(H u ω:ℂ) ∂ν)) →
      ‖chi T-chi 0*(Real.exp (-(1/(β:ℝ))*(∫ r in 0..T,m r)):ℂ)‖≤
        Real.exp ((((Gmax:ℝ)*(∑ a : Fin k,|θ a|))^2/(β:ℝ))*T)*
          (T*D*(∑ a : Fin k,|θ a|)^2/Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceLog_physical_finite_Ito_comparison
    (ι:=ι) β hβ hd M hM J c C C₂ Amax Bmax hc₀ hAmax hBmax Gmax
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hp hI f hfreg hf hfB X hXm A B hA hAA hB hlow hcap hcap₂ hE
  dsimp only
  intro A₀ hA₀ M₀ hM₀ hIto
  let ρe := fun r=>ρ (projIcc 0 T hT r)
  let Xe := fun r=>X (projIcc 0 T hT r)
  let Me := fun r=>M₀ (projIcc 0 T hT r)
  have hρeq (r : ℝ) (hr : r∈Icc 0 T) : ρe r=ρ r := by
    dsimp only [ρe];rw [projIcc_of_mem hT hr]
  have hXeq (r : ℝ) (hr : r∈Icc 0 T) : Xe r=X r := by
    dsimp only [Xe];rw [projIcc_of_mem hT hr]
  have hMeq (r : ℝ) (hr : r∈Icc 0 T) : Me r=M₀ r := by
    dsimp only [Me];rw [projIcc_of_mem hT hr]
  have hρem : Measurable (Function.uncurry ρe) := hρm.comp
    (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hXem : Measurable (Function.uncurry Xe) := hXm.comp
    (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hMem : Measurable (Function.uncurry Me) := hM₀.comp
    (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hz : (0:ℝ)∈Icc 0 T := ⟨le_rfl,hT⟩
  have htT : T∈Icc 0 T := ⟨hT,le_rfl⟩
  have hItoE : ∀ r∈Icc 0 T,
      (∫ ω,sourceRieszFinitePhase (A₀ ω+Me r ω) ∂ν)=
      (∫ ω,sourceRieszFinitePhase (A₀ ω+Me 0 ω) ∂ν)-(1/(β:ℝ):ℝ) •
        (∫ u in 0..r,∫ ω,sourceRieszFinitePhase (A₀ ω+Me u ω)*
          ((∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) u z‖^2
            ∂sourceRieszLocalEmpiricalLaw N (Xe u ω) : ℝ):ℂ) ∂ν) := by
    intro r hr
    have heq : (∫ u in 0..r,∫ ω,sourceRieszFinitePhase (A₀ ω+Me u ω)*
          ((∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) u z‖^2
            ∂sourceRieszLocalEmpiricalLaw N (Xe u ω) : ℝ):ℂ) ∂ν)=
        (∫ u in 0..r,∫ ω,sourceRieszFinitePhase (A₀ ω+M₀ u ω)*
          ((∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) u z‖^2
            ∂sourceRieszLocalEmpiricalLaw N (X u ω) : ℝ):ℂ) ∂ν) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hr.1] at hu
      have huT : u∈Icc 0 T := ⟨hu.1,hu.2.trans hr.2⟩
      dsimp only
      rw [hMeq u huT,hXeq u huT]
    simpa only [hMeq r hr,hMeq 0 hz,heq] using hIto r hr
  have hb := hfactory T hT k t θ ht N hN Ω ν ρe hρem
    (fun r hr=>by simpa only [hρeq r hr] using hprob r hr)
    (fun r hr=>by simpa only [hρeq r hr] using hρ r hr)
    (fun r hr=>by simpa only [hρeq r hr] using hp r hr)
    (fun r hr=>by simpa only [hρeq r hr] using hI r hr)
    f hfreg hf hfB Xe hXem A B hA hAA hB
    (by simpa only [hρeq 0 hz] using hlow)
    (fun r hr=>by simpa only [hρeq r hr] using hcap r hr)
    (fun r hr=>by simpa only [hρeq r hr] using hcap₂ r hr)
    (fun r hr=>by simpa only [hρeq r hr,hρeq 0 hz,hXeq r hr] using hE r hr)
    A₀ hA₀ Me hMem hItoE
  have heq : (∫ r in 0..T,∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      ∂gaussianRieszDensityMeasure (ρe r))=
      (∫ r in 0..T,∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      ∂gaussianRieszDensityMeasure (ρ r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hT] at hr
    dsimp only
    rw [hρeq r hr]
  simpa only [hMeq T htT,hMeq 0 hz,heq] using hb

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_interval_physical_finite_Ito_comparison
#print axioms DGRHS.Commutator.exists_sourceLog_interval_physical_finite_Ito_comparison
