import DGRHS.Commutator.SourceLogFiniteTerminal
import DGRHS.Commutator.SourceLogPhysicalFiniteCFInterval

/-! Original logarithmic source3933--4015 finite-N characteristic comparison.
Adapted from the exact independently reviewed R62 positive-Riesz assembly,
using original logarithmic physical factories and horizon-only measurability. The same
weighted stopped raw noise process appears in primitive particle Ito and in
the primitive finite phase Ito formula. Its zero initial value identifies
chi(0) with the actual initial fluctuation. No independence between the
initial fluctuation and terminal noise, factorization or CF limit is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal ENNReal RealInnerProductSpace BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceLog_finite_terminal_CF_comparison
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K Gmax : ℝ≥0) (M : ℝ) (hM : 0≤M)
    (J c C C₂ Amax Bmax : ℝ) (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) :
    ∃ Dc Dl : ℝ,0≤Dc ∧ 0≤Dl ∧ ∀ (T : ℝ),0≤T → ∀ (k : ℕ) (t θ : Fin k→ℝ),
      (∀ a,t a∈Icc 0 T) → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      (∀ r∈Icc 0 T,Integrable logPhysicalPair
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) →
      (∀ r∈Icc 0 T,-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
        (fun x y=>logPhysicalPair (x,y))) →
      ∀ (f : Fin k→ℝ→E→ℝ),(∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r)) →
      (∀ a,∀ r∈Icc 0 (t a),∀ z,‖iteratedFDeriv ℝ 2 (f a r) z‖≤(K:ℝ)) →
      (∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ)) →
      (∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ)) →
      ∀ (L : ℝ),(∀ a,∀ r∈Icc 0 (t a),∀ z,|f a r z|≤L) →
      (∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),∀ z,
        deriv (fun u=>f a u z) r+(β:ℝ)⁻¹*laplacian (f a r) z=
          ∫ y,sourceLogTransportKernel 1 (gradient (f a r)) (z,y)
            ∂gaussianRieszDensityMeasure (ρ r)) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (fun p : Icc (0:ℝ) T×Ω=>X p.1 p.2) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) →
      (∀ r∈Icc 0 T,G r≤Amax) → (∀ r∈Icc 0 T,B r≤Bmax) →
      c≤(sourceLogSingularPartition β (ρ 0) N).toReal →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition β (ρ r) N).toReal≤C) →
      (∀ r∈Icc 0 T,(sourceLogSingularPartition (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) (ρ r) N).toReal≤C₂) →
      (∀ r∈Icc 0 T,sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      ∀ (m : Fin k→ℝ→Ω→ℝ),(∀ a,Measurable (fun p : Icc (0:ℝ) T×Ω=>m a p.1 p.2)) →
      (∀ a,∀ ω,m a 0 ω=0) →
      (∀ a,∀ᵐ ω ∂ν,(∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω))-
        (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω))=
        (∫ r in Ioc 0 (t a),sourceLogEmpiricalTestDrift (β:ℝ) (f a) N r (X r ω))+m a (t a) ω) →
      (∀ a,(∫ z,f a (t a) z ∂gaussianRieszDensityMeasure (ρ (t a)))-
        (∫ z,f a 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 (t a),sourceLogMeanTestDrift (β:ℝ) (f a) r (gaussianRieszDensityMeasure (ρ r))) →
      let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω))
      let Z := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X (t a) ω))
      let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m a (min r (t a)) ω)
      let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      let Φ := fun r ω=>sourceRieszFinitePhase (A₀ ω+W r ω)
      let chi := fun r=>∫ ω,Φ r ω ∂ν
      (∀ r∈Icc 0 T,chi r=chi 0-(1/(β:ℝ):ℝ) •
        (∫ u in 0..r,∫ ω,Φ u ω*((∫ z,S u z ∂sourceRieszLocalEmpiricalLaw N (X u ω) : ℝ):ℂ) ∂ν)) →
      ‖(∫ ω,sourceRieszFinitePhase (Z ω) ∂ν)-
        (∫ ω,sourceRieszFinitePhase (A₀ ω) ∂ν)*
          (Real.exp (-(1/(β:ℝ))*(∫ r in 0..T,∫ z,S r z ∂gaussianRieszDensityMeasure (ρ r))):ℂ)‖≤
        T*Dc*(∑ a,|θ a|)/(2*Real.sqrt N)+
          Real.exp ((((Gmax:ℝ)*(∑ a,|θ a|))^2/(β:ℝ))*T)*
            (T*Dl*(∑ a,|θ a|)^2/Real.sqrt N) := by
  obtain ⟨Dc,hDc,hterminal⟩ := exists_sourceLog_finite_terminal_representation
    (ι:=ι) β hβ hd K M hM J c C Amax Bmax hc hAmax hBmax
  obtain ⟨Dl,hDl,hcf⟩ := exists_sourceLog_interval_physical_finite_Ito_comparison
    (ι:=ι) β hβ hd M hM J c C C₂ Amax Bmax hc hAmax hBmax Gmax
  refine ⟨Dc,Dl,hDc,hDl,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hp hI f hf hK hgrad hfB L hL hback
    X hXm G B hG hGA hB hlow hcap hcap₂ hE m hmm hm0 hIto hweak
  dsimp only
  intro hphase
  let R := fun ω=>∑ a,θ a*(-((Real.sqrt N/2)*(∫ r in Ioc 0 (t a),
    sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r)) (sourceLogTransportKernel 1 (gradient (f a r))) N (X r ω))))
  let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω))
  let Z := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X (t a) ω))
  let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m a (min r (t a)) ω)
  let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
  obtain ⟨hA₀,hZ,hRm,hRi,hRb,hrep⟩ := hterminal T hT k t θ ht N hN Ω ν
    ρ hρm hprob hρ hp hI f hf hK hgrad L hL hback X hXm G B hG hGA hB hlow hcap hE
    (fun a=>m a (t a)) hIto hweak
  have hWm : Measurable (fun p : Icc (0:ℝ) T×Ω=>W p.1 p.2) := by
    apply Finset.measurable_sum
    intro a _
    let rstop := fun p : Icc (0:ℝ) T×Ω=>(⟨min (p.1:ℝ) (t a),
      ⟨le_min p.1.property.1 (ht a).1,(min_le_left _ _).trans p.1.property.2⟩⟩ : Icc (0:ℝ) T)
    have hm : Measurable rstop :=
      ((measurable_subtype_coe.comp measurable_fst).min measurable_const).subtype_mk
    exact (((hmm a).comp (hm.prodMk measurable_snd)).const_mul _).const_mul _
  have hWT (ω : Ω) : W T ω=∑ a,θ a*(Real.sqrt N*m a (t a) ω) := by
    dsimp only [W]
    apply Finset.sum_congr rfl
    intro a _
    rw [min_eq_right (ht a).2]
  have hW0 (ω : Ω) : W 0 ω=0 := by
    dsimp only [W]
    have hh (a : Fin k) : min 0 (t a)=0 := min_eq_left (ht a).1
    simp only [hh,hm0,mul_zero,Finset.sum_const_zero]
  have hcomp := hcf T hT k t θ ht N hN Ω ν ρ hρm hprob hρ hp hI f hf hgrad hfB
    X hXm G B hG hGA hB hlow hcap hcap₂ hE A₀ hA₀ W hWm hphase
  simp only [hW0,add_zero] at hcomp
  have hY : Measurable (fun ω=>A₀ ω+W T ω) :=
    hA₀.add (hWm.comp ((measurable_const (a:=(⟨T,⟨hT,le_rfl⟩⟩ : Icc (0:ℝ) T))).prodMk measurable_id))
  obtain ⟨_,_,hpert⟩ := sourceRiesz_terminal_phase_expectation ν (fun ω=>A₀ ω+W T ω) R hY hRm hRi
  have he : (∫ ω,sourceRieszFinitePhase (Z ω) ∂ν)=
      ∫ ω,sourceRieszFinitePhase (A₀ ω+W T ω+R ω) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hrep] with ω hω
    exact congrArg sourceRieszFinitePhase (hω.trans (by rw [hWT]))
  calc
    _ ≤ ‖(∫ ω,sourceRieszFinitePhase (Z ω) ∂ν)-
        (∫ ω,sourceRieszFinitePhase (A₀ ω+W T ω) ∂ν)‖+
      ‖(∫ ω,sourceRieszFinitePhase (A₀ ω+W T ω) ∂ν)-
        (∫ ω,sourceRieszFinitePhase (A₀ ω) ∂ν)*
          (Real.exp (-(1/(β:ℝ))*(∫ r in 0..T,∫ z,S r z ∂gaussianRieszDensityMeasure (ρ r))):ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (by rw [he];exact hpert.trans hRb) hcomp

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_finite_terminal_CF_comparison
#print axioms DGRHS.Commutator.exists_sourceLog_finite_terminal_CF_comparison
