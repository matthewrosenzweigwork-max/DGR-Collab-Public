import DGRHS.Dynamics.SourceLogPhysicalAdjointIdentity
import DGRHS.Commutator.SourceLogInitialCharacteristic
import DGRHS.Commutator.SourceRieszFiniteTerminal

/-! Original logarithmic finite-family terminal representation on the actual
individual horizons. The common physical remainder constant is chosen before
all times, tests, coefficients, particle counts and processes. Adapted finite
sum argument from author B, whose exact R62 semantic review is recorded. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal ENNReal RealInnerProductSpace BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
set_option maxHeartbeats 1000000 in
theorem exists_sourceLog_finite_terminal_representation
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (hd : 0<(Fintype.card ι:ℝ))
    (K : ℝ≥0) (M : ℝ) (hM : 0≤M)
    (J c C Amax Bmax : ℝ) (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (k : ℕ) (t θ : Fin k→ℝ),
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
      (∀ r∈Icc 0 T,sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      ∀ (m : Fin k→Ω→ℝ),
      (∀ a,∀ᵐ ω ∂ν,(∫ z,f a (t a) z ∂transportEmpiricalLaw N (X (t a) ω))-
        (∫ z,f a 0 z ∂transportEmpiricalLaw N (X 0 ω))=
        (∫ r in Ioc 0 (t a),sourceLogEmpiricalTestDrift (β:ℝ) (f a) N r (X r ω))+m a ω) →
      (∀ a,(∫ z,f a (t a) z ∂gaussianRieszDensityMeasure (ρ (t a)))-
        (∫ z,f a 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 (t a),sourceLogMeanTestDrift (β:ℝ) (f a) r (gaussianRieszDensityMeasure (ρ r))) →
      let R := fun ω=>∑ a,θ a*(-((Real.sqrt N/2)*(∫ r in Ioc 0 (t a),
        sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r)) (sourceLogTransportKernel 1 (gradient (f a r))) N (X r ω))))
      let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω))
      let Z := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X (t a) ω))
      Measurable A₀ ∧ Measurable Z ∧ Measurable R ∧ Integrable R ν ∧
      (∫ ω,|R ω| ∂ν)≤T*D*(∑ a,|θ a|)/(2*Real.sqrt N) ∧
      Z=ᵐ[ν](fun ω=>A₀ ω+(∑ a,θ a*(Real.sqrt N*m a ω))+R ω) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceLog_physical_adjoint_interval_identity
    (ι:=ι) β hβ hd K M hM J c C Amax Bmax hc hAmax hBmax
  refine ⟨D,hD,?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hp hI f hf hK hgrad L hL hback
    X hXm G B hG hGA hB hlow hcap hE m hIto hweak
  let R := fun a ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 (t a),
    sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
      (sourceLogTransportKernel 1 (gradient (f a r))) N (X r ω)))
  have hsub (a : Fin k) {r : ℝ} (hr : r∈Icc 0 (t a)) : r∈Icc 0 T := ⟨hr.1,hr.2.trans (ht a).2⟩
  let inc := fun (a : Fin k) (r : Icc (0:ℝ) (t a))=>(⟨r,hsub a r.property⟩ : Icc (0:ℝ) T)
  have him (a : Fin k) : Measurable (inc a) := measurable_subtype_coe.subtype_mk
  have hsingle (a : Fin k) := hfactory (t a) (ht a).1 N hN Ω ν ρ
    (hρm.comp (((him a).comp measurable_fst).prodMk measurable_snd))
    (fun r hr=>hprob r (hsub a hr)) (fun r hr=>hρ r (hsub a hr))
    (fun r hr=>hp r (hsub a hr)) (fun r hr=>hI r (hsub a hr))
    (f a) (hf a) (hK a)
    ((hgrad a).comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p=>⟨p.1.property,mem_univ _⟩)) L (hL a) (hback a) X
    (hXm.comp (((him a).comp measurable_fst).prodMk measurable_snd))
    G B (fun r hr=>hG r (hsub a hr)) (fun r hr=>hGA r (hsub a hr))
    (fun r hr=>hB r (hsub a hr)) hlow (fun r hr=>hcap r (hsub a hr))
    (fun r hr=>hE r (hsub a hr)) (m a) (hIto a) (hweak a)
  have hRi (a : Fin k) : Integrable (R a) ν := (hsingle a).2.2.2.1
  have hRb (a : Fin k) : (∫ ω,|R a ω| ∂ν)≤T*D/(2*Real.sqrt N) :=
    (hsingle a).2.2.2.2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ht a).2 hD) (by positivity))
  obtain ⟨hi,hb⟩ := sourceRiesz_finite_remainder_L1 ν k θ R (T*D/(2*Real.sqrt N)) hRi hRb
  have hXm' (r : ℝ) (hr : r∈Icc 0 T) : Measurable (X r) :=
    hXm.comp ((measurable_const (a:=(⟨r,hr⟩ : Icc (0:ℝ) T))).prodMk measurable_id)
  refine ⟨?_,?_,?_,hi,by convert hb using 1 <;> ring,?_⟩
  · exact Finset.measurable_sum _ fun a _=>
      ((measurable_sourceLog_empirical_fluctuation (ρ 0) (f a 0)
        (hf a 0 ⟨le_rfl,(ht a).1⟩).continuous.measurable N).comp (hXm' 0 ⟨le_rfl,hT⟩)).const_mul _
  · exact Finset.measurable_sum _ fun a _=>
      ((measurable_sourceLog_empirical_fluctuation (ρ (t a)) (f a (t a))
        (hf a (t a) ⟨(ht a).1,le_rfl⟩).continuous.measurable N).comp (hXm' (t a) (ht a))).const_mul _
  · exact Finset.measurable_sum _ fun a _=>((hsingle a).2.2.1).const_mul _
  · filter_upwards [ae_all_iff.mpr (fun a=>(hsingle a).2.1)] with ω hω
    calc
      _ = ∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ 0) (f a 0) N (X 0 ω)+
          Real.sqrt N*m a ω+R a ω) := Finset.sum_congr rfl fun a _=>congrArg (fun z=>θ a*z) (hω a).2.2
      _ = _ := by simp_rw [mul_add,Finset.sum_add_distrib];rfl

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_finite_terminal_representation
#print axioms DGRHS.Commutator.exists_sourceLog_finite_terminal_representation
