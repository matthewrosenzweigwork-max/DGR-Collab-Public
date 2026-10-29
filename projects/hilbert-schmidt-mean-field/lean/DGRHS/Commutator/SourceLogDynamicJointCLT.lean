import DGRHS.Commutator.SourceLogDynamicCharacteristic
import DGRHS.Commutator.SourceLogInitialCovariance
import DGRHS.Dynamics.SourceDynamicLevy

/-! Original logarithmic dynamic joint Gaussian law, source903--912.
Same initial inverse, actual minimum-horizon gradient covariance, constructed
native centered Gaussian and genuine joint weak convergence. Density, paths
and raw noise need joint measurability only on the original horizon. Adapted
from the independently reviewed R63 positive-Riesz assembly, with logarithmic
physical estimates and actual logarithmic initial Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
set_option maxHeartbeats 1000000 in
theorem exists_sourceLog_dynamic_joint_CLT
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (T : ℝ) (hT : 0≤T)
    (hd : 0<(Fintype.card ι:ℝ)) (K Gmax : ℝ≥0) (M : ℝ) (hM : 0≤M)
    (J c Cpart C₂ Amax Bmax : ℝ) (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax)
    (k : ℕ) (t : Fin k→ℝ) (ht : ∀ a,t a∈Icc 0 T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M)
    (hpair : ∀ r∈Icc 0 T,Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r))))
    (hIbg : ∀ r∈Icc 0 T,-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
      (fun x y=>logPhysicalPair (x,y)))
    (f : Fin k→ℝ→E→ℝ) (hf : ∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r))
    (hK : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖iteratedFDeriv ℝ 2 (f a r) z‖≤(K:ℝ))
    (hgrad : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hfB : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ))
    (L : ℝ) (hL : ∀ a,∀ r∈Icc 0 (t a),∀ z,|f a r z|≤L)
    (hback : ∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),∀ z,
      deriv (fun u=>f a u z) r+(β:ℝ)⁻¹*laplacian (f a r) z=
        ∫ y,sourceLogTransportKernel 1 (gradient (f a r)) (z,y)
          ∂gaussianRieszDensityMeasure (ρ r)) :
    let μ := gaussianRieszDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl,hT⟩
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd (ρ 0) M hM (hρ 0 ⟨le_rfl,hT⟩) (hpair 0 ⟨le_rfl,hT⟩)
    ∃ (hφ : ∀ a,MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v,R0 v+(β:ℝ) • integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+(β:ℝ) • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b=>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫+
          sourceDynamicTimeCovariance (β:ℝ) ρ k t f a b
      let P := multivariateGaussian (0:EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a : Fin k,(∫ z,z a ∂P)=0) ∧
      (∀ a b : Fin k,Integrable (fun z=>z a*z b) P ∧ (∫ z,z a*z b ∂P)=C a b) ∧
      ∀ (Ω : ℕ→Type u),∀ [∀ N,MeasurableSpace (Ω N)],
      ∀ (ν : ∀ N,Measure (Ω N)),∀ [∀ N,IsProbabilityMeasure (ν N)],
      ∀ (X : ∀ N,ℝ→Ω N→Fin N→E),(∀ N,Measurable (fun p : Icc (0:ℝ) T×Ω N=>X N p.1 p.2)) →
      (∀ N,1≤N → (ν N).map (X N 0)=sourceLogSingularGibbs β (ρ 0) N) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) →
      (∀ r∈Icc 0 T,G r≤Amax) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ N,1≤N → c≤(sourceLogSingularPartition β (ρ 0) N).toReal) →
      (∀ N,1≤N → ∀ r∈Icc 0 T,(sourceLogSingularPartition β (ρ r) N).toReal≤Cpart) →
      (∀ N,1≤N → ∀ r∈Icc 0 T,(sourceLogSingularPartition
        (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) (ρ r) N).toReal≤C₂) →
      (∀ N,1≤N → ∀ r∈Icc 0 T,
        sourceLogCollisionFreeEnergy β (ρ r) M N ((ν N).map (X N r))≤
          (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
            (sourceLogSingularGibbs β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      ∀ (m : ∀ N,Fin k→ℝ→Ω N→ℝ),
      (∀ N,1≤N → ∀ a,Measurable (fun p : Icc (0:ℝ) T×Ω N=>m N a p.1 p.2)) →
      (∀ N,1≤N → ∀ a,∀ ω,m N a 0 ω=0) →
      (∀ N,1≤N → ∀ a,∀ᵐ ω ∂ν N,
        (∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X N (t a) ω))-
          (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X N 0 ω))=
          (∫ r in Ioc 0 (t a),sourceLogEmpiricalTestDrift (β:ℝ) (f a) N r (X N r ω))+m N a (t a) ω) →
      (∀ a,(∫ z,f a (t a) z ∂gaussianRieszDensityMeasure (ρ (t a)))-
        (∫ z,f a 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 (t a),sourceLogMeanTestDrift (β:ℝ) (f a) r (gaussianRieszDensityMeasure (ρ r))) →
      (∀ (θ : Fin k→ℝ) (N : ℕ),1≤N →
        let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ 0) (f a 0) N (X N 0 ω))
        let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m N a (min r (t a)) ω)
        let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
        let Φ := fun r ω=>sourceRieszFinitePhase (A₀ ω+W r ω)
        let chi := fun r=>∫ ω,Φ r ω ∂ν N
        ∀ r∈Icc 0 T,chi r=chi 0-(1/(β:ℝ):ℝ) •
          (∫ u in 0..r,∫ ω,Φ u ω*((∫ z,S u z ∂sourceRieszLocalEmpiricalLaw N (X N u ω) : ℝ):ℂ) ∂ν N)) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Ω N)=>WithLp.toLp 2 (fun a : Fin k=>
          Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X N (t a) ω)))
        atTop id ν P := by
  letI := hprob 0 ⟨le_rfl,hT⟩
  obtain ⟨hφ,hSym,hCan,R0,hR1,hR2,hcf⟩ := exists_sourceLog_dynamic_characteristic
    β hβ T hT hd K Gmax M hM J c Cpart C₂ Amax Bmax hc hAmax hBmax k t ht ρ hρm hprob hρ hpair hIbg f hf hK hgrad hfB L hL hback
  refine ⟨hφ,hSym,hCan,R0,hR1,hR2,?_⟩
  let C : Matrix (Fin k) (Fin k) ℝ := fun a b=>
    ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫+
      sourceDynamicTimeCovariance (β:ℝ) ρ k t f a b
  obtain ⟨P0,Z0,hP0,hGauss0,hZ0,hMean0,hCov0⟩ := exists_sourceLog_initial_covariance_witness
    k β hd (ρ 0) M hM (hρ 0 ⟨le_rfl,hT⟩) (hpair 0 ⟨le_rfl,hT⟩) hSym hCan R0 hR2
      (fun a=>(hφ a).toLp (f a 0))
  have hC : C.PosSemidef := by
    have hp := sourceDynamic_total_interval_covariance_posSemidef P0 k Z0 hZ0
      T (β:ℝ) hT hβ.le ρ hρm hprob t (fun a=>(ht a).2) f Gmax hgrad hfB
    simpa only [C,fun a b=>(hCov0 a b).2] using hp
  obtain ⟨hP,hG,hMean,hCov,hchar⟩ := sourceDynamic_gaussian_target k C hC
  refine ⟨hC,hP,hG,hMean,hCov,?_⟩
  intro Ω _ ν _ X hXm hLaw G B hGctrl hGA hB hlow hcap hcap₂ hE m hmm hm0 hIto hweak hphase
  let V := fun (N : ℕ) (ω : Ω N)=>WithLp.toLp 2 (fun a : Fin k=>
    Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X N (t a) ω))
  have hV (N : ℕ) : Measurable (V N) := by
    apply (MeasurableEquiv.toLp 2 (Fin k→ℝ)).measurable.comp
    apply Measurable.of_eval
    intro a
    exact (measurable_sourceLog_empirical_fluctuation _ _
      (hf a (t a) ⟨(ht a).1,le_rfl⟩).continuous.measurable N).comp
        ((hXm N).comp ((measurable_const (a:=(⟨t a,ht a⟩ : Icc (0:ℝ) T))).prodMk measurable_id))
  apply sourceDynamic_scalar_characteristic_clt ν k V (fun N=>(hV N).aemeasurable) C hC
  intro θ
  have hh := hcf Ω ν X hXm hLaw G B hGctrl hGA hB hlow hcap hcap₂ hE m hmm hm0 hIto hweak hphase θ
  have hquad := (sourceDynamic_interval_covariance T (β:ℝ) hT hβ.le ρ hρm hprob
    k t (fun a=>(ht a).2) f Gmax hgrad hfB).2 θ
  have hsum : (∑ a,∑ b,θ a*θ b*C a b)=
      (∑ a,∑ b,θ a*θ b*
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫)+
      (2/(β:ℝ))*(∫ r in Ioc 0 T,∫ z,
        ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2 ∂gaussianRieszDensityMeasure (ρ r)) := by
    dsimp only [C]
    simp_rw [mul_add,Finset.sum_add_distrib]
    rw [hquad]
  have hexp : Complex.exp (-(∑ a,∑ b,θ a*θ b*C a b : ℝ)/2)=
      Complex.exp (-(∑ a,∑ b,θ a*θ b*
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ)/2-
        ((1/(β:ℝ))*(∫ r in 0..T,∫ z,
          ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2 ∂gaussianRieszDensityMeasure (ρ r)) : ℝ)) := by
    congr 1
    rw [hsum,intervalIntegral.integral_of_le hT]
    push_cast
    ring
  rw [hexp]
  simpa only [V,WithLp.ofLp_toLp,sourceRieszFinitePhase,mul_comm] using hh

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_dynamic_joint_CLT
#print axioms DGRHS.Commutator.exists_sourceLog_dynamic_joint_CLT
