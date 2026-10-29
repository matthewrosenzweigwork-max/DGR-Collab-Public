import DGRHS.Commutator.SourceRieszDynamicCharacteristicInterval
import DGRHS.Commutator.SourceRieszInitialCovariance
import DGRHS.Dynamics.SourceDynamicLevy

/-! Original source903--912 finite-dimensional dynamic Gaussian law.
The physical scalar characteristic limit is proved by the preceding interval
endpoint. The static witness has the SAME original inverse by uniqueness;
its proper second moments and the actual stopped-gradient covariance imply
PSD. Native multivariateGaussian and Levy construct and identify the actual
joint weak limit. No desired limit, covariance positivity, Gaussian law or
independence of the initial fluctuation and terminal noise is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_dynamic_joint_CLT
    (s β T M Bmax : ℝ) (hs : 0<s) (hβ : 0<β) (hT : 0≤T)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K Gmax : ℝ≥0)
    (k : ℕ) (t : Fin k→ℝ) (ht : ∀ a,t a∈Icc 0 T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M)
    (f : Fin k→ℝ→E→ℝ) (hf : ∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r))
    (hK : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖iteratedFDeriv ℝ 2 (f a r) z‖≤(K:ℝ))
    (hgrad : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hfB : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ))
    (L : ℝ) (hL : ∀ a,∀ r∈Icc 0 (t a),∀ z,|f a r z|≤L)
    (hback : ∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),∀ z,
      deriv (fun u=>f a u z) r+β⁻¹*laplacian (f a r) z=
        ∫ y,⟪sourceRieszForce s (z-y),gradient (f a r) z-gradient (f a r) y⟫
          ∂gaussianRieszDensityMeasure (ρ r)) :
    let μ := gaussianRieszDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl,hT⟩
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let hh := memLp_gaussianRieszCenteredPhysicalPair s hs (by linarith) (ρ 0) M hM (hρ 0 ⟨le_rfl,hT⟩)
    ∃ (hφ : ∀ a,MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v,R0 v+β • integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+β • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b=>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫+
          sourceDynamicTimeCovariance β ρ k t f a b
      let P := multivariateGaussian (0:EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a : Fin k,(∫ z,z a ∂P)=0) ∧
      (∀ a b : Fin k,Integrable (fun z=>z a*z b) P ∧ (∫ z,z a*z b ∂P)=C a b) ∧
      ∀ (Ω : ℕ→Type u),∀ [∀ N,MeasurableSpace (Ω N)],
      ∀ (ν : ∀ N,Measure (Ω N)),∀ [∀ N,IsProbabilityMeasure (ν N)],
      ∀ (X : ∀ N,ℝ→Ω N→Fin N→E),(∀ N,Measurable (Function.uncurry (X N))) →
      (∀ N,1≤N → (ν N).map (X N 0)=sourceRieszSingularGibbs s β (ρ 0) N) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ N,1≤N → ∀ r∈Icc 0 T,
        sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N ((ν N).map (X N r))≤
          (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
            (sourceRieszSingularGibbs s β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      ∀ (m : ∀ N,Fin k→ℝ→Ω N→ℝ),
      (∀ N,1≤N → ∀ a,Measurable (Function.uncurry (m N a))) →
      (∀ N,1≤N → ∀ a,∀ ω,m N a 0 ω=0) →
      (∀ N,1≤N → ∀ a,∀ᵐ ω ∂ν N,
        (∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X N (t a) ω))-
          (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X N 0 ω))=
          (∫ r in Ioc 0 (t a),sourceRieszEmpiricalTestDrift s β (f a) N r (X N r ω))+m N a (t a) ω) →
      (∀ a,(∫ z,f a (t a) z ∂gaussianRieszDensityMeasure (ρ (t a)))-
        (∫ z,f a 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 (t a),sourceRieszMeanTestDrift s β (ρ r) (f a) r) →
      (∀ (θ : Fin k→ℝ) (N : ℕ),1≤N →
        let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f a 0) N (X N 0 ω))
        let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m N a (min r (t a)) ω)
        let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
        let Φ := fun r ω=>sourceRieszFinitePhase (A₀ ω+W r ω)
        let chi := fun r=>∫ ω,Φ r ω ∂ν N
        ∀ r∈Icc 0 T,chi r=chi 0-(1/β:ℝ) •
          (∫ u in 0..r,∫ ω,Φ u ω*((∫ z,S u z ∂sourceRieszLocalEmpiricalLaw N (X N u ω) : ℝ):ℂ) ∂ν N)) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Ω N)=>WithLp.toLp 2 (fun a : Fin k=>
          Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X N (t a) ω)))
        atTop id ν P := by
  letI := hprob 0 ⟨le_rfl,hT⟩
  obtain ⟨hφ,hSym,hCan,R0,hR1,hR2,hcf⟩ := exists_sourceRiesz_dynamic_characteristic_interval
    s β T M Bmax hs hβ hT hd hM hBmax K Gmax k t ht ρ hρm hprob hρ f hf hK hgrad hfB L hL hback
  refine ⟨hφ,hSym,hCan,R0,hR1,hR2,?_⟩
  let C : Matrix (Fin k) (Fin k) ℝ := fun a b=>
    ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫+
      sourceDynamicTimeCovariance β ρ k t f a b
  obtain ⟨P0,Z0,hP0,hGauss0,hZ0,hMean0,hCov0⟩ := exists_sourceRiesz_initial_covariance_witness
    k s β hs hβ.le (by linarith) (ρ 0) M hM (hρ 0 ⟨le_rfl,hT⟩) hSym hCan R0 hR2
      (fun a=>(hφ a).toLp (f a 0))
  have hC : C.PosSemidef := by
    have hp := sourceDynamic_total_interval_covariance_posSemidef P0 k Z0 hZ0
      T β hT hβ.le ρ hρm hprob t (fun a=>(ht a).2) f Gmax hgrad hfB
    simpa only [C,fun a b=>(hCov0 a b).2] using hp
  obtain ⟨hP,hG,hMean,hCov,hchar⟩ := sourceDynamic_gaussian_target k C hC
  refine ⟨hC,hP,hG,hMean,hCov,?_⟩
  intro Ω _ ν _ X hXm hLaw G B hGctrl hB hE m hmm hm0 hIto hweak hphase
  let V := fun (N : ℕ) (ω : Ω N)=>WithLp.toLp 2 (fun a : Fin k=>
    Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X N (t a) ω))
  have hV (N : ℕ) : Measurable (V N) := by
    apply (MeasurableEquiv.toLp 2 (Fin k→ℝ)).measurable.comp
    apply Measurable.of_eval
    intro a
    exact (measurable_sourceRiesz_empirical_fluctuation _ _
      (hf a (t a) ⟨(ht a).1,le_rfl⟩).continuous.measurable N).comp
        ((hXm N).comp (measurable_const.prodMk measurable_id))
  apply sourceDynamic_scalar_characteristic_clt ν k V (fun N=>(hV N).aemeasurable) C hC
  intro θ
  have hh := hcf Ω ν X hXm hLaw G B hGctrl hB hE m hmm hm0 hIto hweak hphase θ
  have hquad := (sourceDynamic_interval_covariance T β hT hβ.le ρ hρm hprob
    k t (fun a=>(ht a).2) f Gmax hgrad hfB).2 θ
  have hsum : (∑ a,∑ b,θ a*θ b*C a b)=
      (∑ a,∑ b,θ a*θ b*
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫)+
      (2/β)*(∫ r in Ioc 0 T,∫ z,
        ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2 ∂gaussianRieszDensityMeasure (ρ r)) := by
    dsimp only [C]
    simp_rw [mul_add,Finset.sum_add_distrib]
    rw [hquad]
  have hexp : Complex.exp (-(∑ a,∑ b,θ a*θ b*C a b : ℝ)/2)=
      Complex.exp (-(∑ a,∑ b,θ a*θ b*
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ)/2-
        ((1/β)*(∫ r in 0..T,∫ z,
          ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2 ∂gaussianRieszDensityMeasure (ρ r)) : ℝ)) := by
    congr 1
    rw [hsum,intervalIntegral.integral_of_le hT]
    push_cast
    ring
  rw [hexp]
  simpa only [V,WithLp.ofLp_toLp,sourceRieszFinitePhase,mul_comm] using hh

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceRiesz_dynamic_joint_CLT
#print axioms DGRHS.Commutator.exists_sourceRiesz_dynamic_joint_CLT
