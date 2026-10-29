import DGRHS.Commutator.SourceLogClassicalEvolution
import DGRHS.Commutator.SourceLogDynamicJointCLT
import DGRHS.Commutator.SourceLogLiteralDynamics
import DGRHS.Commutator.SourceLogLiteralEmpiricalIto
import DGRHS.Commutator.SourceLogCollisionOccupation

/-! Source865--912 logarithmic dynamic CLT with the same selected classical
propagator in both covariance terms. The every-time integrated fixed-Cb2
mean-field class supplies the moving-test equation through the proved static
FTC/moving derivative/absolute-continuity chain. A desired moving identity,
terminal duality, expected phase or Gaussian law is never an input.

The particle input is the literal gradient SDE with its initial LOG Gibbs law.
The source's primitive time-dependent Ito admissibility contains the literal
off-diagonal gradient drift and actual Brownian integrals. Finite free energy
first gives AE-time collision freedom; only then are these primitives
converted to the checked technical force-zero Brownian constructors. No Riesz
potential, Gibbs law or transport kernel at exponent zero is substituted.
This new body requires actual restricted diagnostics and independent review. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceLog_named_Uprop_dynamic_joint_CLT
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (T : ℝ≥0)
    (M J c Cpart C₂ Amax Bmax : ℝ) (hM : 0≤M)
    (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax)
    (k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (hpair : ∀ r∈Icc 0 (T:ℝ),Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r))))
    (hIbg : ∀ r∈Icc 0 (T:ℝ),-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
      (fun x y=>logPhysicalPair (x,y)))
    (hstatic : SourceLogStaticWeakMeanField (β:ℝ) (T:ℝ) ρ)
    (Dtest : Submodule ℝ (E→ℝ))
    (hwp : SourceLogBackwardClassicalWellPosed T (β:ℝ) ρ Dtest)
    (φ : Fin k→E→ℝ) (hφD : ∀ a,φ a∈Dtest) :
    let f := fun a=>sourceLogUprop T (β:ℝ) ρ Dtest hwp (t a) (ht a) (φ a) (hφD a)
    ((∀ a,∀ r∈Icc 0 (t a:ℝ),
      Integrable (f a r) (gaussianRieszDensityMeasure (ρ r)) ∧
      (∀ z,Integrable (fun y=>sourceLogTransportKernel 1 (gradient (f a r)) (z,y))
        (gaussianRieszDensityMeasure (ρ r))) ∧
      Integrable (sourceLogTransportKernel 1 (gradient (f a r)))
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) ∧
    (∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a:ℝ)),
      Integrable (fun z=>deriv (fun u=>f a u z) r+(β:ℝ)⁻¹*laplacian (f a r) z)
        (gaussianRieszDensityMeasure (ρ r)))) ∧
    let μ := gaussianRieszDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl,T.coe_nonneg⟩
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source
      (show 0<(Fintype.card ι:ℝ) from by exact_mod_cast Fintype.card_pos)
      (ρ 0) M hM (hρ 0 ⟨le_rfl,T.coe_nonneg⟩) (hpair 0 ⟨le_rfl,T.coe_nonneg⟩)
    ∃ (hφ : ∀ a,MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v,R0 v+(β:ℝ) • integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+(β:ℝ) • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b=>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫+
          (2/(β:ℝ))*(∫ r in Ioc 0 (min (t a:ℝ) (t b:ℝ)),
            ∫ z,⟪gradient (f a r) z,gradient (f b r) z⟫ ∂gaussianRieszDensityMeasure (ρ r))
      let P := multivariateGaussian (0:EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a:Fin k,(∫ z,z a ∂P)=0) ∧
      (∀ a b:Fin k,Integrable (fun z=>z a*z b) P ∧ (∫ z,z a*z b ∂P)=C a b) ∧
      ∀ (Ω : ℕ→Type u),∀ [∀ N,MeasurableSpace (Ω N)],
      ∀ (ν : ∀ N,Measure (Ω N)),∀ [∀ N,IsProbabilityMeasure (ν N)],
      ∀ (F : ∀ N,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω N))),
      ∀ (X : ∀ N,ℝ→Ω N→Fin N→E)
        (B : ∀ N,(Fin N×ι)→ℝ≥0→Ω N→ℝ),
      (∀ N,1≤N → SourceLogFiniteHorizonWeakSDE (ν N) (F N) T (β:ℝ) N (X N) (B N)) →
      (∀ N,1≤N → SourceLogInitialGibbsBrownianData (ν N) β (ρ 0) N (X N 0) (B N)) →
      ∀ (G D : ℝ→ℝ),(∀ r∈Icc 0 (T:ℝ),0≤G r) →
      (∀ r∈Icc 0 (T:ℝ),G r≤Amax) → (∀ r∈Icc 0 (T:ℝ),D r≤Bmax) →
      (∀ N,1≤N → ∀ r∈Icc 0 (T:ℝ),c≤(sourceLogSingularPartition β (ρ r) N).toReal) →
      (∀ N,1≤N → ∀ r∈Icc 0 (T:ℝ),(sourceLogSingularPartition β (ρ r) N).toReal≤Cpart) →
      (∀ N,1≤N → ∀ r∈Icc 0 (T:ℝ),(sourceLogSingularPartition
        (⟨2*(β:ℝ),by positivity⟩:ℝ≥0) (ρ r) N).toReal≤C₂) →
      (∀ N,1≤N → ∀ r∈Icc 0 (T:ℝ),
        sourceLogCollisionFreeEnergy β (ρ r) M N ((ν N).map (X N r))≤
          (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
            (sourceLogSingularGibbs β (ρ 0) N)+(D r/(N:ℝ):ℝ)) →
      (∀ Gmax:ℝ≥0,
        (∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ)) →
        ∀ N,1≤N → SourceLogLiteralPhysicalItoAdmissibility (ν N) (F N) T
          (β:ℝ) N k t (ρ 0) f Gmax (X N) (B N)) →
      (∀ N,1≤N → ∀ᵐ ω ∂ν N,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
        ∀ i j:Fin N,i≠j → X N r ω i≠X N r ω j) ∧
      TendstoInDistribution
        (fun (N:ℕ) (ω:Ω N)=>WithLp.toLp 2 (fun a:Fin k=>
          Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (φ a) N (X N (t a) ω)))
        atTop id ν P := by
  classical
  let f := fun a=>sourceLogUprop T (β:ℝ) ρ Dtest hwp (t a) (ht a) (φ a) (hφD a)
  have hsol (a:Fin k) : SourceLogClassicalBackwardSolution (β:ℝ) ρ (t a) (φ a) (f a) :=
    (sourceLogUprop_spec T (β:ℝ) ρ Dtest hwp (t a) (ht a) (φ a) (hφD a)).1
  have hproper (a:Fin k) := SourceLogClassicalBackwardSolution.spatial_properness
    (β:ℝ) (t a) ρ (fun r hr=>hprob r ⟨hr.1,hr.2.trans (ht a)⟩) (φ a) (f a) (hsol a)
  refine ⟨⟨fun a=>(hproper a).1,fun a=>(hproper a).2⟩,?_⟩
  obtain ⟨C,hC,hbound⟩ := sourceLogClassicalBackwardSolution_finite_bounds (β:ℝ) ρ k t φ f hsol
  let K : ℝ≥0 := ⟨C,hC⟩
  have hgradBound : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(K:ℝ) :=
    fun a r hr z=>(hbound a r hr z).2.1
  have hd : 0<(Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  letI := hprob 0 ⟨le_rfl,T.coe_nonneg⟩
  obtain ⟨hφ,hSym,hCan,R0,hR1,hR2,hPSD,hP,hGauss,hMean,hCov,huse⟩ :=
    exists_sourceLog_dynamic_joint_CLT β hβ (T:ℝ) T.coe_nonneg hd K K M hM
      J c Cpart C₂ Amax Bmax hc hAmax hBmax k (fun a=>(t a:ℝ))
      (fun a=>⟨(t a).coe_nonneg,ht a⟩) ρ hρm hprob hρ hpair hIbg f
      (fun a=>(hsol a).spatial_contdiff) (fun a r hr z=>(hbound a r hr z).2.2)
      (fun a=>(hsol a).gradient_continuous) hgradBound C (fun a r hr z=>(hbound a r hr z).1)
      (fun a=>(hsol a).backward_ae (β:ℝ) ρ (t a) (φ a) (f a))
  refine ⟨hφ,hSym,hCan,R0,hR1,hR2,hPSD,hP,hGauss,hMean,hCov,?_⟩
  intro Ω _ ν _ F X B hSDE hInitial G D hG hGA hD hlow hcap hcap₂ hE hIto
  have hcollision (N:ℕ) (hN:1≤N) := sourceLog_gronwall_particle_collision_time
    (ν N) T β M hβ hd hM N hN ρ (X N) (hSDE N hN).measurable_on_horizon
      hprob hρ hpair G D (hE N hN)
  refine ⟨hcollision,?_⟩
  let Xe := fun N=>sourceRieszParticleRealHorizonExtension T N (X N)
  have he (N:ℕ) (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) : Xe N r=X N r :=
    sourceRieszParticleRealHorizonExtension_eq T N (X N) r hr
  have hXem (N:ℕ) : Measurable (Function.uncurry (Xe N)) := by
    by_cases hN : 1≤N
    · exact sourceRieszParticleRealHorizonExtension_measurable T N (X N)
        (hSDE N hN).measurable_on_horizon
    · have hN0 : N=0 := by omega
      subst N
      apply Measurable.of_eval
      intro i
      exact Fin.elim0 i
  have hLaw (N:ℕ) (hN:1≤N) : (ν N).map (Xe N 0)=sourceLogSingularGibbs β (ρ 0) N := by
    rw [he N 0 ⟨le_rfl,T.coe_nonneg⟩]
    exact (hInitial N hN).initial_gibbs
  have hEe (N:ℕ) (hN:1≤N) (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) :
      sourceLogCollisionFreeEnergy β (ρ r) M N ((ν N).map (Xe N r))≤
        (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(D r/(N:ℝ):ℝ) := by
    simpa only [he N r hr] using hE N hN r hr
  have hf0 (a:Fin k) : Measurable (f a 0) :=
    ((hsol a).spatial_contdiff 0 ⟨le_rfl,(t a).coe_nonneg⟩).continuous.measurable
  have hex (n:{N:ℕ // 1≤N}) := exists_sourceLog_source_fixed_martingale_inputs
    (ν n.1) (F n.1) T (β:ℝ) hβ n.1 k (Nat.succ_le_iff.mp n.2) t ht (ρ 0) f hf0
    (fun a=>(hsol a).gradient_continuous) K hgradBound (Xe n.1) (B n.1)
    (SourceRieszFiniteHorizonWeakSDE.extended (ν n.1) (F n.1) T 0 (β:ℝ) n.1
      (X n.1) (B n.1) ((hSDE n.1 n.2).to_zero (ν n.1) (F n.1) T (β:ℝ)
        n.1 (X n.1) (B n.1) (hcollision n.1 n.2)))
    (SourceLogPhysicalItoAdmissibility.horizon_extension (ν n.1) (F n.1) T (β:ℝ)
      n.1 k t ht (ρ 0) f K (X n.1) (B n.1)
      (SourceLogLiteralPhysicalItoAdmissibility.to_physical (ν n.1) (F n.1) T (β:ℝ)
        n.1 k t ht (ρ 0) f K (X n.1) (B n.1)
        (hIto K hgradBound n.1 n.2) (hcollision n.1 n.2)))
  choose m hmm hm0 hmc hMart hLp hEmp hPhase using hex
  let mAll := fun (N:ℕ)=>if hN:1≤N then m ⟨N,hN⟩ else fun (_:Fin k) (_:ℝ) (_:Ω N)=>(0:ℝ)
  have hweak (a:Fin k) := (SourceLogMeanFieldTestEvolution.time_test_identity
    (β:ℝ) (t a:ℝ) (t a).coe_nonneg ρ (f a)
    (hstatic.classical_test_evolution (β:ℝ) (T:ℝ) T.coe_nonneg ρ hprob M hM hρ
      (t a) (ht a) (φ a) (f a) (hsol a))).2
  have hlim := huse Ω ν Xe
    (fun N=>(hXem N).comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)) hLaw G D hG hGA hD
    (fun N hN=>hlow N hN 0 ⟨le_rfl,T.coe_nonneg⟩) hcap hcap₂ hEe mAll
    (fun N hN a=>by
      simpa only [mAll,dif_pos hN,Function.comp_def,Function.uncurry] using
        (hmm ⟨N,hN⟩ a).comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    (fun N hN a ω=>by simpa only [mAll,dif_pos hN] using hm0 ⟨N,hN⟩ a ω)
    (fun N hN a=>by
      simpa only [mAll,dif_pos hN,sourceRieszLocalEmpiricalLaw_eq_transport] using hEmp ⟨N,hN⟩ a)
    hweak
    (fun θ N hN=>by
      simpa only [mAll,dif_pos hN,sourceRieszEmpiricalStoppedSquare,
        sourceRieszLocalEmpiricalLaw_eq_transport] using hPhase ⟨N,hN⟩ θ)
  have hobs : (fun (N:ℕ) (ω:Ω N)=>WithLp.toLp 2 (fun a:Fin k=>
      Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (Xe N (t a) ω)))=
      (fun (N:ℕ) (ω:Ω N)=>WithLp.toLp 2 (fun a:Fin k=>
        Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ (t a)) (φ a) N (X N (t a) ω))) := by
    funext N ω
    congr 1
    funext a
    rw [he N (t a) ⟨(t a).coe_nonneg,ht a⟩,(hsol a).terminal]
  rw [hobs] at hlim
  exact hlim

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.exists_sourceLog_named_Uprop_dynamic_joint_CLT
#print axioms DGRHS.Commutator.exists_sourceLog_named_Uprop_dynamic_joint_CLT
