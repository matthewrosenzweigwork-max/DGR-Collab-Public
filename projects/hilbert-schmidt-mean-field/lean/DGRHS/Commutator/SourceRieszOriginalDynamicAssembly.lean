import DGRHS.Commutator.SourceRieszDynamicJointCLT
import DGRHS.Commutator.SourceRieszSourceMartingaleAssembly
import DGRHS.Commutator.SourceRieszMeanFieldTestEvolution
import DGRHS.Commutator.SourceRieszCollisionOccupation

/-! UNCOMPILED source-facing positive-Riesz joint CLT assembly. The primitive
inputs are the finite-horizon additive SDE, literal initial Gibbs/driver data,
the source differential mean-field/backward evolution, and source-authorized
samplewise Itô formulas for the same actual physical integrals. The raw
martingales, terminal time-test formula, expected phase, collision occupation,
and actual Gaussian weak limit are conclusions of the dependency chain.
The terminal observables are the prescribed tests phi; f has their literal
terminal boundary values. The source chooses f as its unique backward solution.
No global particle measurability/adaptedness is added to the original horizon.
This candidate and its new draft imports require restricted compilation and
independent source review; it is not an accepted original export. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_dynamic_joint_CLT_of_source_solutions
    (s β : ℝ) (T : ℝ≥0) (M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K Gmax : ℝ≥0)
    (k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (φ : Fin k→E→ℝ) (f : Fin k→ℝ→E→ℝ) (hterminal : ∀ a,f a (t a)=φ a)
    (hf : ∀ a,∀ r∈Icc 0 (t a:ℝ),ContDiff ℝ 2 (f a r))
    (hK : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖iteratedFDeriv ℝ 2 (f a r) z‖≤(K:ℝ))
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a:ℝ) ×ˢ univ))
    (hfB : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ))
    (L : ℝ) (hL : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,|f a r z|≤L)
    (hback : ∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a:ℝ)),∀ z,
      deriv (fun u=>f a u z) r+β⁻¹*laplacian (f a r) z=
        ∫ y,⟪sourceRieszForce s (z-y),gradient (f a r) z-gradient (f a r) y⟫
          ∂gaussianRieszDensityMeasure (ρ r))
    (hmean : ∀ a,SourceRieszMeanFieldTestEvolution s β (t a:ℝ) ρ (f a)) :
    let μ := gaussianRieszDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl,T.coe_nonneg⟩
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let hh := memLp_gaussianRieszCenteredPhysicalPair s hs (by linarith) (ρ 0) M hM
      (hρ 0 ⟨le_rfl,T.coe_nonneg⟩)
    ∃ (hφ : ∀ a,MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v,R0 v+β • integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+β • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b=>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫+
          sourceDynamicTimeCovariance β ρ k (fun a=>(t a:ℝ)) f a b
      let P := multivariateGaussian (0:EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a:Fin k,(∫ z,z a ∂P)=0) ∧
      (∀ a b:Fin k,Integrable (fun z=>z a*z b) P ∧ (∫ z,z a*z b ∂P)=C a b) ∧
      ∀ (Ω : ℕ→Type u),∀ [∀ N,MeasurableSpace (Ω N)],
      ∀ (ν : ∀ N,Measure (Ω N)),∀ [∀ N,IsProbabilityMeasure (ν N)],
      ∀ (F : ∀ N,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω N))),
      ∀ (X : ∀ N,ℝ→Ω N→Fin N→E)
        (B : ∀ N,(Fin N×ι)→ℝ≥0→Ω N→ℝ),
      (∀ N,1≤N → SourceRieszFiniteHorizonWeakSDE (ν N) (F N) T s β N (X N) (B N)) →
      (∀ N,1≤N → SourceRieszInitialGibbsBrownianData (ν N) s β (ρ 0) N (X N 0) (B N)) →
      ∀ (G D : ℝ→ℝ),(∀ r∈Icc 0 (T:ℝ),0≤G r) → (∀ r∈Icc 0 (T:ℝ),D r≤Bmax) →
      (∀ N,1≤N → ∀ r∈Icc 0 (T:ℝ),
        sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N ((ν N).map (X N r))≤
          (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
            (sourceRieszSingularGibbs s β (ρ 0) N)+(D r/(N:ℝ):ℝ)) →
      (∀ N,1≤N → SourceRieszPhysicalItoAdmissibility (ν N) (F N) T s β N k t (ρ 0) f Gmax (X N) (B N)) →
      (∀ N,1≤N → ∀ᵐ ω ∂ν N,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
        ∀ i j:Fin N,i≠j → X N r ω i≠X N r ω j) ∧
      TendstoInDistribution
        (fun (N:ℕ) (ω:Ω N)=>WithLp.toLp 2 (fun a:Fin k=>
          Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (φ a) N (X N (t a) ω)))
        atTop id ν P := by
  classical
  letI := hprob 0 ⟨le_rfl,T.coe_nonneg⟩
  obtain ⟨hφ,hSym,hCan,R0,hR1,hR2,hC,hP,hGauss,hMean,hCov,huse⟩ :=
    exists_sourceRiesz_dynamic_joint_CLT s β (T:ℝ) M Bmax hs hβ T.coe_nonneg hd hM hBmax
      K Gmax k (fun a=>(t a:ℝ)) (fun a=>⟨(t a).coe_nonneg,ht a⟩)
      ρ hρm hprob hρ f hf hK hgrad hfB L hL hback
  refine ⟨hφ,hSym,hCan,R0,hR1,hR2,hC,hP,hGauss,hMean,hCov,?_⟩
  intro Ω _ ν _ F X B hSDE hInitial G D hG hD hE hIto
  refine ⟨?_,?_⟩
  · intro N hN
    exact sourceRiesz_gronwall_particle_collision_time (ν N) T s β M hs hβ hd hM N hN
      ρ (X N) (hSDE N hN).measurable_on_horizon hprob hρ G D (hE N hN)
  · let Xe := fun N=>sourceRieszParticleRealHorizonExtension T N (X N)
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
    have hLaw (N:ℕ) (hN:1≤N) : (ν N).map (Xe N 0)=sourceRieszSingularGibbs s β (ρ 0) N := by
      exact (SourceRieszInitialGibbsBrownianData.horizon_extension (ν N) T s β (ρ 0) N
        (X N) (B N) (hInitial N hN)).initial_gibbs
    have hEe (N:ℕ) (hN:1≤N) (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) :
        sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N ((ν N).map (Xe N r))≤
          (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
            (sourceRieszSingularGibbs s β (ρ 0) N)+(D r/(N:ℝ):ℝ) := by
      simpa only [he N r hr] using hE N hN r hr
    have hf0 (a:Fin k) : Measurable (f a 0) :=
      (hf a 0 ⟨le_rfl,(t a).coe_nonneg⟩).continuous.measurable
    have hex (n:{N:ℕ // 1≤N}) := exists_sourceRiesz_source_fixed_martingale_inputs
      (ν n.1) (F n.1) T s β hβ n.1 k (Nat.succ_le_iff.mp n.2) t ht (ρ 0) f hf0 hgrad Gmax hfB
      (Xe n.1) (B n.1)
      (SourceRieszFiniteHorizonWeakSDE.extended (ν n.1) (F n.1) T s β n.1 (X n.1) (B n.1)
        (hSDE n.1 n.2))
      (SourceRieszPhysicalItoAdmissibility.horizon_extension (ν n.1) (F n.1) T s β n.1 k t ht
        (ρ 0) f Gmax (X n.1) (B n.1) (hIto n.1 n.2))
    choose m hmm hm0 hmc hMart hLp hEmp hPhase using hex
    let mAll := fun (N:ℕ)=>if hN:1≤N then m ⟨N,hN⟩ else fun (_:Fin k) (_:ℝ) (_:Ω N)=>(0:ℝ)
    have hweak (a:Fin k) := (SourceRieszMeanFieldTestEvolution.time_test_identity
      s β (t a:ℝ) (t a).coe_nonneg ρ (f a) (hmean a)).2
    have hlim := huse Ω ν Xe hXem hLaw G D hG hD hEe mAll
      (fun N hN a=>by simpa only [mAll,dif_pos hN] using hmm ⟨N,hN⟩ a)
      (fun N hN a ω=>by simpa only [mAll,dif_pos hN] using hm0 ⟨N,hN⟩ a ω)
      (fun N hN a=>by simpa only [mAll,dif_pos hN] using hEmp ⟨N,hN⟩ a)
      hweak
      (fun θ N hN=>by
        simpa only [mAll,dif_pos hN,sourceRieszEmpiricalStoppedSquare] using hPhase ⟨N,hN⟩ θ)
    have hobs : (fun (N:ℕ) (ω:Ω N)=>WithLp.toLp 2 (fun a:Fin k=>
        Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (Xe N (t a) ω)))=
        (fun (N:ℕ) (ω:Ω N)=>WithLp.toLp 2 (fun a:Fin k=>
          Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (φ a) N (X N (t a) ω))) := by
      funext N ω
      congr 1
      funext a
      rw [he N (t a) ⟨(t a).coe_nonneg,ht a⟩,hterminal a]
    rw [hobs] at hlim
    exact hlim

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.exists_sourceRiesz_dynamic_joint_CLT_of_source_solutions
#print axioms DGRHS.Commutator.exists_sourceRiesz_dynamic_joint_CLT_of_source_solutions
