import DGRHS.Commutator.SourceRieszClassicalBackwardInterface
import DGRHS.Commutator.SourceRieszOriginalDynamicAssembly
import DGRHS.Commutator.SourceRieszLiteralSourceDynamics

/-! UNCOMPILED positive-Riesz source865--912 named-propagator export.
The selected unique classical solutions, not arbitrary AE backward identities,
are used in both literal covariance terms. The mean-field admissible class is
explicitly its differential time-tested formulation; a bare pointwise PDE is
not asserted to imply it. Spatial properness below rules out accidental use of
totalized improper integrals. Primitive physical Itô admissibility is required
for each valid deterministic gradient bound; it contains no desired terminal,
phase, bracket or Gaussian conclusion. Its particle SDE and empirical Ito
drift use the literal potential gradient as INPUT. Collision occupation is
derived first, independently of any SDE conversion. LOG is outside this module. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Precise differential time-test reading of the source mean-field solution
class for the classical backward tests. The time-test endpoint identity is
proved by absolute-continuity FTC, never part of this predicate. -/
def SourceRieszMeanFieldClassicalTested
    (T : ℝ≥0) (s β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ)) : Prop :=
  ∀ t:ℝ≥0,t≤T → ∀ φ:E→ℝ,φ∈D → ∀ f:ℝ→E→ℝ,
    SourceRieszClassicalBackwardSolution s β ρ t φ f →
      SourceRieszMeanFieldTestEvolution s β (t:ℝ) ρ f

/-- All spatial quantities in the tested mean-field equation are proper.
The difference of gradients retains the cancellation of the source adjoint
operator; separate uncancelled force convolutions are not asserted proper. -/
theorem SourceRieszClassicalBackwardSolution.spatial_properness
    (s β : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ))
    (t : ℝ≥0) (ρ : ℝ→E→ℝ) (M : ℝ) (hM : 0≤M)
    (hprob : ∀ r∈Icc 0 (t:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (t:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (φ : E→ℝ) (f : ℝ→E→ℝ)
    (h : SourceRieszClassicalBackwardSolution s β ρ t φ f) :
    (∀ r∈Icc 0 (t:ℝ),
      Integrable (f r) (gaussianRieszDensityMeasure (ρ r)) ∧
      (∀ z,Integrable (fun y=>⟪sourceRieszForce s (z-y),gradient (f r) z-gradient (f r) y⟫)
        (gaussianRieszDensityMeasure (ρ r))) ∧
      Integrable (sourceRieszTransportKernel 1 s (gradient (f r)))
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) ∧
    ∀ᵐ r ∂volume.restrict (Ioc 0 (t:ℝ)),
      Integrable (fun z=>deriv (fun u=>f u z) r+β⁻¹*laplacian (f r) z)
        (gaussianRieszDensityMeasure (ρ r)) := by
  obtain ⟨C,hC,hb⟩ := h.bounded
  let K : ℝ≥0 := ⟨C,hC⟩
  have hspace : ∀ r∈Icc 0 (t:ℝ),
      Integrable (f r) (gaussianRieszDensityMeasure (ρ r)) ∧
      (∀ z,Integrable (fun y=>⟪sourceRieszForce s (z-y),gradient (f r) z-gradient (f r) y⟫)
        (gaussianRieszDensityMeasure (ρ r))) ∧
      Integrable (sourceRieszTransportKernel 1 s (gradient (f r)))
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r))) := by
    intro r hr
    letI := hprob r hr
    have hg := sourceAdjoint_gradient_lipschitz_of_hessian_bound (f r)
      (h.spatial_contdiff r hr) K (fun z=>(hb r hr z).2.2)
    refine ⟨?_,?_,(sourceRieszLocalTransport_pair s 1 hs hd hg (ρ r) M hM (hρ r hr)).1⟩
    · apply (integrable_const C).mono' (h.spatial_contdiff r hr).continuous.measurable.aestronglyMeasurable
      exact ae_of_all _ (fun z=>by simpa only [Real.norm_eq_abs] using (hb r hr z).1)
    · intro z
      simpa only [sourceRieszTransportKernel_force s hs] using
        (sourceRieszLocalTransport_section s 1 hs (by linarith) hg (ρ r) M hM (hρ r hr) z).1
  refine ⟨hspace,?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc,SourceRieszClassicalBackwardSolution.backward_ae s β ρ t φ f h] with r hr hback
  letI := hprob r ⟨hr.1.le,hr.2⟩
  have hp := (hspace r ⟨hr.1.le,hr.2⟩).2.2
  have he : (fun z=>deriv (fun u=>f u z) r+β⁻¹*laplacian (f r) z)=
      (fun z=>∫ y,sourceRieszTransportKernel 1 s (gradient (f r)) (z,y)
        ∂gaussianRieszDensityMeasure (ρ r)) := by
    funext z
    simpa only [sourceRieszTransportKernel_force s hs] using hback z
  rw [he]
  exact hp.integral_prod_left

theorem exists_sourceRiesz_named_Uprop_dynamic_joint_CLT
    (s β : ℝ) (T : ℝ≥0) (M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax)
    (k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (Dtest : Submodule ℝ (E→ℝ))
    (hwp : SourceRieszBackwardClassicalWellPosed T s β ρ Dtest)
    (hmean : SourceRieszMeanFieldClassicalTested T s β ρ Dtest)
    (φ : Fin k→E→ℝ) (hφD : ∀ a,φ a∈Dtest) :
    let f := fun a=>sourceRieszUprop T s β ρ Dtest hwp (t a) (ht a) (φ a) (hφD a)
    ((∀ a,∀ r∈Icc 0 (t a:ℝ),
      Integrable (f a r) (gaussianRieszDensityMeasure (ρ r)) ∧
      (∀ z,Integrable (fun y=>⟪sourceRieszForce s (z-y),gradient (f a r) z-gradient (f a r) y⟫)
        (gaussianRieszDensityMeasure (ρ r))) ∧
      Integrable (sourceRieszTransportKernel 1 s (gradient (f a r)))
        ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))) ∧
    (∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a:ℝ)),
      Integrable (fun z=>deriv (fun u=>f a u z) r+β⁻¹*laplacian (f a r) z)
        (gaussianRieszDensityMeasure (ρ r)))) ∧
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
          (2/β)*(∫ r in Ioc 0 (min (t a:ℝ) (t b:ℝ)),
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
      (∀ N,1≤N → SourceRieszLiteralFiniteHorizonSDE (ν N) (F N) T s β N (X N) (B N)) →
      (∀ N,1≤N → SourceRieszInitialGibbsBrownianData (ν N) s β (ρ 0) N (X N 0) (B N)) →
      ∀ (G D : ℝ→ℝ),(∀ r∈Icc 0 (T:ℝ),0≤G r) → (∀ r∈Icc 0 (T:ℝ),D r≤Bmax) →
      (∀ N,1≤N → ∀ r∈Icc 0 (T:ℝ),
        sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N ((ν N).map (X N r))≤
          (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
            (sourceRieszSingularGibbs s β (ρ 0) N)+(D r/(N:ℝ):ℝ)) →
      (∀ Gmax:ℝ≥0,
        (∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ)) →
        ∀ N,1≤N → SourceRieszLiteralPhysicalItoAdmissibility (ν N) (F N) T s β N k t (ρ 0) f Gmax (X N) (B N)) →
      (∀ N,1≤N → ∀ᵐ ω ∂ν N,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
        ∀ i j:Fin N,i≠j → X N r ω i≠X N r ω j) ∧
      TendstoInDistribution
        (fun (N:ℕ) (ω:Ω N)=>WithLp.toLp 2 (fun a:Fin k=>
          Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (φ a) N (X N (t a) ω)))
        atTop id ν P := by
  classical
  let f := fun a=>sourceRieszUprop T s β ρ Dtest hwp (t a) (ht a) (φ a) (hφD a)
  have hsol (a:Fin k) : SourceRieszClassicalBackwardSolution s β ρ (t a) (φ a) (f a) :=
    (sourceRieszUprop_spec T s β ρ Dtest hwp (t a) (ht a) (φ a) (hφD a)).1
  have hproper (a:Fin k) := SourceRieszClassicalBackwardSolution.spatial_properness
    s β hs hd (t a) ρ M hM
      (fun r hr=>hprob r ⟨hr.1,hr.2.trans (ht a)⟩)
      (fun r hr=>hρ r ⟨hr.1,hr.2.trans (ht a)⟩) (φ a) (f a) (hsol a)
  refine ⟨⟨fun a=>(hproper a).1,fun a=>(hproper a).2⟩,?_⟩
  obtain ⟨C,hC,hbound⟩ := sourceRieszClassicalBackwardSolution_finite_bounds s β ρ k t φ f hsol
  let K : ℝ≥0 := ⟨C,hC⟩
  have hgradBound : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(K:ℝ) :=
    fun a r hr z=>(hbound a r hr z).2.1
  letI := hprob 0 ⟨le_rfl,T.coe_nonneg⟩
  obtain ⟨hφ,hSym,hCan,R0,hR1,hR2,hPSD,hP,hGauss,hMean,hCov,huse⟩ :=
    exists_sourceRiesz_dynamic_joint_CLT_of_source_solutions s β T M Bmax hs hβ hd hM hBmax
      K K k t ht ρ hρm hprob hρ φ f (fun a=>(hsol a).terminal)
      (fun a=>(hsol a).spatial_contdiff) (fun a r hr z=>(hbound a r hr z).2.2)
      (fun a=>(hsol a).gradient_continuous) hgradBound C (fun a r hr z=>(hbound a r hr z).1)
      (fun a=>SourceRieszClassicalBackwardSolution.backward_ae s β ρ (t a) (φ a) (f a) (hsol a))
      (fun a=>hmean (t a) (ht a) (φ a) (hφD a) (f a) (hsol a))
  refine ⟨hφ,hSym,hCan,R0,hR1,hR2,hPSD,hP,hGauss,hMean,hCov,?_⟩
  intro Ω _ ν _ F X B hSDE hInitial G D hG hD hE hIto
  have hcollision (N:ℕ) (hN:1≤N) :
      ∀ᵐ ω ∂ν N,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
        ∀ i j:Fin N,i≠j → X N r ω i≠X N r ω j :=
    sourceRiesz_gronwall_particle_collision_time (ν N) T s β M hs hβ hd hM N hN
      ρ (X N) (hSDE N hN).measurable_on_horizon hprob hρ G D (hE N hN)
  have hweak (N:ℕ) (hN:1≤N) :
      SourceRieszFiniteHorizonWeakSDE (ν N) (F N) T s β N (X N) (B N) :=
    SourceRieszLiteralFiniteHorizonSDE.to_weak (ν N) (F N) T s β hs N (X N) (B N)
      (hSDE N hN) (hcollision N hN)
  exact huse Ω ν F X B hweak hInitial G D hG hD hE
    (fun N hN=>SourceRieszLiteralPhysicalItoAdmissibility.to_physical
      (ν N) (F N) T s β hs N k t ht (ρ 0) f K (X N) (B N)
      (hIto K hgradBound N hN) (hcollision N hN))

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszMeanFieldClassicalTested
#print axioms DGRHS.Commutator.SourceRieszMeanFieldClassicalTested
#check @DGRHS.Commutator.SourceRieszClassicalBackwardSolution.spatial_properness
#print axioms DGRHS.Commutator.SourceRieszClassicalBackwardSolution.spatial_properness
#check @DGRHS.Commutator.exists_sourceRiesz_named_Uprop_dynamic_joint_CLT
#print axioms DGRHS.Commutator.exists_sourceRiesz_named_Uprop_dynamic_joint_CLT
