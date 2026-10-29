import DGRHS.Commutator.SourceRieszOriginalDynamicCLT
import DGRHS.Commutator.SourceCompactTestTrace

/-! Theorem 2.13 (TeX 862-914), positive Riesz case, narrow-continuity form of the original-class
wrapper `exists_sourceRiesz_original_class_named_Uprop_dynamic_joint_CLT`.

Owner convention (2026-10-06): a mean-field trajectory in a well-posed class includes narrow
continuity of `t -> mu^t`. The input `htrace : SourceCompactTestContinuousTrace T rho` of the
original-class wrapper is replaced by a narrowly continuous `ProbabilityMeasure` path on `[0,T]`
agreeing with `gaussianRieszDensityMeasure (rho r)`; the trace is derived by
`sourceCompactTestContinuousTrace_of_narrow`. Every other premise and the whole conclusion are
copied verbatim from the original-class wrapper. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_original_class_narrow_dynamic_joint_CLT
    (s β : ℝ) (T : ℝ≥0) (M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax)
    (k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (Dtest : Submodule ℝ (E→ℝ))
    (hwp : SourceRieszBackwardClassicalWellPosed T s β ρ Dtest)
    (hdist : SourceRieszPVDistributionalWeakMeanField s β (T:ℝ) ρ)
    (μpath : ℝ → ProbabilityMeasure E)
    (hμpath : ContinuousOn μpath (Icc 0 (T:ℝ)))
    (hρμ : ∀ r∈Icc 0 (T:ℝ),(μpath r : Measure E)=gaussianRieszDensityMeasure (ρ r))
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
        atTop id ν P :=
  exists_sourceRiesz_original_class_named_Uprop_dynamic_joint_CLT s β T M Bmax hs hβ hd hM hBmax
    k t ht ρ hρm hprob hρ Dtest hwp hdist
    (sourceCompactTestContinuousTrace_of_narrow (T:ℝ) ρ μpath hμpath hρμ)
    φ hφD

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRiesz_original_class_narrow_dynamic_joint_CLT
#print axioms DGRHS.Commutator.exists_sourceRiesz_original_class_narrow_dynamic_joint_CLT
