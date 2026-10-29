import DGRHS.Commutator.SourceLogNamedUpropDynamicCLT
import DGRHS.Commutator.SourceLogDistributionalClass

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Source 862--914 (thm:dynamicLinearStatisticsCLT), LOG case `s = 0`, on the
source-admissible ORIGINAL trajectory class read as follows: the mean-field
equation holds distributionally in time against compact C-infinity spatial
tests, with the literal unsymmetrized force term read as a principal value,
with a proper L1 compact-test generator, and with the continuous trace of the
supplied every-time law (implied by narrow continuity of the supplied path).

This replaces exactly one premise of the reviewed R147 endpoint
`exists_sourceLog_named_Uprop_dynamic_joint_CLT` -- the every-time integrated
bounded-C2 class `SourceLogStaticWeakMeanField` -- by these primitive
distributional data, through `SourceLogPVDistributionalWeakMeanField.to_static`.
Every other premise and the complete conclusion (selected `sourceLogUprop` in
both covariance terms, Gaussian law, finite-dimensional convergence) are
copied verbatim from the R147 statement bytes
`ecc9be4f752b90fc2a5ac00dc8a561667c4f55ac94c75e7f03dae10336679574`.
Source assumptions retained as assumptions: backward classical
well-posedness/regularity (`hwp`), primitive literal Ito admissibility,
literal SDE and initial Gibbs data, Gronwall and partition bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceLog_original_class_named_Uprop_dynamic_joint_CLT
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
    (hdist : SourceLogPVDistributionalWeakMeanField (β:ℝ) (T:ℝ) ρ)
    (htrace : SourceCompactTestContinuousTrace (T:ℝ) ρ)
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
        atTop id ν P :=
  exists_sourceLog_named_Uprop_dynamic_joint_CLT β hβ T M J c Cpart C₂ Amax Bmax hM hc hAmax
    hBmax k t ht ρ hρm hprob hρ hpair hIbg
    (SourceLogPVDistributionalWeakMeanField.to_static (β:ℝ) (T:ℝ) T.coe_nonneg ρ hprob hdist htrace)
    Dtest hwp φ hφD

end DGRHS.Commutator
