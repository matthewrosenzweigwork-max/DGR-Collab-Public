import DGRHS.Gaussian.GaussianLogCutoffInterpolation
import DGRHS.CLT.SourceLogPartition
import DGRHS.Concentration.SourcePartitionRate

/-! Physical canonical moment and SAME full mean-zero operator data. The
original exp(-4 beta potential) derives actual doubled moments, not UI premises. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.SourceRepulsiveLogRate
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

theorem exists_double_moments (β : ℝ) (hβ : 0≤β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    ∃ MH MK : ℝ,
      (∀ N : ℕ,Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
        (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) x))
            (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) ∧
      (∀ N : ℕ,(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
        (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) x)
            ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤MH) ∧
      ∀ η : ℝ,0<η →η≤1 →∀ N : ℕ,1≤N →
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
          (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)) x))
              (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
        (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
          (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
            (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogTruncatedPair η)) x)
              ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤MK := by
  have ht : Integrable (fun x=>Real.exp (-2*(2*β)*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ) := by
    convert htail using 1
    funext x
    congr 1
    ring
  obtain ⟨MH,hH⟩ := logPhysicalCanonical_uniform_exponential (2*β) (by positivity) hd ρ M hM hρ hpair ht
  obtain ⟨MK,hK⟩ := gaussianLogCutoffCanonical_uniform_exponential (2*β) (by positivity) hd ρ M hM hρ hpair ht
  have he (N : ℕ) (q : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι→ℝ) (x : Fin N→EuclideanSpace ℝ ι) :
      (2*β)*iidNegativeStatistic N q x=-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x := by
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
    ring
  simp_rw [he] at hH hK
  have hAll (N : ℕ) : Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) x))
          (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
        (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) x)
            ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤max MH 1 := by
    by_cases hn : N=0
    · subst N
      simp only [DGRHS.CanonicalVariance.normalizedOffDiagonalSum,Fintype.card_fin,Nat.cast_zero,
        inv_zero,zero_mul,mul_zero,Real.exp_zero]
      exact ⟨integrable_const _,by simpa only [integral_const,probReal_univ,one_smul] using le_max_right MH 1⟩
    · exact ⟨(hH N (by omega)).1,((hH N (by omega)).2).trans (le_max_left MH 1)⟩
  exact ⟨max MH 1,MK,(fun N=>(hAll N).1),(fun N=>(hAll N).2),hK⟩

 theorem exists_full_canonical_limit (β : ℝ) (hβ : 0≤β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p) (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i)=eig i • e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i=>β*eig i) ∧
      HasProd (fun i=>(1+β*eig i)*Real.exp (-(β*eig i)))
        (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)) ∧
      Tendsto (canonicalPartition μ β h) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹)) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let h := hoeffdingCentered μ logPhysicalPair
  let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  obtain ⟨hs,hc,hp⟩ := DGRHS.CLT.sourceLogKernel_properties hd ρ M hM hρ hpair
  obtain ⟨MH,MK,hDouble,bDouble,_⟩ := exists_double_moments β hβ hd ρ M hM hρ hpair htail
  obtain ⟨κ,eig,e,hκ,he,hFactory⟩ := DGRHS.CLT.exists_sourceMeanZeroPartitionLimit h hh hs hc hp
  have hExpDouble (N : ℕ) : (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
      (2*DGRHS.CLT.sourceParticleExponent h (fun _=>0) 0 β N x))=
      (fun x=>Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    unfold DGRHS.CLT.sourceParticleExponent
    simp only [Finset.sum_const_zero,mul_zero,sub_zero,add_zero]
    congr 1
    ring
  obtain ⟨hD,hProd,hT⟩ := hFactory (fun _=>0) (integrable_const _) 0 β 2 MH hβ (by norm_num)
    (fun N=>by rw [hExpDouble];exact hDouble N) (fun N=>by rw [hExpDouble];exact bDouble N)
  refine ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,?_⟩
  change Tendsto (fun N=>∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
    (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) ∂Measure.pi (fun _ : Fin N=>μ)) atTop _
  simpa only [DGRHS.CLT.sourceParticleExponent,Finset.sum_const_zero,mul_zero,sub_zero,add_zero,
    integral_zero,Real.exp_zero,one_mul,canonicalPartition,h,μ] using hT

end DGRHS.SourceRepulsiveLogRate
#check @DGRHS.SourceRepulsiveLogRate.exists_double_moments
#print axioms DGRHS.SourceRepulsiveLogRate.exists_double_moments
#check @DGRHS.SourceRepulsiveLogRate.exists_full_canonical_limit
#print axioms DGRHS.SourceRepulsiveLogRate.exists_full_canonical_limit
