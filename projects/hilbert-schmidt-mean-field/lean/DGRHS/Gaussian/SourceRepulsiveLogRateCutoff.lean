import DGRHS.Gaussian.SourceRepulsiveLogRateFeature

/-! The genuine fixed-cutoff N^-1 Laplace rate for the actual logarithmic
kernel and its same integral operator, from the constructed physical feature. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.SourceRepulsiveLogRate
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

theorem exists_cutoff_partition_rate (β : ℝ) (hβ : 0<β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    ∃ L : ℝ,0<L ∧ ∀ (η : ℝ) (hη : 0<η),η≤1 →
      let μ := gaussianRieszDensityMeasure ρ
      let h := hoeffdingCentered μ (gaussianLogTruncatedPair η)
      let hh := memLp_logPhysicalCenteredTruncatedPair η hη hd ρ M hM hρ hpair
      ∃ (σ : Type u) (eig : σ→ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
        Countable σ ∧ (∀ i,DGRHS.Kernel.integralOperator h hh (e i)=eig i • e i) ∧
        0<DGRHS.Kernel.regularizedDet (fun i=>β*eig i) ∧
        HasProd (fun i=>(1+β*eig i)*Real.exp (-(β*eig i)))
          (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)) ∧
        Tendsto (canonicalPartition μ β h) atTop
          (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹)) ∧
        ∀ N : ℕ,1≤N →
          Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
            (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N=>μ)) ∧
          |canonicalPartition μ β h N-(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹|≤
            L*Real.exp (L*(1+Real.log (1/η)))/(N:ℝ) := by
  let μ := gaussianRieszDensityMeasure ρ
  obtain ⟨K,hK,hMoment⟩ := exists_feature_moment_uniform β hβ hd ρ M hM hρ hpair htail
  let Q := (26*β^2+12*β^3)*K^2
  let L := 1+Q+4*β
  have hQ : 0≤Q := by dsimp [Q];positivity
  have hL : 0<L := by dsimp [L];linarith
  refine ⟨L,hL,?_⟩
  intro η hη hη1
  dsimp only
  let H := Lp ℂ 2 (gaussianLogPhaseMeasure ι η)
  letI : MeasurableSpace H := borel _
  letI : BorelSpace H := ⟨rfl⟩
  letI : TopologicalSpace.SeparableSpace H := separableSpace_gaussianLogPhaseHilbert η
  let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  let h := hoeffdingCentered μ (gaussianLogTruncatedPair η)
  let hh := memLp_logPhysicalCenteredTruncatedPair η hη hd ρ M hM hρ hpair
  have hk := stronglyMeasurable_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  have hmean := integral_gaussianLogCenteredInfiniteFeature_eq_zero η hη hd ρ M hM hρ hpair
  have heq : h =ᵐ[μ.prod μ] featureKernel k :=
    ae_gaussianLogTruncatedPair_eq_infiniteFeatureGram η hη hd ρ M hM hρ hpair
  obtain ⟨hMi,bMi⟩ := hMoment η hη hη1
  obtain ⟨σ,eig,e,hσ,he,hpos,hsummable,htrace,hRate⟩ :=
    exists_sourceKernelParticleStatistic_feature_rate β hβ.le h hh k hk hMi hmean heq
  obtain ⟨hProd,hDet,hRate'⟩ := sourceKernel_eigenbasis_feature_rate β hβ.le h hh k hk hMi hmean heq eig e he
  simp_rw [sourceKernelParticleStatistic_eq_normalized] at hRate'
  have hl0 : 0≤Real.log (1/η) := Real.log_nonneg (by
    apply (le_div_iff₀ hη).mpr
    linarith)
  have hCoeff : (26*β^2+12*β^3)*(∫ x,featureExponentialMomentWeight β k x ∂μ)^2 ≤
      Q*Real.exp (4*β*Real.log (1/η)) := by
    have hm0 : 0≤∫ x,featureExponentialMomentWeight β k x ∂μ :=
      integral_nonneg (fun x=>by unfold featureExponentialMomentWeight;positivity)
    have hp := pow_le_pow_left₀ hm0 bMi 2
    have he : (Real.exp (2*β*Real.log (1/η)))^2=Real.exp (4*β*Real.log (1/η)) := by
      rw [←Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [mul_pow,he] at hp
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤26*β^2+12*β^3 by positivity)
    simpa only [Q,mul_assoc] using hh
  have hFinal : Q*Real.exp (4*β*Real.log (1/η))≤L*Real.exp (L*(1+Real.log (1/η))) := by
    have hQL : Q≤L := by dsimp [L];linarith
    have h4L : 4*β≤L := by dsimp [L];linarith
    apply mul_le_mul hQL (Real.exp_le_exp.mpr _) (Real.exp_nonneg _) hL.le
    nlinarith [mul_le_mul_of_nonneg_right h4L hl0]
  have hAll : ∀ N : ℕ,1≤N →
      Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
        (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N=>μ)) ∧
      |canonicalPartition μ β h N-(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹|≤
        L*Real.exp (L*(1+Real.log (1/η)))/(N:ℝ) := by
    intro N hN
    refine ⟨(hRate' N hN).1,((hRate' N hN).2).trans ?_⟩
    exact div_le_div_of_nonneg_right (hCoeff.trans hFinal) (Nat.cast_nonneg N)
  exact ⟨σ,eig,e,hσ,he,hDet,hProd,
    partition_tendsto_of_reciprocal_error _ _ _ (fun N hN=>(hAll N hN).2),hAll⟩

end DGRHS.SourceRepulsiveLogRate
#check @DGRHS.SourceRepulsiveLogRate.exists_cutoff_partition_rate
#print axioms DGRHS.SourceRepulsiveLogRate.exists_cutoff_partition_rate
