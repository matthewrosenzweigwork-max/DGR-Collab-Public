import DGRHS.Commutator.SourceRieszTransportGibbs

/-! Source Appendix A.1's positive-Riesz large-temperature prefactor.
The genuine physical Jensen lower bound is retained before normalization.
The remaining-temperature cap is derived from the checked physical partition,
not supplied as a hypothesis. Original TeX lines4130–4157, SHA2566f52778d…dac0c.
This does not certify the separate named quantitative Cub profile package. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszLocalParticleWeight_jensen_original (s β : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N)
    (hi : Integrable (fun ω=>Real.exp (sourceRieszLocalParticleExponent ρ s β N ω))
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) :
    Real.exp (β*sourceRieszLocalPhysicalEnergy ρ s) ≤
      ∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : E=>gaussianRieszPhysicalPair s (x,y)
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := sourceRieszLocalPhysicalPotential ρ s
  let I := sourceRieszLocalPhysicalEnergy ρ s
  have hn : 0<N := by omega
  have hpair := (memLp_gaussianRieszPhysicalPair s hs (by linarith) ρ M hM hρ).integrable (by norm_num)
  have hh := memLp_gaussianRieszCenteredPhysicalPair s hs (by linarith) ρ M hM hρ
  have hc := DGRHS.integral_centeredKernel_right μ W hpair
  have hF := memLp_gaussianRieszPhysicalPotential s hs (by linarith) ρ M hM hρ
  have hX : Integrable (fun ω : Fin N→E=>Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N ω))
      (Measure.pi (fun _ : Fin N=>μ)) := by
    convert hi using 1
    funext ω
    rw [sourceRieszLocalParticleExponent_eq ρ s β N hn]
  have hl := sourceAffinePartition_lower μ β I h hh hc F hF N hN hX
  have hmean : β*(∫ x,F x ∂μ)-β*I=β*I := by
    change β*(∫ x,DGRHS.potential μ W x ∂μ)-β*DGRHS.interactionEnergy μ W=β*DGRHS.interactionEnergy μ W
    rw [DGRHS.integral_potential μ W hpair]
    ring
  rw [hmean] at hl
  change Real.exp (β*I) ≤ ∫ ω : Fin N→E,
    Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N ω) ∂Measure.pi (fun _ : Fin N=>μ) at hl
  convert hl using 1
  congr 1
  funext ω
  rw [sourceRieszLocalParticleExponent_eq ρ s β N hn]

/-- A normalization step on the actual singular Gibbs law. The final theorem
below constructs its numerator rather than assuming the desired moment. -/
lemma sourceRieszTransport_Gibbs_bound_original (s M : ℝ) (n : ℕ)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (β : ℝ) (hβ : 0<β) {K : ℝ≥0} {v : E→E}
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (σ : ℝ) (N : ℕ) (hN : 1≤N)
    (C : ℝ) (hC : 0≤C)
    (hi : Integrable (fun ω=>Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω))
      (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)))
    (hb : (∫ ω,Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤C) :
    Integrable (fun ω=>Real.exp (σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
      sourceRieszLocalTransportEnergy ρ s n v N ω)) (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N) ∧
    (∫ ω,Real.exp (σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
      sourceRieszLocalTransportEnergy ρ s n v N ω) ∂DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≤
      Real.exp (-β*sourceRieszLocalPhysicalEnergy ρ s)*C := by
  obtain ⟨Cp,hCp,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  have hp := hPart N hN
  have hj := sourceRieszLocalParticleWeight_jensen_original s β hs hd ρ M hM hρ N hN hp.1
  rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
  let A := fun ω : Fin N→E=>σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
    sourceRieszLocalTransportEnergy ρ s n v N ω
  have hSum (ω : Fin N→E) : sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω=
      sourceRieszLocalParticleExponent ρ s β N ω+A ω := by
    dsimp [sourceRieszTransportAllBetaExponent,A]
    ring
  have ht : Integrable (fun ω=>Real.exp (A ω))
      ((Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted
        (sourceRieszLocalParticleExponent ρ s β N)) := by
    apply (integrable_tilted_iff hp.1 _).mpr
    apply hi.congr
    exact ae_of_all _ fun ω=>by
      change Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)=
        Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)*Real.exp (A ω)
      rw [hSum,Real.exp_add]
  refine ⟨ht,?_⟩
  change (∫ ω,Real.exp (A ω) ∂(Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted
    (sourceRieszLocalParticleExponent ρ s β N))≤_
  rw [integral_exp_tilted]
  change (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω+A ω)
    ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))/(∫ ω,
    Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤_
  simp_rw [←hSum]
  have hzpos : 0<(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) :=
    lt_of_lt_of_le (Real.exp_pos _) hj
  apply (div_le_iff₀ hzpos).mpr
  calc
    _ ≤ C := hb
    _ = (Real.exp (-β*sourceRieszLocalPhysicalEnergy ρ s)*C)*
        Real.exp (β*sourceRieszLocalPhysicalEnergy ρ s) := by
      rw [show -β*sourceRieszLocalPhysicalEnergy ρ s=-(β*sourceRieszLocalPhysicalEnergy ρ s) by ring,
        Real.exp_neg,inv_eq_one_div]
      field_simp [Real.exp_ne_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left hj (mul_nonneg (Real.exp_pos _).le hC)

def sourceRieszTransportOriginalCem (β βloc I Cub : ℝ) : ℝ :=
  if β≤βloc then Real.exp 1+glzUniversalTailConstant
  else Real.exp (-β*I)*Real.sqrt (Real.exp 1+glzUniversalTailConstant)*Real.sqrt Cub

/-- The exact small/large-temperature source moment constant, including its
large-temperature interaction-energy prefactor. The remaining cap is proper,
uniform in N, and constructed from the physical particle partition. -/
theorem sourceRieszTransport_Gibbs_original_constants (s M : ℝ) (n : ℕ)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (β : ℝ) (hβ : 0<β) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    ∃ Cub : ℝ, 1≤Cub ∧
      (∀ hlarge : sourceRieszLocalBeta (ι:=ι) s M<β, ∀ N : ℕ, 1≤N→
        Integrable (fun ω=>Real.exp (sourceRieszLocalParticleExponent ρ s
          (2*β-sourceRieszLocalBeta (ι:=ι) s M) N ω))
          (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
        (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s
          (2*β-sourceRieszLocalBeta (ι:=ι) s M) N ω)
          ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤Cub) ∧
      ∀ σ : ℝ, |σ|≤1→∀ N : ℕ, 1≤N→
        Integrable (fun ω=>Real.exp (σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
          sourceRieszLocalTransportEnergy ρ s n v N ω)) (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N) ∧
        (∫ ω,Real.exp (σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*
          sourceRieszLocalTransportEnergy ρ s n v N ω) ∂DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≤
          sourceRieszTransportOriginalCem β (sourceRieszLocalBeta (ι:=ι) s M)
            (sourceRieszLocalPhysicalEnergy ρ s) Cub := by
  have hloc := (sourceRieszLocalBeta_properties (ι:=ι) s M hs (by linarith) hM).1
  have hL := glzUniversalTailConstant_pos
  by_cases hsmall : β≤sourceRieszLocalBeta (ι:=ι) s M
  · refine ⟨1,le_rfl,?_,?_⟩
    · intro hlarge
      exact False.elim (not_lt_of_ge hsmall hlarge)
    intro σ hσ N hN
    have he : sourceRieszTransportAllBetaExponent ρ s M n β σ K v N=
        sourceRieszLocalNumeratorExponent ρ s n β σ K v N := by
      funext ω
      simp only [sourceRieszTransportAllBetaExponent,sourceRieszTransportEpsilon,ite_eq_left hsmall]
      unfold sourceRieszLocalNumeratorExponent sourceRieszLocalParticleExponent
      ring
    have hnum := sourceRieszLocal_numerator s n hs hd β σ hβ hσ hv ρ M hM hρ N hN hsmall
    rw [←he] at hnum
    have hb := sourceRieszTransport_Gibbs_bound_original s M n hs hd hM β hβ ρ hρ σ N hN
      (Real.exp 1+glzUniversalTailConstant) (by positivity) hnum.1 hnum.2
    have hI : 0≤sourceRieszLocalPhysicalEnergy ρ s := by
      unfold sourceRieszLocalPhysicalEnergy
      apply mul_nonneg (by norm_num)
      exact integral_nonneg (fun p=>by unfold gaussianRieszPhysicalPair;positivity)
    have hexp : Real.exp (-β*sourceRieszLocalPhysicalEnergy ρ s)≤1 := by
      simpa only [Real.exp_zero, neg_mul] using Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hβ.le hI))
    refine ⟨hb.1,?_⟩
    simp only [sourceRieszTransportOriginalCem,if_pos hsmall]
    exact hb.2.trans (by nlinarith [Real.exp_pos (-β*sourceRieszLocalPhysicalEnergy ρ s),Real.exp_pos 1])
  · have hlarge := lt_of_not_ge hsmall
    have htemp : 0≤2*β-sourceRieszLocalBeta (ι:=ι) s M := by linarith
    obtain ⟨Cp,hCp,hpart⟩ := sourceRieszLocalParticleWeight_uniform s
      (2*β-sourceRieszLocalBeta (ι:=ι) s M) hs htemp hd ρ M hM hρ
    refine ⟨max Cp 1,le_max_right _ _,?_,?_⟩
    · intro _ N hN
      exact ⟨(hpart N hN).1,(hpart N hN).2.2.trans (le_max_left _ _)⟩
    intro σ hσ N hN
    have hn : 0<N := by omega
    let X := fun ω : Fin N→E=>sourceRieszLocalNumeratorExponent ρ s n
      (sourceRieszLocalBeta (ι:=ι) s M) σ K v N ω/2
    let Y := sourceRieszLocalParticleExponent ρ s (β-sourceRieszLocalBeta (ι:=ι) s M/2) N
    have hX : Measurable X := (measurable_sourceRieszLocalNumeratorExponent ρ s n
      (sourceRieszLocalBeta (ι:=ι) s M) σ hv N hn).div_const 2
    have hY : Measurable Y := measurable_sourceRieszLocalParticleExponent ρ s _ N hn
    have hXX (ω : Fin N→E) : 2*X ω=sourceRieszLocalNumeratorExponent ρ s n
        (sourceRieszLocalBeta (ι:=ι) s M) σ K v N ω := by dsimp[X];ring
    have hYY (ω : Fin N→E) : 2*Y ω=sourceRieszLocalParticleExponent ρ s
        (2*β-sourceRieszLocalBeta (ι:=ι) s M) N ω := by
      unfold Y sourceRieszLocalParticleExponent
      ring
    have hx := sourceRieszLocal_numerator s n hs hd (sourceRieszLocalBeta (ι:=ι) s M)
      σ hloc hσ hv ρ M hM hρ N hN le_rfl
    have hy := hpart N hN
    have hxi : Integrable (fun ω=>Real.exp (2*X ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by simpa only [hXX] using hx.1
    have hyi : Integrable (fun ω=>Real.exp (2*Y ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by simpa only [hYY] using hy.1
    obtain ⟨hi,hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y hX.aemeasurable hY.aemeasurable hxi hyi
    have hSum (ω : Fin N→E) : X ω+Y ω=sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω :=
      (sourceRieszTransportAllBetaExponent_large ρ s M n β σ K v N hlarge ω).symm
    simp_rw [hSum] at hi hb
    simp_rw [hXX,hYY] at hb
    have hbound := hb.trans (mul_le_mul (Real.sqrt_le_sqrt hx.2)
      (Real.sqrt_le_sqrt (hy.2.2.trans (le_max_left Cp (1 : ℝ))))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hg := sourceRieszTransport_Gibbs_bound_original s M n hs hd hM β hβ ρ hρ σ N hN
      (Real.sqrt (Real.exp 1+glzUniversalTailConstant)*Real.sqrt (max Cp 1)) (by positivity) hi hbound
    refine ⟨hg.1,?_⟩
    simpa only [sourceRieszTransportOriginalCem,if_neg hsmall,mul_assoc] using hg.2

end DGRHS.Commutator
