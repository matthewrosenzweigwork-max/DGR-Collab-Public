import DGRHS.Commutator.SourceRieszCommonPartition
import DGRHS.Commutator.SourceRieszTransportGibbs

/-! Common-family source Riesz transport constants: chosen before the velocity,
its Lipschitz constant, the probability density, the sign, or particle number.
The transport parameter keeps the exact source small/large-beta expression. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- A common unnormalized numerator bound, for all actual Lipschitz velocities. -/
theorem sourceRieszCommon_numerator (s M : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ C : ℝ,0<C ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ σ : ℝ,|σ|≤1 → ∀ N : ℕ,1≤N →
      Integrable (fun ω=>Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤C := by
  have hloc := (sourceRieszLocalBeta_properties (ι:=ι) s M hs (by linarith) hM).1
  have hL := glzUniversalTailConstant_pos
  by_cases hsmall : β≤sourceRieszLocalBeta (ι:=ι) s M
  · refine ⟨Real.exp 1+glzUniversalTailConstant,by positivity,?_⟩
    intro K v hv ρ hprob hρ σ hσ N hN
    let _ := hprob
    have he : sourceRieszTransportAllBetaExponent ρ s M n β σ K v N=
        sourceRieszLocalNumeratorExponent ρ s n β σ K v N := by
      funext ω
      simp only [sourceRieszTransportAllBetaExponent,sourceRieszTransportEpsilon,ite_eq_left hsmall]
      unfold sourceRieszLocalNumeratorExponent sourceRieszLocalParticleExponent
      ring
    rw [he]
    exact sourceRieszLocal_numerator s n hs hd β σ hβ hσ hv ρ M hM hρ N hN hsmall
  · have hlarge := lt_of_not_ge hsmall
    have htemp : 0≤2*β-sourceRieszLocalBeta (ι:=ι) s M := by linarith
    obtain ⟨Cp,hCp,hpart⟩ := sourceRieszCommon_particle_moment (ι:=ι) s (2*β-sourceRieszLocalBeta (ι:=ι) s M) M hs htemp hM hd
    refine ⟨Real.sqrt (Real.exp 1+glzUniversalTailConstant)*Real.sqrt Cp,
      mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hCp),?_⟩
    intro K v hv ρ hprob hρ σ hσ N hN
    let _ := hprob
    have hn : 0<N := lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN
    let X := fun ω : Fin N→E=>sourceRieszLocalNumeratorExponent ρ s n (sourceRieszLocalBeta (ι:=ι) s M) σ K v N ω/2
    let Y := sourceRieszLocalParticleExponent ρ s (β-sourceRieszLocalBeta (ι:=ι) s M/2) N
    have hX : Measurable X := (measurable_sourceRieszLocalNumeratorExponent ρ s n (sourceRieszLocalBeta (ι:=ι) s M) σ hv N hn).div_const 2
    have hY : Measurable Y := measurable_sourceRieszLocalParticleExponent ρ s _ N hn
    have hXX (ω : Fin N→E) : 2*X ω=sourceRieszLocalNumeratorExponent ρ s n (sourceRieszLocalBeta (ι:=ι) s M) σ K v N ω := by dsimp[X];ring
    have hYY (ω : Fin N→E) : 2*Y ω=sourceRieszLocalParticleExponent ρ s (2*β-sourceRieszLocalBeta (ι:=ι) s M) N ω := by
      unfold Y sourceRieszLocalParticleExponent
      ring
    have hx := sourceRieszLocal_numerator s n hs hd (sourceRieszLocalBeta (ι:=ι) s M) σ hloc hσ hv ρ M hM hρ N hN le_rfl
    have hy := hpart ρ hprob hρ N hN
    have hxi : Integrable (fun ω=>Real.exp (2*X ω)) (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by simpa only [hXX] using hx.1
    have hyi : Integrable (fun ω=>Real.exp (2*Y ω)) (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by simpa only [hYY] using hy.1
    obtain ⟨hi,hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y hX.aemeasurable hY.aemeasurable hxi hyi
    have hSum (ω : Fin N→E) : X ω+Y ω=sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω := by
      exact (sourceRieszTransportAllBetaExponent_large ρ s M n β σ K v N hlarge ω).symm
    simp_rw [hSum] at hi hb
    simp_rw [hXX,hYY] at hb
    exact ⟨hi,hb.trans (mul_le_mul (Real.sqrt_le_sqrt hx.2) (Real.sqrt_le_sqrt hy.2.2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-- Common literal-Gibbs moment, including constant velocity. The positive
parameter is specified, rather than existentially reselected for each density. -/
theorem sourceRieszCommon_Gibbs_moment (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β) :
    ∃ C : ℝ,1≤C ∧ ∀ (K : ℝ≥0) (v : E→E),LipschitzWith K v →
      0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
      ∀ ρ : E→ℝ,IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ σ : ℝ,|σ|≤1 → ∀ N : ℕ,1≤N →
      Integrable (fun ω=>Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω)) (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N) ∧
      (∫ ω,Real.exp (σ*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*
        sourceRieszLocalTransportEnergy ρ s n v N ω) ∂DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≤C := by
  obtain ⟨C,hC,hNum⟩ := sourceRieszCommon_numerator (ι:=ι) s M n hs hd hM β hβ
  obtain ⟨Cp,hCp,hPart⟩ := sourceRieszCommon_particle_moment (ι:=ι) s β M hs hβ.le hM hd
  refine ⟨max C 1,le_max_right _ _,?_⟩
  intro K v hv
  refine ⟨sourceRieszPositiveTransportParameter_pos s M n K β hs hd hM hβ,?_⟩
  intro ρ hprob hρ σ hσ N hN
  let _ := hprob
  by_cases hk : K=0
  · have hv0 : LipschitzWith 0 v := by simpa only [hk] using hv
    let _ := DGRHS.CLT.sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
    simp only [sourceRieszLocalTransportEnergy_eq_zero ρ s n hn hv0,mul_zero,Real.exp_zero]
    exact ⟨integrable_const 1,by simpa using le_max_right C 1⟩
  · simp only [sourceRieszPositiveTransportParameter,ite_eq_right hk]
    have hi := hNum K v hv ρ hprob hρ σ hσ N hN
    have hp := hPart ρ hprob hρ N hN
    rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
    let A := fun ω : Fin N→E=>σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
    have hSum (ω : Fin N→E) : sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω=
        sourceRieszLocalParticleExponent ρ s β N ω+A ω := by
      dsimp [sourceRieszTransportAllBetaExponent,A]
      ring
    have ht : Integrable (fun ω=>Real.exp (A ω))
        ((Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted (sourceRieszLocalParticleExponent ρ s β N)) := by
      apply (integrable_tilted_iff hp.1 _).mpr
      apply hi.1.congr
      exact ae_of_all _ fun ω=>by
        change Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)=
          Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)*Real.exp (A ω)
        rw [hSum,Real.exp_add]
    refine ⟨ht,?_⟩
    change (∫ ω,Real.exp (A ω) ∂(Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)).tilted
      (sourceRieszLocalParticleExponent ρ s β N))≤max C 1
    rw [integral_exp_tilted]
    change (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω+A ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))/(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤max C 1
    simp_rw [←hSum]
    have hdpos : 0<(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by linarith [hp.2.1]
    apply (div_le_iff₀ hdpos).mpr
    exact (hi.2.trans (le_max_left _ _)).trans (le_mul_of_one_le_right (le_trans hC.le (le_max_left _ _)) hp.2.1)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszCommon_numerator
#print axioms DGRHS.Commutator.sourceRieszCommon_numerator
#check @DGRHS.Commutator.sourceRieszCommon_Gibbs_moment
#print axioms DGRHS.Commutator.sourceRieszCommon_Gibbs_moment
