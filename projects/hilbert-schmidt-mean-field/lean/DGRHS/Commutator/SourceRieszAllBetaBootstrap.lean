import DGRHS.Commutator.SourceRieszLocalPartition
import DGRHS.CLT.BoundedLinearWeightMoments

/-! Actual source positive-Riesz all-temperature Hölder bootstrap. The
remaining Gibbs factor uses genuine source particle moments; no desired
partition or commutator moment estimate is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszTransportEpsilon (s M : ℝ) (n : ℕ) (K β : ℝ) : ℝ :=
  if β≤sourceRieszLocalBeta (ι:=ι) s M then sourceRieszLocalCoefficient (ι:=ι) s n K β
  else sourceRieszLocalCoefficient (ι:=ι) s n K (sourceRieszLocalBeta (ι:=ι) s M)/2

lemma sourceRieszTransportEpsilon_pos (s M : ℝ) (n : ℕ) (K β : ℝ)
    (hs : 0<s) (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hK : 0<K) (hβ : 0<β) :
    0<sourceRieszTransportEpsilon (ι:=ι) s M n K β := by
  have hloc := (sourceRieszLocalBeta_properties (ι:=ι) s M hs hd hM).1
  have hC := (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).1
  unfold sourceRieszTransportEpsilon sourceRieszLocalCoefficient
  split_ifs <;> positivity

def sourceRieszTransportAllBetaExponent (ρ : E→ℝ) (s M : ℝ) (n : ℕ) (β σ : ℝ)
    (K : ℝ≥0) (v : E→E) (N : ℕ) (ω : Fin N→E) : ℝ :=
  σ*sourceRieszTransportEpsilon (ι:=ι) s M n K β*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω+
    sourceRieszLocalParticleExponent ρ s β N ω

/-- Actual large-beta decomposition with the SAME An and physical source energy. -/
lemma sourceRieszTransportAllBetaExponent_large (ρ : E→ℝ) (s M : ℝ) (n : ℕ) (β σ : ℝ)
    (K : ℝ≥0) (v : E→E) (N : ℕ) (hβ : sourceRieszLocalBeta (ι:=ι) s M<β) (ω : Fin N→E) :
    sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω=
      sourceRieszLocalNumeratorExponent ρ s n (sourceRieszLocalBeta (ι:=ι) s M) σ K v N ω/2+
      sourceRieszLocalParticleExponent ρ s (β-sourceRieszLocalBeta (ι:=ι) s M/2) N ω := by
  simp only [sourceRieszTransportAllBetaExponent,sourceRieszTransportEpsilon,ite_eq_right (not_le.mpr hβ)]
  unfold sourceRieszLocalNumeratorExponent sourceRieszLocalParticleExponent
  ring

/-- Proper unnormalized all-temperature numerator with a single constant
common to all N≥1 and both signs, entirely from original physical data. -/
theorem sourceRieszTransport_allBeta_numerator (s M : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    ∃ C : ℝ,0<C ∧ ∀ σ : ℝ,|σ|≤1→∀ N : ℕ,1≤N→
      Integrable (fun ω=>Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω))
        (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))≤C := by
  have hloc := (sourceRieszLocalBeta_properties (ι:=ι) s M hs (by linarith) hM).1
  have hL := glzUniversalTailConstant_pos
  by_cases hsmall : β≤sourceRieszLocalBeta (ι:=ι) s M
  · refine ⟨Real.exp 1+glzUniversalTailConstant,by positivity,?_⟩
    intro σ hσ N hN
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
    obtain ⟨Cp,hCp,hpart⟩ := sourceRieszLocalParticleWeight_uniform s (2*β-sourceRieszLocalBeta (ι:=ι) s M) hs htemp hd ρ M hM hρ
    refine ⟨Real.sqrt (Real.exp 1+glzUniversalTailConstant)*Real.sqrt Cp,
      mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hCp),?_⟩
    intro σ hσ N hN
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
    have hy := hpart N hN
    have hxi : Integrable (fun ω=>Real.exp (2*X ω)) (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by simpa only [hXX] using hx.1
    have hyi : Integrable (fun ω=>Real.exp (2*Y ω)) (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by simpa only [hYY] using hy.1
    obtain ⟨hi,hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y hX.aemeasurable hY.aemeasurable hxi hyi
    have hSum (ω : Fin N→E) : X ω+Y ω=sourceRieszTransportAllBetaExponent ρ s M n β σ K v N ω := by
      exact (sourceRieszTransportAllBetaExponent_large ρ s M n β σ K v N hlarge ω).symm
    simp_rw [hSum] at hi hb
    simp_rw [hXX,hYY] at hb
    exact ⟨hi,hb.trans (mul_le_mul (Real.sqrt_le_sqrt hx.2) (Real.sqrt_le_sqrt hy.2.2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszTransportEpsilon
#print axioms DGRHS.Commutator.sourceRieszTransportEpsilon

#check DGRHS.Commutator.sourceRieszTransportEpsilon_pos
#print axioms DGRHS.Commutator.sourceRieszTransportEpsilon_pos

#check DGRHS.Commutator.sourceRieszTransportAllBetaExponent
#print axioms DGRHS.Commutator.sourceRieszTransportAllBetaExponent

#check DGRHS.Commutator.sourceRieszTransportAllBetaExponent_large
#print axioms DGRHS.Commutator.sourceRieszTransportAllBetaExponent_large

#check DGRHS.Commutator.sourceRieszTransport_allBeta_numerator
#print axioms DGRHS.Commutator.sourceRieszTransport_allBeta_numerator
