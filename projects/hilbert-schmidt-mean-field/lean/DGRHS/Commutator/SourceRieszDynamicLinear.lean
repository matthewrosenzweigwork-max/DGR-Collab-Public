import DGRHS.Commutator.SourceRieszCommonPartition
import DGRHS.Commutator.SourceRieszTransportGibbs
import DGRHS.Dynamics.BoundedRawProductLinearMGF
import DGRHS.Entropy.AbsoluteExponentialTransfer

/-! Original positive-Riesz dynamicEntropyTransfers(iii): actual bounded
measurable raw fluctuation, before any L2 representative is chosen. Actual
product Hoeffding, doubled literal source partition and lower normalizer >=1
supply the Gibbs moments; finite literal Gibbs KL supplies proper absolute
expectation. No desired MGF, moment or expectation is a hypothesis. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Concentration DGRHS.Dynamics DGRHS.Entropy
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszDynamicRawFluctuation (ρ q : E→ℝ) (N : ℕ) (ω : Fin N→E) : ℝ :=
  (Real.sqrt N)⁻¹*∑ i : Fin N,(q (ω i)-∫ y,q y ∂gaussianRieszDensityMeasure ρ)

lemma measurable_sourceRieszDynamicRawFluctuation (ρ q : E→ℝ) (hq : Measurable q) (N : ℕ) :
    Measurable (sourceRieszDynamicRawFluctuation ρ q N) := by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact (hq.comp (measurable_pi_apply i)).sub_const _

/-- Actual normalized literal-Gibbs MGF from the doubled source partition cap. -/
theorem sourceRieszDynamicLinear_Gibbs_two_signs (s β : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ))
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N) (C₂ L : ℝ) (hL : 0≤L)
    (hC₂ : (sourceRieszSingularPartition s (2*β) ρ N).toReal≤C₂)
    (q : E→ℝ) (hq : Measurable q) (a b : ℝ)
    (hqbound : ∀ x,q x∈Set.Icc a b) (hwidth : ‖b-a‖≤L)
    (σ : ℝ) (hσ : |σ|=1) :
    Integrable (fun ω=>Real.exp (σ*sourceRieszDynamicRawFluctuation ρ q N ω))
      (sourceRieszSingularGibbs s β ρ N) ∧
    (∫ ω,Real.exp (σ*sourceRieszDynamicRawFluctuation ρ q N ω)
      ∂sourceRieszSingularGibbs s β ρ N)≤Real.sqrt (Real.exp (L^2/2))*Real.sqrt C₂ := by
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let S := sourceRieszDynamicRawFluctuation ρ q N
  let X := sourceRieszLocalParticleExponent ρ s β N
  let Y := fun ω=>σ*S ω
  have hn : 0<N := by omega
  have hX : Measurable X := measurable_sourceRieszLocalParticleExponent ρ s β N hn
  have hY : Measurable Y := (measurable_sourceRieszDynamicRawFluctuation ρ q hq N).const_mul σ
  obtain ⟨_,_,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  obtain ⟨_,_,hPart₂⟩ := sourceRieszLocalParticleWeight_uniform s (2*β) hs (by positivity) hd ρ M hM hρ
  have hXX (ω : Fin N→E) : 2*X ω=sourceRieszLocalParticleExponent ρ s (2*β) N ω := by
    dsimp [X,sourceRieszLocalParticleExponent]
    ring
  have hXi : Integrable (fun ω=>Real.exp (2*X ω)) P := by
    simpa only [hXX] using (hPart₂ N hN).1
  have hXB : (∫ ω,Real.exp (2*X ω) ∂P)≤C₂ := by
    have hnonneg : 0≤physicalRieszSourcePartition s (2*β) ρ N := integral_nonneg fun _=>(Real.exp_pos _).le
    rw [sourceRieszSingularPartition_eq_integral s (2*β) hs (by positivity) (by linarith) ρ M hM hρ N,
      ENNReal.toReal_ofReal hnonneg] at hC₂
    simp_rw [hXX]
    exact hC₂
  obtain ⟨hYi,hYB⟩ := boundedRawProductLinearMGF (μ:=μ) q hq a b hqbound (2*σ) N
  have hcoef : ((((‖b-a‖₊/2)^2:ℝ≥0):ℝ))=(‖b-a‖/2)^2 := by simp
  have hsq : σ^2=1 := by nlinarith [sq_abs σ]
  have hw : ‖b-a‖^2≤L^2 := by nlinarith [sq_nonneg (L-‖b-a‖),norm_nonneg (b-a)]
  have hYY (ω : Fin N→E) : 2*Y ω=(2*σ)*sourceRieszDynamicRawFluctuation ρ q N ω := by dsimp [Y,S];ring
  have hYproper : Integrable (fun ω=>Real.exp (2*Y ω)) P := by simpa only [hYY,sourceRieszDynamicRawFluctuation] using hYi
  have hYbound : (∫ ω,Real.exp (2*Y ω) ∂P)≤Real.exp (L^2/2) := by
    simp_rw [hYY]
    apply hYB.trans
    apply Real.exp_le_exp.mpr
    rw [hcoef]
    nlinarith
  obtain ⟨hNum,hNumB⟩ := exponential_sum_integral_cs X Y hX.aemeasurable hY.aemeasurable hXi hYproper
  have hNB : (∫ ω,Real.exp (X ω+Y ω) ∂P)≤Real.sqrt (Real.exp (L^2/2))*Real.sqrt C₂ := by
    have h := hNumB.trans (mul_le_mul (Real.sqrt_le_sqrt hXB) (Real.sqrt_le_sqrt hYbound)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    simpa only [mul_comm] using h
  rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
  have hProper : Integrable (fun ω=>Real.exp (Y ω)) (P.tilted X) := by
    apply (integrable_tilted_iff (hPart N hN).1 _).mpr
    apply hNum.congr
    exact ae_of_all _ fun ω=>by change Real.exp (X ω+Y ω)=Real.exp (X ω)*Real.exp (Y ω);rw [Real.exp_add]
  refine ⟨hProper,?_⟩
  change (∫ ω,Real.exp (Y ω) ∂P.tilted X)≤_
  rw [integral_exp_tilted]
  have hZ : 0<(∫ ω,Real.exp (X ω) ∂P) := by linarith [(hPart N hN).2.1]
  apply (div_le_iff₀ hZ).mpr
  exact hNB.trans (le_mul_of_one_le_right (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hPart N hN).2.1)

/-- Common absolute fluctuation bound from the actual entropy and doubled
normalizer controls. Width, not the interval location, controls the test. -/
theorem sourceRieszDynamicLinear_absolute_bound (s β : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ)) (H L C₂ : ℝ) (hL : 0≤L) :
    ∃ D : ℝ,0≤D ∧ ∀ (ρ : E→ℝ) (M : ℝ),0≤M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ (N : ℕ),1≤N →
      (sourceRieszSingularPartition s (2*β) ρ N).toReal≤C₂ →
      ∀ (q : E→ℝ),Measurable q → ∀ a b : ℝ,
      (∀ x,q x∈Set.Icc a b) → ‖b-a‖≤L →
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ →
      (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal≤H →
      Integrable (sourceRieszDynamicRawFluctuation ρ q N) ν ∧
      (∫ ω,|sourceRieszDynamicRawFluctuation ρ q N ω| ∂ν)≤D := by
  let C := Real.sqrt (Real.exp (L^2/2))*Real.sqrt C₂
  let D := max (H+Real.log (2*C)) 0
  refine ⟨D,le_max_right _ _,?_⟩
  intro ρ M hM hμ hρ N hN hC₂ q hq a b hqbound hwidth ν hν hKL hH
  let S := sourceRieszDynamicRawFluctuation ρ q N
  have hS : StronglyMeasurable S := (measurable_sourceRieszDynamicRawFluctuation ρ q hq N).stronglyMeasurable
  have hp := sourceRieszDynamicLinear_Gibbs_two_signs s β hs hβ hd ρ M hM hρ N hN C₂ L hL hC₂ q hq a b hqbound hwidth 1 (by norm_num)
  have hm := sourceRieszDynamicLinear_Gibbs_two_signs s β hs hβ hd ρ M hM hρ N hN C₂ L hL hC₂ q hq a b hqbound hwidth (-1) (by norm_num)
  let _ := sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
  obtain ⟨hi,hb⟩ := entropy_absolute_expectation_scaled_of_two_exponential_bounds
    (sourceRieszSingularGibbs s β ρ N) ν S hS 1 (by norm_num)
    (by simpa only [one_mul] using hp.1) (by simpa only [neg_one_mul,one_mul] using hm.1) hKL C
    (by simpa only [one_mul] using hp.2) (by simpa only [neg_one_mul,one_mul] using hm.2)
  refine ⟨hi,?_⟩
  simp only [inv_one,one_mul] at hb
  exact (hb.trans (add_le_add hH le_rfl)).trans (le_max_left _ _)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszDynamicRawFluctuation
#print axioms DGRHS.Commutator.sourceRieszDynamicRawFluctuation
#check @DGRHS.Commutator.measurable_sourceRieszDynamicRawFluctuation
#print axioms DGRHS.Commutator.measurable_sourceRieszDynamicRawFluctuation
#check @DGRHS.Commutator.sourceRieszDynamicLinear_Gibbs_two_signs
#print axioms DGRHS.Commutator.sourceRieszDynamicLinear_Gibbs_two_signs
#check @DGRHS.Commutator.sourceRieszDynamicLinear_absolute_bound
#print axioms DGRHS.Commutator.sourceRieszDynamicLinear_absolute_bound
