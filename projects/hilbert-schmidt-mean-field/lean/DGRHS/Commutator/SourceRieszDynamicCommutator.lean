import DGRHS.Commutator.SourceRieszCommonGibbs
import DGRHS.Commutator.SourceRieszEntropicTransport
import DGRHS.Entropy.AbsoluteExponentialTransfer

/-! Original positive-Riesz dynamicEntropyTransfers(ii). Actual same-kernel
common literal-Gibbs moments give proper ABSOLUTE first commutator expectation.
K=0 included through the proved positive transport parameter. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRieszDynamic_common_commutator (s β M H : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (K : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (v : E→E),LipschitzWith K v → ∀ (ρ : E→ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ N : ℕ,1≤N →
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ →
      (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal≤H →
      Integrable (sourceRieszLocalTransportEnergy ρ s 1 v N) ν ∧
      (∫ ω,|sourceRieszLocalTransportEnergy ρ s 1 v N ω| ∂ν)≤D/(N:ℝ) := by
  obtain ⟨C,hC,hmom⟩ := sourceRieszCommon_Gibbs_moment (ι:=ι) s M 1 (by omega) hs hd hM β hβ
  let ε := sourceRieszPositiveTransportParameter (ι:=ι) s M 1 K β
  have hε : 0<ε := sourceRieszPositiveTransportParameter_pos s M 1 K β hs hd hM hβ
  let D := max (ε⁻¹*(H+Real.log (2*C))) 0
  refine ⟨D,le_max_right _ _,?_⟩
  intro v hv ρ hprob hρ N hN ν hν hKL hH
  let Q := sourceRieszSingularGibbs s β ρ N
  letI := sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
  let a := sourceRieszLocalTransportEnergy ρ s 1 v N
  have ha : StronglyMeasurable (fun ω=>(N:ℝ)*a ω) :=
    (measurable_sourceRieszScaledTransportEnergy ρ s 1 hv N hN).stronglyMeasurable
  have hp := (hmom K v hv).2 ρ hprob hρ 1 (by norm_num) N hN
  have hm := (hmom K v hv).2 ρ hprob hρ (-1) (by norm_num) N hN
  have hp' : Integrable (fun ω=>Real.exp (ε*((N:ℝ)*a ω))) Q := by
    simpa only [one_mul,mul_assoc] using hp.1
  have hm' : Integrable (fun ω=>Real.exp (-(ε*((N:ℝ)*a ω)))) Q := by
    simpa only [neg_one_mul,neg_mul,mul_assoc,one_mul] using hm.1
  have hbP : (∫ ω,Real.exp (ε*((N:ℝ)*a ω)) ∂Q)≤C := by
    simpa only [one_mul,mul_assoc] using hp.2
  have hbM : (∫ ω,Real.exp (-(ε*((N:ℝ)*a ω))) ∂Q)≤C := by
    simpa only [neg_one_mul,neg_mul,mul_assoc,one_mul] using hm.2
  obtain ⟨hi,hb⟩ := entropy_absolute_expectation_scaled_of_two_exponential_bounds Q ν
    (fun ω=>(N:ℝ)*a ω) ha ε hε hp' hm' hKL C hbP hbM
  have hn : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hai : Integrable a ν := by
    have h := hi.const_mul (N:ℝ)⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using h
  have he : (fun ω=>|(N:ℝ)*a ω|)=(fun ω=>(N:ℝ)*|a ω|) := by
    funext ω
    rw [abs_mul,abs_of_pos hn]
  rw [he,integral_const_mul] at hb
  have hc := mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr hε.le)
  have hfinal : (N:ℝ)*(∫ ω,|a ω| ∂ν)≤D :=
    (hb.trans (by linarith)).trans (le_max_left _ _)
  exact ⟨hai,(le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hfinal)⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszDynamic_common_commutator
#print axioms DGRHS.Commutator.sourceRieszDynamic_common_commutator
