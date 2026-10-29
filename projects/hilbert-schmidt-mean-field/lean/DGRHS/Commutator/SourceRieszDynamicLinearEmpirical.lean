import DGRHS.Commutator.SourceRieszDynamicLinear
import DGRHS.Commutator.SourceRieszLocalEmpirical

/-! Literal empirical observable and genuine common-density dynamic(iii) bound.
The doubled partition control is derived from the original physical master,
with its constant chosen before density, test, particle number and law. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszDynamicEmpiricalDifference (ρ q : E→ℝ) (N : ℕ) (ω : Fin N→E) : ℝ :=
  (∫ x,q x ∂sourceRieszLocalEmpiricalLaw N ω)-∫ x,q x ∂gaussianRieszDensityMeasure ρ

lemma sourceRieszDynamicEmpiricalDifference_eq (ρ q : E→ℝ) (N : ℕ) (hN : 1≤N) (ω : Fin N→E) :
    sourceRieszDynamicEmpiricalDifference ρ q N ω=
      (Real.sqrt N)⁻¹*sourceRieszDynamicRawFluctuation ρ q N ω := by
  classical
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hsq := Real.sq_sqrt hn.le
  unfold sourceRieszDynamicEmpiricalDifference sourceRieszDynamicRawFluctuation
  rw [integral_sourceRieszLocalEmpiricalLaw]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hi : (Real.sqrt (N:ℝ))⁻¹*(Real.sqrt (N:ℝ))⁻¹=(N:ℝ)⁻¹ := by
    rw [←mul_inv_rev,←pow_two,hsq]
  rw [←mul_assoc,hi]
  field_simp

/-- Exact source rate, with common constant BEFORE rho, q, N and competitor.
No desired moment or normalizer bound remains among the physical hypotheses. -/
theorem sourceRieszDynamicLinear_common_empirical (s β M H L : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hL : 0≤L) :
    ∃ D : ℝ,0≤D ∧ ∀ (ρ : E→ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x≤M) → ∀ (N : ℕ),1≤N →
      ∀ (q : E→ℝ),Measurable q → ∀ a b : ℝ,
      (∀ x,q x∈Set.Icc a b) → ‖b-a‖≤L →
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ →
      (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal≤H →
      Integrable (sourceRieszDynamicRawFluctuation ρ q N) ν ∧
      Integrable (sourceRieszDynamicEmpiricalDifference ρ q N) ν ∧
      (∫ ω,|sourceRieszDynamicEmpiricalDifference ρ q N ω| ∂ν)≤D/Real.sqrt N := by
  obtain ⟨C₂,hC₂pos,hC₂⟩ := sourceRieszCommon_particle_moment (ι:=ι) s (2*β) M hs (by positivity) hM hd
  obtain ⟨D,hD,hbound⟩ := sourceRieszDynamicLinear_absolute_bound (ι:=ι) s β hs hβ hd H L C₂ hL
  refine ⟨D,hD,?_⟩
  intro ρ hprob hρ N hN q hq a b hqb hwidth ν hν hKL hH
  have hpart : (sourceRieszSingularPartition s (2*β) ρ N).toReal≤C₂ := by
    have hp := hC₂ ρ hprob hρ N hN
    have hnonneg : 0≤DGRHS.Concentration.physicalRieszSourcePartition s (2*β) ρ N :=
      integral_nonneg fun _=>(Real.exp_pos _).le
    rw [sourceRieszSingularPartition_eq_integral s (2*β) hs (by positivity) (by linarith) ρ M hM hρ N,
      ENNReal.toReal_ofReal hnonneg]
    exact hp.2.2
  obtain ⟨hi,hb⟩ := hbound ρ M hM hρ N hN hpart q hq a b hqb hwidth ν hKL hH
  have heq := funext (sourceRieszDynamicEmpiricalDifference_eq ρ q N hN)
  have hiE : Integrable (sourceRieszDynamicEmpiricalDifference ρ q N) ν := by
    rw [heq]
    exact hi.const_mul _
  refine ⟨hi,hiE,?_⟩
  simp_rw [heq,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [integral_const_mul]
  simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszDynamicEmpiricalDifference
#print axioms DGRHS.Commutator.sourceRieszDynamicEmpiricalDifference
#check @DGRHS.Commutator.sourceRieszDynamicEmpiricalDifference_eq
#print axioms DGRHS.Commutator.sourceRieszDynamicEmpiricalDifference_eq
#check @DGRHS.Commutator.sourceRieszDynamicLinear_common_empirical
#print axioms DGRHS.Commutator.sourceRieszDynamicLinear_common_empirical
