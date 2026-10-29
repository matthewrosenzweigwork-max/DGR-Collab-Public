import DGRHS.Commutator.SourceRieszLocalNumerator
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Genuine finite empirical product integrals for the singular Riesz
transport kernel. Proper every-x density sections and finite atomic
integrability justify all four offcollision terms; no bounded-kernel premise. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace DGRHS.Commutator
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

def sourceRieszLocalEmpiricalLaw (N : ℕ) (ω : Fin N→X) : Measure X :=
  (N:ℝ≥0)⁻¹ • Measure.sum (fun i : Fin N=>Measure.dirac (ω i))

instance sourceRieszLocalEmpiricalLaw_finite (N : ℕ) (ω : Fin N→X) :
    IsFiniteMeasure (sourceRieszLocalEmpiricalLaw N ω) := by
  unfold sourceRieszLocalEmpiricalLaw
  infer_instance

omit [MeasurableSingletonClass X] in
lemma sourceRieszLocalEmpiricalLaw_probability (N : ℕ) (hN : 0<N) (ω : Fin N→X) :
    IsProbabilityMeasure (sourceRieszLocalEmpiricalLaw N ω) := by
  constructor
  have hm : (Measure.sum (fun i : Fin N=>Measure.dirac (ω i))) univ=(N:ℝ≥0∞) := by simp
  rw [sourceRieszLocalEmpiricalLaw,Measure.coe_nnreal_smul_apply,hm]
  change (↑((N:ℝ≥0)⁻¹):ℝ≥0∞)*↑(N:ℝ≥0)=1
  rw [←ENNReal.coe_mul,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')]
  rfl

lemma integrable_sourceRieszLocalEmpiricalLaw (N : ℕ) (ω : Fin N→X) (f : X→ℝ) :
    Integrable f (sourceRieszLocalEmpiricalLaw N ω) := by
  have hi : Integrable f (Measure.sum (fun i : Fin N=>Measure.dirac (ω i))) :=
    integrable_sum_measure (fun _=>integrable_dirac (by simp)) (hasSum_fintype (fun i : Fin N=>∫ x,‖f x‖ ∂Measure.dirac (ω i))).summable
  exact hi.smul_measure_nnreal

lemma integral_sourceRieszLocalEmpiricalLaw (N : ℕ) (ω : Fin N→X) (f : X→ℝ) :
    (∫ x,f x ∂sourceRieszLocalEmpiricalLaw N ω)=(N:ℝ)⁻¹*∑ i : Fin N,f (ω i) := by
  have hi : Integrable f (Measure.sum (fun i : Fin N=>Measure.dirac (ω i))) :=
    integrable_sum_measure (fun _=>integrable_dirac (by simp)) (hasSum_fintype (fun i : Fin N=>∫ x,‖f x‖ ∂Measure.dirac (ω i))).summable
  rw [sourceRieszLocalEmpiricalLaw,integral_smul_nnreal_measure,integral_sum_measure hi]
  simp [tsum_fintype,NNReal.smul_def,NNReal.coe_inv]

lemma sourceRieszLocalEmpirical_pair (ν : Measure X) [IsFiniteMeasure ν]
    (h : X×X→ℝ) (hm : Measurable h) (hi : ∀ x,Integrable (fun y=>h (x,y)) ν)
    (N : ℕ) (ω : Fin N→X) :
    Integrable h ((sourceRieszLocalEmpiricalLaw N ω).prod ν) ∧
    (∫ p,h p ∂(sourceRieszLocalEmpiricalLaw N ω).prod ν)=
      (N:ℝ)⁻¹*∑ i : Fin N,∫ y,h (ω i,y) ∂ν := by
  have hp : Integrable h ((sourceRieszLocalEmpiricalLaw N ω).prod ν) :=
    (integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hi,integrable_sourceRieszLocalEmpiricalLaw N ω _⟩
  refine ⟨hp,?_⟩
  rw [integral_prod _ hp]
  exact integral_sourceRieszLocalEmpiricalLaw N ω _

lemma sourceRieszLocalEmpirical_square (h : X×X→ℝ) (hm : Measurable h)
    (N : ℕ) (ω : Fin N→X) :
    Integrable h ((sourceRieszLocalEmpiricalLaw N ω).prod (sourceRieszLocalEmpiricalLaw N ω)) ∧
    (∫ p,h p ∂(sourceRieszLocalEmpiricalLaw N ω).prod (sourceRieszLocalEmpiricalLaw N ω))=
      ((N:ℝ)^2)⁻¹*∑ i : Fin N,∑ j : Fin N,h (ω i,ω j) := by
  have hp := sourceRieszLocalEmpirical_pair (sourceRieszLocalEmpiricalLaw N ω) h hm
    (fun _=>integrable_sourceRieszLocalEmpiricalLaw N ω _) N ω
  refine ⟨hp.1,?_⟩
  rw [hp.2]
  simp_rw [integral_sourceRieszLocalEmpiricalLaw]
  rw [←Finset.mul_sum]
  simp only [pow_two,mul_inv_rev]
  ring

section Physical
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszLocalTransport_restrict_offCollision (ν : Measure (E×E)) (n : ℕ) (s : ℝ) (v : E→E) :
    (∫ p in {p : E×E | p.1 ≠ p.2},sourceRieszTransportKernel n s v p ∂ν)=
      ∫ p,sourceRieszTransportKernel n s v p ∂ν := by
  classical
  have hs : MeasurableSet {p : E×E | p.1 ≠ p.2} := (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  rw [←integral_indicator hs]
  congr 1
  funext p
  by_cases hp : p.1=p.2 <;> simp [Set.indicator,hp,sourceRieszTransportKernel]

/-- Exact source offcollision signed empirical-square observable, with proper
product integrals, including configurations with repeated spatial locations. -/
theorem sourceRieszLocalTransportEnergy_offCollision (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 0<N) (ω : Fin N→E) :
    let μ := gaussianRieszDensityMeasure ρ
    let μN := sourceRieszLocalEmpiricalLaw N ω
    let h := sourceRieszTransportKernel n s v
    Integrable h (μN.prod μN) ∧ Integrable h (μN.prod μ) ∧ Integrable h (μ.prod μN) ∧ Integrable h (μ.prod μ) ∧
    sourceRieszLocalTransportEnergy ρ s n v N ω=
      (∫ p in {p : E×E | p.1 ≠ p.2},h p ∂μN.prod μN)-
      (∫ p in {p : E×E | p.1 ≠ p.2},h p ∂μN.prod μ)-
      (∫ p in {p : E×E | p.1 ≠ p.2},h p ∂μ.prod μN)+
      (∫ p in {p : E×E | p.1 ≠ p.2},h p ∂μ.prod μ) := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  let μN := sourceRieszLocalEmpiricalLaw N ω
  let h := sourceRieszTransportKernel n s v
  have hm := measurable_sourceRieszTransportKernel s n hv
  have hsq := sourceRieszLocalEmpirical_square h hm N ω
  have hpair := sourceRieszLocalEmpirical_pair μ h hm
    (fun x=>(sourceRieszLocalTransport_section s n hs (by linarith) hv ρ M hM hρ x).1) N ω
  have hswap : (fun p : E×E=>h p.swap)=h := by
    funext p
    exact sourceRieszTransportKernel_symmetric s n v p
  have hiRev : Integrable h (μ.prod μN) := by
    have hp : Integrable (fun p : E×E=>h p.swap) (μ.prod μN) := integrable_swap_iff.mpr hpair.1
    rw [hswap] at hp
    exact hp
  refine ⟨hsq.1,hpair.1,hiRev,(sourceRieszLocalTransport_pair s n hs hd hv ρ M hM hρ).1,?_⟩
  simp_rw [sourceRieszLocalTransport_restrict_offCollision]
  have hIntSwap : (∫ p,h p ∂μ.prod μN)=∫ p,h p ∂μN.prod μ := by
    rw [←integral_prod_swap]
    rw [hswap]
  rw [hIntSwap,hsq.2,hpair.2,sourceRieszLocalTransportEnergy_raw ρ s n v N hN]
  have hsum : DGRHS.CanonicalVariance.offDiagonalSum h ω=∑ i : Fin N,∑ j : Fin N,h (ω i,ω j) := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    have hp := Finset.sum_union (f:=fun p : Fin N×Fin N=>h (ω p.1,ω p.2))
      (Finset.disjoint_diag_offDiag (Finset.univ : Finset (Fin N)))
    rw [Finset.diag_union_offDiag,Finset.sum_product] at hp
    have hz : (∑ p ∈ (Finset.univ : Finset (Fin N)).diag,h (ω p.1,ω p.2))=0 := by
      simp [Finset.diag,h,sourceRieszTransportKernel]
    rw [hz,zero_add] at hp
    exact hp.symm
  rw [hsum]
  ring

end Physical
end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocalEmpiricalLaw
#print axioms DGRHS.Commutator.sourceRieszLocalEmpiricalLaw

#check DGRHS.Commutator.sourceRieszLocalEmpiricalLaw_probability
#print axioms DGRHS.Commutator.sourceRieszLocalEmpiricalLaw_probability

#check DGRHS.Commutator.integrable_sourceRieszLocalEmpiricalLaw
#print axioms DGRHS.Commutator.integrable_sourceRieszLocalEmpiricalLaw

#check DGRHS.Commutator.integral_sourceRieszLocalEmpiricalLaw
#print axioms DGRHS.Commutator.integral_sourceRieszLocalEmpiricalLaw

#check DGRHS.Commutator.sourceRieszLocalEmpirical_pair
#print axioms DGRHS.Commutator.sourceRieszLocalEmpirical_pair

#check DGRHS.Commutator.sourceRieszLocalEmpirical_square
#print axioms DGRHS.Commutator.sourceRieszLocalEmpirical_square

#check DGRHS.Commutator.sourceRieszLocalTransport_restrict_offCollision
#print axioms DGRHS.Commutator.sourceRieszLocalTransport_restrict_offCollision

#check DGRHS.Commutator.sourceRieszLocalTransportEnergy_offCollision
#print axioms DGRHS.Commutator.sourceRieszLocalTransportEnergy_offCollision
