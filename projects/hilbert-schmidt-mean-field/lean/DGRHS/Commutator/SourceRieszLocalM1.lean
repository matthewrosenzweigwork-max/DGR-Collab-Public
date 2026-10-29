import DGRHS.Commutator.SourceRieszLocalStatisticAlgebra
import DGRHS.Commutator.SourceRieszLocalAdaptiveSize
import DGRHS.CLT.SourceTiltedJointFactory
import DGRHS.Concentration.SourcePartitionRate

/-! Actual source local exponent and physical master event reduction. The
Gaussian widening is fixed at two. No event comparison, exponential bound,
or desired source-energy conclusion is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszLocalPhysicalPotential (ρ : E→ℝ) (s : ℝ) (x : E) : ℝ :=
  ∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ

def sourceRieszLocalPhysicalEnergy (ρ : E→ℝ) (s : ℝ) : ℝ :=
  (1/2:ℝ)*(∫ p,gaussianRieszPhysicalPair s p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))

def sourceRieszLocalAbsorptionConstant (s M : ℝ) : ℝ :=
  1+(7/4:ℝ)*sourceRieszLocalShortPotential (ι:=ι) s 1 M

def sourceRieszLocalExponent (ρ : E→ℝ) (s M : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0) (v : E→E)
    (N : ℕ) (ω : Fin N→E) : ℝ :=
  (3/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s M ι-
    2*σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*iidNegativeStatistic N
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszTransportKernel n s v)) ω+
    DGRHS.CLT.sourceParticleExponent (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) γ N ω

lemma sourceRieszLocal_energy_normalization (β : ℝ) (h : E×E→ℝ) (N : ℕ) (ω : Fin N→E) :
    β*iidNegativeStatistic N h ω=-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h ω := by
  have hSum : iidCoupledSum N h ω=∑ i : Fin N,∑ j : Fin N,if i=j then 0 else h (ω i,ω j) := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    simp only [ne_eq,ite_not]
  rw [←sourceKernelParticleStatistic_eq_normalized]
  unfold iidNegativeStatistic sourceKernelParticleStatistic
  rw [hSum]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma sourceRieszLocalAbsorptionConstant_pos (s M : ℝ) (hs : 0<s)
    (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) : 0<sourceRieszLocalAbsorptionConstant (ι:=ι) s M := by
  have h := sourceRieszLocalShortPotential_nonneg (ι:=ι) s 1 M hs (by norm_num) hM hd
  unfold sourceRieszLocalAbsorptionConstant
  linarith

lemma sourceRieszLocalShortAbsorption_scale (s η M : ℝ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) :
    (7/4:ℝ)*sourceRieszLocalShortPotential (ι:=ι) s η M≤
      sourceRieszLocalAbsorptionConstant (ι:=ι) s M*η^((Fintype.card ι:ℝ)-s) := by
  have hp : 0≤η^((Fintype.card ι:ℝ)-s) := Real.rpow_nonneg hη.le _
  simp only [sourceRieszLocalShortPotential,sourceRieszLocalAbsorptionConstant,Real.one_rpow]
  nlinarith

lemma sourceRieszLocal_oneBody_bound (ρ : E→ℝ) (s M γ : ℝ) (hs : 0<s)
    (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hγ : 0≤γ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N) (ω : Fin N→E) :
    γ*((N:ℝ)⁻¹*∑ i : Fin N,sourceRieszLocalPhysicalPotential ρ s (ω i))-
      γ*sourceRieszLocalPhysicalEnergy ρ s ≤ γ*gaussianRieszPhysicalPotentialConstant s M ι := by
  have hn : 0<(N:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN)
  have hsum : (∑ i : Fin N,sourceRieszLocalPhysicalPotential ρ s (ω i))≤
      (N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι := by
    calc
      _ ≤ ∑ _ : Fin N,gaussianRieszPhysicalPotentialConstant s M ι :=
        Finset.sum_le_sum (fun i _=>(sourceRiesz_full_potential_bound s hs hd ρ M hM hρ (ω i)).2.2)
      _ = _ := by simp
  have hmean : 0≤sourceRieszLocalPhysicalEnergy ρ s := by
    unfold sourceRieszLocalPhysicalEnergy
    apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun p=>by unfold gaussianRieszPhysicalPair;positivity)
  have ha : (N:ℝ)⁻¹*(∑ i : Fin N,sourceRieszLocalPhysicalPotential ρ s (ω i))≤gaussianRieszPhysicalPotentialConstant s M ι := by
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using h
  nlinarith [mul_le_mul_of_nonneg_left ha hγ]

lemma ae_sourceRieszLocalExponent_cutoff_bound (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ),
      sourceRieszLocalExponent ρ s M n γ σ K v N ω ≤
        (7/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s M ι+
          (1/2:ℝ)*iidNegativeStatistic N (sourceRieszLocalCenteredCutoff (gaussianRieszDensityMeasure ρ) s η n γ σ K v) ω+
          sourceRieszLocalAbsorptionConstant (ι:=ι) s M*γ*(N:ℝ)*η^((Fintype.card ι:ℝ)-s) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hT := ae_physical_iidNegativeStatistic_congr μ N _ _
    (ae_sourceRieszLocalCenteredTransport_split s η n hs hη (by linarith) hv ρ M hM hρ)
  have hE := ae_physical_iidNegativeStatistic_congr μ N _ _
    (ae_sourceRieszLocalCenteredEnergy_split s (2*η) hs (by positivity) hd ρ M hM hρ)
  have hQ := ae_sourceRieszLocalCutoff_statistic μ s η n γ σ hs hη hv N
  filter_upwards [hT,hE,hQ] with ω hωT hωE hωQ
  rw [physical_iidNegativeStatistic_add] at hωT hωE
  have hS := sourceRieszLocalShortAbsorption_statistic s η n hs hη (by linarith) γ σ hγ hσ hv ρ M hM hρ N hN ω
  have hB := sourceRieszLocal_oneBody_bound ρ s M γ hs (by linarith) hM hγ hρ N hN ω
  have hA := mul_le_mul_of_nonneg_left (sourceRieszLocalShortAbsorption_scale s η M hs hη (by linarith) hM)
    (by positivity : 0≤γ*(N:ℝ))
  unfold sourceRieszLocalExponent DGRHS.CLT.sourceParticleExponent
  rw [←sourceRieszLocal_energy_normalization γ,hωT,hωE]
  nlinarith [hS,hB,hA,hωQ]

lemma ae_sourceRieszLocal_event_reduction (s : ℝ) (n : ℕ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0<γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (hsmall : (7/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s M ι≤1/4)
    (u : ℝ) (hu : 1≤u) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ),
      u≤sourceRieszLocalExponent ρ s M n γ σ K v N ω →
      u ≤ iidNegativeStatistic N (sourceRieszLocalCenteredCutoff (gaussianRieszDensityMeasure ρ) s
        (sourceRieszLocalAdaptiveScale (ι:=ι) s (sourceRieszLocalAbsorptionConstant (ι:=ι) s M) γ N u) n γ σ K v) ω := by
  let C := sourceRieszLocalAbsorptionConstant (ι:=ι) s M
  let η := sourceRieszLocalAdaptiveScale (ι:=ι) s C γ N u
  have hC : 0<C := sourceRieszLocalAbsorptionConstant_pos s M hs (by linarith) hM
  have hn : 0<(N:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN)
  have hu0 : 0<u := by linarith
  have hη : 0<η := (gaussianRieszAdaptiveScale_pos_le 1 (4*C*γ) N u (Fintype.card ι) s (by norm_num) (by positivity) hn hu0).1
  have hp := gaussianRieszAdaptiveScale_power_le 1 (4*C*γ) N u (Fintype.card ι) s (by norm_num) (by positivity) hn hu0 (by linarith)
  have hlast : C*γ*(N:ℝ)*η^((Fintype.card ι:ℝ)-s)≤u/4 := by
    have h := mul_le_mul_of_nonneg_left hp (by positivity : 0≤C*γ*(N:ℝ))
    change C*γ*(N:ℝ)*η^((Fintype.card ι:ℝ)-s)≤C*γ*(N:ℝ)*(u/(4*C*γ*(N:ℝ))) at h
    convert h using 1 <;> field_simp [hC.ne',hγ.ne',hn.ne'] <;> ring
  filter_upwards [ae_sourceRieszLocalExponent_cutoff_bound s η n hs hη hd γ σ hγ.le hσ hv ρ M hM hρ N hN] with ω hω
  intro hx
  change sourceRieszLocalExponent ρ s M n γ σ K v N ω≤_ at hω
  nlinarith [hω,hsmall,hlast,hu]

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocalPhysicalPotential
#print axioms DGRHS.Commutator.sourceRieszLocalPhysicalPotential

#check DGRHS.Commutator.sourceRieszLocalPhysicalEnergy
#print axioms DGRHS.Commutator.sourceRieszLocalPhysicalEnergy

#check DGRHS.Commutator.sourceRieszLocalAbsorptionConstant
#print axioms DGRHS.Commutator.sourceRieszLocalAbsorptionConstant

#check DGRHS.Commutator.sourceRieszLocalExponent
#print axioms DGRHS.Commutator.sourceRieszLocalExponent

#check DGRHS.Commutator.sourceRieszLocal_energy_normalization
#print axioms DGRHS.Commutator.sourceRieszLocal_energy_normalization

#check DGRHS.Commutator.sourceRieszLocalAbsorptionConstant_pos
#print axioms DGRHS.Commutator.sourceRieszLocalAbsorptionConstant_pos

#check DGRHS.Commutator.sourceRieszLocalShortAbsorption_scale
#print axioms DGRHS.Commutator.sourceRieszLocalShortAbsorption_scale

#check DGRHS.Commutator.sourceRieszLocal_oneBody_bound
#print axioms DGRHS.Commutator.sourceRieszLocal_oneBody_bound

#check DGRHS.Commutator.ae_sourceRieszLocalExponent_cutoff_bound
#print axioms DGRHS.Commutator.ae_sourceRieszLocalExponent_cutoff_bound

#check DGRHS.Commutator.ae_sourceRieszLocal_event_reduction
#print axioms DGRHS.Commutator.ae_sourceRieszLocal_event_reduction
