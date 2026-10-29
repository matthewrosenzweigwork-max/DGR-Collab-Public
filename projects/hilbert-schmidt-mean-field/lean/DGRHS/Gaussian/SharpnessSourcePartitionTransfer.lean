import DGRHS.Gaussian.SharpnessCriticalPartitionDivergence
import DGRHS.Gaussian.SharpnessSupercriticalPartitionDivergence
import DGRHS.CLT.IidCanonicalNormalization

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical Topology
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

/-- Literal source affine energy comparison, with proper source weights
proved directly from the bounded physical potential. -/
theorem sharpness_riesz_source_partition_lower (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι:ℝ)-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) (hN : 1 ≤ N) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable (fun x => Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H F I N x))
      (Measure.pi (fun _ => μ)) ∧
    Real.exp (-β*I)*(∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x)
      ∂Measure.pi (fun _ => μ)) ≤
      ∫ x,Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H F I N x)
        ∂Measure.pi (fun _ => μ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  let P := Measure.pi (fun _ : Fin N => μ)
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  let stat := sourceKernelParticleStatistic H N
  let avg := fun x : Fin N → EuclideanSpace ℝ ι => (N:ℝ)⁻¹*∑ i : Fin N,F (x i)
  let A := fun x => -β/2*stat x
  let Y := fun x => A x+β*avg x-β*I
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hF := DGRHS.integrable_potential μ W (sharpness_riesz_pair_integrable s hs ha ρ M hM hρ)
  have hstat := sharpness_particle_integrable μ H (sharpness_centered_riesz_integrable s hs ha ρ M hM hρ) N
  have havg : Integrable avg P := (integrable_finsetSum Finset.univ
    (fun i _ => (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable hF)).const_mul _
  have hY : Integrable Y P := ((hstat.const_mul (-β/2)).add (havg.const_mul β)).sub (integrable_const _)
  have hB : 0 ≤ B := ((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
    (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2
  have hCanon := sharpness_particle_exponential_integrable H hstat (2*B) (by positivity)
    (fun p => by simpa only [neg_mul] using sharpness_centered_riesz_pointwise_lower s hs ha ρ M hM hρ p) hN β hβ
  have hBounds (x : Fin N → EuclideanSpace ℝ ι) : 0 ≤ avg x ∧ avg x ≤ B := by
    have hp (i : Fin N) := (sharpness_riesz_potential_bound s hs ha ρ M hM hρ (x i)).2
    constructor
    · apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
      exact Finset.sum_nonneg (fun i _ => (hp i).1)
    · have hh : (∑ i : Fin N,F (x i)) ≤ (N:ℝ)*B := by
        calc
          _ ≤ ∑ _i : Fin N,B := Finset.sum_le_sum (fun i _ => (hp i).2)
          _ = _ := by simp
      have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Nat.cast_nonneg N))
      simpa only [←mul_assoc,inv_mul_cancel₀ hn,one_mul] using hh'
  have hUpper (x) : Real.exp (Y x) ≤ Real.exp (β*B-β*I)*Real.exp (A x) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [Y]
    nlinarith [mul_le_mul_of_nonneg_left (hBounds x).2 hβ]
  have hProper : Integrable (fun x => Real.exp (Y x)) P :=
    (hCanon.const_mul _).mono' (Real.continuous_exp.comp_aestronglyMeasurable hY.aestronglyMeasurable)
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hUpper x))
  have hLower (x) : Real.exp (-β*I)*Real.exp (A x) ≤ Real.exp (Y x) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [Y]
    nlinarith [mul_nonneg hβ (hBounds x).1]
  have he (x : Fin N → EuclideanSpace ℝ ι) :
      -β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H F I N x = Y x := by
    rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent H F I β (by omega)]
    rw [←DGRHS.CLT.sourceStatistic_eq_normalized]
  change Integrable (fun x => Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H F I N x)) P ∧
    Real.exp (-β*I)*(∫ x,Real.exp (A x) ∂P) ≤
      ∫ x,Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H F I N x) ∂P
  simp_rw [he]
  refine ⟨hProper,?_⟩
  rw [←integral_const_mul]
  exact integral_mono (hCanon.const_mul _) hProper hLower

/-- Original literal canonical source partition divergence, including the
critical endpoint, with all physical properness hypotheses discharged. -/
theorem sharpness_riesz_source_partition_diverges (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι:ℝ)-s) (hsharp : (Fintype.card ι:ℝ) ≤ 2*s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (β : ℝ) (hβ : 0 < β) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    (∀ N : ℕ,1 ≤ N → Integrable (fun x => Real.exp
      (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H (DGRHS.potential μ W)
        (DGRHS.interactionEnergy μ W) N x)) (Measure.pi (fun _ => μ))) ∧
    Tendsto (fun N : ℕ => ∫ x,Real.exp
      (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy H (DGRHS.potential μ W)
        (DGRHS.interactionEnergy μ W) N x) ∂Measure.pi (fun _ => μ)) atTop atTop := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
  have hz : Tendsto (fun N : ℕ => ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x)
      ∂Measure.pi (fun _ => μ)) atTop atTop := by
    rcases hsharp.eq_or_lt with he|hlt
    · exact (sharpness_critical_centered_partition_diverges s hs he.symm ρ hρm M hM hρ β hβ).2
    · exact (sharpness_supercritical_centered_partition_diverges s hs ha hlt ρ hρm M hM hρ β hβ).2
  refine ⟨fun N hN => (sharpness_riesz_source_partition_lower s hs ha ρ M hM hρ β hβ.le N hN).1,?_⟩
  have ht := Tendsto.const_mul_atTop (Real.exp_pos (-β*DGRHS.interactionEnergy μ W)) hz
  apply tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (sharpness_riesz_source_partition_lower s hs ha ρ M hM hρ β hβ.le N hN).2

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_riesz_source_partition_lower
#print axioms DGRHS.Gaussian.sharpness_riesz_source_partition_diverges
#check @DGRHS.Gaussian.sharpness_riesz_source_partition_diverges
