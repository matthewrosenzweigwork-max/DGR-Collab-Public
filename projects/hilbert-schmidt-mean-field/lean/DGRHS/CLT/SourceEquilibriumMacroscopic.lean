import DGRHS.CLT.MacroscopicFreeEnergy
import DGRHS.CLT.SourceEquilibriumPartition

/-! Exact original canonical splitting and logarithm on the explicitly finite
potential-energy domain. The literal collision-zero ENNReal partition is
proved positive and finite before its real value is used. Differential entropy
integrability is derived from EL and finite V; it is not a separate premise.
The meaning of "thermal equilibrium measure" in the source must still discharge
finite V before the full original corollary is certified. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian

lemma equilibrium_macroscopic_prefactor {S : Type*} [MeasurableSpace S]
    (ν₀ μ : Measure S) [SigmaFinite ν₀] [NeZero ν₀] [IsProbabilityMeasure μ]
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hW : Integrable (Function.uncurry W) (μ.prod μ)) (hV : Integrable V μ)
    (hEL : ν₀.tilted (fun x => -β * (V x + DGRHS.potential μ W x)) = μ) (N : ℕ) :
    (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂ν₀)^N *
      Real.exp (β * (N : ℝ) * DGRHS.interactionEnergy μ W) =
      Real.exp (-β * (N : ℝ) * macroscopicFreeEnergy ν₀ μ W V β) := by
  let f := fun x => -β * (V x + DGRHS.potential μ W x)
  have hZ := integral_exp_pos (integrable_exp_of_tilted_probability f hEL)
  have h := (equilibrium_entropy_free_energy ν₀ μ W V β hβ hW hV hEL).2.2
  rw [← Real.exp_log hZ, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  dsimp only [f]
  linear_combination -(N : ℝ) * h

lemma log_inv_sqrt_regularizedDet {κ : Type*} (eig : κ → ℝ) (β : ℝ)
    (hD : 0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i)) :
    Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹) =
      -(1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) := by
  rw [Real.log_inv, Real.log_sqrt hD.le]
  ring

variable {ι : Type*} [Fintype ι]

theorem sourceLog_equilibrium_macroscopic (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (V : EuclideanSpace ℝ ι → ℝ)
    (hV : Integrable V (gaussianRieszDensityMeasure ρ))
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -(β : ℝ) *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)) x)) =
      gaussianRieszDensityMeasure ρ) (N : ℕ) (hN : 1 ≤ N) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
    (0 < canonicalSingularPartition volume W V (β : ℝ) N ∧
      canonicalSingularPartition volume W V (β : ℝ) N < ∞) ∧
    Integrable (llr μ volume) μ ∧
    (canonicalSingularPartition volume W V (β : ℝ) N).toReal =
      Real.exp (-(β : ℝ) * (N : ℝ) * macroscopicFreeEnergy volume μ W V (β : ℝ)) *
        (sourceLogSingularPartition β ρ N).toReal ∧
    Real.log (canonicalSingularPartition volume W V (β : ℝ) N).toReal =
      -(β : ℝ) * (N : ℝ) * macroscopicFreeEnergy volume μ W V (β : ℝ) +
        Real.log (sourceLogSingularPartition β ρ N).toReal := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
  have hcanon := sourceLog_equilibrium_canonical β hβ hd ρ M hM hρ hpair V hEL N hN
  have hent := equilibrium_entropy_free_energy volume μ W V (β : ℝ) hβ.ne' hpair hV hEL
  have hfactor := sourceLog_equilibrium_partition β hβ hd ρ M hM hρ hpair V hEL N hN
  dsimp only at hfactor
  have hpre := equilibrium_macroscopic_prefactor volume μ W V (β : ℝ) hβ.ne' hpair hV hEL N
  rw [hpre] at hfactor
  have hproper := sourceLogSingularPartition_pos_finite β hd ρ M hM hρ hpair N
  have hk : 0 < (sourceLogSingularPartition β ρ N).toReal :=
    ENNReal.toReal_pos hproper.1.ne' hproper.2.ne
  refine ⟨⟨hcanon.2.1, hcanon.2.2.1⟩, hent.1, hfactor, ?_⟩
  rw [hfactor, Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp]

theorem sourceRiesz_equilibrium_macroscopic (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (V : EuclideanSpace ℝ ι → ℝ)
    (hV : Integrable V (gaussianRieszDensityMeasure ρ))
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => gaussianRieszPhysicalPair s (a,b)) x)) = gaussianRieszDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    (0 < canonicalSingularPartition volume W V β N ∧
      canonicalSingularPartition volume W V β N < ∞) ∧
    Integrable (llr μ volume) μ ∧
    (canonicalSingularPartition volume W V β N).toReal =
      Real.exp (-β * (N : ℝ) * macroscopicFreeEnergy volume μ W V β) *
        (sourceRieszSingularPartition s β ρ N).toReal ∧
    Real.log (canonicalSingularPartition volume W V β N).toReal =
      -β * (N : ℝ) * macroscopicFreeEnergy volume μ W V β +
        Real.log (sourceRieszSingularPartition s β ρ N).toReal := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  have hpair : Integrable (Function.uncurry W) (μ.prod μ) :=
    (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  have hcanon := sourceRiesz_equilibrium_canonical s β hs hβ ha ρ M hM hρ V hEL N hN
  have hent := equilibrium_entropy_free_energy volume μ W V β hβ.ne' hpair hV hEL
  have hfactor := sourceRiesz_equilibrium_partition s β hs hβ ha ρ M hM hρ V hEL N hN
  dsimp only at hfactor
  have hpre := equilibrium_macroscopic_prefactor volume μ W V β hβ.ne' hpair hV hEL N
  rw [hpre] at hfactor
  have hproper := sourceRieszSingularPartition_pos_finite s β hs hβ.le ha ρ M hM hρ N
  have hk : 0 < (sourceRieszSingularPartition s β ρ N).toReal :=
    ENNReal.toReal_pos hproper.1.ne' hproper.2.ne
  refine ⟨⟨hcanon.2.1, hcanon.2.2.1⟩, hent.1, hfactor, ?_⟩
  rw [hfactor, Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp]

end DGRHS.CLT
#check @DGRHS.CLT.equilibrium_macroscopic_prefactor
#print axioms DGRHS.CLT.equilibrium_macroscopic_prefactor
#check @DGRHS.CLT.log_inv_sqrt_regularizedDet
#print axioms DGRHS.CLT.log_inv_sqrt_regularizedDet
#check @DGRHS.CLT.sourceLog_equilibrium_macroscopic
#print axioms DGRHS.CLT.sourceLog_equilibrium_macroscopic
#check @DGRHS.CLT.sourceRiesz_equilibrium_macroscopic
#print axioms DGRHS.CLT.sourceRiesz_equilibrium_macroscopic
