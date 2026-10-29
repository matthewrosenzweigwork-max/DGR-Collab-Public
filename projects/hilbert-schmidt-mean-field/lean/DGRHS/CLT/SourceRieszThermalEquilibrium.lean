import DGRHS.CLT.ThermalMacroscopicFreeEnergy
import DGRHS.CLT.SourceEquilibriumCorrection

/-! Source543--584 thermal interpretation: actual potential and genuine density
entropy are combined BEFORE integration. The preserved Serfaty primary thermal
source permits cancellation of separately divergent terms. These theorems use
the independently defined combined cost, prove it proper from actual EL, and
retain the physical canonical partition and original determinant/rate. They
are explicitly distinct from the separate-integral free energy; agreement on
its proper domain is thermalMacroscopicFreeEnergy_eq_separate. No source
infinity-minus-infinity formula is asserted to have a totalized real value. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u

lemma equilibrium_thermal_macroscopic_prefactor {S : Type*} [MeasurableSpace S]
    (ν₀ μ : Measure S) [SigmaFinite ν₀] [NeZero ν₀] [IsProbabilityMeasure μ]
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hW : Integrable (Function.uncurry W) (μ.prod μ))
    (hEL : ν₀.tilted (fun x => -β * (V x + DGRHS.potential μ W x)) = μ) (N : ℕ) :
    (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂ν₀)^N *
      Real.exp (β * (N : ℝ) * DGRHS.interactionEnergy μ W) =
      Real.exp (-β * (N : ℝ) * thermalMacroscopicFreeEnergy ν₀ μ W V β) := by
  let f := fun x => -β * (V x + DGRHS.potential μ W x)
  have hZ := integral_exp_pos (integrable_exp_of_tilted_probability f hEL)
  have h := (equilibrium_thermal_combined_cost ν₀ μ W V β hβ hW hEL).2.2
  rw [← Real.exp_log hZ, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  dsimp only [f]
  linear_combination -(N : ℝ) * h

variable {ι : Type u} [Fintype ι]

theorem sourceRiesz_thermal_equilibrium_macroscopic (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => gaussianRieszPhysicalPair s (a,b)) x)) = gaussianRieszDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    (0 < canonicalSingularPartition volume W V β N ∧
      canonicalSingularPartition volume W V β N < ∞) ∧
    Integrable (fun x => β * V x + llr μ volume x) μ ∧
    (canonicalSingularPartition volume W V β N).toReal =
      Real.exp (-β * (N : ℝ) * thermalMacroscopicFreeEnergy volume μ W V β) *
        (sourceRieszSingularPartition s β ρ N).toReal ∧
    Real.log (canonicalSingularPartition volume W V β N).toReal =
      -β * (N : ℝ) * thermalMacroscopicFreeEnergy volume μ W V β +
        Real.log (sourceRieszSingularPartition s β ρ N).toReal := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  have hpair : Integrable (Function.uncurry W) (μ.prod μ) :=
    (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  have hcanon := sourceRiesz_equilibrium_canonical s β hs hβ ha ρ M hM hρ V hEL N hN
  have hcost := equilibrium_thermal_combined_cost volume μ W V β hβ.ne' hpair hEL
  have hfactor := sourceRiesz_equilibrium_partition s β hs hβ ha ρ M hM hρ V hEL N hN
  dsimp only at hfactor
  have hpre := equilibrium_thermal_macroscopic_prefactor volume μ W V β hβ.ne' hpair hEL N
  rw [hpre] at hfactor
  have hproper := sourceRieszSingularPartition_pos_finite s β hs hβ.le ha ρ M hM hρ N
  have hk : 0 < (sourceRieszSingularPartition s β ρ N).toReal :=
    ENNReal.toReal_pos hproper.1.ne' hproper.2.ne
  refine ⟨⟨hcanon.2.1, hcanon.2.2.1⟩, hcost.1, hfactor, ?_⟩
  rw [hfactor, Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp]

theorem sourceRiesz_thermal_equilibrium_correction (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => gaussianRieszPhysicalPair s (a,b)) x)) = gaussianRieszDensityMeasure ρ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    ∃ (hh : MemLp h 2 (μ.prod μ)) (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Integrable (fun x => β * V x + llr μ volume x) μ ∧
      Tendsto (fun N => Real.log (canonicalSingularPartition volume W V β N).toReal +
        β * (N : ℝ) * thermalMacroscopicFreeEnergy volume μ W V β) atTop
        (𝓝 (β * DGRHS.interactionEnergy μ W -
          (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < canonicalSingularPartition volume W V β N ∧
          canonicalSingularPartition volume W V β N < ∞) ∧
        |Real.log (canonicalSingularPartition volume W V β N).toReal -
          (-β * (N : ℝ) * thermalMacroscopicFreeEnergy volume μ W V β +
            β * DGRHS.interactionEnergy μ W -
              (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))| ≤
            C * (Real.log (Real.exp 1 + (N : ℝ)))^(-(((Fintype.card ι : ℝ)-2*s)/(2*s))) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  obtain ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hProd,hT,hLog,C,hC,hRate⟩ :=
    sourceRieszSingularPartition_original_rate s β hs hβ.le ha ρ M hM hρ
  have hdet := log_inv_sqrt_regularizedDet eig β hD
  rw [hdet] at hLog
  simp only [neg_mul, ← sub_eq_add_neg] at hLog
  have hcanon N (hN : 1 ≤ N) :=
    sourceRiesz_thermal_equilibrium_macroscopic s β hs hβ ha ρ M hM hρ V hEL N hN
  refine ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hProd,(hcanon 1 (by norm_num)).2.1,
    hLog.congr' ((eventually_ge_atTop 1).mono fun N hN => ?_),C,hC,?_⟩
  · dsimp only
    rw [(hcanon N hN).2.2.2]
    ring
  · intro N hN
    refine ⟨(hcanon N hN).1,?_⟩
    have hr := (hRate N hN).2.2.2
    rw [hdet] at hr
    convert hr using 1
    rw [(hcanon N hN).2.2.2]
    congr 1
    ring

end DGRHS.CLT
set_option pp.universes true
set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#check @DGRHS.CLT.equilibrium_thermal_macroscopic_prefactor
#print axioms DGRHS.CLT.equilibrium_thermal_macroscopic_prefactor
#check @DGRHS.CLT.sourceRiesz_thermal_equilibrium_macroscopic
#print axioms DGRHS.CLT.sourceRiesz_thermal_equilibrium_macroscopic
#check @DGRHS.CLT.sourceRiesz_thermal_equilibrium_correction
#print axioms DGRHS.CLT.sourceRiesz_thermal_equilibrium_correction
