import DGRHS.CLT.SourceEquilibriumCorrection
import DGRHS.CLT.EquilibriumFinitePotential

/-! Original LOG thermal corollary with the genuine macroscopic free energy,
literal collision-zero canonical partition and quantitative determinant
correction. Bounded density and original absolute pair-log energy derive
finite differential entropy and potential energy from the thermal identity.
The four-beta potential tail is used only for the original quantitative rate.
No desired entropy, finite-V or canonical asymptotic is a premise.
Source559--584, SHA6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

theorem sourceLog_equilibrium_macroscopic_original (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) (V : EuclideanSpace ℝ ι → ℝ)
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
  have hV := (sourceLog_equilibrium_finite_potential ρ M hM hρ hpair V
    (β : ℝ) hβ.ne' hEL).1
  exact sourceLog_equilibrium_macroscopic β hβ hd ρ M hM hρ hpair V hV hEL N hN

theorem sourceLog_equilibrium_correction_original (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-4 * (β : ℝ) *
      logPhysicalPotential (gaussianRieszDensityMeasure ρ) x)) (gaussianRieszDensityMeasure ρ))
    (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -(β : ℝ) *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)) x)) =
      gaussianRieszDensityMeasure ρ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p) (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i) ∧
      HasProd (fun i => (1 + (β : ℝ) * eig i) * Real.exp (-((β : ℝ) * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)) ∧
      Integrable (llr μ volume) μ ∧
      Tendsto (fun N => Real.log (canonicalSingularPartition volume W V (β : ℝ) N).toReal +
        (β : ℝ) * (N : ℝ) * macroscopicFreeEnergy volume μ W V (β : ℝ)) atTop
        (𝓝 ((β : ℝ) * DGRHS.interactionEnergy μ W -
          (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < canonicalSingularPartition volume W V (β : ℝ) N ∧
          canonicalSingularPartition volume W V (β : ℝ) N < ∞) ∧
        |Real.log (canonicalSingularPartition volume W V (β : ℝ) N).toReal -
          (-(β : ℝ) * (N : ℝ) * macroscopicFreeEnergy volume μ W V (β : ℝ) +
            (β : ℝ) * DGRHS.interactionEnergy μ W -
              (1/2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))| ≤
            C * (Real.exp 1 + (N : ℝ))^(-c) := by
  have hV := (sourceLog_equilibrium_finite_potential ρ M hM hρ hpair V
    (β : ℝ) hβ.ne' hEL).1
  exact sourceLog_equilibrium_correction β hβ hd ρ M hM hρ hpair htail V hV hEL

end DGRHS.CLT
set_option pp.maxSteps 1000000
#check @DGRHS.CLT.sourceLog_equilibrium_macroscopic_original
#print axioms DGRHS.CLT.sourceLog_equilibrium_macroscopic_original
#check @DGRHS.CLT.sourceLog_equilibrium_correction_original
#print axioms DGRHS.CLT.sourceLog_equilibrium_correction_original
