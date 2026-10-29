import DGRHS.Gaussian.PeriodicRieszOriginalRate

/-!
Packet P9d, unit 1 (part 7): torus Theorem 2.2(ii), Riesz branch `0 < s < d/2` (TeX 504-529, 1941-2159;
Remark 2.1 for the torus), in the shape of `DGRHS.CLT.sourceRieszSingularPartition_original_rate`.

RANGE RESTRICTION (not a weakening of the source statement by choice, a property of the chosen
truncation): the heat-shift truncation `g_τ` has `‖g - g_τ‖²_{L²(Haar)} ≍ τ^{(d-2s)/2}` only for
`d - 2s < 4`; for `d - 2s > 4` the heat shift saturates at `τ²`, so the printed exponent
`(d-2s)/(2s)` is reached by `periodicRieszSingularPartition_original_rate` only under
`hd4 : d - 2s < 4`, and the second theorem gives the saturated exponent `2/s` for `d - 2s > 4`.
The full printed range needs a truncation with high-order vanishing multiplier and its own
uniform exponential moment (see the P9d return packet).  This was delivered by packet P9f with the
lower-cut Mellin family: `periodicRieszSingularPartition_original_rate_full`
(`PeriodicRieszLowerCutTheorem22ii.lean`) is the same statement without `hd4`, and implies both
theorems of this module.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Torus Theorem 2.2(ii), Riesz branch, printed exponent, for `d - 2s < 4`. -/
theorem periodicRieszSingularPartition_original_rate (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hd4 : (Fintype.card ι : ℝ) - 2 * s < 4)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Tendsto (fun N => (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < periodicRieszSingularPartition s β hs2 ρ N ∧
          periodicRieszSingularPartition s β hs2 ρ N < ⊤) ∧
        Real.exp (β * I) ≤ (periodicRieszSingularPartition s β hs2 ρ N).toReal ∧
        |(periodicRieszSingularPartition s β hs2 ρ N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(((Fintype.card ι : ℝ) - 2 * s) / (2 * s))) ∧
        |Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal -
          (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(((Fintype.card ι : ℝ) - 2 * s) / (2 * s))) := by
  have hd : 0 < (Fintype.card ι : ℝ) - 2 * s := by linarith
  have hexp : (((Fintype.card ι : ℝ) - 2 * s) / 2) / s = ((Fintype.card ι : ℝ) - 2 * s) / (2 * s) := by
    field_simp
  have h := periodicRieszSingularPartition_rate_of_remainder s β hs hβ hs2
    (((Fintype.card ι : ℝ) - 2 * s) / 2) (by positivity)
    (periodicRieszRemainder_integral_sq_le_sharp s hs hs2 hd4) ρ M hM hρ
  simpa only [hexp] using h

/-- Torus Theorem 2.2(ii), Riesz branch, beyond the heat-shift saturation threshold
`d - 2s > 4`: exponent `2/s` (the printed exponent `(d-2s)/(2s)` is larger and is not reached by
this truncation family). -/
theorem periodicRieszSingularPartition_rate_saturated (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hd4 : 4 < (Fintype.card ι : ℝ) - 2 * s)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Tendsto (fun N => (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < periodicRieszSingularPartition s β hs2 ρ N ∧
          periodicRieszSingularPartition s β hs2 ρ N < ⊤) ∧
        Real.exp (β * I) ≤ (periodicRieszSingularPartition s β hs2 ρ N).toReal ∧
        |(periodicRieszSingularPartition s β hs2 ρ N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(2 / s)) ∧
        |Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal -
          (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(2 / s)) :=
  periodicRieszSingularPartition_rate_of_remainder s β hs hβ hs2 2 (by norm_num)
    (by
      obtain ⟨C, hC0, hC⟩ := periodicRieszRemainder_integral_sq_le_saturated s hs hs2 hd4
      exact ⟨C, hC0, fun τ hτ _ => by
        rw [show (τ ^ (2 : ℝ)) = τ ^ 2 by norm_num]; exact hC τ hτ⟩) ρ M hM hρ

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRieszSingularPartition_original_rate
#print axioms DGRHS.Periodic.periodicRieszSingularPartition_rate_saturated
