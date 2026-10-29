import DGRHS.Gaussian.PeriodicRieszLowerCutOriginalRate

/-!
Packet P9f, unit 3: torus Theorem 2.2(ii), Riesz branch `0 < s < d/2` (TeX 504-529, 1941-2159;
Remark 2.1 for the torus), at the PRINTED exponent `(d-2s)/(2s)` with NO range restriction, in the
shape of `DGRHS.CLT.sourceRieszSingularPartition_original_rate` and of
`periodicRieszSingularPartition_original_rate` (P9d, which needed `d - 2s < 4`).

The truncation is the paper's own Mellin lower cut `g_η = F_s ∫_{t>η²} t^{(d-s)/2-1}(p_t - 1) dt`
(`eq:HCRStruncDef`): its remainder satisfies `‖g - g_η‖²_{L²} ≲ η^{d-2s}` for every `0 < s < d/2`
(`periodicRieszLCRemainder_integral_sq_le`), unlike the heat shift, which saturates at `η⁴`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Torus Theorem 2.2(ii), Riesz branch, printed exponent `(d-2s)/(2s)` for the full range
`0 < s < d/2` (no restriction `d - 2s < 4`): the lower-cut truncation family. -/
theorem periodicRieszSingularPartition_original_rate_full (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ))
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
  have h := periodicRieszSingularPartition_rate_of_remainder_LC s β hs hβ hs2
    (((Fintype.card ι : ℝ) - 2 * s) / 2) (by positivity)
    (periodicRieszLCRemainder_integral_sq_le s hs hs2) ρ M hM hρ
  simpa only [hexp] using h

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRieszSingularPartition_original_rate_full
