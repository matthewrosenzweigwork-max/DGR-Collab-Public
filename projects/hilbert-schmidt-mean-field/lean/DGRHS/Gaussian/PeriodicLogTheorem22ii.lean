import DGRHS.Gaussian.PeriodicLogOriginalRate

/-!
Packet P9g, unit 2 (part 7): torus Theorem 2.2(ii), LOG branch `s = 0` (TeX 504-529, 1941-2159;
Remark 2.1 for the torus), in the shape of the Euclidean exports
`DGRHS.CLT.sourceLogSingularPartition_original_rate` and
`DGRHS.CLT.sourceLogSingularPartition_original_log_rate`: the same `∃ hh hSym hCan κ eig e`,
`HasProd`, `Tendsto` of `K_N.toReal` to `e^{βI_μ} det₂^{-1/2}` and of its log, `∃ c C` with
`0 < c ≤ 1/2`, positivity/finiteness, the Jensen lower bound `e^{βI_μ} ≤ K_N` and the power rate
`(e+N)^{-c}` for both `K_N` and `log K_N`.

HYPOTHESES.  `periodicLogSingularPartition_original_rate` assumes only those of part (i)
(`0 ≤ β`, probability density `ρ ≤ M` Haar-a.e.).  The two extra hypotheses of the printed part (ii)
(`eq:logRateExtraAssumptions`: `∫ e^{-4βh_μ} dμ < ∞` and `g̃ ∈ L²(μ⊗μ)`) hold automatically on the
torus class (`periodicLogPotential_exp_integrable`, `periodicLogCentered_memLp`), so the theorem is
the printed statement with those two hypotheses discharged;
`periodicLogSingularPartition_original_rate_printed` restates it with them as (unused) hypotheses.

RANGE.  The printed rate exponent `c_log(β,μ) > 0` is unspecified, so the heat-shift family covers
every dimension `d ≥ 1`: the remainder `‖g - g_τ‖² ≲ τ^θ` holds for `θ = min 1 (d/4)`
(`periodicLogRemainder_integral_sq_le_weak`); the saturation of the heat shift at `τ²` for `d > 4` only
bounds the best exponent, which is not part of the printed LOG statement.  No lower-cut family is
needed.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Torus Theorem 2.2(ii), LOG branch: power rate `(e+N)^{-c_log}` with `0 < c_log ≤ 1/2`, together
with the determinant limit `K_N → e^{β I_μ} det₂^{-1/2}`, for every dimension. -/
theorem periodicLogSingularPartition_original_rate (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
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
      Tendsto (fun N => (periodicLogSingularPartition β ρ N).toReal) atTop
        (𝓝 (Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (periodicLogSingularPartition β ρ N).toReal) atTop
        (𝓝 (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < periodicLogSingularPartition β ρ N ∧ periodicLogSingularPartition β ρ N < ⊤) ∧
        Real.exp (β * I) ≤ (periodicLogSingularPartition β ρ N).toReal ∧
        |(periodicLogSingularPartition β ρ N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) ∧
        |Real.log (periodicLogSingularPartition β ρ N).toReal -
          (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
  intro μ W h I
  obtain ⟨θ, hθ, hrem⟩ := periodicLogRemainder_integral_sq_le_weak (ι := ι)
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable
  have hFm := periodicLogPotential_memLp ρ M hM hρ
  have hK : ∀ᵐ x ∂μ, DGRHS.potential μ W x ≤ M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicLogKernel_potential_abs_le ρ M hM hρ x)
  have hc : β * (∫ y, DGRHS.potential μ W y ∂μ) - β * I = β * I := by
    rw [DGRHS.integral_potential μ W hW]
    ring
  obtain ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hT, hLog, c, C, hc0, hc1, hC, hRate⟩ :=
    periodicLogPhysical_affine_partition_rate β hβ θ hθ hrem ρ M hM hρ
      (DGRHS.potential μ W) hFm _ I hK
  rw [hc] at hT hLog hRate
  have hpos := periodicLogOperator_positive θ hθ hrem ρ M hM hρ hh
  have hP := DGRHS.SourceRepulsiveRieszRate.hasProd_actual_meanZero_spectrum _ hh hSym hCan hpos
    eig e he β hβ
  have hEq (N : ℕ) (hN : 1 ≤ N) : periodicLogSourcePartition β ρ N =
      sourceAffinePartition μ β I h (DGRHS.potential μ W) N :=
    sourceEnergy_partition_eq_affine μ β I h (DGRHS.potential μ W) N hN
  have hEv : periodicLogSourcePartition β ρ =ᶠ[atTop]
      sourceAffinePartition μ β I h (DGRHS.potential μ W) :=
    (eventually_ge_atTop 1).mono fun N hN => hEq N hN
  have hToReal (N : ℕ) : (periodicLogSingularPartition β ρ N).toReal =
      periodicLogSourcePartition β ρ N := by
    rw [periodicLogSingularPartition_eq_integral β hβ ρ M hM hρ N]
    exact ENNReal.toReal_ofReal (by
      unfold periodicLogSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)
  have hEv' : (fun N => (periodicLogSingularPartition β ρ N).toReal) =ᶠ[atTop]
      sourceAffinePartition μ β I h (DGRHS.potential μ W) :=
    hEv.mono (fun N hN => by
      show (periodicLogSingularPartition β ρ N).toReal = _
      rw [hToReal N]; exact hN)
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hP, hT.congr' hEv'.symm,
    hLog.congr' (hEv'.symm.mono fun N hN => congrArg Real.log hN), c, C, hc0, hc1, hC, ?_⟩
  intro N hN
  obtain ⟨_, hLow, hAbs, hAbsLog⟩ := hRate N hN
  refine ⟨periodicLogSingularPartition_pos_finite β hβ ρ M hM hρ N, ?_⟩
  rw [hToReal N, hEq N hN]
  exact ⟨hLow, hAbs, hAbsLog⟩

/-- The same theorem with the two extra hypotheses of the printed part (ii)
(`eq:logRateExtraAssumptions`) restated literally.  Both are automatic on the torus class
(`periodicLogPotential_exp_integrable`, `periodicLogCentered_memLp`); they are not used. -/
theorem periodicLogSingularPartition_original_rate_printed (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (_htail : Integrable (fun x => Real.exp (-4 * β * DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x)) (periodicCappedDensityMeasure ρ))
    (_hL2 : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
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
      Tendsto (fun N => (periodicLogSingularPartition β ρ N).toReal) atTop
        (𝓝 (Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (periodicLogSingularPartition β ρ N).toReal) atTop
        (𝓝 (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < periodicLogSingularPartition β ρ N ∧ periodicLogSingularPartition β ρ N < ⊤) ∧
        Real.exp (β * I) ≤ (periodicLogSingularPartition β ρ N).toReal ∧
        |(periodicLogSingularPartition β ρ N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) ∧
        |Real.log (periodicLogSingularPartition β ρ N).toReal -
          (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) :=
  periodicLogSingularPartition_original_rate β hβ ρ M hM hρ

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogSingularPartition_original_rate
#print axioms DGRHS.Periodic.periodicLogSingularPartition_original_rate_printed
