import DGRHS.Gaussian.PeriodicRieszLowerCutOperatorPositive
import DGRHS.Gaussian.PeriodicRieszLowerCutMaster
import DGRHS.Gaussian.PeriodicRieszOriginalRate
import DGRHS.Gaussian.PeriodicRieszTruncationFamilyRate

/-!
Packet P9f, unit 3 (part 3): the canonical (centered, mean-zero) torus partition rate for the
lower-cut family, the periodic form of `exists_uniform_riesz_log_partition_rate` (TeX Steps 1-4 of
Proposition 5.5, 1941-2087), with the printed remainder exponent: uniform moments for the exact kernel
and the lower-cut truncations (`0 < τ ≤ a`), the fixed-scale Laplace estimate, the finite-`N`
comparison, and the cutoff choice `η(N)=((2L)⁻¹ log N)^{-1/s}` with `τ = η²`.
Analogue of `PeriodicRieszCanonicalRate` (the one-body inputs of `PeriodicRieszOriginalRate` are reused).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Uniform exponential moments of the lower-cut truncations (continuous representative), uniform in
`0 < τ ≤ a` for some `0 < a ≤ 1`. -/
theorem periodicLC_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ (C a : ℝ), 0 < a ∧ a ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ a → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (periodicLCCentered (periodicCappedDensityMeasure ρ) s τ) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (periodicLCCentered (periodicCappedDensityMeasure ρ) s τ) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, a, ha, ha1, hC⟩ := periodicRieszLowerCut_uniform_exponential s β hs hβ hs2 ρ M hM hρ
  refine ⟨C, a, ha, ha1, fun τ hτ hτa n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hC τ hτ hτa n hn
  have hpair : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 τ (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => periodicRieszLCKernel s τ (q.1 - q.2)) :=
    periodicDensity_pair_ae_of_haar ρ _ (periodicRieszPhysicalTail_ae_LCKernel s τ hs hs2 hτ)
  have hstat := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) n _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _ hpair)
  have hexp : (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPhysicalTail s 0 τ (q.1 - q.2))) ω))
      =ᵐ[Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (β * iidNegativeStatistic n
        (periodicLCCentered (periodicCappedDensityMeasure ρ) s τ) ω)) := by
    filter_upwards [hstat] with ω hω
    rw [hω]
  exact ⟨hi.congr hexp, by rw [← integral_congr_ae hexp]; exact hb⟩

/-- The canonical periodic Riesz partition `K_N^{can}` converges to `det₂^{-1/2}` with the rate
`(log(e+N))^{-θ/s}`, where `θ` is the exponent of the scale-`η=√τ` remainder
`‖h̃ - h̃_τ‖ ≲ η^θ` (lower-cut truncation, `τ = η²`). -/
theorem exists_periodic_riesz_canonical_rate_LC (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszLCRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicRieszCentered s hs2 μ
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      Tendsto (canonicalPartition μ β h) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (canonicalPartition μ β h N)) atTop
        (𝓝 (Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |canonicalPartition μ β h N -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) ∧
        |Real.log (canonicalPartition μ β h N) -
          Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) := by
  exact (periodicLCFamily s hs0 hs2).canonical_rate β hs0 hβ hs2 θ hθ ρ M hM hρ
    (periodicRieszLCResidual_of_remainder s hs0 hs2 θ hrem ρ M hM hρ)
    (periodicLC_uniform_exponential s (2 * β) hs0 (by positivity) hs2 ρ M hM hρ)

end DGRHS.Periodic
