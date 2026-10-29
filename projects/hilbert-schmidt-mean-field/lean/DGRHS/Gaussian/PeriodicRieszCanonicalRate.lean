import DGRHS.Gaussian.PeriodicRieszOperatorPositive
import DGRHS.Gaussian.PeriodicRieszTruncationFamilyRate
import DGRHS.Concentration.SourceRateAssembly

/-!
Packet P9d, unit 1 (part 5): the canonical (centered, mean-zero) torus partition rate, the periodic
form of `exists_uniform_riesz_log_partition_rate` (TeX Steps 1-4 of Proposition 5.5, 1941-2087):
uniform moments for the exact and the heat-shifted kernels, the fixed-scale Laplace estimate, the
finite-`N` comparison, the cutoff choice `η(N)=((2L)⁻¹ log N)^{-1/s}` with `τ = η²`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Uniform exponential moments of the heat-shifted truncations (continuous representative). -/
theorem periodicTrunc_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (periodicTruncCentered (periodicCappedDensityMeasure ρ) s τ) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (periodicTruncCentered (periodicCappedDensityMeasure ρ) s τ) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC⟩ := periodicRieszCutoff_uniform_exponential s β hs hβ hs2 ρ M hM hρ
  refine ⟨C, fun τ hτ n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hC τ hτ.le n hn
  have hpair : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => periodicRieszTruncKernel s τ (q.1 - q.2)) :=
    periodicDensity_pair_ae_of_haar ρ _ (periodicRieszMellinGreen_ae_truncKernel s τ hs hs2 hτ)
  have hstat := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) n _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _ hpair)
  have hexp : (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω))
      =ᵐ[Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (β * iidNegativeStatistic n
        (periodicTruncCentered (periodicCappedDensityMeasure ρ) s τ) ω)) := by
    filter_upwards [hstat] with ω hω
    rw [hω]
  exact ⟨hi.congr hexp, by rw [← integral_congr_ae hexp]; exact hb⟩


/-- The uniform exponential moments of the heat-shifted truncations, as the `a = 1` instance of the
generic `UniformExponential` hypothesis of the family rate assembly (Packet P12c). -/
lemma periodicTruncFamily_uniformExponential (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (periodicTruncFamily s hs0 hs2).UniformExponential β ρ := by
  obtain ⟨C, hC⟩ := periodicTrunc_uniform_exponential s β hs0 hβ hs2 ρ M hM hρ
  exact ⟨C, 1, one_pos, le_rfl, fun τ hτ _ n hn => hC τ hτ n hn⟩


/-- The canonical periodic Riesz partition `K_N^{can}` converges to `det₂^{-1/2}` with the rate
`(log(e+N))^{-θ/s}`, where `θ` is the exponent of the scale-`η=√τ` remainder
`‖h̃ - h̃_τ‖ ≲ η^θ` (heat-shift truncation). -/
theorem exists_periodic_riesz_canonical_rate (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
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
  exact (periodicTruncFamily s hs0 hs2).canonical_rate β hs0 hβ hs2 θ hθ ρ M hM hρ
    (periodicRieszResidual_of_remainder s hs0 hs2 θ hrem ρ M hM hρ)
    (periodicTruncFamily_uniformExponential s (2 * β) hs0 (by positivity) hs2 ρ M hM hρ)

end DGRHS.Periodic
