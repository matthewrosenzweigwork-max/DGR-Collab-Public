import DGRHS.Gaussian.PeriodicRieszMasterData
import DGRHS.Gaussian.PeriodicRieszTimeParticleSplit
import DGRHS.Gaussian.PeriodicPositiveMellinNearField
import DGRHS.CLT.IidCanonicalNormalization
import DGRHS.CLT.SourceWeightCorrection
import DGRHS.CLT.SourceExponentCLT

/-!
Packet P9b, unit 5: Step 1 of the proof of Proposition 2.7 / the case `0<s<d/2` of
Theorem 2.2(i) (TeX 1545-1551) on the torus (Remark 2.1), the periodic analogue of
`DGRHS.CLT.sourceRieszPartition_uniform`:

* the exact periodic Riesz kernel `periodicRieszKernel` has a bounded one-body potential
  `F x = ∫ g(x-y) dμ(y)` for every capped density law (the torus form of `h_μ ∈ L^∞`);
* the uniform exponential moment of the master layer-cake (`periodicRieszCutoff_uniform_exponential`
  at `τ = 0`) transfers to the exact kernel;
* the modulated partition integrand `exp(-β N F_N(x,μ)-like)` is integrable with a bound uniform in `N`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Torus form of `h_μ = g * μ ∈ L^∞` (TeX 1545): the potential of a bounded-density law is
bounded, for the actual integrable periodic Riesz kernel. -/
lemma periodicRieszKernel_potential_abs_le (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (x : PeriodicTorus ι) :
    |DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)) x| ≤
      M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι := by
  have hg := periodicRieszKernel_integrable s hs2
  have hnn := periodicDensityRow_nonnegative_bound ρ M hM hρ (fun z => |periodicRieszKernel s hs2 z|)
    hg.abs (fun z => abs_nonneg _) x
  have hint := periodicDensityRow_integrable_of_haar ρ M hρ _ hg x
  unfold DGRHS.potential
  calc |∫ y, periodicRieszKernel s hs2 (x - y) ∂periodicCappedDensityMeasure ρ|
      ≤ ∫ y, |periodicRieszKernel s hs2 (x - y)| ∂periodicCappedDensityMeasure ρ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := periodicCappedDensityMeasure ρ)
            (fun y => periodicRieszKernel s hs2 (x - y))
    _ ≤ _ := hnn

/-- The uniform exponential moment, transferred from the heat-shifted Mellin representative at
`τ = 0` to the actual Fourier-defined even kernel `periodicRieszKernel`. -/
theorem periodicRieszKernel_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC⟩ := periodicRieszCutoff_uniform_exponential s β hs hβ hs2 ρ M hM hρ
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hC 0 le_rfl n hn
  have hpair : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s 0 (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => periodicRieszKernel s hs2 (q.1 - q.2)) :=
    periodicDensity_pair_ae_of_haar ρ _ (periodicRieszMellinGreen_ae_kernel s hs2)
  have hstat := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) n _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _ hpair)
  have hexp : (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s 0 (q.1 - q.2))) ω))
      =ᵐ[Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) ω)) := by
    filter_upwards [hstat] with ω hω
    rw [hω]
  exact ⟨hi.congr hexp, by rw [← integral_congr_ae hexp]; exact hb⟩

/-- Periodic analogue of `DGRHS.CLT.sourceRieszPartition_uniform` (Theorem 2.2(i), Remark 2.1):
for every probability density `ρ ≤ M` on the torus, the modulated partition integrand of the
repulsive Riesz gas with the periodic Riesz kernel is integrable and bounded uniformly in `N`. -/
theorem periodicRieszPartition_uniform (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun (x y : PeriodicTorus ι) => periodicRieszKernel s hs2 (x - y)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      Integrable (fun x : Fin N → PeriodicTorus ι =>
        Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι,
        Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  intro μ W h F I
  obtain ⟨C, hC⟩ := periodicRieszKernel_uniform_exponential s β hs hβ hs2 ρ M hM hρ
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2)
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hW
  have hK : ∀ᵐ x ∂μ, F x ≤ M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicRieszKernel_potential_abs_le s hs2 ρ M hM hρ x)
  have he (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp (β *
      iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
  have hProper : ∀ N, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro N hN
    have hi := (hC N hN).1
    rw [he N] at hi
    exact hi
  have hBound : ∀ N, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
    intro N hN
    have hb := (hC N hN).2
    rw [he N] at hb
    exact hb
  have hmom := DGRHS.CLT.sourceWeight_of_canonical_moments h F hF _ hK I β hβ C hProper hBound
  refine ⟨max (max (Real.exp (β * ((M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι) - I)) * C)
    (Real.exp (-β * I))) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro N hN
  simp_rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ (show 0 < N by omega)]
  exact ⟨(hmom N).1, ((hmom N).2).trans (le_max_left _ _)⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRieszKernel_potential_abs_le
#print axioms DGRHS.Periodic.periodicRieszKernel_uniform_exponential
#print axioms DGRHS.Periodic.periodicRieszPartition_uniform
