import DGRHS.Gaussian.PeriodicLogMellinBand
import DGRHS.Gaussian.PeriodicRieszTimeParticleSplit

/-!
Packet P9e, unit 2 (part 3): the near-field / band / tail decomposition of the torus LOG Mellin
representative and the particle comparison (the torus form of the LOG particle split and of
`ae_gaussianLogSource_adaptive_comparison`'s inputs, TeX 1673-1717).

For heat times `0 < delta <= a <= 1`, Haar-almost everywhere
`G_tau = Band(delta,a) + Short(delta) + Tail(a) - a^(d/2)/(d/2)`, the constant is removed by
Hoeffding centering, and for a bounded-density law the negative statistic of the full centered
kernel is bounded by the band statistic plus a near-field term `b N M delta^(d/2)/(d/2)` (positive
short range) plus the uniform tail cap `2 b ` `periodicLogTailConst`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLogGreen_ae_time_split (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hδa : δ ≤ a) :
    periodicUnshiftedMellinHeatGreen (ι := ι) (periodicLogMellinExponent ι) τ =ᵐ[periodicHaar ι]
      (fun x => (periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a x +
        periodicPositiveMellinShort (periodicLogMellinExponent ι) τ δ x) +
        periodicLogMellinTail τ a x -
        a ^ (periodicLogMellinExponent ι + 1) / (periodicLogMellinExponent ι + 1)) := by
  filter_upwards [periodicPositiveMellinShort_ae_split (ι := ι) (periodicLogMellinExponent ι) τ δ a
    periodicLogMellinExponent_gt hτ hδ hδa,
    periodicLogMellinTail_eq_cutoff_ae (ι := ι) τ a hτ (hδ.trans hδa)] with x hs ht
  rw [ht]
  dsimp only [periodicMellinCutoff]
  linarith

lemma periodicLogGreen_centered_ae_time_split (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι =>
            periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2)) +
          hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι =>
            periodicPositiveMellinShort (periodicLogMellinExponent ι) τ δ (q.1 - q.2))) +
          hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι =>
            periodicLogMellinTail τ a (q.1 - q.2)) := by
  let μ := periodicCappedDensityMeasure ρ
  let W : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q =>
    periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2)
  let V : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q =>
    periodicPositiveMellinShort (periodicLogMellinExponent ι) τ δ (q.1 - q.2)
  let R : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun q => periodicLogMellinTail τ a (q.1 - q.2)
  let C : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun _ =>
    a ^ (periodicLogMellinExponent ι + 1) / (periodicLogMellinExponent ι + 1)
  have hW : Integrable W (μ.prod μ) :=
    (periodicLogBand_pair_proper τ δ a hτ hδ hδa ha1 μ).2.2
  have hV : Integrable V (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ _ hρ _
      (periodicPositiveMellinShort_integrable (ι := ι) (periodicLogMellinExponent ι) τ δ
        periodicLogMellinExponent_gt hτ)
  have hR : Integrable R (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ _ hρ _
      (periodicLogMellinTail_integrable τ a hτ (hδ.le.trans hδa))
  have he : (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2)) =ᵐ[μ.prod μ]
      ((W + V) + R) - C :=
    periodicDensity_pair_ae_of_haar ρ _
      (periodicLogGreen_ae_time_split τ δ a hτ hδ.le hδa)
  have h1 := ae_hoeffdingCentered_congr μ _ _ he
  have h2 := ae_hoeffdingCentered_sub μ ((W + V) + R) C ((hW.add hV).add hR) (integrable_const _)
  have h3 := ae_hoeffdingCentered_add μ (W + V) R (hW.add hV) hR
  have h4 := ae_hoeffdingCentered_add μ W V hW hV
  have hC : hoeffdingCentered μ C = 0 := periodicHoeffdingCentered_constant μ _
  filter_upwards [h1, h2, h3, h4] with q hq1 hq2 hq3 hq4
  rw [hq1, hq2]
  simp only [Pi.sub_apply, hC, Pi.zero_apply, sub_zero]
  rw [hq3]
  simp only [Pi.add_apply]
  rw [hq4]
  rfl

lemma periodicLogGreen_particle_ae_time_split (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) x =
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2))) x +
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicPositiveMellinShort (periodicLogMellinExponent ι) τ δ (q.1 - q.2))) x +
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicLogMellinTail τ a (q.1 - q.2))) x := by
  have he := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (periodicLogGreen_centered_ae_time_split τ δ a hτ hδ hδa ha1 ρ M hρ)
  filter_upwards [he] with x hx
  rw [hx, physical_iidNegativeStatistic_add, physical_iidNegativeStatistic_add]

/-- Mass of the positive short range: `int_0^eps t^p dt = eps^(d/2)/(d/2)`. -/
lemma periodicLogShort_mass_nonneg (ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ ε ^ (periodicLogMellinExponent ι + 1) / (periodicLogMellinExponent ι + 1) := by
  have h := periodicLogMellinExponent_gt (ι := ι)
  have := Real.rpow_nonneg hε (periodicLogMellinExponent ι + 1)
  have h1 : 0 < periodicLogMellinExponent ι + 1 := by linarith
  positivity

lemma periodicLogShort_density_particle_bound (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicPositiveMellinShort (periodicLogMellinExponent ι) τ ε (q.1 - q.2))) x ≤
      (N : ℝ) * (M * (ε ^ (periodicLogMellinExponent ι + 1) /
        (periodicLogMellinExponent ι + 1))) := by
  apply ae_physical_iidNegativeStatistic_bound (periodicCappedDensityMeasure ρ) N hN
  · exact mul_nonneg hM (periodicLogShort_mass_nonneg (ι := ι) ε hε)
  · refine Eventually.of_forall (fun p => ?_)
    have h := periodicDensityCentered_nonnegative_lower ρ M hM hρ _
      (periodicPositiveMellinShort_integrable (ι := ι) (periodicLogMellinExponent ι) τ ε
        periodicLogMellinExponent_gt hτ)
      (periodicPositiveMellinShort_nonneg (ι := ι) (periodicLogMellinExponent ι) τ ε hτ) p
    rwa [periodicPositiveMellinShort_mass (ι := ι) (periodicLogMellinExponent ι) τ ε
      periodicLogMellinExponent_gt hτ hε] at h

/-- Particle comparison of the full (unnormalized) LOG Mellin kernel with its band, torus form of
the LOG adaptive comparison inputs. -/
lemma periodicLogGreen_particle_comparison (τ δ a b : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      b * iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) x ≤
      b * iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2))) x +
      b * (N : ℝ) * (M * (δ ^ (periodicLogMellinExponent ι + 1) /
        (periodicLogMellinExponent ι + 1))) +
      b * (2 * periodicLogTailConst ι a) := by
  filter_upwards [periodicLogGreen_particle_ae_time_split τ δ a hτ hδ hδa ha1 ρ M hρ N,
    periodicLogShort_density_particle_bound τ δ hτ hδ.le ρ M hM hρ N hN] with x hsplit hnear
  have htail := periodicLogMellinTail_particle_cap τ a hτ (hδ.trans_le hδa)
    (periodicCappedDensityMeasure ρ) N hN x
  rw [hsplit]
  have hn := mul_le_mul_of_nonneg_left hnear hb
  have ht := mul_le_mul_of_nonneg_left htail hb
  nlinarith

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogGreen_ae_time_split
#print axioms DGRHS.Periodic.periodicLogGreen_centered_ae_time_split
#print axioms DGRHS.Periodic.periodicLogGreen_particle_ae_time_split
#print axioms DGRHS.Periodic.periodicLogShort_density_particle_bound
#print axioms DGRHS.Periodic.periodicLogGreen_particle_comparison
