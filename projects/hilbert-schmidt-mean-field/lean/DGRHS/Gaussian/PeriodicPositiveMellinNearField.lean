import DGRHS.Gaussian.PeriodicPositiveMellinCutoff
import DGRHS.Gaussian.PeriodicBoundedBackgroundL2
import DGRHS.Gaussian.PhysicalStatisticAlgebra

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Actual bounded-density short-range potential
and centered-particle lower bounds for the positive Mellin cutoff. Generic
helpers are instantiated with the concrete kernel; no desired concentration,
partition envelope, or event comparison is a hypothesis. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicDensityPair_integrable_of_haar (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (g : PeriodicTorus ι → ℝ)
    (hg : Integrable g (periodicHaar ι)) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => g (p.1 - p.2))
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) := by
  have hi := (periodicHaar_preserving_difference (ι := ι)).integrable_comp_of_integrable hg
  exact (hi.smul_measure (c := ENNReal.ofReal M * ENNReal.ofReal M) (by finiteness)).mono_measure
    (periodicCappedDensityMeasure_prod_le ρ M hρ)

lemma periodicDensityRow_integrable_of_haar (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (g : PeriodicTorus ι → ℝ)
    (hg : Integrable g (periodicHaar ι)) (x : PeriodicTorus ι) :
    Integrable (fun y => g (x - y)) (periodicCappedDensityMeasure ρ) :=
  (((periodicHaar_preserving_sub_left x).integrable_comp_of_integrable hg).smul_measure
    (c := ENNReal.ofReal M) (by finiteness)).mono_measure
      (periodicCappedDensityMeasure_le ρ M hρ)

lemma periodicDensityRow_nonnegative_bound (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hg : Integrable g (periodicHaar ι))
    (hg0 : ∀ x, 0 ≤ g x) (x : PeriodicTorus ι) :
    (∫ y, g (x - y) ∂periodicCappedDensityMeasure ρ) ≤
      M * ∫ z, g z ∂periodicHaar ι := by
  have hi := (periodicHaar_preserving_sub_left x).integrable_comp_of_integrable hg
  have h := integral_mono_measure (periodicCappedDensityMeasure_le ρ M hρ)
    (Eventually.of_forall (fun y => hg0 (x - y)))
    (hi.smul_measure (c := ENNReal.ofReal M) (by finiteness))
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hM, smul_eq_mul,
    integral_sub_left_eq_self] using h

lemma periodicDensityColumn_nonnegative_bound (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hg : Integrable g (periodicHaar ι))
    (hg0 : ∀ x, 0 ≤ g x) (y : PeriodicTorus ι) :
    (∫ x, g (x - y) ∂periodicCappedDensityMeasure ρ) ≤
      M * ∫ z, g z ∂periodicHaar ι := by
  have hi := (MeasureTheory.measurePreserving_sub_right (periodicHaar ι) y).integrable_comp_of_integrable hg
  have h := integral_mono_measure (periodicCappedDensityMeasure_le ρ M hρ)
    (Eventually.of_forall (fun x => hg0 (x - y)))
    (hi.smul_measure (c := ENNReal.ofReal M) (by finiteness))
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hM, smul_eq_mul,
    integral_sub_right_eq_self] using h

lemma periodicDensityCentered_nonnegative_lower (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (g : PeriodicTorus ι → ℝ) (hg : Integrable g (periodicHaar ι))
    (hg0 : ∀ x, 0 ≤ g x) (p : PeriodicTorus ι × PeriodicTorus ι) :
    -hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q => g (q.1 - q.2)) p ≤ 2 * (M * ∫ z, g z ∂periodicHaar ι) := by
  have h1 := periodicDensityRow_nonnegative_bound ρ M hM hρ g hg hg0 p.1
  have h2 := periodicDensityColumn_nonnegative_bound ρ M hM hρ g hg hg0 p.2
  have h0 := hg0 (p.1 - p.2)
  have hm : 0 ≤ ∫ q : PeriodicTorus ι × PeriodicTorus ι, g (q.1 - q.2)
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ) :=
    integral_nonneg (fun q => hg0 (q.1 - q.2))
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  linarith

lemma periodicRieszPositiveShort_density_pair_integrable (s τ ε : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszPositiveShort s τ ε (p.1 - p.2))
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  periodicDensityPair_integrable_of_haar ρ M hρ _
    (periodicRieszPositiveShort_integrable s τ ε hsd hτ)

lemma periodicRieszPositiveShort_density_potential_bound (s τ ε : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (x : PeriodicTorus ι) :
    (∫ y, periodicRieszPositiveShort s τ ε (x - y) ∂periodicCappedDensityMeasure ρ) ≤
      M * (periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2))) := by
  have h := periodicDensityRow_nonnegative_bound ρ M hM hρ _
    (periodicRieszPositiveShort_integrable s τ ε hsd hτ)
    (periodicRieszPositiveShort_nonneg s τ ε hs hτ) x
  rwa [periodicRieszPositiveShort_mass s τ ε hsd hτ hε] at h

lemma periodicRieszPositiveShort_density_centered_lower (s τ ε : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    -hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q => periodicRieszPositiveShort s τ ε (q.1 - q.2)) p ≤
      2 * (M * (periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)))) := by
  have h := periodicDensityCentered_nonnegative_lower ρ M hM hρ _
    (periodicRieszPositiveShort_integrable s τ ε hsd hτ)
    (periodicRieszPositiveShort_nonneg s τ ε hs hτ) p
  rwa [periodicRieszPositiveShort_mass s τ ε hsd hτ hε] at h

lemma periodicRieszPositiveShort_density_particle_bound (s τ ε : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q => periodicRieszPositiveShort s τ ε (q.1 - q.2))) x ≤
      (N : ℝ) * (M * (periodicRieszMellinFactor ι s *
        (ε ^ (((Fintype.card ι : ℝ) - s) / 2) / (((Fintype.card ι : ℝ) - s) / 2)))) := by
  apply ae_physical_iidNegativeStatistic_bound (periodicCappedDensityMeasure ρ) N hN
  · have hC := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
    have hd : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
    positivity
  · exact Eventually.of_forall
      (periodicRieszPositiveShort_density_centered_lower s τ ε hs hsd hτ hε ρ M hM hρ)

end DGRHS.Periodic
