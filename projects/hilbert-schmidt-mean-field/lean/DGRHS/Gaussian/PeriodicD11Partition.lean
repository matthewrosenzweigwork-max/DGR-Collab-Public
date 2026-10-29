import DGRHS.Gaussian.PeriodicD11ParticleMean
import DGRHS.Gaussian.PeriodicSupercriticalPartition

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian.D11Imported.HighDim
open DGRHS.Gaussian.D11Imported.HighDim.Eleven

/-- The actual wrapped-Cauchy density gives an unconditional lower bound on
all particle numbers of the original partition; the weighted energy is proper. -/
theorem periodic_d11_trial_partition_lower (β : ℝ)
    (N : ℕ) (hN : 1 ≤ N) :
    ENNReal.ofReal (Real.exp (β/2*((N:ℝ)-1)*periodicD11GreenEnergy -
      (N:ℝ)*entropy competitorDensity)) ≤
      periodicAttractivePartition (ι := Fin 11) β N := by
  let μ := Measure.pi (fun _ : Fin N => periodicHaar (Fin 11))
  let f := periodicD11ParticleDensity N
  let U := periodicParticleExponent (ι := Fin 11) β N
  obtain ⟨C,hf⟩ := periodicD11ParticleDensity_positiveBounded N
  have hn := periodicD11ParticleDensity_integral N
  have hpos (x : Fin N → Torus 11) : 0 ≤ f x := (periodicD11ParticleDensity_pos N x).le
  have heq (g : (Fin N → Torus 11) → ℝ) :
      (∫ x,g x ∂Measure.pi (fun _ : Fin N => periodicD11Measure)) = ∫ x,f x*g x ∂μ := by
    rw [periodicD11_particle_law N]
    rw [integral_withDensity_eq_integral_toReal_smul (periodicD11ParticleDensity_measurable N).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (ENNReal.ofReal (f x)).toReal*g x = f x*g x
      rw [ENNReal.toReal_ofReal (hpos x)]
  have hproper := (periodicD11_particle_exponent_mean β N hN).1
  rw [periodicD11_particle_law N] at hproper
  have hfu : Integrable (fun x => f x*U x) μ := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (periodicD11ParticleDensity_measurable N).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hproper
    convert h using 1
    ext x
    change f x*U x = (ENNReal.ofReal (f x)).toReal*U x
    rw [ENNReal.toReal_ofReal (hpos x)]
  have hv := positive_density_partition_lower μ hf hn
    (periodicParticleExponent_measurable β N).aestronglyMeasurable hfu
  have hE := (periodicD11_particle_exponent_mean β N hN).2
  have hL := (periodicD11_particle_log_mean N).2
  rw [heq] at hE hL
  change _ ≤ periodicAttractivePartition (ι := Fin 11) β N at hv
  rw [hE,hL] at hv
  exact hv

/-- A slightly stronger rational ratio provides the strict margin needed for
the source's global-minimization threshold bound. No new normalization is used. -/
lemma periodicD11_negative_free_energy_stronger :
    entropy competitorDensity-
      ((8653/8680:ℝ)*periodicStabilityThreshold (Fin 11))/2*periodicD11GreenEnergy<0 := by
  have h := periodicD11_energy_lower
  have he := competitor_entropy_bound
  have hm := mul_lt_mul_of_pos_left h (by norm_num : (0:ℝ)<(8653/8680)/2)
  nlinarith

lemma periodicD11_negative_free_energy_of_le (β : ℝ)
    (hβ : (8653/8680:ℝ)*periodicStabilityThreshold (Fin 11)≤β) :
    entropy competitorDensity-β/2*periodicD11GreenEnergy<0 := by
  have hm := mul_le_mul_of_nonneg_right hβ periodicD11GreenEnergy_nonneg
  linarith [periodicD11_negative_free_energy_stronger]

theorem periodic_d11_exponential_lower (β : ℝ)
    (hβ : (8653/8680:ℝ)*periodicStabilityThreshold (Fin 11)≤β) :
    ∃ c A : ℝ,0<c ∧ ∀ N : ℕ,1≤N →
      ENNReal.ofReal (Real.exp ((N:ℝ)*c-A))≤periodicAttractivePartition (ι := Fin 11) β N := by
  refine ⟨β/2*periodicD11GreenEnergy-entropy competitorDensity,β/2*periodicD11GreenEnergy,
    by linarith [periodicD11_negative_free_energy_of_le β hβ],?_⟩
  intro N hN
  convert periodic_d11_trial_partition_lower β N hN using 1
  congr 2
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_d11_trial_partition_lower
#print axioms DGRHS.Periodic.periodic_d11_exponential_lower
#check @DGRHS.Periodic.periodic_d11_exponential_lower
