import DGRHS.Gaussian.PeriodicTrialVariational
import DGRHS.Gaussian.PeriodicTrialInstability

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Actual attractive positive-sign off-diagonal partition on normalized Haar.
ENNReal keeps collision divergence distinct from totalized real integration. -/
def periodicAttractivePartition (β : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Fin N → PeriodicTorus ι,ENNReal.ofReal (Real.exp (periodicParticleExponent β N x))
    ∂Measure.pi (fun _ : Fin N => periodicHaar ι)

lemma periodicTrialParticleDensity_positiveBounded (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) (N : ℕ) :
    DGRHS.Concentration.PositiveBounded (Measure.pi (fun _ : Fin N => periodicHaar ι))
      (periodicTrialParticleDensity i ε N) ((1/2)^N) ((3/2)^N) := by
  classical
  refine ⟨(periodicTrialParticleDensity_measurable i ε N).aestronglyMeasurable,by positivity,
    pow_le_pow_left₀ (by norm_num) (by norm_num) N,Filter.Eventually.of_forall fun x => ?_⟩
  constructor
  · have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun _ : Fin N => (1/2:ℝ)) (g := fun j => periodicCosineTrialDensity i ε (x j))
      (fun _ _ => by norm_num) (fun j _ => (periodicCosineTrialDensity_bounds i ε hε (x j)).1)
    simpa [periodicTrialParticleDensity,div_pow] using h
  · have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun j : Fin N => periodicCosineTrialDensity i ε (x j)) (g := fun _ => (3/2:ℝ))
      (fun j _ => by linarith [(periodicCosineTrialDensity_bounds i ε hε (x j)).1])
      (fun j _ => (periodicCosineTrialDensity_bounds i ε hε (x j)).2)
    simpa [periodicTrialParticleDensity,div_pow] using h

lemma periodicTrialParticleDensity_integral (i : ι) (ε : ℝ) (N : ℕ) :
    (∫ x,periodicTrialParticleDensity i ε N x ∂Measure.pi (fun _ : Fin N => periodicHaar ι))=1 := by
  unfold periodicTrialParticleDensity
  rw [integral_fintype_prod_eq_prod]
  simp only [periodicCosineTrialDensity_integral,Finset.prod_const_one]

lemma periodicParticleExponent_measurable (β : ℝ) (N : ℕ) :
    Measurable (periodicParticleExponent (ι := ι) β N) := by
  classical
  unfold periodicParticleExponent
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i=j
  · simp only [hij,if_true]; exact measurable_const
  · simp only [hij,if_false]
    exact periodicLogKernel_measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

/-- The product-trial lower bound is derived from the constructed probability
law, exact off-diagonal mean, proper trial entropy and scalar log inequality. -/
theorem periodic_cosine_trial_partition_lower (i : ι) (ε β : ℝ) (hε : |ε| ≤ 1/2)
    (N : ℕ) (hN : 1 ≤ N) :
    ENNReal.ofReal (Real.exp (β/2*((N:ℝ)-1)*(ε^2/(2*periodicStabilityThreshold ι)) -
      (N:ℝ)*(∫ x,periodicCosineTrialDensity i ε x*Real.log (periodicCosineTrialDensity i ε x) ∂periodicHaar ι))) ≤
      periodicAttractivePartition (ι := ι) β N := by
  let μ := Measure.pi (fun _ : Fin N => periodicHaar ι)
  let f := periodicTrialParticleDensity i ε N
  let U := periodicParticleExponent (ι := ι) β N
  have hf := periodicTrialParticleDensity_positiveBounded i ε hε N
  have hn := periodicTrialParticleDensity_integral i ε N
  have hpos (x : Fin N → PeriodicTorus ι) : 0 ≤ f x := (periodicTrialParticleDensity_pos i ε hε N x).le
  have heq (g : (Fin N → PeriodicTorus ι) → ℝ) :
      (∫ x,g x ∂Measure.pi (fun _ : Fin N => periodicCosineTrialMeasure i ε)) = ∫ x,f x*g x ∂μ := by
    rw [periodicTrial_particle_law i ε hε N]
    rw [integral_withDensity_eq_integral_toReal_smul (periodicTrialParticleDensity_measurable i ε N).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (ENNReal.ofReal (f x)).toReal*g x = f x*g x
      rw [ENNReal.toReal_ofReal (hpos x)]
  have hproper := (periodicTrial_particle_exponent_mean i ε β hε N hN).1
  rw [periodicTrial_particle_law i ε hε N] at hproper
  have hfu : Integrable (fun x => f x*U x) μ := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (periodicTrialParticleDensity_measurable i ε N).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hproper
    convert h using 1
    ext x
    change f x*U x = (ENNReal.ofReal (f x)).toReal*U x
    rw [ENNReal.toReal_ofReal (hpos x)]
  have hv := positive_density_partition_lower μ hf hn
    (periodicParticleExponent_measurable β N).aestronglyMeasurable hfu
  have hE := (periodicTrial_particle_exponent_mean i ε β hε N hN).2
  have hL := (periodicTrial_particle_log_mean i ε hε N).2
  rw [heq] at hE hL
  change _ ≤ periodicAttractivePartition (ι := ι) β N at hv
  rw [hE,hL] at hv
  exact hv

/-- A true above-threshold exponential lower bound, with no finiteness or
pressure conclusion supplied as a premise. Infinite partitions satisfy this
extended lower bound; below-collision properness is a separate obligation. -/
theorem exists_periodic_supercritical_exponential_lower (β : ℝ)
    (hβ : periodicStabilityThreshold ι < β) :
    ∃ c A : ℝ,0 < c ∧ ∀ N : ℕ,1 ≤ N →
      ENNReal.ofReal (Real.exp ((N:ℝ)*c-A)) ≤ periodicAttractivePartition (ι := ι) β N := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨ε,hε,hεsmall,hneg⟩ := exists_periodic_cosine_negative_free_energy β hβ i
  let E := ε^2/(2*periodicStabilityThreshold ι)
  let S := ∫ x,periodicCosineTrialDensity i ε x*Real.log (periodicCosineTrialDensity i ε x) ∂periodicHaar ι
  rw [periodicLog_cosine_trial_pair_energy i ε hεsmall] at hneg
  refine ⟨β/2*E-S,β/2*E,by dsimp [E,S]; linarith,?_⟩
  intro N hN
  convert periodic_cosine_trial_partition_lower i ε β hεsmall N hN using 1
  congr 2
  dsimp [E,S]
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_cosine_trial_partition_lower
#print axioms DGRHS.Periodic.exists_periodic_supercritical_exponential_lower
#check @DGRHS.Periodic.exists_periodic_supercritical_exponential_lower
