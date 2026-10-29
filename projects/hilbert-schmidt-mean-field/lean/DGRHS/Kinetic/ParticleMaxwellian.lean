import DGRHS.Kinetic.Maxwellian

/-! The source's N-particle standard quadratic kinetic energy in its N*d
real coordinates. The normalizing constant and Gibbs tensorization are
computed, rather than assumed as a probability-factor premise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Kinetic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

def particleKineticEnergy (N : ℕ) (v : (Fin N × ι) → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N, ∑ j : ι, (v (i,j))^2

theorem particle_kinetic_exponent (β : ℝ) (N : ℕ) (v : (Fin N × ι) → ℝ) :
    kineticExponent β v = -β * particleKineticEnergy N v := by
  unfold kineticExponent particleKineticEnergy
  rw [Fintype.sum_prod_type]
  ring

theorem particle_kinetic_partition (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    (∫ v : (Fin N × ι) → ℝ, Real.exp (-β * particleKineticEnergy N v)) =
      (Real.sqrt (2*Real.pi/β))^(N * Fintype.card ι) := by
  simp_rw [←particle_kinetic_exponent]
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    kinetic_partition (J := Fin N × ι) β hβ

theorem particle_maxwellian_probability (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    IsProbabilityMeasure (maxwellian (Fin N × ι) β) :=
  maxwellian_probability β hβ

theorem particle_maxwellian_density (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    maxwellian (Fin N × ι) β = volume.withDensity
      (fun v : (Fin N × ι) → ℝ => ENNReal.ofReal
        (Real.exp (-β * particleKineticEnergy N v) /
          (Real.sqrt (2*Real.pi/β))^(N * Fintype.card ι))) := by
  simpa only [←particle_kinetic_exponent,Fintype.card_prod,Fintype.card_fin,
    kineticExponent] using maxwellian_density (J := Fin N × ι) β hβ

theorem particle_kinetic_gibbs_factorization (μ : Measure X) [SFinite μ]
    (H : X → ℝ) (hH : Measurable H) (β : ℝ) (N : ℕ) :
    (μ.prod (volume : Measure ((Fin N × ι) → ℝ))).tilted
      (fun z => -β * (H z.1 + particleKineticEnergy N z.2)) =
      (μ.tilted (fun x => -β * H x)).prod (maxwellian (Fin N × ι) β) := by
  have he (z : X × ((Fin N × ι) → ℝ)) :
      -β * (H z.1 + particleKineticEnergy N z.2) =
        (-β * H z.1) + kineticExponent β z.2 := by
    rw [particle_kinetic_exponent]
    ring
  simp_rw [he]
  exact gibbs_separable_tensor μ volume (fun x => -β * H x)
    (kineticExponent β) (hH.const_mul _) (by unfold kineticExponent; fun_prop)

theorem particle_kinetic_full_partition (μ : Measure X) [SFinite μ]
    (H : X → ℝ) (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    (∫ z : X × ((Fin N × ι) → ℝ),
      Real.exp (-β * (H z.1 + particleKineticEnergy N z.2)) ∂μ.prod volume) =
        (∫ x, Real.exp (-β * H x) ∂μ) *
          (Real.sqrt (2*Real.pi/β))^(N * Fintype.card ι) := by
  have he (z : X × ((Fin N × ι) → ℝ)) :
      -β * (H z.1 + particleKineticEnergy N z.2) =
        (-β * H z.1) - (β/2)*∑ j : Fin N × ι, (z.2 j)^2 := by
    unfold particleKineticEnergy
    rw [Fintype.sum_prod_type]
    ring
  simp_rw [he]
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    kinetic_full_partition (J := Fin N × ι) μ (fun x => -β * H x) β hβ

end DGRHS.Kinetic
#check @DGRHS.Kinetic.particleKineticEnergy
#print axioms DGRHS.Kinetic.particleKineticEnergy
#check @DGRHS.Kinetic.particle_kinetic_exponent
#print axioms DGRHS.Kinetic.particle_kinetic_exponent
#check @DGRHS.Kinetic.particle_kinetic_partition
#print axioms DGRHS.Kinetic.particle_kinetic_partition
#check @DGRHS.Kinetic.particle_maxwellian_probability
#print axioms DGRHS.Kinetic.particle_maxwellian_probability
#check @DGRHS.Kinetic.particle_maxwellian_density
#print axioms DGRHS.Kinetic.particle_maxwellian_density
#check @DGRHS.Kinetic.particle_kinetic_gibbs_factorization
#print axioms DGRHS.Kinetic.particle_kinetic_gibbs_factorization
#check @DGRHS.Kinetic.particle_kinetic_full_partition
#print axioms DGRHS.Kinetic.particle_kinetic_full_partition
