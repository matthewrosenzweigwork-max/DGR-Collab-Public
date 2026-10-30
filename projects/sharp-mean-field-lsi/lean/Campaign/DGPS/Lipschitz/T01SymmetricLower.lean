import DGPS.Equilibrium.Hessian
import DGPS.Variational.FrozenGibbs
import DGPS.Particle.Gibbs
import DGPS.Particle.Symmetry
import DGPS.FiniteN.Tools.Hubbard
import DGPS.FiniteN.Tools.Rothaus
import FullLabeledLSI.Paper.Prop23Ground2

/-!
# Canonical centered Gibbs/reference identities for T01

These identities supply the change of measure needed before reference-product occupation
compactness can be applied. They use continuous interaction data only. They do not assert a
particle lower limit; uniform density moments and the limiting form comparison remain separate
analytic obligations.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The centered interaction U-statistic, including its generally nonzero diagonal. -/
noncomputable def centeredParticlePotential (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (x : ParticleSpace d N) : ℝ :=
  (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, DGPS.centeredKernel A μ (x i) (x j)

theorem centeredParticlePotential_continuous (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) :
    Continuous (centeredParticlePotential A μ N) := by
  unfold centeredParticlePotential
  have hsum : Continuous (fun x : ParticleSpace d N =>
      ∑ i, ∑ j, DGPS.centeredKernel A μ (x i) (x j)) := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    have hp : Continuous (fun x : ParticleSpace d N => (x i, x j)) :=
      (continuous_apply i).prodMk (continuous_apply j)
    exact (DGPS.continuous_centeredKernel A μ).comp hp
  exact hsum.const_mul _

/-- Exact centering of the canonical Hamiltonian; the mean-interaction constant is retained. -/
theorem particleHamiltonian_eq_centered (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (x : ParticleSpace d N) :
    particleHamiltonian A N x =
      (∑ i, frozenPotential A (μ : Measure (Torus d)) (x i)) +
        centeredParticlePotential A μ N x - (N : ℝ) * meanInteraction A μ / 2 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.pos.ne'
  have hsum : (∑ i : Fin N, ∑ j : Fin N, DGPS.centeredKernel A μ (x i) (x j)) =
      (∑ i, ∑ j, A.W (x i) (x j)) -
        2 * (N : ℝ) * (∑ i, interactionConvolution A μ (x i)) +
          (N : ℝ) ^ 2 * meanInteraction A μ := by
    simp only [DGPS.centeredKernel, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  unfold interactionConvolution at hsum
  simp only [particleHamiltonian, centeredParticlePotential, frozenPotential,
    Finset.sum_add_distrib]
  rw [hsum]
  field_simp [hN]
  <;> ring

/-- Algebraic expression for the centered partition function. Its integral interpretation is
proved below when the reference is an actual fixed point. -/
noncomputable def centeredParticleNormalizer (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) : ℝ :=
  particlePartition A N /
    (frozenPartition A (μ : Measure (Torus d)) ^ (N : ℕ) *
      Real.exp ((N : ℝ) * meanInteraction A μ / 2))

theorem centeredParticleNormalizer_pos (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) :
    0 < centeredParticleNormalizer A μ N :=
  div_pos (DGPS.Particle.particlePartition_pos A N)
    (mul_pos (pow_pos (frozenPartition_pos A (μ : Measure (Torus d))) _) (Real.exp_pos _))

/-- The particle density relative to the product frozen-Gibbs reference. -/
noncomputable def centeredParticleDensity (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (x : ParticleSpace d N) : ℝ :=
  Real.exp (-centeredParticlePotential A μ N x) / centeredParticleNormalizer A μ N

theorem centeredParticleDensity_pos (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (x : ParticleSpace d N) :
    0 < centeredParticleDensity A μ N x :=
  div_pos (Real.exp_pos _) (centeredParticleNormalizer_pos A μ N)

theorem centeredParticleDensity_continuous (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) :
    Continuous (centeredParticleDensity A μ N) :=
  (centeredParticlePotential_continuous A μ N).neg.rexp.div_const _

theorem particleDensity_eq_centered_mul_frozen (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (x : ParticleSpace d N) :
    particleDensity A N x = centeredParticleDensity A μ N x *
      ∏ i : Fin N, frozenDensity A (μ : Measure (Torus d)) (x i) := by
  have hZ := (DGPS.Particle.particlePartition_pos A N).ne'
  have hqZ := (frozenPartition_pos A (μ : Measure (Torus d))).ne'
  have hE := (Real.exp_pos ((N : ℝ) * meanInteraction A μ / 2)).ne'
  have hprod : (∏ i : Fin N, frozenDensity A (μ : Measure (Torus d)) (x i)) =
      Real.exp (-(∑ i, frozenPotential A (μ : Measure (Torus d)) (x i))) /
        frozenPartition A (μ : Measure (Torus d)) ^ (N : ℕ) := by
    simp only [frozenDensity, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, Finset.sum_neg_distrib]
  rw [hprod, particleDensity, particleHamiltonian_eq_centered]
  unfold centeredParticleDensity centeredParticleNormalizer
  rw [show -((∑ i, frozenPotential A (μ : Measure (Torus d)) (x i)) +
      centeredParticlePotential A μ N x - (N : ℝ) * meanInteraction A μ / 2) =
      -centeredParticlePotential A μ N x +
        (N : ℝ) * meanInteraction A μ / 2 +
          -(∑ i, frozenPotential A (μ : Measure (Torus d)) (x i)) by ring,
    Real.exp_add, Real.exp_add]
  field_simp [hZ, hqZ, hE]
  <;> ring

/-- At a fixed point, the reference in the centered formula is exactly `μ` to the Nth power. -/
theorem particleLaw_eq_centered_reference (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+) :
    particleLaw A N = (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))).withDensity
      (fun x => ENNReal.ofReal (centeredParticleDensity A μ N x)) := by
  have href : (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) =
      (particleHaar d N).withDensity
        (fun x => ENNReal.ofReal (∏ i : Fin N, frozenDensity A
          (μ : Measure (Torus d)) (x i))) := by
    conv_lhs => rw [← hμ]
    exact DGPS.FiniteN.Tools.Hubbard.pi_withDensity_ofReal
      (m := haar d) (frozenDensity A (μ : Measure (Torus d)))
      (frozenGibbs A μ).integrable_density
      (fun x => (div_pos (Real.exp_pos _) (frozenPartition_pos A
        (μ : Measure (Torus d)))).le) (N : ℕ)
  have hprod : Measurable (fun x : ParticleSpace d N =>
      ENNReal.ofReal (∏ i : Fin N, frozenDensity A (μ : Measure (Torus d)) (x i))) :=
    (Finset.measurable_prod _ fun i _ =>
      ((frozenDensity_continuous A (μ : Measure (Torus d))).measurable.comp
        (measurable_pi_apply i))).ennreal_ofReal
  rw [href, ← withDensity_mul₀ hprod.aemeasurable
    (centeredParticleDensity_continuous A μ N).measurable.ennreal_ofReal.aemeasurable]
  unfold particleLaw
  congr 1
  funext x
  change ENNReal.ofReal (particleDensity A N x) =
    ENNReal.ofReal (∏ i : Fin N, frozenDensity A (μ : Measure (Torus d)) (x i)) *
      ENNReal.ofReal (centeredParticleDensity A μ N x)
  calc ENNReal.ofReal (particleDensity A N x) =
      ENNReal.ofReal (centeredParticleDensity A μ N x *
        ∏ i : Fin N, frozenDensity A (μ : Measure (Torus d)) (x i)) :=
          congrArg ENNReal.ofReal (particleDensity_eq_centered_mul_frozen A μ N x)
    _ = ENNReal.ofReal (centeredParticleDensity A μ N x) *
        ENNReal.ofReal (∏ i : Fin N, frozenDensity A (μ : Measure (Torus d)) (x i)) :=
      ENNReal.ofReal_mul (centeredParticleDensity_pos A μ N x).le
    _ = _ := mul_comm _ _

theorem integral_particleLaw_eq_centered (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) :
    ∫ x, f x ∂particleLaw A N =
      ∫ x, centeredParticleDensity A μ N x * f x
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  rw [particleLaw_eq_centered_reference A μ hμ N,
    integral_withDensity_eq_integral_toReal_smul
      (centeredParticleDensity_continuous A μ N).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (centeredParticleDensity_pos A μ N x).le]

theorem centeredParticleDensity_mass_one (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+) :
    ∫ x, centeredParticleDensity A μ N x
      ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) = 1 := by
  have h := integral_particleLaw_eq_centered A μ hμ N (fun _ => 1)
  simpa using h.symm

theorem centeredParticleNormalizer_eq_integral (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+) :
    centeredParticleNormalizer A μ N =
      ∫ x, Real.exp (-centeredParticlePotential A μ N x)
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  have h := centeredParticleDensity_mass_one A μ hμ N
  unfold centeredParticleDensity at h
  rw [integral_div] at h
  exact ((div_eq_one_iff_eq (centeredParticleNormalizer_pos A μ N).ne').1 h).symm

/-- Ground-state transform into the canonical equilibrium product reference. -/
noncomputable def centeredParticleRoot (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (f : ParticleSpace d N → ℝ)
    (x : ParticleSpace d N) : ℝ :=
  f x * Real.sqrt (centeredParticleDensity A μ N x)

theorem centeredParticleRoot_sq (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (f : ParticleSpace d N → ℝ)
    (x : ParticleSpace d N) :
    centeredParticleRoot A μ N f x ^ 2 = centeredParticleDensity A μ N x * f x ^ 2 := by
  unfold centeredParticleRoot
  rw [mul_pow, Real.sq_sqrt (centeredParticleDensity_pos A μ N x).le, mul_comm]

theorem centeredParticleRoot_mass (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) :
    ∫ x, centeredParticleRoot A μ N f x ^ 2
      ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) =
        ∫ x, f x ^ 2 ∂particleLaw A N := by
  simp_rw [centeredParticleRoot_sq]
  exact (integral_particleLaw_eq_centered A μ hμ N (fun x => f x ^ 2)).symm

theorem centeredParticlePotential_permute (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (σ : Equiv.Perm (Fin N))
    (x : ParticleSpace d N) :
    centeredParticlePotential A μ N (permuteParticles σ x) =
      centeredParticlePotential A μ N x := by
  unfold centeredParticlePotential permuteParticles
  congr 1
  rw [← Equiv.sum_comp σ (fun i => ∑ j, DGPS.centeredKernel A μ (x i) (x j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp σ (fun j => DGPS.centeredKernel A μ (x (σ i)) (x j))

theorem centeredParticleDensity_permute (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (σ : Equiv.Perm (Fin N))
    (x : ParticleSpace d N) :
    centeredParticleDensity A μ N (permuteParticles σ x) =
      centeredParticleDensity A μ N x := by
  simp only [centeredParticleDensity, centeredParticlePotential_permute]

theorem reference_absolutelyContinuous_particleLaw (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+) :
    (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≪ particleLaw A N := by
  rw [particleLaw_eq_centered_reference A μ hμ N]
  exact withDensity_absolutelyContinuous'
    (centeredParticleDensity_continuous A μ N).measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x =>
      (ENNReal.ofReal_pos.2 (centeredParticleDensity_pos A μ N x)).ne')

theorem particleLaw_rnDeriv_reference (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+) :
    (fun x => ((particleLaw A N).rnDeriv
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) x).toReal) =ᵐ[
        Measure.pi fun _ : Fin N => (μ : Measure (Torus d))] centeredParticleDensity A μ N := by
  rw [particleLaw_eq_centered_reference A μ hμ N]
  filter_upwards [Measure.rnDeriv_withDensity
    (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))
    (centeredParticleDensity_continuous A μ N).measurable.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (centeredParticleDensity_pos A μ N x).le]

/-- The ground-state transform preserves the actual a.e. symmetry used by occupation compactness. -/
theorem centeredParticleRoot_symmetric (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) (hf : IsSymmetricParticleFun A N f)
    (σ : Equiv.Perm (Fin N)) :
    (fun x => centeredParticleRoot A μ N f (x ∘ σ)) =ᵐ[
      Measure.pi fun _ : Fin N => (μ : Measure (Torus d))] centeredParticleRoot A μ N f := by
  have h := (reference_absolutelyContinuous_particleLaw A μ hμ N).ae_le (hf σ)
  filter_upwards [h] with x hx
  change f (permuteParticles σ x) = f x at hx
  change f (permuteParticles σ x) *
      Real.sqrt (centeredParticleDensity A μ N (permuteParticles σ x)) = _
  rw [hx, centeredParticleDensity_permute]
  rfl

/-- Exact entropy change of reference for bounded tests, including zero mass. The two legacy
helpers used below are generic probability-space entropy lemmas and carry no `Hyp` premise. -/
theorem centeredParticleRoot_entropy (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) (hf : MemLp f 2 (particleLaw A N)) {B : ℝ}
    (hB : ∀ᵐ x ∂particleLaw A N, |f x| ≤ B) :
    (homogeneousEntropy (particleLaw A N) (fun x => f x ^ 2)).toReal =
      (homogeneousEntropy (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))
        (fun x => centeredParticleRoot A μ N f x ^ 2)).toReal +
      (∫ x, centeredParticleRoot A μ N f x ^ 2 * centeredParticlePotential A μ N x
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) +
      Real.log (centeredParticleNormalizer A μ N) *
        (∫ x, centeredParticleRoot A μ N f x ^ 2
          ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) := by
  let P := particleLaw A N
  let Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  let p := centeredParticleDensity A μ N
  let U := centeredParticlePotential A μ N
  let K := centeredParticleNormalizer A μ N
  let u := fun x : ParticleSpace d N => f x ^ 2
  let v := fun x : ParticleSpace d N => centeredParticleRoot A μ N f x ^ 2
  have hp0 : ∀ x, 0 < p x := centeredParticleDensity_pos A μ N
  have hu0 : ∀ x, 0 ≤ u x := fun x => sq_nonneg _
  have hv0 : ∀ x, 0 ≤ v x := fun x => sq_nonneg _
  have hvu : ∀ x, v x = p x * u x := centeredParticleRoot_sq A μ N f
  have hac : Q ≪ P := reference_absolutelyContinuous_particleLaw A μ hμ N
  have humP : AEStronglyMeasurable u P := hf.aestronglyMeasurable.pow 2
  have humQ : AEStronglyMeasurable u Q := humP.mono_ac hac
  have hpm : Measurable p := (centeredParticleDensity_continuous A μ N).measurable
  have hvmQ : AEStronglyMeasurable v Q :=
    (hpm.aestronglyMeasurable.mul humQ).congr
      (Filter.Eventually.of_forall fun x => (hvu x).symm)
  have huBP : ∀ᵐ x ∂P, u x ≤ B ^ 2 := hB.mono fun x hx => by
    change f x ^ 2 ≤ B ^ 2
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have huBQ : ∀ᵐ x ∂Q, u x ≤ B ^ 2 := hac.ae_le huBP
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (centeredParticleDensity_continuous A μ N).continuousOn
  have hpC : ∀ x, p x ≤ C := fun x =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC x (Set.mem_univ x))
  have hC0 : 0 ≤ C := (hp0 (fun _ => 0)).le.trans (hpC _)
  have hvCQ : ∀ᵐ x ∂Q, v x ≤ C * B ^ 2 := huBQ.mono fun x hx => by
    rw [hvu]
    exact mul_le_mul (hpC x) hx (hu0 x) hC0
  have hiu : Integrable u P := hf.integrable_sq
  have hiv : Integrable v Q := Integrable.of_bound (C := C * B ^ 2) hvmQ
    (hvCQ.mono fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (hv0 x)]; exact hx)
  have hilP : Integrable (fun x => u x * Real.log (u x)) P :=
    SharpLSI.FL.g2_integrable_mul_log_of_bdd humP (Filter.Eventually.of_forall hu0) huBP
  have hilQ : Integrable (fun x => v x * Real.log (v x)) Q :=
    SharpLSI.FL.g2_integrable_mul_log_of_bdd hvmQ (Filter.Eventually.of_forall hv0) hvCQ
  obtain ⟨CU, hCU⟩ := isCompact_univ.exists_bound_of_continuousOn
    (centeredParticlePotential_continuous A μ N).continuousOn
  have hUm : Measurable U := (centeredParticlePotential_continuous A μ N).measurable
  have hivU : Integrable (fun x => v x * U x) Q :=
    Integrable.of_bound (C := C * B ^ 2 * CU) (hvmQ.mul hUm.aestronglyMeasurable)
      (hvCQ.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 x)]
        exact mul_le_mul hx (by simpa [Real.norm_eq_abs] using hCU x (Set.mem_univ x))
          (abs_nonneg _) (mul_nonneg hC0 (sq_nonneg _)))
  have hm : ∫ x, u x ∂P = ∫ x, v x ∂Q := (centeredParticleRoot_mass A μ hμ N f).symm
  have hpt : ∀ x, p x * (u x * Real.log (u x)) =
      v x * Real.log (v x) + v x * U x + Real.log K * v x := by
    intro x
    rcases (hu0 x).eq_or_lt with hx | hx
    · have hvx : v x = 0 := by rw [hvu, ← hx, mul_zero]
      rw [← hx, hvx]
      simp
    · have hlp : Real.log (p x) = -U x - Real.log K := by
        change Real.log (Real.exp (-U x) / K) = -U x - Real.log K
        rw [Real.log_div (Real.exp_pos _).ne'
          (centeredParticleNormalizer_pos A μ N).ne', Real.log_exp]
      have hlv : Real.log (v x) = Real.log (p x) + Real.log (u x) := by
        rw [hvu, Real.log_mul (hp0 x).ne' hx.ne']
      rw [hlv, hlp, hvu]
      ring
  have hlog : ∫ x, u x * Real.log (u x) ∂P =
      (∫ x, v x * Real.log (v x) ∂Q) + (∫ x, v x * U x ∂Q) +
        Real.log K * ∫ x, v x ∂Q := by
    rw [integral_particleLaw_eq_centered A μ hμ N]
    change (∫ x, p x * (u x * Real.log (u x)) ∂Q) = _
    simp_rw [hpt]
    rw [integral_add (f := fun x => v x * Real.log (v x) + v x * U x)
      (g := fun x => Real.log K * v x) (hilQ.add hivU) (hiv.const_mul _),
      integral_add (f := fun x => v x * Real.log (v x)) (g := fun x => v x * U x)
        hilQ hivU, integral_const_mul]
  change (homogeneousEntropy P u).toReal =
    ((homogeneousEntropy Q v).toReal + ∫ x, v x * U x ∂Q) +
      Real.log K * ∫ x, v x ∂Q
  rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hiu,
    DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hiv,
    SharpLSI.FL.g2_ent_toReal_formula P u hu0 hiu hilP,
    SharpLSI.FL.g2_ent_toReal_formula Q v hv0 hiv hilQ, hlog, hm]
  ring

end DGPS.Lipschitz
