import DGPS.Lipschitz.T01NormalizerLimit

/-!
# The centered particle normalizer from the actual joint fluctuation law

All exponential moments are obtained from the same centered density and its log
normalizer. The limiting exponential is integrable by the particle moment bound.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Lipschitz

open KernelApproximation DGPS.Frontier.LIP051

/-- Remove the normalizing factor using its genuine uniform logarithmic bound. -/
theorem t01_unnormalized_exponential_moment {d : ℕ} (J : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) {p C : ℝ} (hp : 1 < p)
    (hlog : |Real.log (centeredParticleNormalizer J μ N)| ≤ C)
    (hmoment : ∫ x, centeredParticleDensity J μ N x ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C) :
    ∫ x, Real.exp (-centeredParticlePotential J μ N x) ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Real.exp C ^ p * C := by
  let Z := centeredParticleNormalizer J μ N
  have hZ : 0 < Z := centeredParticleNormalizer_pos J μ N
  have hZbound : Z ≤ Real.exp C := by
    rw [← Real.exp_log hZ]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hlog)
  have he : ∀ x, Real.exp (-centeredParticlePotential J μ N x) ^ p =
      Z ^ p * centeredParticleDensity J μ N x ^ p := by
    intro x
    rw [← Real.mul_rpow hZ.le (centeredParticleDensity_pos J μ N x).le]
    congr 1
    dsimp only [Z, centeredParticleDensity]
    field_simp [(centeredParticleNormalizer_pos J μ N).ne']
  simp_rw [he]
  rw [integral_const_mul]
  have hi0 : 0 ≤ ∫ x, centeredParticleDensity J μ N x ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) :=
    integral_nonneg fun x => Real.rpow_nonneg (centeredParticleDensity_pos J μ N x).le _
  exact mul_le_mul (Real.rpow_le_rpow hZ.le hZbound (by linarith)) hmoment hi0
    (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- The actual same-reference normalizer converges to the positive Wick exponential
integral. Its integrability is proved here, not assumed as an extra Gaussian input. -/
theorem t01_centered_particle_normalizer_limit {d : ℕ} (S : Spec d) (aux : Aux S)
    (D : KData d) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y)
    (hfix : (frozenGibbs J (specProbability_LIP016 S)).measure = S.mu)
    {p C : ℝ} (hp : 1 < p)
    (hN : ∀ N : ℕ+,
      |Real.log (centeredParticleNormalizer J (specProbability_LIP016 S) N)| ≤ C ∧
      (∫ x, centeredParticleDensity J (specProbability_LIP016 S) N x ^ p
        ∂Measure.pi (fun _ : Fin N => S.mu)) ≤ C) :
    let Uinf := fun z : ℕ → ℝ =>
      ((QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) z + dK_LIP05101 S D.K) / 2
    Integrable (fun z => Real.exp (-Uinf z)) gaussianCountable_LIP016 ∧
      0 < ∫ z, Real.exp (-Uinf z) ∂gaussianCountable_LIP016 ∧
      Tendsto (fun n : ℕ => centeredParticleNormalizer J (specProbability_LIP016 S)
        ⟨n + 1, Nat.succ_pos n⟩) atTop
        (𝓝 (∫ z, Real.exp (-Uinf z) ∂gaussianCountable_LIP016)) := by
  dsimp only
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let μ := specProbability_LIP016 S
  let Uinf := fun z : ℕ → ℝ =>
    ((QT_LIP05101 S D.K : (ℕ → ℝ) → ℝ) z + dK_LIP05101 S D.K) / 2
  have hjoint := jointFluctuationLimit_LIP051CLOSE S aux D J hD 0
  have hconv := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hjoint.forall_aemeasurable hjoint.aemeasurable_limit).mp hjoint
  have hU (n : ℕ) (x : Fin (n + 1) → Torus d) :
      U_LIP05101 D.K (n + 1) x = centeredParticlePotential J μ ⟨n + 1, Nat.succ_pos n⟩ x := by
    simp only [U_LIP05101, centeredParticlePotential, hD, one_div, μ, PNat.mk_coe]
    rfl
  have hi (n : ℕ) : Integrable (fun x => Real.exp (-U_LIP05101 D.K (n + 1) x))
      (refLaw_LIP05101 S (n + 1)) := by
    unfold refLaw_LIP05101
    simp_rw [hU]
    have hc : Continuous (fun x : Fin (n + 1) → Torus d =>
        Real.exp (-centeredParticlePotential J μ ⟨n + 1, Nat.succ_pos n⟩ x)) :=
      (centeredParticlePotential_continuous J μ ⟨n + 1, Nat.succ_pos n⟩).neg.rexp
    exact hc.integrable_of_hasCompactSupport
      (μ := Measure.pi fun _ : Fin (n + 1) => S.mu) (HasCompactSupport.of_compactSpace _)
  have hpi (n : ℕ) : Integrable (fun x => Real.exp (-U_LIP05101 D.K (n + 1) x) ^ p)
      (refLaw_LIP05101 S (n + 1)) := by
    unfold refLaw_LIP05101
    simp_rw [hU]
    have hc : Continuous (fun x : Fin (n + 1) → Torus d =>
        Real.exp (-centeredParticlePotential J μ ⟨n + 1, Nat.succ_pos n⟩ x) ^ p) :=
      (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
        (centeredParticlePotential_continuous J μ ⟨n + 1, Nat.succ_pos n⟩).neg.rexp
    exact hc.integrable_of_hasCompactSupport
      (μ := Measure.pi fun _ : Fin (n + 1) => S.mu) (HasCompactSupport.of_compactSpace _)
  obtain ⟨hint, hweighted⟩ := t01_weighted_joint_limit
    (P := fun n => refLaw_LIP05101 S (n + 1))
    (A := fun n => blockZ_LIP05101 S 0 (n + 1))
    (U := fun n => U_LIP05101 D.K (n + 1))
    (A' := blockCoord_LIP05101 0) (U' := Uinf)
    (fun G => (hconv G).comp (tendsto_add_atTop_nat 1))
    (w := fun u => Real.exp (-u)) (Real.continuous_exp.comp continuous_neg)
    (fun u => (Real.exp_pos _).le) hp
    (fun n => (hjoint.forall_aemeasurable (n + 1)).aestronglyMeasurable)
    hjoint.aemeasurable_limit.aestronglyMeasurable hi hpi
    (B := Real.exp C ^ p * C) (fun n => by
      simp_rw [hU]
      exact t01_unnormalized_exponential_moment J μ ⟨n + 1, Nat.succ_pos n⟩ hp
        (hN _).1 (hN _).2)
  refine ⟨hint, integral_exp_pos hint, ?_⟩
  have hlim := hweighted (BoundedContinuousFunction.const _ (1 : ℝ))
  simp only [BoundedContinuousFunction.const_apply, mul_one] at hlim
  convert hlim using 1
  funext n
  simp_rw [hU]
  exact centeredParticleNormalizer_eq_integral J μ hfix ⟨n + 1, Nat.succ_pos n⟩

end DGPS.Lipschitz
