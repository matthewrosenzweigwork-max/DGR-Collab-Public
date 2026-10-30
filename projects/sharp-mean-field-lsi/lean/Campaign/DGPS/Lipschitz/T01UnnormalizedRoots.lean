import DGPS.Lipschitz.T01RootReferenceBounds
import SharpSymmetricLSI.Paper.GroundT17

/-!
# Uniform reference bounds for unnormalized actual ground-state roots

Scalar rescaling of the actual roots gives a uniform reference Sobolev bound for
`f * sqrt (exp (-U))` on bounded particle energy classes. The reference density
bound is retained explicitly in the scalar Sobolev lemma.
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal BoundedContinuousFunction InnerProductSpace

namespace DGPS.Lipschitz

variable {d : ℕ}

private theorem reference_const_mul {N : ℕ} (P : BoundedPositiveReference d)
    {u : Config N d → ℝ} (hu : MemH1C (Measure.pi fun _ : Fin N => P.measure) u) (c : ℝ) :
    MemH1C (Measure.pi fun _ : Fin N => P.measure) (fun X => c * u X) ∧
      SharpLSI.FL.refEnergy P.measure (fun X => c * u X) =
        ENNReal.ofReal (c ^ 2) * SharpLSI.FL.refEnergy P.measure u := by
  have hac := SharpLSI.FL.Spectral.ac_map_flat (N := N) P.measure_le_smul_haar
  have hH : MemH1C (Measure.pi fun _ : Fin N => P.measure) (fun X => c * u X) := by
    refine ⟨⟨_, (isWeakGrad_weakGrad hu.1).const_mul c⟩, hu.2.1.const_mul c, ?_⟩
    refine (hu.2.2.const_mul |c|).ae_eq ?_
    filter_upwards [hac.ae_le (weakGrad_const_mul_ae hu.1 c)] with y hy
    show |c| * Real.sqrt (sqNorm (weakGrad (u ∘ unflat) y)) =
      Real.sqrt (sqNorm (weakGrad ((fun X => c * u X) ∘ unflat) y))
    rw [show ((fun X => c * u X) ∘ unflat) = fun y => c * (u ∘ unflat) y from rfl, hy]
    unfold sqNorm
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  refine ⟨hH, ?_⟩
  have hcfg : ∀ᵐ X ∂Measure.pi (fun _ : Fin N => P.measure),
      gradSqC (fun X => c * u X) X = c ^ 2 * gradSqC u X := by
    have he := ae_of_ae_map measurable_flat.aemeasurable
      (hac.ae_le (weakGrad_const_mul_ae hu.1 c))
    filter_upwards [he] with X hX
    rw [gradSqC_eq_sqNorm, gradSqC_eq_sqNorm,
      show ((fun X => c * u X) ∘ unflat) = fun y => c * (u ∘ unflat) y from rfl, hX]
    unfold sqNorm
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
  unfold SharpLSI.FL.refEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae (hcfg.mono fun X hX => ?_)
  change ENNReal.ofReal (gradSqC (fun X => c * u X) X) =
    ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (gradSqC u X)
  rw [hX, ENNReal.ofReal_mul (sq_nonneg c)]

/-- The unnormalized actual roots have a uniform reference Sobolev bound on each
bounded particle mass/energy class. -/
theorem t01_unnormalized_roots_reference_bounds (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hN : ∀ N : ℕ+, |Real.log (centeredParticleNormalizer A μ N)| ≤ C ∧
      ∫ x, centeredParticleDensity A μ N x ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C)
    (B E0 : ℝ) (hB0 : 0 ≤ B) (hE0 : 0 ≤ E0) :
    ∃ L : ℝ, ∀ (N : ℕ+) (f : ParticleH1 A N), (∀ x, |f x| ≤ B) →
      particleEnergy A N f ≤ E0 →
      let Ψ := fun X => f X * Real.sqrt (Real.exp (-centeredParticlePotential A μ N X))
      MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ ∧
      (∫ X, Ψ X ^ 2 ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) ≤ L ∧
      (SharpLSI.FL.refEnergy (μ : Measure (Torus d)) Ψ).toReal ≤ L := by
  obtain ⟨M, hM0, hM⟩ := centeredParticleRoot_uniform_reference_bounds A hA hd μ hfix hp hC0
    (fun N => (hN N).2)
  let R := 2 * E0 + B ^ 2 * M / 2
  refine ⟨Real.exp C * (B ^ 2 + R), fun N f hB hE => ?_⟩
  obtain ⟨hH, hEn, -⟩ := hM B E0 hB0 hE0 N f hB hE
  let K := centeredParticleNormalizer A μ N
  have hK : 0 < K := centeredParticleNormalizer_pos A μ N
  have hKC : K ≤ Real.exp C := by
    rw [← Real.exp_log hK]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hN N).1)
  have hΨ : (fun X => f X * Real.sqrt (Real.exp (-centeredParticlePotential A μ N X))) =
      fun X => Real.sqrt K * centeredParticleRoot A μ N f X := by
    funext X
    unfold centeredParticleRoot centeredParticleDensity
    have he := SharpLSI.sqrt_rescale
      (Real.exp_pos (-centeredParticlePotential A μ N X)).le hK zero_lt_one
    simp only [div_one] at he
    rw [he]
    ring
  obtain ⟨hscaled, hscaledE⟩ := reference_const_mul (frozenGibbs A μ)
    (by simpa only [hfix] using hH) (Real.sqrt K)
  rw [hfix] at hscaled hscaledE
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [hΨ]
    exact hscaled
  · have hmEq : (∫ X, (f X * Real.sqrt (Real.exp (-centeredParticlePotential A μ N X))) ^ 2
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) =
        K * ∫ X, f X ^ 2 ∂particleLaw A N := by
      calc
        _ = ∫ X, (Real.sqrt K * centeredParticleRoot A μ N f X) ^ 2
            ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) :=
          integral_congr_ae (Eventually.of_forall fun X => congrArg (fun t : ℝ => t ^ 2)
            (congrFun hΨ X))
        _ = K * ∫ X, centeredParticleRoot A μ N f X ^ 2
            ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
          simp_rw [mul_pow]
          rw [integral_const_mul, Real.sq_sqrt hK.le]
        _ = _ := by rw [centeredParticleRoot_mass A μ hfix]
    rw [hmEq]
    have hmass : ∫ X, f X ^ 2 ∂particleLaw A N ≤ B ^ 2 := by
      calc
        _ ≤ ∫ _ : ParticleSpace d N, B ^ 2 ∂particleLaw A N :=
          integral_mono (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
            (integrable_const _) (fun X => by
              simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB X) 2)
        _ = _ := by simp
    have hm0 : 0 ≤ ∫ X, f X ^ 2 ∂particleLaw A N := integral_nonneg fun X => sq_nonneg _
    have hR0 : 0 ≤ R := by dsimp only [R]; positivity
    exact (mul_le_mul hKC hmass hm0 (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR0) (Real.exp_pos _).le)
  · rw [hΨ, hscaledE, Real.sq_sqrt hK.le, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le]
    have hRef : (SharpLSI.FL.refEnergy (μ : Measure (Torus d))
        (centeredParticleRoot A μ N f)).toReal ≤ R := by
      have hR0 : 0 ≤ R := by dsimp only [R]; positivity
      change SharpLSI.FL.refEnergy (μ : Measure (Torus d))
        (centeredParticleRoot A μ N f) ≤ ENNReal.ofReal R at hEn
      have ht := (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEn) ENNReal.ofReal_ne_top).mpr hEn
      rw [ENNReal.toReal_ofReal hR0] at ht
      exact ht
    have hR0 : 0 ≤ R := by dsimp only [R]; positivity
    exact (mul_le_mul hKC hRef ENNReal.toReal_nonneg (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg B)) (Real.exp_pos _).le)

end DGPS.Lipschitz
