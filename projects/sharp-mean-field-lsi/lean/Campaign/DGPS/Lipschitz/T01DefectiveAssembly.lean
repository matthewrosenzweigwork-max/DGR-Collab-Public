import DGPS.Lipschitz.T01ReferenceData
import DGPS.Particle.ConditionalForceReplacement
import FullLabeledLSI.Paper.Sec5LNF
import FullLabeledLSI.Paper.Sec5LNG
import FullLabeledLSI.Paper.Sec5LNDefs

/-!
# Conditional-level summation and defective absorption

The arithmetic below consumes conditional-level inequalities, not a defective inequality.
The interaction approximation uses the actual centered kernel and applies to every law.
The entropy identity uses the actual Gibbs/reference change of density. No symmetry or
legacy semiconvexity hypothesis is used.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Sum the per-level mean-field bound. Only the fraction of revealed levels is discarded;
the Fisher term is nonnegative and the force errors retain their full sum. -/
theorem t01_sum_conditional_levels {N M : ℕ} (hN : 0 < N)
    {r ε I : ℝ} (hε : 0 ≤ ε) (hI : 0 ≤ I) (h cp F : ℕ → ℝ)
    (hlevel : ∀ j < N,
      2 * r * (h j + cp j) ≤ (1 + ε) * ((N : ℝ)⁻¹ * I) + (1 + 1 / ε) * F j) :
    2 * r * ((∑ j ∈ Finset.range (N - M), h j) +
      ∑ j ∈ Finset.range (N - M), cp j) ≤
      (1 + ε) * I + (1 + 1 / ε) * ∑ j ∈ Finset.range (N - M), F j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfrac : ((N - M : ℕ) : ℝ) * (N : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hNr]
    exact_mod_cast Nat.sub_le N M
  have hs := Finset.sum_le_sum fun j (hj : j ∈ Finset.range (N - M)) =>
    hlevel j (by have := Finset.mem_range.mp hj; omega)
  have e1 : (∑ j ∈ Finset.range (N - M), 2 * r * (h j + cp j)) =
      2 * r * ((∑ j ∈ Finset.range (N - M), h j) +
        ∑ j ∈ Finset.range (N - M), cp j) := by
    rw [← Finset.sum_add_distrib, ← Finset.mul_sum]
  have e2 : (∑ j ∈ Finset.range (N - M),
      ((1 + ε) * ((N : ℝ)⁻¹ * I) + (1 + 1 / ε) * F j)) =
      (((N - M : ℕ) : ℝ) * (N : ℝ)⁻¹) * ((1 + ε) * I) +
        (1 + 1 / ε) * ∑ j ∈ Finset.range (N - M), F j := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.mul_sum]
    ring
  rw [e1, e2] at hs
  have hmul : (((N - M : ℕ) : ℝ) * (N : ℝ)⁻¹) * ((1 + ε) * I) ≤ (1 + ε) * I :=
    mul_le_of_le_one_left (mul_nonneg (by linarith) hI) hfrac
  linarith only [hs, hmul]

/-- The true centered interaction has the averaged conditional-product estimate, including
the empirical diagonal. The constant is independent of particle number and the comparison law. -/
theorem t01_centered_conditional_products {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ (N : ℕ+) (M : ℕ), 2 ≤ M → M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
        klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ →
        |∑ j ∈ Finset.range ((N : ℕ) - M), SharpLSI.FL.condMeanS ν 2
            (fun z => DGPS.centeredKernel A μ (z 0) (z 1) / 2) j -
          (((N : ℕ) - M : ℕ) : ℝ) / N * ∫ X, centeredParticlePotential A μ N X ∂ν| ≤
          C * (1 + Real.sqrt
            (klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal) := by
  let B : (Fin 2 → Torus d) → ℝ := fun z => DGPS.centeredKernel A μ (z 0) (z 1) / 2
  have hBm : Measurable B := by
    have hm : Measurable (fun z : Fin 2 → Torus d => (z 0, z 1)) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    simpa only [B, Function.comp_def] using
      ((DGPS.continuous_centeredKernel A μ).measurable.comp hm).div_const 2
  obtain ⟨BK, hBK⟩ := SharpLSI.exists_bound_of_continuous (DGPS.continuous_centeredKernel A μ)
  have hBb : ∃ b, ∀ z, |B z| ≤ b := ⟨BK / 2, fun z => by
    dsimp [B]
    rw [abs_div, abs_two]
    exact div_le_div_of_nonneg_right (hBK (z 0, z 1)) zero_le_two⟩
  obtain ⟨C, hC⟩ := SharpLSI.FL.random_products_aux 2 τ hτ B hBm hBb
  refine ⟨C, fun N M hM hMN hτM ν _ hH => ?_⟩
  have h := hC N M hM hMN hτM (μ : Measure (Torus d)) ν hH
  have hU : ∫ X, SharpLSI.empiricalTensor 2 B X ∂ν =
      (∫ X, centeredParticlePotential A μ N X ∂ν) / N := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun X => by
      have he := SharpLSI.mul_empiricalTensor_two (N := N) (DGPS.centeredKernel A μ) X
      change SharpLSI.empiricalTensor 2 B X = centeredParticlePotential A μ N X / N
      rw [eq_div_iff (by exact_mod_cast N.pos.ne' : (N : ℝ) ≠ 0), mul_comm]
      simpa only [B, centeredParticlePotential] using he
  rw [hU] at h
  have he : (((N : ℕ) - M : ℕ) : ℝ) *
      ((∫ X, centeredParticlePotential A μ N X ∂ν) / N) =
      (((N : ℕ) - M : ℕ) : ℝ) / N * ∫ X, centeredParticlePotential A μ N X ∂ν := by ring
  rwa [he] at h

/-- The actual particle relative entropy equals the product-reference entropy plus the
expected centered potential and log normalizer. Finiteness at either reference is equivalent. -/
theorem t01_particle_relative_entropy_identity {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν]
    (hfin : klDiv ν (particleLaw A N) ≠ ⊤) :
    klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ ∧
      (klDiv ν (particleLaw A N)).toReal =
        (klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal +
          (∫ X, centeredParticlePotential A μ N X ∂ν) +
          Real.log (centeredParticleNormalizer A μ N) := by
  let Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  let f : ParticleSpace d N → ℝ := fun X => -centeredParticlePotential A μ N X
  have hf : Measurable f := (centeredParticlePotential_continuous A μ N).neg.measurable
  obtain ⟨B, hB⟩ := SharpLSI.exists_bound_of_continuous
    (centeredParticlePotential_continuous A μ N).neg
  have hZ : ∫ X, Real.exp (f X) ∂Q = centeredParticleNormalizer A μ N :=
    (centeredParticleNormalizer_eq_integral A μ hμ N).symm
  have ht : Q.tilted f = particleLaw A N := by
    unfold Measure.tilted
    rw [hZ]
    exact (particleLaw_eq_centered_reference A μ hμ N).symm
  have hνQ : klDiv ν Q ≠ ⊤ :=
    (klDiv_tilted_ne_top_iff hf hB).1 (by rwa [ht])
  refine ⟨hνQ, ?_⟩
  have he := (klDiv_tilted_forward hf hB hνQ).2
  rw [ht, hZ] at he
  simpa only [f, integral_neg, sub_neg_eq_add] using he

/-- The relative score energy is bounded by the actual Fisher sum and the explicit
particle-force square. This uses factual score data and bounded force representatives only;
no identification with a chosen legacy derivative and no semiconvexity are needed. -/
theorem t01_score_difference_energy_le {d N : ℕ}
    {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hS : SharpLSI.FL.ScoreData V W μ ν Q c C GQ s bF bΔ B) :
    (∑ i, ∫ X, ∑ k : Fin d, (s i k X - SharpLSI.FL.Gpart bF bΔ N X i k) ^ 2 ∂ν) ≤
      2 * SharpLSI.FL.fisherS ν s +
        2 * ∫ X, ∑ i, ∑ k : Fin d, SharpLSI.FL.Gpart bF bΔ N X i k ^ 2 ∂ν := by
  classical
  have hGm : ∀ i k, Measurable fun X : SharpLSI.Config N d =>
      SharpLSI.FL.Gpart bF bΔ N X i k := fun i k => SharpLSI.FL.measurable_Gpart hS.force i k
  have hGi : ∀ i k, Integrable (fun X => SharpLSI.FL.Gpart bF bΔ N X i k ^ 2) ν := fun i k =>
    Integrable.of_bound ((hGm i k).pow_const 2).aestronglyMeasurable
      (((N : ℝ)⁻¹ * ((N : ℝ) * B + B)) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (SharpLSI.FL.abs_Gpart_le hS.force X i k) 2)
  have hDi : ∀ i k, Integrable (fun X => (s i k X - SharpLSI.FL.Gpart bF bΔ N X i k) ^ 2) ν := by
    intro i k
    refine Integrable.mono' (((hS.sL2 i k).add (hGi i k)).const_mul 2)
      (((hS.sM i k).sub (hGm i k)).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (s i k X + SharpLSI.FL.Gpart bF bΔ N X i k)]
  have hper : ∀ i, (∫ X, ∑ k : Fin d, (s i k X - SharpLSI.FL.Gpart bF bΔ N X i k) ^ 2 ∂ν) ≤
      2 * ∑ k, ∫ X, s i k X ^ 2 ∂ν +
        2 * ∫ X, ∑ k : Fin d, SharpLSI.FL.Gpart bF bΔ N X i k ^ 2 ∂ν := by
    intro i
    have hsi := integrable_finsetSum Finset.univ (fun k _ => hS.sL2 i k)
    have hgi := integrable_finsetSum Finset.univ (fun k _ => hGi i k)
    calc
      _ ≤ ∫ X, (2 * ∑ k : Fin d, s i k X ^ 2 +
          2 * ∑ k : Fin d, SharpLSI.FL.Gpart bF bΔ N X i k ^ 2) ∂ν := by
        refine integral_mono (integrable_finsetSum _ fun k _ => hDi i k)
          ((hsi.const_mul 2).add (hgi.const_mul 2)) fun X => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun k _ => by
          nlinarith [sq_nonneg (s i k X + SharpLSI.FL.Gpart bF bΔ N X i k)]
      _ = _ := by
        rw [integral_add (hsi.const_mul 2) (hgi.const_mul 2), integral_const_mul,
          integral_const_mul, integral_finsetSum _ fun k _ => hS.sL2 i k]
  calc
    _ ≤ ∑ i, (2 * ∑ k, ∫ X, s i k X ^ 2 ∂ν +
        2 * ∫ X, ∑ k : Fin d, SharpLSI.FL.Gpart bF bΔ N X i k ^ 2 ∂ν) :=
      Finset.sum_le_sum fun i _ => hper i
    _ = 2 * SharpLSI.FL.fisherS ν s +
        2 * ∑ i, ∫ X, ∑ k : Fin d, SharpLSI.FL.Gpart bF bΔ N X i k ^ 2 ∂ν := by
      simp only [SharpLSI.FL.fisherS, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hGi i k]

end DGPS.Lipschitz
