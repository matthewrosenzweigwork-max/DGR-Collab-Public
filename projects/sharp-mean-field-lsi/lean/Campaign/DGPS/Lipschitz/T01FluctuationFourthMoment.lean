import DGPS.Lipschitz.T01GroundStateSchrodinger
import DGPS.Lipschitz.T01SymmetricLower
import DGPS.Lipschitz.DualGenerator
import SharpSymmetricLSI.Paper.TestEnergy6

/-! Fourth moments of positive spectral fluctuations under the actual particle law. -/

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology
open SharpLSI SharpLSI.FL
open scoped ENNReal

variable {d : ℕ}

/-- The native cylinder coordinate is the same positive-mode empirical fluctuation. -/
theorem t01_dualZ_eq_fluct (eC : ℕ → Torus d → ℝ) (N : ℕ+) {n : ℕ}
    (i : Fin n) (X : ParticleSpace d N) :
    dualZ N (fun k : Fin n => eC (k.val + 1)) X i = SharpLSI.fluct eC N i.val X := by
  unfold dualZ SharpLSI.fluct
  rw [Real.rpow_neg (Nat.cast_nonneg (N : ℕ)), ← Real.sqrt_eq_rpow]

/-- Each fixed-particle fluctuation belongs to L4 under the actual law. -/
theorem t01_particleLaw_fluct_memLp_four (A : InteractionData d)
    {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ SharpLSI.liftT))
    (N : ℕ+) (n : ℕ) : MemLp (fun X => SharpLSI.fluct eC N n X) 4 (particleLaw A N) := by
  obtain ⟨⟨B, hB⟩, hm⟩ := BM_fluct hφ N n
  exact MemLp.of_bound hm.aestronglyMeasurable B (Eventually.of_forall fun X => by
    rw [Real.norm_eq_abs]
    exact hB X)

private theorem fourth_rpow_le_even {q : ℝ} (hq : 0 ≤ q) (k : ℕ)
    (hk : 4 * q ≤ ((2 * k : ℕ) : ℝ)) (z : ℝ) :
    (z ^ 4) ^ q ≤ 1 + z ^ (2 * k) := by
  have h4 : |z| ^ 4 = z ^ 4 := Even.pow_abs (by decide : Even (4 : ℕ)) z
  have heq : (z ^ 4) ^ q = |z| ^ ((4 : ℝ) * q) := by
    rw [← h4, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg z)]
    norm_num
  rw [heq]
  by_cases hz : |z| ≤ 1
  · exact (Real.rpow_le_one (abs_nonneg z) hz (by positivity)).trans
      (le_add_of_nonneg_right (Even.pow_nonneg ⟨k, by omega⟩ z))
  · have h := Real.rpow_le_rpow_of_exponent_le (lt_of_not_ge hz).le hk
    rw [Real.rpow_natCast, pow_abs_two_mul] at h
    linarith

/-- Uniform density moments and reference even moments give actual Gibbs fourth moments. -/
theorem t01_particleLaw_fluct_fourth_moment (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hac : (μ : Measure (Torus d)) ≪ haar d)
    {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : SharpLSI.IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ SharpLSI.liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j)
    {p Bp : ℝ} (hp : 1 < p) (hBp : 0 ≤ Bp)
    (hρ : ∀ N : ℕ+, ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ+,
      Integrable (fun X => SharpLSI.fluct eC N n X ^ 4) (particleLaw A N) ∧
      ∫ X, SharpLSI.fluct eC N n X ^ 4 ∂particleLaw A N ≤ K := by
  let q := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  obtain ⟨k, hk⟩ := exists_nat_ge (2 * q)
  have hk' : 4 * q ≤ ((2 * k : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨C, hC, hCm⟩ := GroundState.fluct_moment_eC hac he hφ heC n k
  refine ⟨Bp ^ (1 / p) * (1 + C) ^ (1 / q), by positivity, fun N => ?_⟩
  let Z : SharpLSI.Config N d → ℝ := fun X => SharpLSI.fluct eC N n X
  obtain ⟨⟨Bz, hBz⟩, hZm⟩ := BM_fluct hφ N n
  have hYbound : ∀ X, ‖Z X ^ 4‖ ≤ Bz ^ 4 := by
    intro X
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hBz X) 4
  have hYmem : ∀ r, MemLp (fun X => Z X ^ 4) r
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := fun r =>
    MemLp.of_bound (hZm.pow_const 4).aestronglyMeasurable (Bz ^ 4)
      (Eventually.of_forall hYbound)
  have hYint : Integrable (fun X => Z X ^ 4) (particleLaw A N) :=
    Integrable.of_bound (hZm.pow_const 4).aestronglyMeasurable (Bz ^ 4)
      (Eventually.of_forall hYbound)
  refine ⟨hYint, ?_⟩
  obtain ⟨Kρ, hKρ⟩ := isCompact_univ.exists_bound_of_continuousOn
    (centeredParticleDensity_continuous A μ N).continuousOn
  have hwbound : ∀ X, ‖centeredParticleDensity A μ N X‖ ≤ Kρ := fun X =>
    hKρ X (Set.mem_univ X)
  have hwmem : ∀ r, MemLp (centeredParticleDensity A μ N) r
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := fun r =>
    MemLp.of_bound (centeredParticleDensity_continuous A μ N).aestronglyMeasurable Kρ
      (Eventually.of_forall hwbound)
  have hhigh : Integrable (fun X => Z X ^ (2 * k))
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) :=
    Integrable.of_bound (hZm.pow_const (2 * k)).aestronglyMeasurable (Bz ^ (2 * k))
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hBz X) (2 * k))
  have hqmom : ∫ X, (Z X ^ 4) ^ q
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ 1 + C := by
    calc
      _ ≤ ∫ X, (1 + Z X ^ (2 * k))
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun X => Real.rpow_nonneg (by positivity) _)
          ((integrable_const 1).add hhigh)
          (Eventually.of_forall fun X => fourth_rpow_le_even hq0.le k hk' (Z X))
      _ = 1 + ∫ X, Z X ^ (2 * k)
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
        rw [integral_add (integrable_const 1) hhigh]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ ≤ 1 + C := by
        gcongr
        simpa only [Z, SharpLSI.FL.QN] using hCm N N.pos
  rw [integral_particleLaw_eq_centered A μ hfix N]
  have hY0 : ∀ X, 0 ≤ Z X ^ 4 := fun X => by positivity
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun X => (centeredParticleDensity_pos A μ N X).le)
    (Eventually.of_forall hY0)
    (hwmem _) (hYmem _)
  refine hholder.trans ?_
  have hw0 : 0 ≤ ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) :=
    integral_nonneg fun X => Real.rpow_nonneg (centeredParticleDensity_pos A μ N X).le _
  have hy0 : 0 ≤ ∫ X, (Z X ^ 4) ^ q
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) :=
    integral_nonneg fun X => Real.rpow_nonneg (hY0 X) _
  have hw := Real.rpow_le_rpow hw0 (hρ N) (one_div_nonneg.mpr hp0.le)
  have hy := Real.rpow_le_rpow hy0 hqmom (one_div_nonneg.mpr hq0.le)
  exact mul_le_mul hw hy (Real.rpow_nonneg hy0 _) (Real.rpow_nonneg hBp _)

end DGPS.Lipschitz
