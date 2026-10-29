import SharpSymmetricLSI.Paper.FormLiminf5
import SharpSymmetricLSI.Paper.TestEnergy8
import SharpSymmetricLSI.Paper.GroundT3

/-!
# R33 (8.20) groundwork: the multiplier `∂_iφ(Z_N) e^{-U_N}`

`h_i = ψ_i(Z_N) e^{-U_N}` with `ψ_i = ∂_iφ`, `φ` a cylinder: bounded, with the bounded weak gradient
`e^{-U_N}(∇ψ_i(Z_N) - ψ_i(Z_N)∇U_N)`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem exists_bound_fderiv_of {J : ℕ} {ψ : (Fin J → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    ∃ K, 0 ≤ K ∧ ∀ z (i : Fin J), |fderiv ℝ ψ z (Pi.single i 1)| ≤ K := by
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  obtain ⟨K, hK⟩ := hcont.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  refine ⟨max K 0, le_max_right _ _, fun z i => ?_⟩
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ ψ z).le_opNorm _).trans ?_
  have h1 : ‖(Pi.single i (1 : ℝ) : Fin J → ℝ)‖ ≤ 1 := by rw [Pi.norm_single, norm_one]
  calc ‖fderiv ℝ ψ z‖ * ‖(Pi.single i (1 : ℝ) : Fin J → ℝ)‖ ≤ max K 0 * 1 :=
        mul_le_mul ((hK z).trans (le_max_left _ _)) h1 (norm_nonneg _) (le_max_right _ _)
    _ = max K 0 := mul_one _

theorem exists_bound_of_compact {J : ℕ} {ψ : (Fin J → ℝ) → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) : ∃ K, 0 ≤ K ∧ ∀ z, |ψ z| ≤ K := by
  obtain ⟨K, hK⟩ := hψ.bounded_above_of_compact_support hc
  exact ⟨max K 0, le_max_right _ _, fun z => (hK z).trans (le_max_left _ _)⟩

/-- `∂_iφ` of a cylinder. -/
noncomputable def cylD (c : Cyl) (i : Fin c.J) (z : Fin c.J → ℝ) : ℝ :=
  fderiv ℝ c.φ z (Pi.single i 1)

theorem contDiff_cylD (c : Cyl) (i : Fin c.J) : ContDiff ℝ 1 (cylD c i) := by
  have h := c.smooth.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)
  exact h.clm_apply contDiff_const

theorem hasCompactSupport_cylD (c : Cyl) (i : Fin c.J) : HasCompactSupport (cylD c i) :=
  c.compact.fderiv_apply (𝕜 := ℝ) _

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) {N : ℕ} (hN : 1 ≤ N) (c : Cyl)
include hyp hμ hφ hN

/-- The gradient of `ψ(Z_N)` for a `C¹` compactly supported `ψ`. -/
noncomputable def gradZ (eC : ℕ → Torus d → ℝ) (N J : ℕ) (ψ : (Fin J → ℝ) → ℝ)
    (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  ∑ j : Fin J, fderiv ℝ ψ (zC eC N J (unflat y)) (Pi.single j 1) *
    ((N : ℝ) ^ (-(1 / 2 : ℝ)) * cgrad (eC (j + 1)) (projBlock p.1 y) p.2)

omit hyp hμ hN in
theorem measurable_zC_unflat (J : ℕ) :
    Measurable fun y : UnitAddTorus (Fin N × Fin d) => zC eC N J (unflat y) :=
  measurable_pi_iff.2 fun i => measurable_const.mul (Finset.measurable_sum _ fun l _ =>
    (measurable_of_contDiff (hφ _)).comp ((measurable_pi_apply l).comp measurable_unflat))

omit hyp hμ hN in
theorem gradZ_props {J : ℕ} {ψ : (Fin J → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∀ p, Measurable fun y => gradZ eC N J ψ y p) ∧ ∃ L, ∀ y p, |gradZ eC N J ψ y p| ≤ L := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_fderiv_of hψ hc
  have hcg : ∀ j : ℕ, ∃ C, ∀ y k, |cgrad (eC j) y k| ≤ C := fun j => exists_bound_cgrad (hφ j)
  choose Cg hCg using hcg
  have hderm : ∀ j : Fin J, Measurable fun z => fderiv ℝ ψ z (Pi.single j 1) := fun j =>
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable
  refine ⟨fun p => ?_, ∑ j : Fin J, K * (|(N : ℝ) ^ (-(1 / 2 : ℝ))| * |Cg (j + 1)|), fun y p => ?_⟩
  · unfold gradZ
    refine Finset.measurable_sum _ fun j _ => ((hderm j).comp (measurable_zC_unflat hφ J)).mul
      (measurable_const.mul ((measurable_cgrad (hφ _) p.2).comp (measurable_projBlock p.1)))
  · unfold gradZ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hK _ _) (mul_le_mul_of_nonneg_left ((hCg _ _ _).trans (le_abs_self _))
      (abs_nonneg _)) (by positivity) hK0

omit hyp hμ hN in
theorem isWeakGrad_gradZ {J : ℕ} {ψ : (Fin J → ℝ) → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    IsWeakGrad (fun y => ψ (zC eC N J (unflat y))) (gradZ eC N J ψ) :=
  isWeakGrad_compZ hφ N ψ hψ

end

end SharpLSI
