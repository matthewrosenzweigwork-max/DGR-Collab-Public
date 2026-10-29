import SharpSymmetricLSI.Paper.LocalStructure2

/-!
# Section 4.2: `ker(I + T)` is finite-dimensional (Phase 3, lane D; R14)

Kernel elements are continuous (`h = -Th`), so `ker(I+T)` is represented in `C(𝕋^d)`; its closed
unit ball (sup norm) is compact by Arzelà–Ascoli and (4.4), hence (Riesz) it is finite-dimensional.
An `L²(μ)`-orthogonal basis is normalised.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology BoundedContinuousFunction
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section lin
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
include hyp

theorem integrable_W_mul {f : Torus d → ℝ} (hf : Integrable f μ) (x : Torus d) :
    Integrable (fun y => W x y * f y) μ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  exact Integrable.mono' (hf.abs.const_mul BW)
    ((hyp.continuous_W.measurable.comp measurable_prodMk_left).aestronglyMeasurable.mul
      hf.aestronglyMeasurable) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_right (hBW (x, y)) (abs_nonneg _))

theorem integrable_aW {f : Torus d → ℝ} (hf : Integrable f μ) :
    Integrable (fun x => ∫ y, W x y * f y ∂μ) μ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  exact Integrable.mono' (integrable_const (BW * ∫ y, |f y| ∂μ)) (aW_aesm hyp μ hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact aW_bdd hyp μ (fun x y => hBW (x, y)) hf x)

theorem Top_lin {u v : Torus d → ℝ} (hu : Integrable u μ) (hv : Integrable v μ) (a b : ℝ)
    (x : Torus d) :
    Top W μ (fun y => a * u y + b * v y) x = a * Top W μ u x + b * Top W μ v x := by
  have e : ∀ x, ∫ y, W x y * (a * u y + b * v y) ∂μ =
      a * ∫ y, W x y * u y ∂μ + b * ∫ y, W x y * v y ∂μ := fun x => by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((integrable_W_mul hyp μ hu x).const_mul a) ((integrable_W_mul hyp μ hv x).const_mul b)]
    congr 1; funext y; ring
  unfold Top
  simp_rw [e]
  rw [integral_add ((integrable_aW hyp μ hu).const_mul a) ((integrable_aW hyp μ hv).const_mul b),
    integral_const_mul, integral_const_mul]
  ring

theorem Top_congr_ae {u v : Torus d → ℝ} (h : u =ᵐ[μ] v) (x : Torus d) :
    Top W μ u x = Top W μ v x := by
  have e : ∀ x, ∫ y, W x y * u y ∂μ = ∫ y, W x y * v y ∂μ := fun x =>
    integral_congr_ae (h.mono fun y hy => by simp only [hy])
  unfold Top; simp_rw [e]

theorem integral_Top {u : Torus d → ℝ} (hu : Integrable u μ) : ∫ x, Top W μ u x ∂μ = 0 := by
  unfold Top
  rw [integral_sub (integrable_aW hyp μ hu) (integrable_const _)]
  simp

end lin

/-- `ker(I + T)` inside the bounded continuous functions. -/
def kerSpace (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Submodule ℝ (Torus d →ᵇ ℝ) where
  carrier := {u | (∀ x, u x + Top W μ u x = 0) ∧ ∫ x, u x ∂μ = 0}
  add_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    have iu : Integrable (⇑u) μ := integrable_of_bdd u.continuous.measurable (C := ‖u‖)
      fun x => by rw [← Real.norm_eq_abs]; exact u.norm_coe_le_norm x
    have iv : Integrable (⇑v) μ := integrable_of_bdd v.continuous.measurable (C := ‖v‖)
      fun x => by rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm x
    refine ⟨fun x => ?_, ?_⟩
    · have := Top_lin hyp μ iu iv 1 1 x
      simp only [coe_add, Pi.add_apply]
      rw [show (⇑u + ⇑v : Torus d → ℝ) = fun y => 1 * u y + 1 * v y by
        funext y; simp only [Pi.add_apply, one_mul], this]
      linarith [hu1 x, hv1 x]
    · simp only [coe_add, Pi.add_apply]
      rw [integral_add iu iv, hu2, hv2, add_zero]
  zero_mem' := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [coe_zero]
      simp only [Pi.zero_apply, Top, mul_zero, integral_zero, sub_zero, add_zero]
    · rw [coe_zero]
      simp only [Pi.zero_apply, integral_zero]
  smul_mem' := by
    rintro c u ⟨hu1, hu2⟩
    have iu : Integrable (⇑u) μ := integrable_of_bdd u.continuous.measurable (C := ‖u‖)
      fun x => by rw [← Real.norm_eq_abs]; exact u.norm_coe_le_norm x
    refine ⟨fun x => ?_, ?_⟩
    · have := Top_lin hyp μ iu iu c 0 x
      simp only [coe_smul, smul_eq_mul]
      rw [show (fun x => c * u x) = fun y => c * u y + 0 * u y by funext y; ring, this]
      rw [zero_mul, add_zero, ← mul_add, hu1 x, mul_zero]
    · simp only [coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul, hu2, mul_zero]

end SharpLSI
