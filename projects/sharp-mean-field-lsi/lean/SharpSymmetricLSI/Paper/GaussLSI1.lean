import SharpSymmetricLSI.Paper.GaussPoincare3

/-!
# (8.10), LSI half (lane s42): Gross' inequality on cylinder functions

`Ent_γ(φ²) λ_G ≤ 2 ℰ_∞(φ)` for cylinder functions `φ` (Paper/GaussForm19 `gross_gamma_block` and
the pointwise bound `quad_mul_lamG_le`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset InformationTheory
open scoped ENNReal ContDiff MatrixOrder

namespace SharpLSI

section cyl
variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C)
  {lam' : ℕ → ℝ}
include hγ

/-- `ent = ofReal ∘ entR` for bounded nonnegative continuous functions. -/
theorem ent_eq_ofReal_entR_of_bdd {u : (ℕ → ℝ) → ℝ} (hu : Continuous u) (hu0 : ∀ z, 0 ≤ u z)
    {B : ℝ} (huB : ∀ z, u z ≤ B) : ent γ u = ENNReal.ofReal (entR γ u) := by
  have := hγ.1
  have hB0 : 0 ≤ B := (hu0 0).trans (huB 0)
  have hi : Integrable u γ := Integrable.of_bound hu.aestronglyMeasurable B
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hu0 z)]; exact huB z)
  have hlog : Integrable (fun z => u z * Real.log (u z)) γ := by
    refine Integrable.of_bound ((Real.continuous_mul_log.comp hu).aestronglyMeasurable)
      (B ^ 2 + 1) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hu0 z
    have h2 := huB z
    rcases h1.eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [zero_mul]; constructor <;> nlinarith [sq_nonneg B]
    have hl := Real.one_sub_inv_le_log_of_pos hpos
    have hlu := Real.log_le_sub_one_of_pos hpos
    have e1 : u z * (1 - (u z)⁻¹) = u z - 1 := by field_simp
    constructor
    · have := mul_le_mul_of_nonneg_left hl h1
      nlinarith [e1]
    · have := mul_le_mul_of_nonneg_left hlu h1
      nlinarith
  rw [ent_eq_formula γ u hu0 hi hlog]
  rfl

variable (hS : ∀ N, (blockMat C N).PosSemidef)
  (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
include hS hnn

/-- **Gross' inequality on cylinder functions**: `Ent_γ(φ²) λ_G ≤ 2 ℰ_∞(φ)`. -/
theorem ent_mul_lamG_le_form (c : Cyl) :
    ent γ (fun z => c.eval z ^ 2) * lamG lam' C ≤ 2 * c.form lam' γ := by
  have := hγ.1
  set d : (ℕ → ℝ) → Fin c.J → ℝ := fun z k => fderiv ℝ c.φ (zBlock c.J z) (Pi.single k 1)
  have hdc : ∀ k : Fin c.J, Continuous fun x => fderiv ℝ c.φ x (Pi.single k 1) := fun k =>
    (c.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hzc : Continuous (zBlock c.J) := continuous_pi fun i => continuous_apply _
  set Qz : (ℕ → ℝ) → ℝ := fun z => ∑ k : Fin c.J, ∑ l : Fin c.J, C k l * d z k * d z l
  have hQc : Continuous Qz := continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (continuous_const.mul ((hdc k).comp hzc)).mul ((hdc l).comp hzc)
  have hQ0 : ∀ z, 0 ≤ Qz z := fun z => by
    have := hnn (range c.J) (extFin (d z))
    rwa [quad_range_extFin] at this
  have hQb : ∃ K, ∀ z, |Qz z| ≤ K := by
    have hb : ∀ k : Fin c.J, ∃ K, ∀ x, ‖fderiv ℝ c.φ x (Pi.single k 1)‖ ≤ K := fun k =>
      ((c.compact.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin c.J → ℝ) →L[ℝ] ℝ =>
        L (Pi.single k 1)) (by simp)).exists_bound_of_continuous (hdc k)
    choose K hK using hb
    refine ⟨∑ k : Fin c.J, ∑ l : Fin c.J, |C k l| * (|K k| * |K l|), fun z => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_))
    rw [abs_mul, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (abs_nonneg _) (abs_nonneg _))
      (abs_nonneg _)
    · rw [← Real.norm_eq_abs]; exact (hK k _).trans (le_abs_self _)
    · rw [← Real.norm_eq_abs]; exact (hK l _).trans (le_abs_self _)
  obtain ⟨K, hK⟩ := hQb
  have hQi : Integrable Qz γ := Integrable.of_bound hQc.aestronglyMeasurable K
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hK z)
  -- the entropy as `entR`
  obtain ⟨B, hB⟩ := c.compact.exists_bound_of_continuous c.smooth.continuous
  have hevc : Continuous fun z => c.eval z ^ 2 := (c.smooth.continuous.comp hzc).pow 2
  have hent : ent γ (fun z => c.eval z ^ 2) = ENNReal.ofReal (entR γ fun z => c.eval z ^ 2) :=
    ent_eq_ofReal_entR_of_bdd hγ hevc (fun z => sq_nonneg _) (B := B ^ 2) fun z => by
      have := hB (zBlock c.J z)
      rw [Real.norm_eq_abs] at this
      have h2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [sq_abs] at h2
      exact h2
  have hG := gross_gamma_block hγ (hS c.J) c.smooth c.compact
  have hint : ENNReal.ofReal (∫ z, Qz z ∂γ) * lamG lam' C ≤ c.form lam' γ := by
    calc ENNReal.ofReal (∫ z, Qz z ∂γ) * lamG lam' C
        = (∫⁻ z, ENNReal.ofReal (Qz z) ∂γ) * lamG lam' C := by
          rw [ofReal_integral_eq_lintegral_ofReal hQi (Eventually.of_forall hQ0)]
      _ = ∫⁻ z, ENNReal.ofReal (Qz z) * lamG lam' C ∂γ :=
          (lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hQc.measurable)).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (∑ i : Fin c.J, lam' i * (fderiv ℝ c.φ (fun j => z j)
            (Pi.single i 1)) ^ 2) ∂γ :=
          lintegral_mono fun z => quad_mul_lamG_le (C := C) (d z)
      _ = c.form lam' γ := rfl
  calc ent γ (fun z => c.eval z ^ 2) * lamG lam' C
      ≤ ENNReal.ofReal (2 * ∫ z, Qz z ∂γ) * lamG lam' C := by
        rw [hent]; gcongr; exact hG
    _ = 2 * (ENNReal.ofReal (∫ z, Qz z ∂γ) * lamG lam' C) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
    _ ≤ 2 * c.form lam' γ := by gcongr

end cyl

end SharpLSI
