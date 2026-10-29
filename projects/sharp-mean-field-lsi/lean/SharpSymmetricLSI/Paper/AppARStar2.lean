import SharpSymmetricLSI.Paper.AppARStar1
import SharpSymmetricLSI.Paper.UpperBound

/-!
# Appendix A.1, heat approximation along a sequence `s_n ↓ 0`

Throughout, `ρ` is a probability density with `√ρ ∈ H¹`, `g = ∇√ρ`, `s_n > 0`, and along the
sequence `e^{s_nΔ}ρ → ρ` in `L¹` and a.e., `e^{s_nΔ}(2√ρ gₖ) → 2√ρ gₖ` a.e. and
`e^{s_nΔ}|g|² → |g|²` a.e. Then `∇√ρ_n → g` a.e. and in `L²` (the pointwise bound of (A.1) and
`∇√ρ = 0` a.e. on `{ρ = 0}`), `D(ρ_n) → D(ρ)` and `G(ρ_n) → G(ρ)`.
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem sqrt_sub_sqrt_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have h1 : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have h2 : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    ring_nf; rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
  calc (Real.sqrt a - Real.sqrt b) ^ 2
      = |Real.sqrt a - Real.sqrt b| * |Real.sqrt a - Real.sqrt b| := by
        rw [abs_mul_abs_self, sq]
    _ ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |a - b| := by
        rw [← h2, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a + Real.sqrt b)]

theorem sum_enorm_sq_eq (a : Fin d → ℝ) : ∑ k, ‖a k‖ₑ ^ 2 = ENNReal.ofReal (sqNorm a) := by
  unfold sqNorm
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
  exact Finset.sum_congr rfl fun k _ => (ofReal_sq_eq_enorm_sq _).symm

namespace H1Dens

variable {ρ : Torus d → ℝ} (h : H1Dens ρ)
include h

theorem continuous_sqrtHeatGrad {t : ℝ} (ht : 0 < t) (k : Fin d) :
    Continuous fun x => sqrtHeatGrad t ρ x k := by
  unfold sqrtHeatGrad
  refine (continuous_heatT ht (h.integrable_flux k)).div
    (continuous_const.mul (continuous_heatT ht h.integrable).sqrt) fun x => ?_
  have := h.heatT_pos ht x
  positivity

theorem integral_heatT_eq {t : ℝ} (ht : 0 < t) : ∫ x, heatT t ρ x ∂haar d = 1 := by
  rw [integral_heatT ht h.integrable]; exact h.one

theorem heatT_h1Dens {t : ℝ} (ht : 0 < t) : H1Dens (heatT t ρ) :=
  ⟨fun x => (h.heatT_pos ht x).le, h.integral_heatT_eq ht, h.memH1_sqrt_heatT ht⟩

/-- The gradients converge a.e. -/
theorem ae_tendsto_sqrtHeatGrad {s : ℕ → ℝ} (hs0 : ∀ n, 0 < s n)
    (hρae : ∀ᵐ x ∂haar d, Tendsto (fun n => heatT (s n) ρ x) atTop (𝓝 (ρ x)))
    (hfae : ∀ᵐ x ∂haar d, ∀ k, Tendsto (fun n => heatT (s n) (fun y => 2 * Real.sqrt (ρ y) *
      weakGrad (fun z => Real.sqrt (ρ z)) y k) x) atTop
        (𝓝 (2 * Real.sqrt (ρ x) * weakGrad (fun z => Real.sqrt (ρ z)) x k)))
    (hqae : ∀ᵐ x ∂haar d, Tendsto (fun n => heatT (s n) (fun y =>
      sqNorm (weakGrad (fun z => Real.sqrt (ρ z)) y)) x) atTop
        (𝓝 (sqNorm (weakGrad (fun z => Real.sqrt (ρ z)) x)))) :
    ∀ᵐ x ∂haar d, ∀ k, Tendsto (fun n => sqrtHeatGrad (s n) ρ x k) atTop
      (𝓝 (weakGrad (fun z => Real.sqrt (ρ z)) x k)) := by
  set g := weakGrad fun z => Real.sqrt (ρ z)
  have hgz := ae_grad_eq_zero_of_eq_zero h.isWeakGrad (h.h1.2.1.integrable one_le_two)
    fun k => (h.memLp_grad k).integrable one_le_two
  filter_upwards [hρae, hfae, hqae, hgz] with x hρx hfx hqx hzx k
  rcases (h.nonneg x).eq_or_lt with h0 | hpos
  · -- on `{ρ = 0}`
    have hs0' : Real.sqrt (ρ x) = 0 := by rw [← h0, Real.sqrt_zero]
    have hg0 := hzx hs0'
    have hq0 : sqNorm (g x) = 0 := by unfold sqNorm; simp [g, hg0]
    rw [show g x k = 0 from hg0 k]
    have hb : ∀ n, |sqrtHeatGrad (s n) ρ x k| ≤
        Real.sqrt (heatT (s n) (fun y => sqNorm (g y)) x) := fun n => by
      refine Real.abs_le_sqrt ?_
      refine le_trans ?_ (h.sqNorm_sqrtHeatGrad_le (hs0 n) x)
      unfold sqNorm
      exact Finset.single_le_sum (f := fun j => sqrtHeatGrad (s n) ρ x j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ k)
    have hz : Tendsto (fun n => Real.sqrt (heatT (s n) (fun y => sqNorm (g y)) x)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto _).comp hqx
      rwa [hq0, Real.sqrt_zero] at this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hb n) hz
  · -- on `{ρ > 0}`
    have hden : Tendsto (fun n => 2 * Real.sqrt (heatT (s n) ρ x)) atTop
        (𝓝 (2 * Real.sqrt (ρ x))) :=
      ((Real.continuous_sqrt.tendsto _).comp hρx).const_mul 2
    have hsp : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 hpos
    have := (hfx k).div hden (by positivity)
    have e : 2 * Real.sqrt (ρ x) * g x k / (2 * Real.sqrt (ρ x)) = g x k := by
      field_simp
    rw [e] at this
    exact this

/-- `∫ |∇√ρ_t|² ≤ ∫ |∇√ρ|²`. -/
theorem lintegral_sqNorm_sqrtHeatGrad_le {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, ∑ k, ‖sqrtHeatGrad t ρ x k‖ₑ ^ 2 ∂haar d ≤
      ∫⁻ x, ∑ k, ‖weakGrad (fun z => Real.sqrt (ρ z)) x k‖ₑ ^ 2 ∂haar d := by
  set q := fun y => sqNorm (weakGrad (fun z => Real.sqrt (ρ z)) y)
  have hq0 : ∀ y, 0 ≤ q y := fun y => by unfold q sqNorm; positivity
  simp_rw [sum_enorm_sq_eq]
  calc ∫⁻ x, ENNReal.ofReal (sqNorm fun k => sqrtHeatGrad t ρ x k) ∂haar d
      ≤ ∫⁻ x, ENNReal.ofReal (heatT t q x) ∂haar d :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (h.sqNorm_sqrtHeatGrad_le ht x)
    _ = ENNReal.ofReal (∫ x, heatT t q x) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_heatT ht h.integrable_sqNorm)
          (Eventually.of_forall fun x =>
            heatT_nonneg ht hq0 h.integrable_sqNorm.aestronglyMeasurable x)).symm
    _ = ENNReal.ofReal (∫ x, q x) := by rw [integral_heatT ht h.integrable_sqNorm]
    _ = ∫⁻ x, ENNReal.ofReal (q x) ∂haar d :=
        ofReal_integral_eq_lintegral_ofReal h.integrable_sqNorm (Eventually.of_forall hq0)

theorem lintegral_sqNorm_ne_top :
    ∫⁻ x, ∑ k, ‖weakGrad (fun z => Real.sqrt (ρ z)) x k‖ₑ ^ 2 ∂haar d ≠ ⊤ := by
  simp_rw [sum_enorm_sq_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal h.integrable_sqNorm
    (Eventually.of_forall fun y => by unfold sqNorm; positivity)]
  exact ENNReal.ofReal_ne_top

/-- The gradients converge in `L²`. -/
theorem L2Tendsto_sqrtHeatGrad {s : ℕ → ℝ} (hs0 : ∀ n, 0 < s n)
    (hae : ∀ᵐ x ∂haar d, ∀ k, Tendsto (fun n => sqrtHeatGrad (s n) ρ x k) atTop
      (𝓝 (weakGrad (fun z => Real.sqrt (ρ z)) x k))) (k : Fin d) :
    L2Tendsto (haar d) (fun n x => sqrtHeatGrad (s n) ρ x k)
      (fun x => weakGrad (fun z => Real.sqrt (ρ z)) x k) := by
  have hv := tendsto_L2_of_ae_vec (μ := haar d)
    (f := fun n x k => sqrtHeatGrad (s n) ρ x k)
    (fun n k => (h.continuous_sqrtHeatGrad (hs0 n) k).measurable.aemeasurable)
    (fun k => (h.isWeakGrad.aestronglyMeasurable_grad k).aemeasurable) hae
    (fun n => h.lintegral_sqNorm_sqrtHeatGrad_le (hs0 n)) h.lintegral_sqNorm_ne_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv (fun _ => zero_le)
    fun n => lintegral_mono fun x => ?_
  exact Finset.single_le_sum
    (f := fun j => ‖sqrtHeatGrad (s n) ρ x j - weakGrad (fun z => Real.sqrt (ρ z)) x j‖ₑ ^ 2)
    (fun _ _ => zero_le) (Finset.mem_univ k)

/-- `√ρ_n → √ρ` in `L²`. -/
theorem L2Tendsto_sqrt_heatT {s : ℕ → ℝ} (hs0 : ∀ n, 0 < s n)
    (hL1 : Tendsto (fun n => ∫⁻ x, ‖heatT (s n) ρ x - ρ x‖ₑ ∂haar d) atTop (𝓝 0)) :
    L2Tendsto (haar d) (fun n x => Real.sqrt (heatT (s n) ρ x)) (fun x => Real.sqrt (ρ x)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun _ => zero_le)
    fun n => lintegral_mono fun x => ?_
  rw [← ofReal_sq_eq_enorm_sq, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (sqrt_sub_sqrt_sq_le (h.heatT_pos (hs0 n) x).le (h.nonneg x))

end H1Dens

end SharpLSI
