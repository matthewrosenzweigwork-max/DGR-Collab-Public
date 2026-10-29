import SharpSymmetricLSI.Paper.AppAFisher
import SharpSymmetricLSI.Infra.SmoothWeakGrad
import SharpSymmetricLSI.Defs.D06_Dissipation

/-!
# Appendix A, (A.1): heat-kernel Cauchy–Schwarz and monotonicity of the Fisher information

For `√ρ ∈ H¹`, `∇e^{tΔ}ρ = e^{tΔ}(2√ρ∇√ρ)`, and Cauchy–Schwarz for the probability kernel gives
`|∇e^{tΔ}ρ|² ≤ 4 e^{tΔ}ρ · e^{tΔ}|∇√ρ|²` pointwise. Since `e^{tΔ}ρ` is smooth and positive,
`I(e^{tΔ}ρ) = ∫ |∇e^{tΔ}ρ|² / e^{tΔ}ρ ≤ 4 ∫ e^{tΔ}|∇√ρ|² = 4 ∫ |∇√ρ|² = I(ρ)`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem appA_aestronglyMeasurable_grad {u : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad u g) (k : ι) :
    AEStronglyMeasurable (fun y => g y k) volume := by
  have := (h.locInt_grad k).aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_secT (ι := ι))
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp [Function.comp, liftT_secT]

omit [Fintype ι] [DecidableEq ι] in
/-- An elementary form of Cauchy–Schwarz. -/
theorem sq_le_of_forall_pos {X A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (h : ∀ l > 0, |X| ≤ l * A + B / l) : X ^ 2 ≤ 4 * A * B := by
  rcases eq_or_ne X 0 with hX | hX
  · rw [hX]
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hA.le) hB
    simpa using this
  · have hXp : 0 < |X| := abs_pos.2 hX
    have h1 := h (|X| / (2 * A)) (by positivity)
    have e : |X| / (2 * A) * A + B / (|X| / (2 * A)) = |X| / 2 + 2 * A * B / |X| := by
      field_simp
    rw [e] at h1
    have h2 : |X| ^ 2 ≤ 4 * A * B := by
      have : |X| / 2 ≤ 2 * A * B / |X| := by linarith
      rw [le_div_iff₀ hXp] at this
      nlinarith
    rwa [sq_abs] at h2

omit [DecidableEq ι] in
theorem integrable_heatP_mul_sub {t : ℝ} (ht : 0 < t) {h : UnitAddTorus ι → ℝ} (hh : Integrable h)
    (z : UnitAddTorus ι) : Integrable fun w => heatP t w * h (z - w) := by
  obtain ⟨M, hM⟩ := heatP_bdd (ι := ι) ht
  refine (hh.comp_sub_left z).bdd_mul (c := M) (measurable_heatP ht).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs]; exact hM w

omit [DecidableEq ι] in
/-- **Heat-kernel Cauchy–Schwarz.** -/
theorem heatT_sq_le {t : ℝ} (ht : 0 < t) {a b : UnitAddTorus ι → ℝ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) (z : UnitAddTorus ι) (hA : 0 < heatT t (fun y => a y ^ 2) z) :
    heatT t (fun y => 2 * a y * b y) z ^ 2 ≤
      4 * heatT t (fun y => a y ^ 2) z * heatT t (fun y => b y ^ 2) z := by
  have hab : Integrable fun y => 2 * a y * b y :=
    ((ha.integrable_mul hb).const_mul 2).congr (Eventually.of_forall fun y => by
      simp only [Pi.mul_apply]; ring)
  have ha2 : Integrable fun y => a y ^ 2 := ha.integrable_sq
  have hb2 : Integrable fun y => b y ^ 2 := hb.integrable_sq
  refine sq_le_of_forall_pos hA ?_ fun l hl => ?_
  · rw [heatT_eq ht hb2.aestronglyMeasurable]
    exact integral_nonneg fun w => mul_nonneg (heatP_pos ht w).le (sq_nonneg _)
  · rw [heatT_eq ht hab.aestronglyMeasurable, heatT_eq ht ha2.aestronglyMeasurable,
      heatT_eq ht hb2.aestronglyMeasurable, ← integral_const_mul, ← integral_div,
      ← integral_add ((integrable_heatP_mul_sub ht ha2 z).const_mul l)
        ((integrable_heatP_mul_sub ht hb2 z).div_const l)]
    refine (abs_integral_le_integral_abs).trans (integral_mono
      (integrable_heatP_mul_sub ht hab z).abs
      (((integrable_heatP_mul_sub ht ha2 z).const_mul l).add
        ((integrable_heatP_mul_sub ht hb2 z).div_const l)) fun w => ?_)
    have hP := (heatP_pos ht w).le
    have key : |2 * a (z - w) * b (z - w)| ≤ l * a (z - w) ^ 2 + b (z - w) ^ 2 / l := by
      rw [abs_le]
      constructor
      · have : 0 ≤ (l * a (z - w) + b (z - w)) ^ 2 / l := by positivity
        have e : (l * a (z - w) + b (z - w)) ^ 2 / l =
            l * a (z - w) ^ 2 + b (z - w) ^ 2 / l + 2 * a (z - w) * b (z - w) := by
          field_simp; ring
        linarith
      · have : 0 ≤ (l * a (z - w) - b (z - w)) ^ 2 / l := by positivity
        have e : (l * a (z - w) - b (z - w)) ^ 2 / l =
            l * a (z - w) ^ 2 + b (z - w) ^ 2 / l - 2 * a (z - w) * b (z - w) := by
          field_simp; ring
        linarith
    rw [abs_mul, abs_of_nonneg hP]
    calc heatP t w * |2 * a (z - w) * b (z - w)|
        ≤ heatP t w * (l * a (z - w) ^ 2 + b (z - w) ^ 2 / l) :=
          mul_le_mul_of_nonneg_left key hP
      _ = l * (heatP t w * a (z - w) ^ 2) + heatP t w * b (z - w) ^ 2 / l := by ring

end General

end SharpLSI
