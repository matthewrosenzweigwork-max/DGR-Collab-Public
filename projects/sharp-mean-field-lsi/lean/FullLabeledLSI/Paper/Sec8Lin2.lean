import FullLabeledLSI.Paper.Sec8Lin1
import FullLabeledLSI.Paper.Sec3Equil
import FullLabeledLSI.Statements.S07_Prop_3_1

/-!
# Section 8.3 (linearization), part 2: Lipschitz bookkeeping and the relative Fisher information

For a positive Lipschitz density `p` and bounded Lipschitz `ha`, `hb` with `1 + t ha, 1 + t hb ∈ [1/2, 3/2]`:
`I(p(1 + t ha) | p(1 + t hb)) = t² ∫ p J_t` with `J_t = (1 + t ha) ∑_k (∂_k ha/(1 + t ha) - ∂_k hb/(1 + t hb))²`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

theorem lip_data {u : Torus d → ℝ} (hu : ∃ L : ℝ≥0, LipschitzWith L u) :
    Continuous u ∧ IsWeakGrad u (lipGrad u) ∧ (∃ K : ℝ, ∀ x k, |lipGrad u x k| ≤ K) ∧
      ∀ k, Measurable fun x => lipGrad u x k := by
  obtain ⟨L, hL⟩ := hu
  have hc := hL.continuous
  exact ⟨hc, isWeakGrad_lipGrad hc (lipschitz_comp_liftT hL),
    ⟨L, fun x k => abs_lipGrad_le (lipschitz_comp_liftT hL) x k⟩, fun k => measurable_lipGrad hc k⟩

theorem lip_smul {u : Torus d → ℝ} (c : ℝ) (hu : ∃ L : ℝ≥0, LipschitzWith L u) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => c * u x) := by
  obtain ⟨L, hL⟩ := hu
  refine ⟨‖c‖₊ * L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have h1 := hL.dist_le_mul x y
  rw [Real.dist_eq] at h1 ⊢
  rw [← mul_sub, abs_mul]
  calc |c| * |u x - u y| ≤ |c| * (L * dist x y) := by gcongr
    _ = ↑(‖c‖₊ * L) * dist x y := by push_cast; rw [Real.norm_eq_abs]; ring

theorem lip_add {u v : Torus d → ℝ} (hu : ∃ L : ℝ≥0, LipschitzWith L u)
    (hv : ∃ L : ℝ≥0, LipschitzWith L v) : ∃ L : ℝ≥0, LipschitzWith L (fun x => u x + v x) := by
  obtain ⟨L, hL⟩ := hu
  obtain ⟨L', hL'⟩ := hv
  exact ⟨L + L', hL.add hL'⟩

theorem lip_const (c : ℝ) : ∃ L : ℝ≥0, LipschitzWith L (fun _ : Torus d => c) := ⟨0, LipschitzWith.const c⟩

theorem lip_mul {u v : Torus d → ℝ} (hu : ∃ L : ℝ≥0, LipschitzWith L u)
    (hv : ∃ L : ℝ≥0, LipschitzWith L v) {Bu Bv : ℝ} (hBu0 : 0 ≤ Bu) (hBv0 : 0 ≤ Bv)
    (hBu : ∀ x, |u x| ≤ Bu) (hBv : ∀ x, |v x| ≤ Bv) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => u x * v x) := by
  obtain ⟨Lu, hLu⟩ := hu
  obtain ⟨Lv, hLv⟩ := hv
  refine ⟨Lu * Real.toNNReal Bv + Lv * Real.toNNReal Bu, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have h1 := hLu.dist_le_mul x y
  have h2 := hLv.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have e : u x * v x - u y * v y = (u x - u y) * v x + u y * (v x - v y) := by ring
  rw [e]
  have hd0 : 0 ≤ dist x y := dist_nonneg
  push_cast [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ hBu0, Real.coe_toNNReal _ hBv0]
  calc |(u x - u y) * v x + u y * (v x - v y)|
      ≤ |(u x - u y) * v x| + |u y * (v x - v y)| := abs_add_le _ _
    _ = |u x - u y| * |v x| + |u y| * |v x - v y| := by rw [abs_mul, abs_mul]
    _ ≤ (Lu * dist x y) * Bv + Bu * (Lv * dist x y) := by
        gcongr
        · exact hBv x
        · exact hBu y
    _ = _ := by ring

theorem lip_sum {ι : Type*} (s : Finset ι) (f : ι → Torus d → ℝ)
    (hf : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (f i)) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact lip_add (hf a) ih

/-- The integrand of the relative Fisher information along the perturbation. -/
noncomputable def relJ (ga gb : Torus d → Fin d → ℝ) (ha hb : Torus d → ℝ) (t : ℝ)
    (x : Torus d) : ℝ :=
  (1 + t * ha x) * ∑ k, (ga x k / (1 + t * ha x) - gb x k / (1 + t * hb x)) ^ 2

theorem relFisher_alg {p A Bt gp gA gB t : ℝ} (hp : 0 < p) (hA : 0 < A) (hBt : 0 < Bt) :
    (2 * ((gp * A + p * (t * gA)) / (2 * Real.sqrt (p * A))) -
        Real.sqrt (p * A) * (if 0 < p * Bt then 2 * ((gp * Bt + p * (t * gB)) /
          (2 * Real.sqrt (p * Bt))) / Real.sqrt (p * Bt) else 0)) ^ 2 =
      t ^ 2 * (p * (A * (gA / A - gB / Bt) ^ 2)) := by
  rw [if_pos (mul_pos hp hBt)]
  have hu0 : 0 < Real.sqrt (p * A) := Real.sqrt_pos.2 (mul_pos hp hA)
  have hv0 : 0 < Real.sqrt (p * Bt) := Real.sqrt_pos.2 (mul_pos hp hBt)
  have hu2 : Real.sqrt (p * A) * Real.sqrt (p * A) = p * A := Real.mul_self_sqrt (mul_pos hp hA).le
  have hv2 : Real.sqrt (p * Bt) * Real.sqrt (p * Bt) = p * Bt :=
    Real.mul_self_sqrt (mul_pos hp hBt).le
  generalize Real.sqrt (p * A) = u at *
  generalize Real.sqrt (p * Bt) = v at *
  have hX : gp * A + p * (t * gA) = (p * A) * (gp / p + t * gA / A) := by field_simp
  have hY : gp * Bt + p * (t * gB) = (p * Bt) * (gp / p + t * gB / Bt) := by field_simp
  have key : 2 * ((gp * A + p * (t * gA)) / (2 * u)) -
      u * (2 * ((gp * Bt + p * (t * gB)) / (2 * v)) / v) = u * (t * (gA / A - gB / Bt)) := by
    have e1 : 2 * ((gp * A + p * (t * gA)) / (2 * u)) = u * (gp / p + t * gA / A) := by
      rw [hX, ← hu2]; field_simp
    have e2 : u * (2 * ((gp * Bt + p * (t * gB)) / (2 * v)) / v) = u * (gp / p + t * gB / Bt) := by
      rw [hY, ← hv2]; field_simp
    rw [e1, e2]; ring
  rw [key, mul_pow, show u ^ 2 = p * A by rw [sq]; exact hu2]
  ring

end Sec8
end SharpLSI.FL
