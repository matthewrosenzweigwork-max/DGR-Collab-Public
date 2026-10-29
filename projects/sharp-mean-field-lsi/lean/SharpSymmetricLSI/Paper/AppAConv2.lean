import SharpSymmetricLSI.Paper.AppAEnt5
import SharpSymmetricLSI.Paper.AppAConv1

/-!
# Convergence toolkit (2): `L²` convergence of the heat flow, by Fourier series

* `tendsto_L2_of_cf`: Fourier multipliers `c_ε(n) → 1` with `|c_ε(n) - 1| ≤ 1` converge in `L²`.
* `tendsto_heatT_L2`: `e^{εΔ}f → f` in `L²`.
* `tendsto_dpart_heatT_L2`: `∂ⱼe^{εΔ}f → gⱼ` in `L²` for `f ∈ H¹` with weak gradient `g`.
* `integral_dpart_heatT_sq_le`: `∫ (∂ⱼe^{εΔ}f)² ≤ ∫ gⱼ²`.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tendsto_L2_of_cf {β : Type*} {l : Filter β} {a : β → UnitAddTorus ι → ℝ}
    {h : UnitAddTorus ι → ℝ} (hh : MemLp h 2 volume) (ha : ∀ᶠ b in l, MemLp (a b) 2 volume)
    {c : β → (ι → ℤ) → ℝ} (hc : ∀ᶠ b in l, ∀ n, cf (a b) n = c b n * cf h n)
    (hc1 : ∀ᶠ b in l, ∀ n, |c b n - 1| ≤ 1) (hcl : ∀ n, Tendsto (fun b => c b n) l (𝓝 1)) :
    Tendsto (fun b => ∫ x, (a b x - h x) ^ 2) l (𝓝 0) := by
  have hs := (hasSum_sq_mFourierCoeff_real hh).summable
  have hlim : Tendsto (fun b => ∑' n, (c b n - 1) ^ 2 * ‖cf h n‖ ^ 2) l
      (𝓝 (∑' _n : ι → ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
    · have := ((hcl n).sub_const 1).pow 2 |>.mul_const (‖cf h n‖ ^ 2)
      simpa using this
    · filter_upwards [hc1] with b hb n
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : (c b n - 1) ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (c b n - 1), hb n]
      simp only [cf] at this ⊢
      nlinarith [sq_nonneg ‖mFourierCoeff (fun y => (h y : ℂ)) n‖]
  rw [tsum_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [ha, hc] with b hab hcb
  have hP := hasSum_sq_mFourierCoeff_real (u := fun x => a b x - h x) (hab.sub hh)
  rw [← hP.tsum_eq]
  congr 1; funext n
  have := cf_sub (hab.integrable one_le_two) (hh.integrable one_le_two) n
  simp only [cf] at this hcb ⊢
  rw [this, hcb n, ← sub_one_mul, norm_mul, mul_pow, show ((c b n : ℂ) - 1) = ((c b n - 1 : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem heatMult_le_one {t : ℝ} (ht : 0 ≤ t) (n : ι → ℤ) : heatMult t n ≤ 1 := by
  rw [heatMult_eq_exp, Real.exp_le_one_iff]
  have := lamN_nonneg n
  nlinarith

theorem abs_heatMult_sub_one_le {t : ℝ} (ht : 0 ≤ t) (n : ι → ℤ) : |heatMult t n - 1| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [heatMult_pos t n, heatMult_le_one ht n]

theorem tendsto_heatMult (n : ι → ℤ) : Tendsto (fun ε => heatMult ε n) (𝓝[>] 0) (𝓝 1) := by
  simp_rw [heatMult_eq_exp]
  have : Continuous fun ε : ℝ => Real.exp (-lamN n * ε) := by fun_prop
  have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using h

/-- **`e^{εΔ}f → f` in `L²`.** -/
theorem tendsto_heatT_L2 {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    Tendsto (fun ε => ∫ x, (heatT ε f x - f x) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hfi : Integrable f := appA_integrable_of_abs_le' hf hB
  refine tendsto_L2_of_cf (c := fun ε n => heatMult ε n) (memLp_of_abs_le hf hB 2) ?_ ?_ ?_
    tendsto_heatMult
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact memLp_of_continuous (continuous_heatT hε hfi) 2
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact fun n => cf_heatT hε hf hB n
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact fun n => abs_heatMult_sub_one_le hε.le n

theorem cf_dpart_heatT {ε : ℝ} (hε : 0 < ε) {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) {g : UnitAddTorus ι → ι → ℝ} (hg : IsWeakGrad f g)
    (hg2 : ∀ j, MemLp (fun y => g y j) 2 volume) (j : ι) (n : ι → ℤ) :
    cf (dpart_appA (heatT ε f) j) n = heatMult ε n * cf (fun y => g y j) n := by
  have hfi : Integrable f := appA_integrable_of_abs_le' hf hB
  rw [cf_dpart_appA (isSmoothT_heatT hε hfi) j n, cf_heatT hε hf hB n]
  have := mFourierCoeff_grad hg hfi (fun k => (hg2 k).integrable one_le_two) n j
  simp only [cf] at this ⊢
  rw [this]; ring

/-- **`∂ⱼe^{εΔ}f → gⱼ` in `L²`.** -/
theorem tendsto_dpart_heatT_L2 {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) {g : UnitAddTorus ι → ι → ℝ} (hg : IsWeakGrad f g)
    (hg2 : ∀ j, MemLp (fun y => g y j) 2 volume) (j : ι) :
    Tendsto (fun ε => ∫ x, (dpart_appA (heatT ε f) j x - g x j) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hfi : Integrable f := appA_integrable_of_abs_le' hf hB
  refine tendsto_L2_of_cf (h := fun y => g y j) (c := fun ε n => heatMult ε n) (hg2 j) ?_ ?_ ?_
    tendsto_heatMult
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact memLp_of_continuous (continuous_of_isSmoothT
      (isSmoothT_dpart (isSmoothT_heatT hε hfi) j)) 2
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact fun n => cf_dpart_heatT hε hf hB hg hg2 j n
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact fun n => abs_heatMult_sub_one_le hε.le n

/-- **`∫ (∂ⱼe^{εΔ}f)² ≤ ∫ gⱼ²`.** -/
theorem integral_dpart_heatT_sq_le {ε : ℝ} (hε : 0 < ε) {f : UnitAddTorus ι → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) {g : UnitAddTorus ι → ι → ℝ}
    (hg : IsWeakGrad f g) (hg2 : ∀ j, MemLp (fun y => g y j) 2 volume) (j : ι) :
    ∫ x, dpart_appA (heatT ε f) j x ^ 2 ≤ ∫ x, g x j ^ 2 := by
  have hfi : Integrable f := appA_integrable_of_abs_le' hf hB
  have h1 := hasSum_sq_mFourierCoeff_real (memLp_of_continuous (continuous_of_isSmoothT
      (isSmoothT_dpart (isSmoothT_heatT hε hfi) j)) 2)
  have h2 := hasSum_sq_mFourierCoeff_real (hg2 j)
  refine hasSum_le (fun n => ?_) h1 h2
  have := cf_dpart_heatT hε hf hB hg hg2 j n
  simp only [cf] at this
  rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (heatMult_pos ε n)]
  have h0 := heatMult_pos ε n
  have h1 := heatMult_le_one hε.le n
  have : heatMult ε n ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg ‖mFourierCoeff (fun y => ((g y j : ℝ) : ℂ)) n‖]

end SharpLSI
