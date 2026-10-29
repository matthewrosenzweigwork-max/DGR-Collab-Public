import Mathlib

/-!
# Smooth truncated powers for the Moser iteration (Phase 3, lane D)

`q_δ(s) = s²/(1+δs²)`, `F(s) = s q_δ(s)^m`, `G(s) = s q_δ(s)^{2m}`. Both are smooth with bounded
derivatives, `s G(s) = F(s)²`, `F'² ≤ (1+2m) G'`, and `F_δ(s)² ↑ s^{2(2m+1)}` as `δ ↓ 0`.
-/

noncomputable section
open Filter Topology

namespace SharpLSI

/-- `q_δ(s) = s²/(1+δs²)`. -/
def qδ (δ s : ℝ) : ℝ := s ^ 2 / (1 + δ * s ^ 2)

/-- `F(s) = s q_δ(s)^m`. -/
def Fδ (δ : ℝ) (m : ℕ) (s : ℝ) : ℝ := s * qδ δ s ^ m

/-- `G(s) = s q_δ(s)^{2m}`. -/
def Gδ (δ : ℝ) (m : ℕ) (s : ℝ) : ℝ := s * qδ δ s ^ (2 * m)

variable {δ : ℝ} (hδ : 0 < δ)
include hδ

theorem den_pos (s : ℝ) : 0 < 1 + δ * s ^ 2 := by positivity

theorem qδ_nonneg (s : ℝ) : 0 ≤ qδ δ s := div_nonneg (sq_nonneg _) (den_pos hδ s).le

theorem qδ_le_inv (s : ℝ) : qδ δ s ≤ 1 / δ := by
  unfold qδ
  rw [div_le_div_iff₀ (den_pos hδ s) hδ]
  nlinarith [sq_nonneg s]

theorem s_sq_eq (s : ℝ) : s ^ 2 = qδ δ s * (1 + δ * s ^ 2) := by
  unfold qδ; field_simp [(den_pos hδ s).ne']

theorem hasDerivAt_qδ (s : ℝ) : HasDerivAt (qδ δ) (2 * s / (1 + δ * s ^ 2) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have h2 : HasDerivAt (fun s : ℝ => 1 + δ * s ^ 2) (δ * (2 * s)) s :=
    (h1.const_mul δ).const_add 1
  have := h1.div h2 (den_pos hδ s).ne'
  convert this using 1
  · funext s; simp [qδ]
  · field_simp
    ring

theorem hasDerivAt_pow_qδ (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s => s * qδ δ s ^ k)
      (qδ δ s ^ k * (1 + 2 * k / (1 + δ * s ^ 2))) s := by
  have hq := hasDerivAt_qδ hδ s
  refine ((hasDerivAt_id' s).mul (hq.pow k)).congr_deriv ?_
  rcases k with _ | k
  · simp
  · have hD := (den_pos hδ s).ne'
    have hs := s_sq_eq hδ s
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    have h1 : s * ((k + 1 : ℝ) * qδ δ s ^ k * (2 * s / (1 + δ * s ^ 2) ^ 2)) =
        2 * (k + 1) * qδ δ s ^ (k + 1) / (1 + δ * s ^ 2) := by
      calc s * ((k + 1 : ℝ) * qδ δ s ^ k * (2 * s / (1 + δ * s ^ 2) ^ 2))
          = 2 * (k + 1) * qδ δ s ^ k * s ^ 2 / (1 + δ * s ^ 2) ^ 2 := by ring
        _ = 2 * (k + 1) * qδ δ s ^ k * (qδ δ s * (1 + δ * s ^ 2)) / (1 + δ * s ^ 2) ^ 2 := by
            rw [← hs]
        _ = _ := by field_simp; ring
    rw [h1]
    ring

theorem contDiff_qδ : ContDiff ℝ ⊤ (qδ δ) := by
  unfold qδ
  exact (contDiff_id.pow 2).div (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
    fun s => (den_pos hδ s).ne'

theorem contDiff_Fδ (m : ℕ) : ContDiff ℝ 1 (Fδ δ m) := by
  unfold Fδ
  exact (contDiff_id.mul ((contDiff_qδ hδ).pow m)).of_le le_top

theorem contDiff_Gδ (m : ℕ) : ContDiff ℝ 1 (Gδ δ m) := by
  unfold Gδ
  exact (contDiff_id.mul ((contDiff_qδ hδ).pow (2 * m))).of_le le_top

theorem deriv_Fδ (m : ℕ) (s : ℝ) :
    deriv (Fδ δ m) s = qδ δ s ^ m * (1 + 2 * m / (1 + δ * s ^ 2)) :=
  (hasDerivAt_pow_qδ hδ m s).deriv

theorem deriv_Gδ (m : ℕ) (s : ℝ) :
    deriv (Gδ δ m) s = qδ δ s ^ (2 * m) * (1 + 2 * (2 * m : ℕ) / (1 + δ * s ^ 2)) :=
  (hasDerivAt_pow_qδ hδ (2 * m) s).deriv

theorem frac_le (k : ℕ) (s : ℝ) : 2 * (k : ℝ) / (1 + δ * s ^ 2) ≤ 2 * k := by
  rw [div_le_iff₀ (den_pos hδ s)]
  have : (0 : ℝ) ≤ 2 * k * (δ * s ^ 2) := by positivity
  nlinarith

theorem frac_nonneg (k : ℕ) (s : ℝ) : 0 ≤ 2 * (k : ℝ) / (1 + δ * s ^ 2) :=
  div_nonneg (by positivity) (den_pos hδ s).le

theorem abs_deriv_Fδ_le (m : ℕ) (s : ℝ) : |deriv (Fδ δ m) s| ≤ (1 / δ) ^ m * (1 + 2 * m) := by
  rw [deriv_Fδ hδ, abs_of_nonneg (mul_nonneg (pow_nonneg (qδ_nonneg hδ s) _)
    (by linarith [frac_nonneg hδ m s]))]
  exact mul_le_mul (pow_le_pow_left₀ (qδ_nonneg hδ s) (qδ_le_inv hδ s) _)
    (by linarith [frac_le hδ m s]) (by linarith [frac_nonneg hδ m s]) (by positivity)

theorem abs_deriv_Gδ_le (m : ℕ) (s : ℝ) :
    |deriv (Gδ δ m) s| ≤ (1 / δ) ^ (2 * m) * (1 + 2 * (2 * m : ℕ)) := by
  rw [deriv_Gδ hδ, abs_of_nonneg (mul_nonneg (pow_nonneg (qδ_nonneg hδ s) _)
    (by linarith [frac_nonneg hδ (2 * m) s]))]
  exact mul_le_mul (pow_le_pow_left₀ (qδ_nonneg hδ s) (qδ_le_inv hδ s) _)
    (by linarith [frac_le hδ (2 * m) s]) (by linarith [frac_nonneg hδ (2 * m) s]) (by positivity)

theorem deriv_Fδ_sq_le (m : ℕ) (s : ℝ) :
    deriv (Fδ δ m) s ^ 2 ≤ (1 + 2 * m) * deriv (Gδ δ m) s := by
  rw [deriv_Fδ hδ, deriv_Gδ hδ]
  set x := 2 * (m : ℝ) / (1 + δ * s ^ 2)
  have hx0 : 0 ≤ x := frac_nonneg hδ m s
  have hx : x ≤ 2 * m := frac_le hδ m s
  have h2 : 2 * ((2 * m : ℕ) : ℝ) / (1 + δ * s ^ 2) = 2 * x := by
    simp only [x]; push_cast; ring
  rw [h2, mul_pow, ← pow_mul, mul_comm m 2]
  have hq : 0 ≤ qδ δ s ^ (2 * m) := pow_nonneg (qδ_nonneg hδ s) _
  have : (1 + x) ^ 2 ≤ (1 + 2 * m) * (1 + 2 * x) := by nlinarith
  nlinarith

omit hδ in
theorem mul_Gδ (m : ℕ) (s : ℝ) : s * Gδ δ m s = Fδ δ m s ^ 2 := by
  unfold Gδ Fδ; ring

theorem Fδ_sq_le (m : ℕ) (s : ℝ) : Fδ δ m s ^ 2 ≤ (s ^ 2) ^ (2 * m + 1) := by
  unfold Fδ
  have hq : qδ δ s ≤ s ^ 2 := by
    unfold qδ
    rw [div_le_iff₀ (den_pos hδ s)]
    nlinarith [sq_nonneg s, mul_nonneg hδ.le (sq_nonneg s)]
  calc (s * qδ δ s ^ m) ^ 2 = s ^ 2 * qδ δ s ^ (2 * m) := by ring
    _ ≤ s ^ 2 * (s ^ 2) ^ (2 * m) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (qδ_nonneg hδ s) hq _) (sq_nonneg _)
    _ = (s ^ 2) ^ (2 * m + 1) := by ring

omit hδ in
theorem tendsto_Fδ_sq (m : ℕ) (s : ℝ) :
    Tendsto (fun n : ℕ => Fδ (1 / (n + 1)) m s ^ 2) atTop (𝓝 ((s ^ 2) ^ (2 * m + 1))) := by
  have hq : Tendsto (fun n : ℕ => qδ (1 / (n + 1)) s) atTop (𝓝 (s ^ 2)) := by
    unfold qδ
    have : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => s ^ 2 / (1 + 1 / ((n : ℝ) + 1) * s ^ 2)) atTop
        (𝓝 (s ^ 2 / (1 + 0 * s ^ 2))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add (this.mul tendsto_const_nhds)) (by norm_num)
    simpa using h2
  have := (tendsto_const_nhds (x := s)).mul (hq.pow m)
  have h3 := this.pow 2
  unfold Fδ
  convert h3 using 2
  ring

omit hδ in
theorem monotone_Fδ_sq (m : ℕ) (s : ℝ) : Monotone fun n : ℕ => Fδ (1 / (n + 1)) m s ^ 2 := by
  intro a b hab
  dsimp only
  unfold Fδ
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (qδ_nonneg (by positivity) s) ?_ _)
    (sq_nonneg _)
  unfold qδ
  refine div_le_div_of_nonneg_left (sq_nonneg _) (den_pos (by positivity) s) ?_
  have : (1 : ℝ) / (b + 1) ≤ 1 / (a + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  nlinarith [sq_nonneg s]

end SharpLSI
