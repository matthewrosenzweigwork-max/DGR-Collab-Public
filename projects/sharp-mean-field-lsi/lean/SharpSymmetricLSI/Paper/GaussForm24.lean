import SharpSymmetricLSI.Paper.GaussForm23

/-!
# R32 (F5): the simultaneous diagonalization of `Λ` and `C`, and `λ_G = ν_0`

`exists_genEigen_matrix`: with `v_j = √ν_j Λ⁻¹ u_j` (`u_j` the generalized eigenbasis of
`Paper/GaussForm22.lean`): `v_j, Λv_j ∈ ℓ²`, `⟨v_i, C v_j⟩ = δ_{ij}`, `⟨v_i, Λ v_j⟩ = ν_i δ_{ij}`,
`0 < ν_0 ≤ ν_1 ≤ … → ∞`, and `ofReal ν_0 = λ_G` (`lamG`, (8.9)); the lower bound
`ν_0 ⟨x, Cx⟩ ≤ ⟨x, Λx⟩` comes from `rayleigh_ge` and `2⟨x,w⟩ ≤ ⟨x,Λx⟩/ν_0 + ν_0⟨w,Λ⁻¹w⟩`
with `w = Cx`.
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace SharpLSI

section gen
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {lam' : ℕ → ℝ} (hpos : ∀ i, 0 < lam' i)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (hCs : ∀ a b, C a b = C b a)
include hT hS hσ0 hσ hpos hC hCs

/-- **Simultaneous diagonalization of `Λ` and `C`; `λ_G = ν_0`.** -/
theorem exists_genEigen_matrix (htop : Tendsto lam' atTop atTop) :
    ∃ (v : ℕ → ℕ → ℝ) (ν : ℕ → ℝ),
      (∀ j, Summable (fun i => v j i ^ 2) ∧ Summable (fun i => (lam' i * v j i) ^ 2)) ∧
      (∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0) ∧
      (∀ i j, ∑' a, lam' a * v i a * v j a = if i = j then ν i else 0) ∧
      0 < ν 0 ∧ Monotone ν ∧ Tendsto ν atTop atTop ∧
      ENNReal.ofReal (ν 0) = lamG lam' C ∧
      ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i) := by
  obtain ⟨D, hD⟩ := exists_bound_inv_sqrt hpos htop
  obtain ⟨u, ν, hνpos, hmono, htopν, horth, hcomp, heq, hev, hexp⟩ :=
    exists_genEigen_nat hT hS hσ0 hσ hpos hD htop
  have hinvD : ∀ a, (lam' a)⁻¹ ≤ D ^ 2 := fun a => by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hD a) 2
    rwa [sq_abs, inv_pow, Real.sq_sqrt (hpos a).le] at h
  have hsq : ∀ j, √(ν j) * √(ν j) = ν j := fun j => Real.mul_self_sqrt (hνpos j).le
  have hsq0 : ∀ j, √(ν j) ≠ 0 := fun j => (Real.sqrt_pos.2 (hνpos j)).ne'
  set y : ℕ → L2N := fun j => (√(ν j))⁻¹ • u j with hydef
  set v : ℕ → ℕ → ℝ := fun j a => √(ν j) * u j a / lam' a with hvdef
  have hkey : ∀ j, v j = ⇑(y j + hsOp hS (y j)) := fun j => by
    have e : y j + hsOp hS (y j) = (√(ν j))⁻¹ • (u j + hsOp hS (u j)) := by
      simp only [hydef, map_smul, smul_add]
    funext a
    rw [e, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, Pi.add_apply, hsOp_apply,
      hev j a]
    show √(ν j) * u j a / lam' a = _
    have h' : (√(ν j))⁻¹ * ν j = √(ν j) := by
      nth_rw 2 [← hsq j]
      rw [← mul_assoc, inv_mul_cancel₀ (hsq0 j), one_mul]
    nth_rw 1 [← h']
    ring
  have hCv : ∀ j a, ∑' b, C a b * v j b = y j a := fun j a => by
    rw [hkey, tsum_C_mul hT hS hσ0 hσ hC hCs, ipT_symm_of_add hT hS hσ0 hσ]
  have hJ : ∀ i j, ∑' a, u i a * u j a / lam' a = if i = j then 1 else 0 := fun i j => by
    rw [← inner_diagOp_eq hpos hD, horth]
  -- `⟨v_i, C v_j⟩ = δ_{ij}`
  have hvC : ∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0 := by
    intro i j
    simp_rw [hCv]
    have : ∀ a, v i a * y j a = (√(ν i) * (√(ν j))⁻¹) * (u i a * u j a / lam' a) := fun a => by
      simp only [hvdef, hydef, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [this]
    rw [tsum_mul_left, hJ]
    split_ifs with h
    · subst h; rw [mul_inv_cancel₀ (hsq0 i), mul_one]
    · rw [mul_zero]
  -- `⟨v_i, Λ v_j⟩ = ν_i δ_{ij}`
  have hvΛ : ∀ i j, ∑' a, lam' a * v i a * v j a = if i = j then ν i else 0 := by
    intro i j
    have : ∀ a, lam' a * v i a * v j a = (√(ν i) * √(ν j)) * (u i a * u j a / lam' a) :=
      fun a => by simp only [hvdef]; field_simp [(hpos a).ne']
    simp_rw [this]
    rw [tsum_mul_left, hJ]
    split_ifs with h
    · subst h; rw [mul_one, hsq]
    · rw [mul_zero]
  have hsumv : ∀ j, Summable fun i => v j i ^ 2 := fun j => by
    rw [hkey]; exact summable_sq_L2N _
  have hsumΛ : ∀ j, Summable fun i => (lam' i * v j i) ^ 2 := fun j => by
    have : ∀ i, (lam' i * v j i) ^ 2 = ν j * u j i ^ 2 := fun i => by
      simp only [hvdef]; field_simp [(hpos i).ne']; rw [Real.sq_sqrt (hνpos j).le]; ring
    simp_rw [this]; exact (summable_sq_L2N _).mul_left _
  refine ⟨v, ν, fun j => ⟨hsumv j, hsumΛ j⟩, hvC, hvΛ, hνpos 0, hmono, htopν, ?_, ?_⟩
  swap
  · -- `C_{ii} = ∑_j (C v_j)_i²`
    intro i
    set h : L2N := lp.single 2 i (√(lam' i))
    have hJh : diagOp hD h = lp.single 2 i 1 := by
      rw [diagOp_single, inv_mul_cancel₀ (Real.sqrt_pos.2 (hpos i)).ne']
    have := hexp h
    rw [formSolutionOperator_eq hT hS hσ0 hσ hD, inner_diagOp_comm hD h, hJh,
      inner_single_L2N_left, one_mul, ← tsum_C_mul hT hS hσ0 hσ hC hCs] at this
    have hii : ∑' b, C i b * (lp.single 2 i (1 : ℝ) : L2N) b = C i i := by
      rw [tsum_eq_single i fun b hb => by simp [lp.single_apply, Pi.single_apply, hb]]
      simp [lp.single_apply]
    rw [hii] at this
    convert this using 1
    funext j
    rw [hCv, ← inner_diagOp_comm hD (u j) h, hJh, inner_single_L2N_right, mul_one]
    simp only [hydef, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, inv_pow, Real.sq_sqrt (hνpos j).le]
  -- `λ_G = ν_0`
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun x hx => ?_
    obtain ⟨hx2, hxΛ, hx0⟩ := hx
    set X : L2N := mkL2N x hx2
    set w := (ipT hS hσ0 hσ).symm X
    have hXw : X = w + hsOp hS w := (ipT_symm_add hT hS hσ0 hσ X).symm
    have hQC : ∑' a, x a * ∑' b, C a b * x b = formB hS w w := by
      have : ∀ a, ∑' b, C a b * x b = w a := fun a =>
        tsum_C_mul hT hS hσ0 hσ hC hCs X a
      simp_rw [this]
      rw [formB_self hT hS, ← hXw, inner_L2N]
      rfl
    have hw0 : w ≠ 0 := by
      intro h
      apply hx0
      funext a
      have := congrArg (fun z : L2N => z a) hXw
      simp only [h, map_zero, add_zero, lp.coeFn_zero, Pi.zero_apply] at this
      exact this
    have hBpos : 0 < formB hS w w := by
      have h1 := coercive_hsOp hS hσ w
      rw [formB_apply, real_inner_self_eq_norm_sq]
      have : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have : 0 < σ * ‖w‖ ^ 2 := by positivity
      linarith
    -- `2⟨x, w⟩ ≤ ⟨x,Λx⟩/ν_0 + ν_0 ⟨w, Λ⁻¹ w⟩`
    have hRay := rayleigh_ge hT hS hσ0 hσ hpos hD htop hmono hcomp heq w
    rw [show ‖diagOp hD w‖ ^ 2 = ⟪diagOp hD w, diagOp hD w⟫_ℝ from
      (real_inner_self_eq_norm_sq _).symm, inner_diagOp_eq hpos hD] at hRay
    have hw2 : Summable fun a => w a * w a / lam' a :=
      Summable.of_nonneg_of_le (fun a => div_nonneg (mul_self_nonneg _) (hpos a).le)
        (fun a => by
          rw [div_eq_mul_inv, ← sq]
          exact mul_le_mul_of_nonneg_left (hinvD a) (sq_nonneg _) |>.trans_eq (mul_comm _ _))
        ((summable_sq_L2N w).mul_left (D ^ 2))
    have hxw : HasSum (fun a => x a * w a) (formB hS w w) := by
      rw [formB_self hT hS, ← hXw]; exact hasSum_inner_L2N X w
    have hpt : ∀ a, 2 * (x a * w a) ≤
        lam' a * x a ^ 2 / ν 0 + ν 0 * (w a * w a / lam' a) := fun a => by
      have hl := hpos a
      have hn := hνpos 0
      rw [show lam' a * x a ^ 2 / ν 0 + ν 0 * (w a * w a / lam' a) =
          (lam' a ^ 2 * x a ^ 2 + ν 0 ^ 2 * w a ^ 2) / (lam' a * ν 0) by field_simp,
        le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (lam' a * x a - ν 0 * w a)]
    have hsum : 2 * formB hS w w ≤
        (∑' a, lam' a * x a ^ 2) / ν 0 + ν 0 * ∑' a, w a * w a / lam' a := by
      rw [← (hxw.mul_left 2).tsum_eq, ← tsum_div_const, ← tsum_mul_left,
        ← (hxΛ.div_const _).tsum_add (hw2.mul_left _)]
      exact (hxw.mul_left 2).summable.tsum_le_tsum hpt ((hxΛ.div_const _).add (hw2.mul_left _))
    have hfin : ν 0 * (∑' a, x a * ∑' b, C a b * x b) ≤ ∑' a, lam' a * x a ^ 2 := by
      rw [hQC]
      have hn := hνpos 0
      have : formB hS w w ≤ (∑' a, lam' a * x a ^ 2) / ν 0 := by linarith
      rwa [le_div_iff₀ hn, mul_comm] at this
    rw [hQC] at hfin ⊢
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hBpos)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (hνpos 0).le]
    exact ENNReal.ofReal_le_ofReal hfin
  · have hv0 : v 0 ≠ 0 := by
      intro h
      have h1 := hJ 0 0
      have : ∀ a, u 0 a = 0 := fun a => by
        have := congrFun h a
        simp only [hvdef, Pi.zero_apply, div_eq_zero_iff, mul_eq_zero] at this
        rcases this with (h' | h') | h'
        · exact absurd h' (hsq0 0)
        · exact h'
        · exact absurd h' (hpos a).ne'
      simp [this] at h1
    have hΛv : Summable fun i => lam' i * v 0 i ^ 2 := by
      refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hpos i).le (sq_nonneg _))
        (fun i => ?_) ((hsumΛ 0).mul_left (D ^ 2))
      have : lam' i * v 0 i ^ 2 = (lam' i)⁻¹ * (lam' i * v 0 i) ^ 2 := by
        field_simp [(hpos i).ne']
      rw [this]
      exact mul_le_mul_of_nonneg_right (hinvD i) (sq_nonneg _)
    refine (iInf₂_le (v 0) ⟨hsumv 0, hΛv, hv0⟩).trans_eq ?_
    have e1 : ∑' i, lam' i * v 0 i ^ 2 = ν 0 := by
      have h := hvΛ 0 0
      rw [if_pos rfl] at h
      rw [← h]; exact tsum_congr fun a => by ring
    rw [e1, hvC 0 0, if_pos rfl, ENNReal.ofReal_one, div_one]

end gen

end SharpLSI
