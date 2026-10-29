import SharpSymmetricLSI.Paper.GaussForm22

/-!
# R32 (F4): the diagonalization of `(Λ, C)` and `λ_G = ν_0`

* `ipT`: `I + T` as a continuous linear equivalence of `ℓ²` (Lax–Milgram for `B`); `C = (I+T)⁻¹`
  acts on `ℓ²` by its matrix: `∑_b C_{ab} x_b = ((I+T)⁻¹x)_a` (`tsum_C_mul`), given
  `IsInverseOfIPlus T C` and symmetry of `C`.
* `rayleigh_ge`: `B(w,w) ≥ ν_0 ‖Jw‖²` (TauCeti's Rayleigh principle and completeness).
* `exists_genEigen_matrix`: `v_j = √ν_j Λ⁻¹u_j` satisfy `v_j, Λv_j ∈ ℓ²`, `⟨v_i, Cv_j⟩ = δ_{ij}`,
  `⟨v_i, Λv_j⟩ = ν_i δ_{ij}`, `0 < ν_0 ≤ ν_1 ≤ … → ∞`, and `λ_G = ν_0` (`lamG`, (8.9)).
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace SharpLSI

section inv
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)

/-- `I + T` as a continuous linear equivalence of `ℓ²`. -/
noncomputable def ipT : L2N ≃L[ℝ] L2N :=
  (isCoercive_formB hS hσ0 hσ).continuousLinearEquivOfBilin

include hT in
theorem ipT_apply (x : L2N) : ipT hS hσ0 hσ x = x + hsOp hS x := by
  symm
  refine (isCoercive_formB hS hσ0 hσ).unique_continuousLinearEquivOfBilin fun w => ?_
  rw [formB_apply, inner_add_left, inner_hsOp_comm hS hT x w]

include hT in
theorem ipT_symm_add (x : L2N) :
    (ipT hS hσ0 hσ).symm x + hsOp hS ((ipT hS hσ0 hσ).symm x) = x := by
  rw [← ipT_apply hT hS hσ0 hσ, ContinuousLinearEquiv.apply_symm_apply]

include hT in
theorem ipT_symm_of_add (y : L2N) : (ipT hS hσ0 hσ).symm (y + hsOp hS y) = y := by
  rw [← ipT_apply hT hS hσ0 hσ, ContinuousLinearEquiv.symm_apply_apply]

include hT in
theorem inner_ipT_symm_comm (x y : L2N) :
    ⟪(ipT hS hσ0 hσ).symm x, y⟫_ℝ = ⟪x, (ipT hS hσ0 hσ).symm y⟫_ℝ := by
  set x' := (ipT hS hσ0 hσ).symm x
  set y' := (ipT hS hσ0 hσ).symm y
  have hx : x = x' + hsOp hS x' := (ipT_symm_add hT hS hσ0 hσ x).symm
  have hy : y = y' + hsOp hS y' := (ipT_symm_add hT hS hσ0 hσ y).symm
  have h : ⟪x', y' + hsOp hS y'⟫_ℝ = ⟪x' + hsOp hS x', y'⟫_ℝ := by
    rw [inner_add_right, inner_add_left, inner_hsOp_comm hS hT x' y']
  show ⟪x', y⟫_ℝ = ⟪x, y'⟫_ℝ
  conv_lhs => rw [hy]
  conv_rhs => rw [hx]
  exact h

include hT in
/-- `B(w, w) = ⟨(I+T)w, w⟩`. -/
theorem formB_self (w : L2N) : formB hS w w = ⟪w + hsOp hS w, w⟫_ℝ := by
  rw [formB_apply, inner_add_left, inner_hsOp_comm hS hT w w]

variable {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (hCs : ∀ a b, C a b = C b a)

/-- The column `C e_a`. -/
noncomputable def colC (a : ℕ) : L2N := mkL2N (fun b => C b a) (hC a).1

include hS in
theorem colC_add (a : ℕ) : colC hC a + hsOp hS (colC hC a) = lp.single 2 a 1 := by
  ext i
  simp only [lp.coeFn_add, Pi.add_apply, colC, mkL2N_apply, hsOp_apply, lp.single_apply,
    Pi.single_apply]
  have h := ((hC a).2 i).2
  have h1 : Summable fun k => (if i = k then (1 : ℝ) else 0) * C k a :=
    summable_of_ne_finset_zero (s := {i}) fun k hk => by
      simp only [Finset.mem_singleton] at hk; simp [Ne.symm hk]
  have h2 : Summable fun k => T i k * C k a := summable_row_mul hS (colC hC a) i
  simp_rw [add_mul] at h
  rw [h1.tsum_add h2] at h
  have h3 : ∑' k, (if i = k then (1 : ℝ) else 0) * C k a = C i a := by
    rw [tsum_eq_single i fun k hk => by simp [Ne.symm hk]]; simp
  rw [h3] at h
  rw [h]

include hT hC hCs in
/-- **The matrix `C` acts on `ℓ²` as `(I+T)⁻¹`.** -/
theorem tsum_C_mul (x : L2N) (a : ℕ) : ∑' b, C a b * x b = (ipT hS hσ0 hσ).symm x a := by
  have hcol : colC hC a = (ipT hS hσ0 hσ).symm (lp.single 2 a 1) := by
    rw [← colC_add hS hC a, ipT_symm_of_add hT hS hσ0 hσ]
  have e1 : ∑' b, C a b * x b = ⟪colC hC a, x⟫_ℝ := by
    rw [inner_L2N]; exact tsum_congr fun b => by simp [colC, hCs a b]
  rw [e1, hcol, inner_ipT_symm_comm hT hS hσ0 hσ, inner_single_L2N_left, one_mul]

end inv

/-! ### The assembled diagonalization -/

section gen
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {lam' : ℕ → ℝ} (hpos : ∀ i, 0 < lam' i) {D : ℝ} (hD : ∀ i, |(√(lam' i))⁻¹| ≤ D)
include hT hS hσ0 hσ hpos

omit hpos in
/-- The solution operator of the variational problem is `J (I+T)⁻¹ J`. -/
theorem formSolutionOperator_eq (h : L2N) :
    (isCoercive_formB hS hσ0 hσ).formSolutionOperator (diagOp hD) h =
      diagOp hD ((ipT hS hσ0 hσ).symm (diagOp hD h)) := by
  rw [IsCoercive.formSolutionOperator_apply]
  congr 1
  symm
  refine IsCoercive.eq_formSolutionMap _ _ fun v => ?_
  rw [formB_apply, inner_hsOp_comm hS hT, ← inner_add_left, ipT_symm_add hT hS hσ0 hσ,
    inner_diagOp_comm]

omit hT hS hσ0 hσ in
theorem inner_diagOp_eq (x y : L2N) :
    ⟪diagOp hD x, diagOp hD y⟫_ℝ = ∑' a, x a * y a / lam' a := by
  rw [inner_L2N]
  refine tsum_congr fun a => ?_
  rw [diagOp_apply, diagOp_apply]
  have : (√(lam' a))⁻¹ * (√(lam' a))⁻¹ = (lam' a)⁻¹ := by
    rw [← sq, inv_pow, Real.sq_sqrt (hpos a).le]
  rw [div_eq_mul_inv, ← this]; ring

/-- **The Rayleigh bound** `ν_0 ‖Jw‖² ≤ B(w,w)` for the bottom `ν_0` of the eigenbasis. -/
theorem rayleigh_ge (htop : Tendsto lam' atTop atTop) {u : ℕ → L2N} {ν : ℕ → ℝ}
    (hmono : Monotone ν)
    (hcomp : ∀ y : L2N, (∀ j, ⟪diagOp hD (u j), y⟫_ℝ = 0) → y = 0)
    (heq : ∀ j v, formB hS (u j) v = ν j * ⟪diagOp hD (u j), diagOp hD v⟫_ℝ) (w : L2N) :
    ν 0 * ‖diagOp hD w‖ ^ 2 ≤ formB hS w w := by
  have hB := isCoercive_formB hS hσ0 hσ
  have hJ := isCompactOperator_diagOp hD (tendsto_inv_sqrt htop)
  have hsymm := formB_symm hS hT
  have hJne : diagOp hD ≠ 0 := by
    intro h
    have := congrArg (fun L : L2N →L[ℝ] L2N => L (lp.single 2 0 1) 0) h
    simp only [diagOp_single, zero_apply, lp.single_apply_self] at this
    simp only [mul_one, lp.coeFn_zero, Pi.zero_apply] at this
    exact inv_ne_zero (Real.sqrt_pos.2 (hpos 0)).ne' this
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = ‖hB.formSolutionOperator (diagOp hD)‖⁻¹ := ⟨_, rfl⟩
  have hμ : ν 0 ≤ μ := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨u', hu', heq'⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner hJ hsymm hJne
    rw [← hμdef] at heq'
    have horth : ∀ j, ⟪diagOp hD (u j), diagOp hD u'⟫_ℝ = 0 := by
      intro j
      have h1 := heq' (u j)
      have h2 := heq j u'
      rw [hsymm, h2] at h1
      have hc : ⟪diagOp hD u', diagOp hD (u j)⟫_ℝ = ⟪diagOp hD (u j), diagOp hD u'⟫_ℝ :=
        real_inner_comm _ _
      rw [hc] at h1
      have hne : ν j - μ ≠ 0 :=
        sub_ne_zero.2 (ne_of_gt (lt_of_lt_of_le hlt (hmono (Nat.zero_le j))))
      have : (ν j - μ) * ⟪diagOp hD (u j), diagOp hD u'⟫_ℝ = 0 := by rw [sub_mul]; linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    have hJu' := hcomp _ horth
    have h3 := heq' u'
    rw [hJu', inner_zero_left, mul_zero, formB_apply] at h3
    have h4 := coercive_hsOp hS hσ u'
    rw [real_inner_self_eq_norm_sq] at h3
    have : ‖u'‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖u'‖]
    exact hu' (norm_eq_zero.1 (by nlinarith [norm_nonneg u']))
  by_cases hw : diagOp hD w = 0
  · rw [hw, norm_zero]
    have h4 := coercive_hsOp hS hσ w
    rw [formB_apply, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖w‖]
  · have hl := (hB.isLeast_rayleighQuotient hJ hsymm hJne).2 ⟨w, hw, rfl⟩
    have hpos' : 0 < ‖diagOp hD w‖ ^ 2 := by positivity
    rw [← hμdef] at hl
    have := hμ.trans hl
    rw [le_div_iff₀ hpos'] at this
    exact this

end gen

end SharpLSI
