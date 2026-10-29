import SharpSymmetricLSI.Paper.GaussForm16

/-!
# R32 (F1): the operator of a Hilbert–Schmidt matrix on `ℓ²`

For `T : ℕ → ℕ → ℝ` with `∑ T_{ij}² < ∞`, `(Tx)_i = ∑_j T_{ij} x_j` defines `hsOp T : ℓ² →L ℓ²`
with `‖hsOp T‖ ≤ (∑ T_{ij}²)^{1/2}` (`hsOp`); it is symmetric when `T` is (`inner_hsOp_comm`).
If `I + T_n ≥ σ` on all finite sections then `‖x‖² + ⟨x, Tx⟩ ≥ σ‖x‖²` on `ℓ²`
(`coercive_hsOp`), by truncation.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace SharpLSI

/-- `ℓ²(ℕ)`. -/
abbrev L2N := lp (fun _ : ℕ => ℝ) 2

theorem hasSum_sq_L2N (x : L2N) : HasSum (fun i => x i ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_inner (𝕜 := ℝ) x x
  rw [real_inner_self_eq_norm_sq] at h
  simpa [sq] using h

theorem summable_sq_L2N (x : L2N) : Summable fun i => x i ^ 2 := (hasSum_sq_L2N x).summable

theorem norm_sq_L2N (x : L2N) : ‖x‖ ^ 2 = ∑' i, x i ^ 2 := (hasSum_sq_L2N x).tsum_eq.symm

theorem inner_L2N (x y : L2N) : ⟪x, y⟫_ℝ = ∑' i, x i * y i := by
  rw [lp.inner_eq_tsum (𝕜 := ℝ)]
  refine tsum_congr fun i => ?_
  simp [mul_comm]

theorem hasSum_inner_L2N (x y : L2N) : HasSum (fun i => x i * y i) ⟪x, y⟫_ℝ := by
  have h := lp.hasSum_inner (𝕜 := ℝ) x y
  simpa [mul_comm] using h

/-- An `ℓ²` vector from a square-summable sequence. -/
def mkL2N (f : ℕ → ℝ) (hf : Summable fun i => f i ^ 2) : L2N :=
  ⟨f, memℓp_gen (by simpa [Real.norm_eq_abs, sq_abs] using hf)⟩

@[simp] theorem mkL2N_apply (f : ℕ → ℝ) (hf : Summable fun i => f i ^ 2) (i : ℕ) :
    mkL2N f hf i = f i := rfl

section hs
variable {T : ℕ → ℕ → ℝ} (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2)
include hS

theorem summable_row_sq (i : ℕ) : Summable fun j => T i j ^ 2 := hS.prod_factor i

theorem summable_rowSum_sq : Summable fun i => ∑' j, T i j ^ 2 := hS.prod

theorem tsum_rowSum_sq : ∑' i, ∑' j, T i j ^ 2 = ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2 :=
  (hS.tsum_prod).symm

theorem summable_row_mul (x : L2N) (i : ℕ) : Summable fun j => T i j * x j :=
  (tsum_mul_sq_le (summable_row_sq hS i) (summable_sq_L2N x)).1

theorem row_sq_le (x : L2N) (i : ℕ) :
    (∑' j, T i j * x j) ^ 2 ≤ (∑' j, T i j ^ 2) * ‖x‖ ^ 2 := by
  rw [norm_sq_L2N]
  exact (tsum_mul_sq_le (summable_row_sq hS i) (summable_sq_L2N x)).2

theorem summable_hsApply_sq (x : L2N) : Summable fun i => (∑' j, T i j * x j) ^ 2 :=
  Summable.of_nonneg_of_le (fun i => sq_nonneg _) (row_sq_le hS x)
    ((summable_rowSum_sq hS).mul_right _)

/-- The linear map `x ↦ Tx` on `ℓ²`. -/
noncomputable def hsLin : L2N →ₗ[ℝ] L2N where
  toFun x := mkL2N (fun i => ∑' j, T i j * x j) (summable_hsApply_sq hS x)
  map_add' x y := by
    ext i
    simp only [mkL2N_apply, lp.coeFn_add, Pi.add_apply, mul_add]
    exact (summable_row_mul hS x i).tsum_add (summable_row_mul hS y i)
  map_smul' c x := by
    ext i
    simp only [mkL2N_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring

/-- **The bounded operator of a Hilbert–Schmidt matrix.** -/
noncomputable def hsOp : L2N →L[ℝ] L2N :=
  (hsLin hS).mkContinuous (√(∑' p : ℕ × ℕ, T p.1 p.2 ^ 2)) fun x => by
    have h1 : ‖hsLin hS x‖ ^ 2 ≤ (∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) * ‖x‖ ^ 2 := by
      rw [norm_sq_L2N, ← tsum_rowSum_sq hS, ← tsum_mul_right]
      exact (summable_hsApply_sq hS x).tsum_le_tsum (row_sq_le hS x)
        ((summable_rowSum_sq hS).mul_right _)
    have h2 : (∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) * ‖x‖ ^ 2 = (√(∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]
    rw [h2] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

theorem hsOp_apply (x : L2N) (i : ℕ) : hsOp hS x i = ∑' j, T i j * x j := rfl

/-- `|x_i T_ij y_j|` is summable over pairs. -/
theorem summable_abs_triple (x y : L2N) :
    Summable fun p : ℕ × ℕ => |x p.1 * T p.1 p.2 * y p.2| := by
  have hxy : Summable fun p : ℕ × ℕ => (x p.1 * y p.2) ^ 2 := by
    simp_rw [mul_pow]
    exact (summable_sq_L2N x).mul_of_nonneg (summable_sq_L2N y) (fun _ => sq_nonneg _)
      (fun _ => sq_nonneg _)
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => ?_) ((hS.add hxy).div_const 2)
  have := two_mul_le_add_sq |T p.1 p.2| |x p.1 * y p.2|
  rw [sq_abs, sq_abs] at this
  rw [show x p.1 * T p.1 p.2 * y p.2 = T p.1 p.2 * (x p.1 * y p.2) by ring, abs_mul]
  simp only [Pi.add_apply]
  linarith

theorem inner_hsOp (x y : L2N) :
    ⟪x, hsOp hS y⟫_ℝ = ∑' p : ℕ × ℕ, x p.1 * T p.1 p.2 * y p.2 := by
  have hs := (summable_abs_triple hS x y).of_abs
  rw [inner_L2N, hs.tsum_prod]
  refine tsum_congr fun i => ?_
  rw [hsOp_apply, ← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- **`T` symmetric ⇒ `hsOp T` symmetric.** -/
theorem inner_hsOp_comm (hT : ∀ i j, T i j = T j i) (x y : L2N) :
    ⟪x, hsOp hS y⟫_ℝ = ⟪hsOp hS x, y⟫_ℝ := by
  rw [real_inner_comm y (hsOp hS x), inner_hsOp, inner_hsOp]
  have hs := (summable_abs_triple hS x y).of_abs
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hT p.1 p.2]
  ring

end hs

/-! ### Truncation and coercivity -/

/-- `P_n x`. -/
noncomputable def truncL2N (n : ℕ) (x : L2N) : L2N :=
  mkL2N (fun i => if i < n then x i else 0) (by
    refine (summable_of_ne_finset_zero (s := Finset.range n) fun i hi => ?_)
    simp only [Finset.mem_range] at hi; simp [hi])

theorem tendsto_truncL2N (x : L2N) : Tendsto (fun n => truncL2N n x) atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n, ‖truncL2N n x - x‖ ^ 2 = ∑' i, x (i + n) ^ 2 := fun n => by
    rw [norm_sq_L2N]
    have e : ∀ i, (truncL2N n x - x) i ^ 2 = if i < n then 0 else x i ^ 2 := fun i => by
      simp only [lp.coeFn_sub, Pi.sub_apply, truncL2N, mkL2N_apply]
      split_ifs <;> simp
    simp_rw [e]
    have hf : Summable (fun i => if i < n then (0 : ℝ) else x i ^ 2) :=
      (summable_sq_L2N x).of_nonneg_of_le (fun i => by split_ifs <;> positivity)
        fun i => by split_ifs <;> simp [sq_nonneg]
    rw [← hf.sum_add_tsum_nat_add n]
    have h1 : ∑ i ∈ Finset.range n, (if i < n then (0 : ℝ) else x i ^ 2) = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [Finset.mem_range.1 hi]
    rw [h1, zero_add]
    exact tsum_congr fun i => by simp
  have h0 := tendsto_sum_nat_add fun i => x i ^ 2
  have h1 : Tendsto (fun n => ‖truncL2N n x - x‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hsq]; exact h0
  have := h1.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

section coer
variable {T : ℕ → ℕ → ℝ} (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ}
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
include hS hσ

theorem coercive_trunc (n : ℕ) (x : L2N) :
    σ * ‖truncL2N n x‖ ^ 2 ≤ ‖truncL2N n x‖ ^ 2 + ⟪truncL2N n x, hsOp hS (truncL2N n x)⟫_ℝ := by
  set y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i : Fin n => x i
  have hnorm : ‖truncL2N n x‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [norm_sq_L2N, EuclideanSpace.norm_sq_eq, tsum_eq_sum (s := Finset.range n) fun i hi => by
      simp only [Finset.mem_range] at hi; simp [truncL2N, hi]]
    rw [← Fin.sum_univ_eq_sum_range (fun i => truncL2N n x i ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [truncL2N, y, i.isLt, sq_abs]
  have hq : ⟪truncL2N n x, hsOp hS (truncL2N n x)⟫_ℝ = ⟪y, secOp T n y⟫_ℝ := by
    rw [inner_L2N, inner_euclid, tsum_eq_sum (s := Finset.range n) fun i hi => by
      simp only [Finset.mem_range] at hi; simp [truncL2N, hi]]
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hr : hsOp hS (truncL2N n x) i = ∑ j : Fin n, T i j * x j := by
      rw [hsOp_apply, tsum_eq_sum (s := Finset.range n) fun j hj => by
        simp only [Finset.mem_range] at hj; simp [truncL2N, hj]]
      rw [← Fin.sum_univ_eq_sum_range (fun j => T i j * truncL2N n x j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [truncL2N, j.isLt]
    rw [hr, secOp_apply]
    simp [truncL2N, y, i.isLt]
  rw [hnorm, hq]
  exact hσ n y

/-- **Coercivity on `ℓ²`**: `σ‖x‖² ≤ ‖x‖² + ⟨x, Tx⟩`. -/
theorem coercive_hsOp (x : L2N) : σ * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ⟪x, hsOp hS x⟫_ℝ := by
  have ht := tendsto_truncL2N x
  have hc : Continuous fun z : L2N => ‖z‖ ^ 2 + ⟪z, hsOp hS z⟫_ℝ - σ * ‖z‖ ^ 2 := by
    fun_prop
  have := (hc.tendsto x).comp ht
  have h0 : 0 ≤ ‖x‖ ^ 2 + ⟪x, hsOp hS x⟫_ℝ - σ * ‖x‖ ^ 2 :=
    ge_of_tendsto this (Eventually.of_forall fun n => by
      simp only [Function.comp_apply]
      linarith [coercive_trunc hS hσ n x])
  linarith

end coer

end SharpLSI
