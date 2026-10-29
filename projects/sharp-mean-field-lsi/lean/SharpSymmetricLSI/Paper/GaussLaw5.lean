import SharpSymmetricLSI.Paper.GaussLaw4

/-!
# R27 groundwork: `⟨u_n, (I+T_n)⁻¹u_n⟩ → ⟨v, C v⟩`

With `x = C(v 1_s) ∈ ℓ²` (`(I+T)x = v 1_s`), the error `e_n = P_n x - (I+T_n)⁻¹u_n` solves
`(I+T_n)e_n = -r_n`, `r_{n,i} = ∑_{k≥n} T_{ik}x_k`. Hence `σ‖e_n‖ ≤ ‖r_n‖`, and
`‖r_n‖² ≤ (∑ T_{ij}²)(∑_{k≥n} x_k²) → 0`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace

namespace SharpLSI

/-- `P_n x`. -/
def projVec (x : ℕ → ℝ) (n : ℕ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i : Fin n => x i

/-- `r_{n,i} = ∑_k T_{i,k+n} x_{k+n}`. -/
noncomputable def tailVec (T : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i : Fin n => ∑' k, T i (k + n) * x (k + n)

theorem projVec_spec {T : ℕ → ℕ → ℝ} {x w : ℕ → ℝ} (hx : ∀ i, x i + ∑' k, T i k * x k = w i)
    (hTx : ∀ i, Summable fun k => T i k * x k) (n : ℕ) :
    projVec x n + secOp T n (projVec x n) =
      WithLp.toLp 2 (fun i : Fin n => w i) - tailVec T x n := by
  ext i
  simp only [projVec, tailVec, PiLp.add_apply, PiLp.sub_apply, secOp_apply]
  have h1 := (hTx i).sum_add_tsum_nat_add n
  have h2 := Fin.sum_univ_eq_sum_range (fun j => T i j * x j) n
  have h3 := hx i
  linarith

theorem tail_sq_le {T : ℕ → ℕ → ℝ} (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {x : ℕ → ℝ}
    (hx : Summable fun k => x k ^ 2) (n : ℕ) :
    ‖tailVec T x n‖ ^ 2 ≤ (∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) * ∑' k, x (k + n) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have hx' : Summable fun k => x (k + n) ^ 2 := (summable_nat_add_iff n).2 hx
  have hrow : ∀ i, Summable fun k => T i k ^ 2 := fun i => hS.prod_factor i
  have hrow' : ∀ i, Summable fun k => T i (k + n) ^ 2 := fun i =>
    (summable_nat_add_iff n).2 (hrow i)
  have h1 : ∀ i : Fin n, ‖tailVec T x n i‖ ^ 2 ≤ (∑' k, T i k ^ 2) * ∑' k, x (k + n) ^ 2 := by
    intro i
    simp only [tailVec, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    refine (tsum_mul_sq_le (hrow' i) hx').2.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun _ => sq_nonneg _)
    have := (hrow i).sum_add_tsum_nat_add n
    have h0 : 0 ≤ ∑ k ∈ Finset.range n, T i k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun _ => sq_nonneg _)
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑' k, T i k ^ 2) n, hS.tsum_prod]
  exact Summable.sum_le_tsum _ (fun i _ => tsum_nonneg fun _ => sq_nonneg _) hS.prod

theorem eventually_lt_of_finset (s : Finset ℕ) : ∀ᶠ n in atTop, ∀ i ∈ s, i < n := by
  refine Filter.eventually_atTop.2 ⟨s.sup id + 1, fun n hn i hi => ?_⟩
  have := Finset.le_sup (f := id) hi
  simp only [id] at this
  omega

section res
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (s : Finset ℕ) (v : ℕ → ℝ)
include hS hσ0 hσ hC

/-- The finite-section error. -/
theorem norm_err_le (n : ℕ) :
    σ * ‖projVec (cvec C s v) n - secRes hT (finVec s v n)‖ ≤ ‖tailVec T (cvec C s v) n‖ := by
  set e := projVec (cvec C s v) n - secRes hT (finVec s v n)
  set r := tailVec T (cvec C s v) n
  have hTx : ∀ i, Summable fun k => T i k * cvec C s v k := fun i =>
    (tsum_mul_sq_le (hS.prod_factor i) (summable_cvec_sq hC s v)).1
  have hP := projVec_spec (cvec_eq hS hC s v) hTx n
  have hR := secRes_spec hT (finVec s v n) (secEig_pos hT hσ0 hσ n)
  have he : e + secOp T n e = -r := by
    have : e + secOp T n e = (projVec (cvec C s v) n + secOp T n (projVec (cvec C s v) n)) -
        (secRes hT (finVec s v n) + secOp T n (secRes hT (finVec s v n))) := by
      simp only [e, map_sub]; abel
    rw [this, hP, hR]
    change finVec s v n - r - finVec s v n = -r
    abel
  have h1 := hσ n e
  have h2 : ‖e‖ ^ 2 + ⟪e, secOp T n e⟫_ℝ = -⟪e, r⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_right, he, inner_neg_right]
  have h3 : -⟪e, r⟫_ℝ ≤ ‖e‖ * ‖r‖ := (neg_le_abs _).trans (abs_real_inner_le_norm e r)
  rcases (norm_nonneg e).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · refine le_of_mul_le_mul_right ?_ h0
    nlinarith

theorem tendsto_inner_err :
    Tendsto (fun n => ⟪finVec s v n, projVec (cvec C s v) n - secRes hT (finVec s v n)⟫_ℝ)
      atTop (𝓝 0) := by
  set S := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2
  set V := ∑ i ∈ s, v i ^ 2
  have htail := tendsto_sum_nat_add (fun k => cvec C s v k ^ 2)
  have hb : Tendsto (fun n => V * S / σ ^ 2 * ∑' k, cvec C s v (k + n) ^ 2) atTop (𝓝 0) := by
    simpa using htail.const_mul (V * S / σ ^ 2)
  have hsq : Tendsto (fun n => ⟪finVec s v n, projVec (cvec C s v) n -
      secRes hT (finVec s v n)⟫_ℝ ^ 2) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
      (Eventually.of_forall fun _ => sq_nonneg _) ?_
    filter_upwards [eventually_lt_of_finset s] with n hn
    set e := projVec (cvec C s v) n - secRes hT (finVec s v n)
    have h1 : ⟪finVec s v n, e⟫_ℝ ^ 2 ≤ ‖finVec s v n‖ ^ 2 * ‖e‖ ^ 2 := by
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    have h2 := norm_err_le hT hS hσ0 hσ hC s v n
    have h3 := tail_sq_le hS (summable_cvec_sq hC s v) n
    have h4 : σ ^ 2 * ‖e‖ ^ 2 ≤ ‖tailVec T (cvec C s v) n‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 2
    rw [norm_finVec_sq s hn] at h1
    have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h5 : ‖e‖ ^ 2 ≤ S * (∑' k, cvec C s v (k + n) ^ 2) / σ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc _ ≤ V * ‖e‖ ^ 2 := h1
      _ ≤ V * (S * (∑' k, cvec C s v (k + n) ^ 2) / σ ^ 2) := mul_le_mul_of_nonneg_left h5 hV
      _ = _ := by ring
  have habs := hsq.sqrt
  simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

/-- **Convergence of the finite-section resolvents.** -/
theorem tendsto_inner_secRes :
    Tendsto (fun n => ⟪finVec s v n, secRes hT (finVec s v n)⟫_ℝ) atTop
      (𝓝 (∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)) := by
  have h := (tendsto_const_nhds (x := ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)).sub
    (tendsto_inner_err hT hS hσ0 hσ hC s v)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_lt_of_finset s] with n hn
  have h1 : ⟪finVec s v n, projVec (cvec C s v) n⟫_ℝ = ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j := by
    have h2 : ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j = ∑ i ∈ s, v i * cvec C s v i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cvec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [inner_euclid, h2, ← sum_fin_ite s hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [finVec, projVec, PiLp.toLp_apply]
    split_ifs <;> simp
  rw [inner_sub_right, h1]
  ring

end res

end SharpLSI
