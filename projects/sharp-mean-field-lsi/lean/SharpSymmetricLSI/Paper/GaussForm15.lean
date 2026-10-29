import SharpSymmetricLSI.Paper.GaussForm14
import SharpSymmetricLSI.Paper.GaussLaw8

/-!
# R32 (C1): the covariance `C = (I+T)⁻¹` under `I + T ≥ σ`

Given the finite-section bound `I + T_n ≥ σ` (the conclusion of Prop. 2.1 through
`secOp_ge_of_prop21`), `T` symmetric and Hilbert–Schmidt, and `(I+T)C = I`:
* `C` is symmetric (`C_symm_of_secOp`): `C_{ij} = lim ⟨e_i, (I+T_n)⁻¹ e_j⟩` and the finite resolvents are
  symmetric;
* `0 ≤ ⟨v, C v⟩ ≤ |v|²/σ` for finitely supported `v` (`quadC_le`);
* hence every finite block of `C` is positive semidefinite (`blockMat_posSemidef`).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace

namespace SharpLSI

section res
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C)

/-- The finite-section resolvent is symmetric. -/
theorem inner_secRes_comm {n : ℕ} (u w : EuclideanSpace ℝ (Fin n)) :
    ⟪u, secRes hT w⟫_ℝ = ⟪w, secRes hT u⟫_ℝ := by
  rw [secRes, secRes, inner_sum, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm u, real_inner_comm w]
  ring

include hS hσ0 hσ hC in
/-- The finite-section error tested against another finite vector. -/
theorem tendsto_inner_err' (s s' : Finset ℕ) (v v' : ℕ → ℝ) :
    Tendsto (fun n => ⟪finVec s' v' n, projVec (cvec C s v) n - secRes hT (finVec s v n)⟫_ℝ)
      atTop (𝓝 0) := by
  set S := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2
  set V := ∑ i ∈ s', v' i ^ 2
  have htail := tendsto_sum_nat_add (fun k => cvec C s v k ^ 2)
  have hb : Tendsto (fun n => V * S / σ ^ 2 * ∑' k, cvec C s v (k + n) ^ 2) atTop (𝓝 0) := by
    simpa using htail.const_mul (V * S / σ ^ 2)
  have hsq : Tendsto (fun n => ⟪finVec s' v' n, projVec (cvec C s v) n -
      secRes hT (finVec s v n)⟫_ℝ ^ 2) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
      (Eventually.of_forall fun _ => sq_nonneg _) ?_
    filter_upwards [eventually_lt_of_finset s'] with n hn
    set e := projVec (cvec C s v) n - secRes hT (finVec s v n)
    have h1 : ⟪finVec s' v' n, e⟫_ℝ ^ 2 ≤ ‖finVec s' v' n‖ ^ 2 * ‖e‖ ^ 2 := by
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    have h2 := norm_err_le hT hS hσ0 hσ hC s v n
    have h3 := tail_sq_le hS (summable_cvec_sq hC s v) n
    have h4 : σ ^ 2 * ‖e‖ ^ 2 ≤ ‖tailVec T (cvec C s v) n‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 2
    rw [norm_finVec_sq s' hn] at h1
    have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h5 : ‖e‖ ^ 2 ≤ S * (∑' k, cvec C s v (k + n) ^ 2) / σ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc _ ≤ V * ‖e‖ ^ 2 := h1
      _ ≤ V * (S * (∑' k, cvec C s v (k + n) ^ 2) / σ ^ 2) := mul_le_mul_of_nonneg_left h5 hV
      _ = _ := by ring
  have habs := hsq.sqrt
  simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at habs
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

include hS hσ0 hσ hC in
/-- `C_{ij} = lim ⟨e_i, (I+T_n)⁻¹ e_j⟩`. -/
theorem tendsto_inner_secRes_single (i j : ℕ) :
    Tendsto (fun n => ⟪finVec {i} (fun _ => 1) n, secRes hT (finVec {j} (fun _ => 1) n)⟫_ℝ)
      atTop (𝓝 (C i j)) := by
  have h := tendsto_inner_err' hT hS hσ0 hσ hC {j} {i} (fun _ => 1) (fun _ => 1)
  have h2 : Tendsto (fun n => ⟪finVec {i} (fun _ => (1 : ℝ)) n,
      projVec (cvec C {j} (fun _ => 1)) n⟫_ℝ) atTop (𝓝 (C i j)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_of_finset {i}] with n hn
    have hc : C i j = ∑ k ∈ ({i} : Finset ℕ), 1 * cvec C {j} (fun _ => 1) k := by
      simp [cvec]
    rw [inner_euclid, hc, ← sum_fin_ite {i} hn]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [finVec, projVec, PiLp.toLp_apply]
    split_ifs <;> simp
  have h3 := h2.sub h
  rw [sub_zero] at h3
  refine h3.congr fun n => ?_
  rw [inner_sub_right]; ring

include hT hS hσ0 hσ hC in
/-- **`C` is symmetric.** -/
theorem C_symm_of_secOp (i j : ℕ) : C i j = C j i :=
  tendsto_nhds_unique (tendsto_inner_secRes_single hT hS hσ0 hσ hC i j)
    ((tendsto_inner_secRes_single hT hS hσ0 hσ hC j i).congr fun _ => inner_secRes_comm hT _ _)

include hT hS hσ0 hσ hC in
/-- `⟨v, C v⟩ ≤ |v|²/σ`. -/
theorem quadC_le (s : Finset ℕ) (v : ℕ → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j ≤ (∑ i ∈ s, v i ^ 2) / σ := by
  refine le_of_tendsto (tendsto_inner_secRes hT hS hσ0 hσ hC s v) ?_
  filter_upwards [eventually_lt_of_finset s] with n hn
  rw [inner_secRes, ← norm_finVec_sq s hn, ← sum_inner_secVec_sq hT (finVec s v n),
    Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : σ ≤ 1 + secEig hT n k := by have := secEig_ge hT (hσ n) k; linarith
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hσ0 hk) (sq_nonneg _)

include hT hS hσ0 hσ hC in
/-- **Every finite block of `C` is positive semidefinite.** -/
theorem blockMat_posSemidef (N : ℕ) : (blockMat C N).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun t => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, blockMat, Matrix.of_apply, star_trivial]
    exact C_symm_of_secOp hT hS hσ0 hσ hC _ _
  · rw [star_trivial, ← quad_extVec]
    exact quadC_nonneg hT hS hσ0 hσ hC _ _

end res

end SharpLSI
