import SharpSymmetricLSI.Paper.GaussLaw2

/-!
# R27 groundwork: uniform bounds for the finite-section Gaussian integrals

If `‖y‖² + ⟨y, A_n y⟩ ≥ σ‖y‖²` then every eigenvalue `t_k ≥ σ - 1`; `∑ t_k² = ∑_{i,j<n} A_{ij}²`;
with `x - log(1+x) ≤ x²/δ` for `1 + x ≥ δ`, the product of the multivariate Gaussian integral is
bounded by `exp((q² ∑ A_{ij}² + ‖u‖²)/(2δ))`. The resolvent `(I + A_n)⁻¹u` is built from the
eigenbasis.
-/

open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace NNReal

namespace SharpLSI

theorem sub_log_le_sq_div {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ 1 + x) :
    x - Real.log (1 + x) ≤ x ^ 2 / δ := by
  have hy : 0 < 1 + x := hδ.trans_le hx
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
  rw [Real.log_inv] at h1
  have h2 : x - Real.log (1 + x) ≤ x ^ 2 / (1 + x) := by
    have : x ^ 2 / (1 + x) = x - 1 + (1 + x)⁻¹ := by field_simp; ring
    rw [this]; linarith
  refine h2.trans ?_
  exact div_le_div_of_nonneg_left (sq_nonneg x) hδ hx

theorem sub_log_nonneg {x : ℝ} (hx : 0 < 1 + x) : 0 ≤ x - Real.log (1 + x) := by
  have := Real.log_le_sub_one_of_pos hx; linarith

theorem inv_sqrt_eq_exp {y : ℝ} (hy : 0 < y) : (√y)⁻¹ = rexp (-(Real.log y / 2)) := by
  rw [Real.exp_neg, ← Real.log_sqrt hy.le, Real.exp_log (Real.sqrt_pos.2 hy)]

variable {n : ℕ} {A : ℕ → ℕ → ℝ} (hA : ∀ i j, A i j = A j i)

theorem secEig_ge {σ : ℝ}
    (hσ : ∀ y : EuclideanSpace ℝ (Fin n), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp A n y⟫_ℝ)
    (k : Fin n) : σ - 1 ≤ secEig hA n k := by
  have h := hσ (secVec hA n k)
  rw [inner_secVec_secOp, real_inner_self_eq_norm_sq,
    (secVec hA n).orthonormal.1 k] at h
  linarith

theorem sum_secEig_sq :
    ∑ k, secEig hA n k ^ 2 = ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by
  have h := LinearMap.trace_eq_sum_inner (secOp A n ∘ₗ secOp A n) (secVec hA n)
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)] at h
  have hl : ∀ k, ⟪secVec hA n k, (secOp A n ∘ₗ secOp A n) (secVec hA n k)⟫_ℝ =
      secEig hA n k ^ 2 := by
    intro k
    rw [LinearMap.comp_apply, inner_secVec_secOp, inner_secVec_secOp,
      real_inner_self_eq_norm_sq, (secVec hA n).orthonormal.1 k]; ring
  have hr : ∀ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      (secOp A n ∘ₗ secOp A n) (EuclideanSpace.basisFun (Fin n) ℝ i)⟫_ℝ =
      ∑ j : Fin n, A i j ^ 2 := by
    intro i
    rw [LinearMap.comp_apply, ← secOp_isSymmetric hA, real_inner_self_eq_norm_sq,
      EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [secOp_apply, EuclideanSpace.basisFun_apply, hA j i]
  simp_rw [hl, hr] at h
  exact h.symm

theorem sum_inner_secVec_sq (u : EuclideanSpace ℝ (Fin n)) :
    ∑ k, ⟪secVec hA n k, u⟫_ℝ ^ 2 = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (secVec hA n).sum_inner_mul_inner u u]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm u]; ring

/-- The product value of the Gaussian integral. -/
noncomputable def gaussProd (q : ℝ) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ k, (rexp (q * secEig hA n k / 2) * ((√(1 + q * secEig hA n k))⁻¹ *
    rexp ((1 + q * secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ ^ 2 / 2)))

theorem gaussProd_eq (q : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ k, 0 < 1 + q * secEig hA n k) :
    gaussProd hA q u = rexp (∑ k, ((q * secEig hA n k - Real.log (1 + q * secEig hA n k)) / 2 +
      (1 + q * secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ ^ 2 / 2)) := by
  rw [gaussProd, Real.exp_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [inv_sqrt_eq_exp (hpos k), ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem gaussProd_le {q δ : ℝ} (hδ : 0 < δ) (u : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ k, δ ≤ 1 + q * secEig hA n k) :
    gaussProd hA q u ≤
      rexp ((q ^ 2 * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 + ‖u‖ ^ 2) / (2 * δ)) := by
  rw [gaussProd_eq hA q u fun k => hδ.trans_le (hpos k)]
  refine Real.exp_le_exp.2 ?_
  rw [← sum_secEig_sq hA, ← sum_inner_secVec_sq hA u, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := sub_log_le_sq_div hδ (hpos k)
  have hp : 0 < 1 + q * secEig hA n k := hδ.trans_le (hpos k)
  have h2 : (1 + q * secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ ^ 2 ≤
      ⟪secVec hA n k, u⟫_ℝ ^ 2 / δ := by
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hδ (hpos k)
  have h3 : (q * secEig hA n k) ^ 2 / δ = q ^ 2 * secEig hA n k ^ 2 / δ := by ring
  rw [h3] at h1
  have : (q ^ 2 * secEig hA n k ^ 2 + ⟪secVec hA n k, u⟫_ℝ ^ 2) / (2 * δ) =
      (q ^ 2 * secEig hA n k ^ 2 / δ) / 2 + (⟪secVec hA n k, u⟫_ℝ ^ 2 / δ) / 2 := by
    field_simp
  rw [this]
  linarith

theorem one_le_gaussProd_zero (hpos : ∀ k, 0 < 1 + secEig hA n k) :
    1 ≤ gaussProd hA 1 (0 : EuclideanSpace ℝ (Fin n)) := by
  rw [gaussProd_eq hA 1 0 (by simpa using hpos)]
  refine Real.one_le_exp (Finset.sum_nonneg fun k _ => ?_)
  simp only [one_mul, inner_zero_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_div, add_zero]
  exact div_nonneg (sub_log_nonneg (hpos k)) zero_le_two

theorem gaussProd_one (u : EuclideanSpace ℝ (Fin n)) (hpos : ∀ k, 0 < 1 + secEig hA n k) :
    gaussProd hA 1 u = gaussProd hA 1 (0 : EuclideanSpace ℝ (Fin n)) *
      rexp (∑ k, (1 + secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ ^ 2 / 2) := by
  have hp : ∀ k, 0 < 1 + 1 * secEig hA n k := by simpa using hpos
  rw [gaussProd_eq hA 1 u hp, gaussProd_eq hA 1 0 hp, ← Real.exp_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-! ### The resolvent of the finite section -/

/-- `(I + A_n)⁻¹ u` through the eigenbasis. -/
noncomputable def secRes (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ k, ((1 + secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ) • secVec hA n k

theorem secRes_spec (u : EuclideanSpace ℝ (Fin n)) (hpos : ∀ k, 0 < 1 + secEig hA n k) :
    secRes hA u + secOp A n (secRes hA u) = u := by
  conv_rhs => rw [← (secVec hA n).sum_repr' u]
  rw [secRes, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, secOp_secVec, smul_smul, ← add_smul]
  congr 1
  field_simp [(hpos k).ne']

theorem inner_secRes (u : EuclideanSpace ℝ (Fin n)) :
    ⟪u, secRes hA u⟫_ℝ = ∑ k, (1 + secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ ^ 2 := by
  rw [secRes, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_smul_right, real_inner_comm u]; ring

end SharpLSI
