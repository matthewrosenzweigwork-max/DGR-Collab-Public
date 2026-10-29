import SharpSymmetricLSI.Paper.GaussLaw1

/-!
# R27 groundwork: the multivariate Gaussian integral of a quadratic exponential

For a symmetric `A` with finite section `A_n` (eigenvalues `t_k`, orthonormal eigenvectors `b_k`)
and `1 + q t_k > 0`,
`∫ exp(⟨u,y⟩ - q Q_n(y)/2) dγ_n = ∏_k e^{q t_k/2} (1+q t_k)^{-1/2} exp(⟨b_k,u⟩²/(2(1+q t_k)))`,
`Q_n(y) = ∑_{i,j<n} A_{ij}(y_i y_j - δ_{ij}) = ∑_k t_k(⟨b_k,y⟩² - 1)`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace NNReal

namespace SharpLSI

variable {n : ℕ}

/-- `Q_n(y) = ∑_{i,j<n} A_{ij}(y_i y_j - δ_{ij})` on `ℝⁿ`. -/
def quadFin (A : ℕ → ℕ → ℝ) (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j * (y i * y j - if i = j then 1 else 0)

theorem finrank_euclid : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin

section eig
variable {A : ℕ → ℕ → ℝ} (hA : ∀ i j, A i j = A j i)

/-- The eigenvalues of the finite section. -/
noncomputable def secEig (n : ℕ) : Fin n → ℝ := (secOp_isSymmetric (n := n) hA).eigenvalues finrank_euclid

/-- The orthonormal eigenvectors of the finite section. -/
noncomputable def secVec (n : ℕ) : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (secOp_isSymmetric (n := n) hA).eigenvectorBasis finrank_euclid

theorem secOp_secVec (k : Fin n) : secOp A n (secVec hA n k) = secEig hA n k • secVec hA n k :=
  (secOp_isSymmetric hA).apply_eigenvectorBasis finrank_euclid k

theorem inner_secVec_secOp (k : Fin n) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪secVec hA n k, secOp A n y⟫_ℝ = secEig hA n k * ⟪secVec hA n k, y⟫_ℝ := by
  rw [← secOp_isSymmetric hA, secOp_secVec, real_inner_smul_left]

theorem inner_secOp_self_eig (y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, secOp A n y⟫_ℝ = ∑ k, secEig hA n k * ⟪secVec hA n k, y⟫_ℝ ^ 2 := by
  rw [← (secVec hA n).sum_inner_mul_inner y (secOp A n y)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_secVec_secOp, real_inner_comm y]; ring

theorem trace_secOp_eig : ∑ i : Fin n, A i i = ∑ k, secEig hA n k := by
  rw [← trace_secOp, LinearMap.trace_eq_sum_inner _ (secVec hA n)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_secVec_secOp, real_inner_self_eq_norm_sq, (secVec hA n).orthonormal.1 k]; ring

theorem quadFin_eq_eig (y : EuclideanSpace ℝ (Fin n)) :
    quadFin A n y = ∑ k, secEig hA n k * (⟪secVec hA n k, y⟫_ℝ ^ 2 - 1) := by
  have h1 : quadFin A n y = ⟪y, secOp A n y⟫_ℝ - ∑ i : Fin n, A i i := by
    rw [inner_secOp_self]
    unfold quadFin
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [h1, inner_secOp_self_eig hA, trace_secOp_eig hA]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]

theorem quadFin_sum (x : Fin n → ℝ) :
    quadFin A n (∑ k, x k • secVec hA n k) = ∑ k, secEig hA n k * (x k ^ 2 - 1) := by
  rw [quadFin_eq_eig hA]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(secVec hA n).orthonormal.inner_right_fintype]

/-- **The multivariate Gaussian integral.** -/
theorem integral_exp_quadFin (q : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ k, 0 < 1 + q * secEig hA n k) :
    ∫ y, rexp (⟪u, y⟫_ℝ - q * quadFin A n y / 2) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
      ∏ k, (rexp (q * secEig hA n k / 2) * ((√(1 + q * secEig hA n k))⁻¹ *
        rexp ((1 + q * secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ ^ 2 / 2))) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (secVec hA n)]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      rexp (⟪u, y⟫_ℝ - q * quadFin A n y / 2) := by
    unfold quadFin
    fun_prop
  rw [integral_map (Continuous.aemeasurable (by fun_prop)) hcont.aestronglyMeasurable]
  have hpt : ∀ x : Fin n → ℝ, rexp (⟪u, ∑ k, x k • secVec hA n k⟫_ℝ -
      q * quadFin A n (∑ k, x k • secVec hA n k) / 2) =
      ∏ k, (rexp (q * secEig hA n k / 2) * rexp (⟪secVec hA n k, u⟫_ℝ * x k -
        q * secEig hA n k * x k ^ 2 / 2)) := by
    intro x
    rw [quadFin_sum, Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.exp_sum,
      ← Real.exp_add]
    congr 1
    rw [inner_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right, real_inner_comm]; ring
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod (f := fun k (xk : ℝ) => rexp (q * secEig hA n k / 2) *
    rexp (⟪secVec hA n k, u⟫_ℝ * xk - q * secEig hA n k * xk ^ 2 / 2))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  congr 1
  exact integral_exp_quad_gaussian (hpos k)

theorem prod_exp_quadFin_pos (q : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ k, 0 < 1 + q * secEig hA n k) :
    0 < ∏ k, (rexp (q * secEig hA n k / 2) * ((√(1 + q * secEig hA n k))⁻¹ *
        rexp ((1 + q * secEig hA n k)⁻¹ * ⟪secVec hA n k, u⟫_ℝ ^ 2 / 2))) :=
  Finset.prod_pos fun k _ => mul_pos (Real.exp_pos _)
    (mul_pos (inv_pos.2 (Real.sqrt_pos.2 (hpos k))) (Real.exp_pos _))

theorem integrable_exp_quadFin (q : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ k, 0 < 1 + q * secEig hA n k) :
    Integrable (fun y => rexp (⟪u, y⟫_ℝ - q * quadFin A n y / 2))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  by_contra h
  have h1 := integral_exp_quadFin hA q u hpos
  rw [integral_undef h] at h1
  have := prod_exp_quadFin_pos hA q u hpos
  linarith

end eig

end SharpLSI
