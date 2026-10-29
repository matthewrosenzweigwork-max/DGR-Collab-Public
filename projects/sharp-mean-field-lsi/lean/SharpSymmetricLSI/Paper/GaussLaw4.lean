import SharpSymmetricLSI.Paper.GaussLaw3
import SharpSymmetricLSI.Paper.ULimit3

/-!
# R27 groundwork: the finite sections under `γ` and convergence of the resolvents

* `∫ exp(t ∑_{i∈s} vᵢ zᵢ - q Q_n(z)/2) dγ` is the product value of the multivariate Gaussian
  integral (the first `n` coordinates of `γ` are the standard Gaussian of `ℝⁿ`).
* If `I + T_n ≥ σ` for all finite sections and `C = (I+T)⁻¹` (`IsInverseOfIPlus`), then
  `⟨u_n, (I+T_n)⁻¹u_n⟩ → ∑_{i,j∈s} vᵢ C_{ij} vⱼ`: with `x = Cv ∈ ℓ²`, the error
  `e = P_n x - (I+T_n)⁻¹u_n` solves `(I+T_n)e = -r_n`, `r_{n,i} = ∑_{k≥n} T_{ik}x_k`, so
  `σ‖e‖ ≤ ‖r_n‖ ≤ ‖T‖_{HS} (∑_{k≥n} x_k²)^{1/2} → 0`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace

namespace SharpLSI

/-! ### Transfer to `γ` -/

theorem measurable_gaussVec (n : ℕ) : Measurable (gaussVec n) :=
  (WithLp.measurable_toLp 2 _).comp (by fun_prop)

theorem quadFin_gaussVec (T : ℕ → ℕ → ℝ) (n : ℕ) (z : ℕ → ℝ) :
    quadFin T n (gaussVec n z) = quadTrunc T n z := by
  rw [quadTrunc_eq_fin]
  unfold quadFin chaosH
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [gaussVec, Fin.val_inj]

/-- The vector `(vᵢ 1_{i∈s})_{i<n}`. -/
def finVec (s : Finset ℕ) (v : ℕ → ℝ) (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i : Fin n => if (i : ℕ) ∈ s then v i else 0

theorem sum_fin_ite (s : Finset ℕ) {n : ℕ} (hs : ∀ i ∈ s, i < n) (g : ℕ → ℝ) :
    ∑ i : Fin n, (if (i : ℕ) ∈ s then g i else 0) = ∑ i ∈ s, g i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ∈ s then g i else 0), Finset.sum_ite_mem]
  congr 1
  ext i
  simp only [Finset.mem_inter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hs i h, h⟩⟩

theorem inner_finVec_gaussVec (s : Finset ℕ) {n : ℕ} (hs : ∀ i ∈ s, i < n) (v z : ℕ → ℝ) :
    ⟪finVec s v n, gaussVec n z⟫_ℝ = ∑ i ∈ s, v i * z i := by
  rw [inner_euclid, ← sum_fin_ite s hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [finVec, gaussVec, PiLp.toLp_apply]
  split_ifs <;> simp

theorem norm_finVec_sq (s : Finset ℕ) {n : ℕ} (hs : ∀ i ∈ s, i < n) (v : ℕ → ℝ) :
    ‖finVec s v n‖ ^ 2 = ∑ i ∈ s, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← sum_fin_ite s hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [finVec, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  split_ifs <;> simp

section transfer
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i) {n : ℕ}

theorem exp_quad_comp (s : Finset ℕ) (hs : ∀ i ∈ s, i < n) (v : ℕ → ℝ) (t q : ℝ) :
    (fun z => rexp (t * ∑ i ∈ s, v i * z i - q * quadTrunc T n z / 2)) =
      (fun y => rexp (⟪t • finVec s v n, y⟫_ℝ - q * quadFin T n y / 2)) ∘ gaussVec n := by
  funext z
  simp only [Function.comp, real_inner_smul_left, inner_finVec_gaussVec s hs, quadFin_gaussVec]

theorem continuous_exp_quad (u : EuclideanSpace ℝ (Fin n)) (q : ℝ) :
    Continuous fun y : EuclideanSpace ℝ (Fin n) => rexp (⟪u, y⟫_ℝ - q * quadFin T n y / 2) := by
  unfold quadFin; fun_prop

theorem integral_gammaRef_exp_quad (s : Finset ℕ) (hs : ∀ i ∈ s, i < n) (v : ℕ → ℝ) (t q : ℝ)
    (hpos : ∀ k, 0 < 1 + q * secEig hT n k) :
    ∫ z, rexp (t * ∑ i ∈ s, v i * z i - q * quadTrunc T n z / 2) ∂gammaRef =
      gaussProd hT q (t • finVec s v n) := by
  have h := integral_map (μ := gammaRef) (measurable_gaussVec n).aemeasurable
    (continuous_exp_quad (T := T) (t • finVec s v n) q).aestronglyMeasurable
  rw [gammaRef_map_gaussVec, integral_exp_quadFin hT q _ hpos] at h
  rw [exp_quad_comp s hs v t q]
  exact h.symm

theorem integrable_gammaRef_exp_quad (s : Finset ℕ) (hs : ∀ i ∈ s, i < n) (v : ℕ → ℝ) (t q : ℝ)
    (hpos : ∀ k, 0 < 1 + q * secEig hT n k) :
    Integrable (fun z => rexp (t * ∑ i ∈ s, v i * z i - q * quadTrunc T n z / 2)) gammaRef := by
  rw [exp_quad_comp s hs v t q]
  refine (integrable_map_measure (continuous_exp_quad _ q).aestronglyMeasurable
    (measurable_gaussVec n).aemeasurable).1 ?_
  rw [gammaRef_map_gaussVec]
  exact integrable_exp_quadFin hT q _ hpos

end transfer

/-! ### Cauchy–Schwarz for series -/

theorem tsum_mul_sq_le {a b : ℕ → ℝ} (ha : Summable fun k => a k ^ 2)
    (hb : Summable fun k => b k ^ 2) :
    Summable (fun k => a k * b k) ∧ (∑' k, a k * b k) ^ 2 ≤ (∑' k, a k ^ 2) * ∑' k, b k ^ 2 := by
  have hab : Summable fun k => a k * b k := by
    refine Summable.of_norm_bounded ((ha.add hb).div_const 2) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have := two_mul_le_add_sq |a k| |b k|
    rw [sq_abs, sq_abs] at this
    linarith
  refine ⟨hab, ?_⟩
  have h1 := ((hab.hasSum.tendsto_sum_nat).pow 2)
  have h2 := (ha.hasSum.tendsto_sum_nat).mul (hb.hasSum.tendsto_sum_nat)
  exact le_of_tendsto_of_tendsto' h1 h2 fun n =>
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) a b

/-! ### Convergence of the finite-section resolvents -/

section res
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (s : Finset ℕ) (v : ℕ → ℝ)

include hσ0 hσ in
theorem secEig_pos (n : ℕ) (k : Fin n) : 0 < 1 + secEig hT n k := by
  have := secEig_ge hT (hσ n) k; linarith

/-- `x = C(v 1_s)`. -/
def cvec (C : ℕ → ℕ → ℝ) (s : Finset ℕ) (v : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ s, C k j * v j

include hC in
theorem summable_cvec_sq : Summable fun k => cvec C s v k ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => sq_sum_le_card_mul_sum_sq (s := s) (f := fun j => C k j * v j)) ?_
  refine Summable.mul_left _ (summable_sum fun j _ => ?_)
  simp_rw [mul_pow]
  exact (hC j).1.mul_right _

include hC hS in
theorem cvec_eq (i : ℕ) : cvec C s v i + ∑' k, T i k * cvec C s v k = if i ∈ s then v i else 0 := by
  have hsum : ∀ j ∈ s, Summable fun k => ((if i = k then 1 else 0) + T i k) * C k j * v j :=
    fun j _ => ((hC j).2 i).1.of_abs.mul_right _
  have h1 : ∑' k, ((if i = k then 1 else 0) + T i k) * cvec C s v k =
      ∑ j ∈ s, (if i = j then 1 else 0) * v j := by
    simp_rw [cvec, Finset.mul_sum, ← mul_assoc]
    rw [Summable.tsum_finsetSum hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tsum_mul_right, ((hC j).2 i).2]
  have hd : HasSum (fun k => (if i = k then 1 else 0) * cvec C s v k) (cvec C s v i) := by
    have := hasSum_single (f := fun k => (if i = k then (1 : ℝ) else 0) * cvec C s v k) i
      (fun k hk => by simp [Ne.symm hk])
    simpa using this
  have hT' : Summable fun k => T i k * cvec C s v k := by
    exact (tsum_mul_sq_le (hS.prod_factor i) (summable_cvec_sq hC s v)).1
  rw [← hd.tsum_eq, ← Summable.tsum_add hd.summable hT']
  simp_rw [← add_mul]
  rw [h1]
  simp_rw [ite_mul, one_mul, zero_mul]
  exact Finset.sum_ite_eq s i v

end res

end SharpLSI
