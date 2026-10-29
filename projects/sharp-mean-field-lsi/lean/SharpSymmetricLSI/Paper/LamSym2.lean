import SharpSymmetricLSI.Paper.LamSym1
import SharpSymmetricLSI.Paper.SubGaussSq
import SharpSymmetricLSI.Paper.ForceApprox9

/-!
# R33 groundwork: moments of the linear tests

`f_N = N^{-1/2} ∑_l g(X_l)` with `g = ∑ v_i e_i` bounded and centered; Hoeffding gives
`∫ e^{a f_N²} dμ^{⊗N} ≤ c_G` uniformly in `N`, hence all moments, and under `P_N` (Hölder with (5.6))
`sup_N E_{P_N} f_N⁴ < ∞`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `g = ∑ v_i e_i`. -/
noncomputable def linG (eC : ℕ → Torus d → ℝ) {J : ℕ} (v : Fin J → ℝ) (x : Torus d) : ℝ :=
  ∑ i, v i * eC (i + 1) x

theorem linTest_eq (eC : ℕ → Torus d → ℝ) (N J : ℕ) (v : Fin J → ℝ) (X : Config N d) :
    linTest eC N J v X = (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, linG eC v (X l) := by
  simp only [linTest, linCLM_apply, zC, linG, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem linTest_sq (eC : ℕ → Torus d → ℝ) (N J : ℕ) (v : Fin J → ℝ) (X : Config N d) :
    linTest eC N J v X ^ 2 = (∑ l, linG eC v (X l)) ^ 2 / N := by
  rw [linTest_eq, mul_pow, rpow_neg_half_sq, inv_mul_eq_div]

section
variable {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) {J : ℕ} (v : Fin J → ℝ)
include hφ

theorem measurable_linG : Measurable (linG eC v) :=
  Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_of_contDiff (hφ _))

theorem exists_bound_linG : ∃ B, 0 ≤ B ∧ ∀ x, |linG eC v x| ≤ B := by
  have h : ∀ i : Fin J, ∃ C, ∀ x, |eC (i + 1) x| ≤ C := fun i => exists_bound_of_contDiff (hφ _)
  choose C hC using h
  refine ⟨∑ i, |v i| * |C i|, by positivity, fun x => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hC i x).trans (le_abs_self _)) (abs_nonneg _)

/-- **Uniform square-exponential moment** of `f_N` under `μ^{⊗N}`. -/
theorem exp_moment_linTest {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hcent : ∀ j, ∫ x, eC (j + 1) x ∂μ = 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ X, ENNReal.ofReal (rexp (a * linTest eC N J v X ^ 2))
        ∂Measure.pi (fun _ : Fin N => μ) ≤ gaussSqConst := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_linG hφ v
  have h0 : ∫ x, linG eC v x ∂μ = 0 := by
    unfold linG
    rw [integral_finsetSum (f := fun (i : Fin J) (x : Torus d) => v i * eC (↑i + 1) x) _
      fun i _ => (integrable_of_bdd (measurable_of_contDiff (hφ _))
      fun x => (exists_bound_of_contDiff (hφ (i + 1))).choose_spec x).const_mul _]
    exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, hcent, mul_zero]
  set c : ℝ := 1 / (4 * (B ^ 2 + 1))
  have hc0 : 0 ≤ c := by positivity
  have hcB : c * B ^ 2 ≤ 1 / 4 := by
    have h1 : 0 < B ^ 2 + 1 := by positivity
    rw [show c * B ^ 2 = B ^ 2 / (4 * (B ^ 2 + 1)) by simp only [c]; field_simp]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  refine ⟨c / 2, by positivity, fun N hN => ?_⟩
  refine le_trans (lintegral_mono fun X => ?_) (lintegral_exp_sq_sum_le μ N (measurable_linG hφ v)
    hB h0 hc0 hcB)
  refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
  rw [linTest_sq]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := sq_nonneg (∑ l, linG eC v (X l))
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have : c / 2 * (∑ l, linG eC v (X l)) ^ 2 * ((N : ℝ) + 1) ≤
      c * (∑ l, linG eC v (X l)) ^ 2 * N := by
    have := mul_nonneg hc0 hs
    nlinarith
  linarith

end

end SharpLSI
