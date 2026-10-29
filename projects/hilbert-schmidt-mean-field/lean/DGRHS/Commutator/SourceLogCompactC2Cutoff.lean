import DGRHS.Commutator.SourceBoundedC2Fourier
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! RECORDS-ONLY / UNCOMPILED. No compiler request has evaluated this file.
A geometric cutoff constructor. No measure, weak equation, time trace, or
PDE conclusion is a premise. Native sources are bound in the sibling index.
The coarse bound 4*B*C is uniform over every radius n+1 and derivative order
0,1,2; B depends only on one fixed unit/two-radius bump, C only on the test.
This constructs compact C2 functions, not compact C-infinity functions. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

structure SourceLogCompactC2Approximation (φ : E → ℝ) where
  test : ℕ → E → ℝ
  smooth : ∀ n, ContDiff ℝ 2 (test n)
  compact : ∀ n, HasCompactSupport (test n)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  deriv_bound : ∀ n j, j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j (test n) x‖ ≤ bound
  local_eq : ∀ x, ∀ᶠ n in atTop, test n =ᶠ[𝓝 x] φ

def sourceLogRadiusBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (n : ℝ) + 1
  rOut := 2 * ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith

lemma sourceLogRadiusBump_eq_comp (n : ℕ) :
    (sourceLogRadiusBump (ι := ι) n : E → ℝ) =
      (sourceLogRadiusBump (ι := ι) 0 : E → ℝ) ∘
        (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hratio : 2 * ((n : ℝ) + 1) / ((n : ℝ) + 1) = 2 := by field_simp
  funext x
  simp only [ContDiffBump.apply, sourceLogRadiusBump, Nat.cast_zero,
    zero_add, mul_one, div_one, inv_one, sub_zero, one_smul,
    Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, hratio]

lemma sourceLogRadiusBump_uniform_derivatives :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n j, j ≤ 2 → ∀ x : E,
      ‖iteratedFDeriv ℝ j (sourceLogRadiusBump (ι := ι) n) x‖ ≤ B := by
  let χ := sourceLogRadiusBump (ι := ι) 0
  obtain ⟨B,hB,hχ⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv
    χ.contDiff 2
  refine ⟨B,hB,?_⟩
  intro n j hj x
  let L : E →L[ℝ] E := ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E
  have ha : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have ha1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    have hden : 1 ≤ (n : ℝ) + 1 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have he := mul_inv_cancel₀ hn
    have hh := mul_le_mul_of_nonneg_right hden ha
    nlinarith
  have hL : ‖L‖ ≤ 1 := by
    calc
      ‖L‖ = |((n : ℝ) + 1)⁻¹| * ‖ContinuousLinearMap.id ℝ E‖ := by
        simp only [L, norm_smul, Real.norm_eq_abs]
      _ ≤ ((n : ℝ) + 1)⁻¹ * 1 := by
        rw [abs_of_nonneg ha]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ha
      _ ≤ 1 := by simpa only [mul_one] using ha1
  rw [sourceLogRadiusBump_eq_comp]
  rw [L.iteratedFDeriv_comp_right (χ.contDiff : ContDiff ℝ 2 (χ : E → ℝ)) x
    (by exact_mod_cast hj)]
  have hnorm := (iteratedFDeriv ℝ j (χ : E → ℝ) (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hnorm
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (χ : E → ℝ) (L x)‖ * ‖L‖ ^ j := hnorm
    _ ≤ B * 1 := mul_le_mul (hχ j hj (L x))
      (pow_le_one₀ (norm_nonneg L) hL) (pow_nonneg (norm_nonneg L) j) hB
    _ = B := mul_one B

lemma exists_sourceLogCompactC2Approximation (φ : E → ℝ)
    (hφ : SourceBoundedC2Test φ) : Nonempty (SourceLogCompactC2Approximation φ) := by
  obtain ⟨B,hB,hχ⟩ := sourceLogRadiusBump_uniform_derivatives (ι := ι)
  obtain ⟨hφC,C,hC,hφb⟩ := hφ
  let ψ : ℕ → E → ℝ := fun n x => sourceLogRadiusBump (ι := ι) n x * φ x
  have hBC : 0 ≤ B*C := mul_nonneg hB hC
  refine ⟨⟨ψ, fun n => (sourceLogRadiusBump n).contDiff.mul hφC,
    fun n => (sourceLogRadiusBump n).hasCompactSupport.mul_right,
    4*B*C, by positivity, ?_, ?_⟩⟩
  · intro n j hj x
    have hmul := norm_iteratedFDeriv_mul_le
      ((sourceLogRadiusBump (ι := ι) n).contDiff : ContDiff ℝ 2 _) hφC x
      (n := j) (by exact_mod_cast hj)
    have hs : (∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (sourceLogRadiusBump (ι := ι) n) x‖ *
        ‖iteratedFDeriv ℝ (j-i) φ x‖) ≤
        ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      gcongr
      · exact hχ n i (hij.trans hj) x
      · exact hφb (j-i) ((Nat.sub_le _ _).trans hj) x
    have hsum : (∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * B * C) ≤ 4*B*C := by
      interval_cases j <;> norm_num [Finset.sum_range_succ] <;> nlinarith
    exact hmul.trans (hs.trans hsum)
  · intro x
    obtain ⟨N,hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hball : x ∈ Metric.ball (0 : E) ((n : ℝ) + 1) := by
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      simpa only [Metric.mem_ball, dist_zero_right] using
        (show ‖x‖ < (n : ℝ) + 1 by linarith)
    have he := (sourceLogRadiusBump (ι := ι) n).eventuallyEq_one_of_mem_ball hball
    filter_upwards [he] with y hy
    change sourceLogRadiusBump (ι := ι) n y * φ y = φ y
    change sourceLogRadiusBump (ι := ι) n y = (1 : ℝ) at hy
    rw [hy, one_mul]

end DGRHS.Commutator
