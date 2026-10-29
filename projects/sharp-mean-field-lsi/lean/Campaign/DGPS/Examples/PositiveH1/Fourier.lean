import Mathlib
import DGPS.Foundations.SobolevFourier

/-!
# Fourier coefficient and tail bounds (H1001)

For `a_n = n^(-7/4)` (`n ≥ 2`), `A = Σ a_n`, `A_M = Σ_{n>M} a_n`, `B_M² = 2π² Σ_{n>M} n^(-3/2)`,
`C_M = Σ_{n>M} a_n/(2πn)²`, we prove, for `M ≥ 2`,
`A ≤ 4/3`, `B_1 ≤ 2π`, `A_M ≤ (4/3) M^(-3/4)`, `B_M ≤ 2π M^(-1/4)`,
`C_M ≤ M^(-11/4)/(11π²)`, summability of the series, and that all three tails tend to zero.

Reading choices: `a n = 0` for `n < 2` (the series start at `n = 2`); tails are
`tsum`s over `n : ℕ` with the indicator `if M < n`; `B M` is the nonnegative square root.
-/

open Filter Topology

namespace DGPS.Examples.PositiveH1.Fourier

/-- `a_n = n^(-7/4)` for `n ≥ 2`, and `0` below. -/
noncomputable def a (n : ℕ) : ℝ := if 2 ≤ n then (n : ℝ) ^ (-(7 / 4 : ℝ)) else 0

/-- `A = Σ_{n ≥ 2} a_n`. -/
noncomputable def A : ℝ := ∑' n : ℕ, a n

/-- `A_M = Σ_{n > M} a_n`. -/
noncomputable def tailA (M : ℕ) : ℝ := ∑' n : ℕ, if M < n then a n else 0

/-- `B_M = √(2π² Σ_{n > M} n^(-3/2))`. -/
noncomputable def B (M : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi ^ 2 * ∑' n : ℕ, if M < n then (n : ℝ) ^ (-(3 / 2 : ℝ)) else 0)

/-- `C_M = Σ_{n > M} a_n / (2π n)²`. -/
noncomputable def C (M : ℕ) : ℝ :=
  ∑' n : ℕ, if M < n then a n / (2 * Real.pi * (n : ℝ)) ^ 2 else 0

/-- The generic tail series `Σ_{n > M} n^(-p)`. -/
noncomputable def tailSeries (p : ℝ) (M : ℕ) (n : ℕ) : ℝ := if M < n then (n : ℝ) ^ (-p) else 0

theorem tailSeries_nonneg (p : ℝ) (M n : ℕ) : 0 ≤ tailSeries p M n := by
  unfold tailSeries
  split_ifs
  · positivity
  · exact le_rfl

theorem tailSeries_partial (p : ℝ) (M K : ℕ) :
    ∑ n ∈ Finset.range (M + 1 + K), tailSeries p M n
      = ∑ i ∈ Finset.range K, ((M : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-p) := by
  rw [Finset.sum_range_add]
  have h0 : ∑ n ∈ Finset.range (M + 1), tailSeries p M n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have : n ≤ M := by simpa [Nat.lt_succ_iff] using hn
    simp [tailSeries, not_lt.mpr this]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have : M < M + 1 + i := by omega
  simp [tailSeries, this]
  congr 1
  ring

/-- Integral comparison: `Σ_{n>M} n^(-p) ≤ M^(1-p)/(p-1)` for `p > 1`, `M ≥ 1`. -/
theorem tailSeries_bound {p : ℝ} (hp : 1 < p) {M : ℕ} (hM : 1 ≤ M) :
    Summable (tailSeries p M) ∧ ∑' n, tailSeries p M n ≤ (M : ℝ) ^ (1 - p) / (p - 1) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hbound : ∀ K : ℕ, ∑ n ∈ Finset.range (M + 1 + K), tailSeries p M n
      ≤ (M : ℝ) ^ (1 - p) / (p - 1) := by
    intro K
    rw [tailSeries_partial]
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc (M : ℝ) (M + K)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hMpos hx.1) hxy (by linarith)
    have hsi := hanti.sum_le_integral
    have hint : ∫ x in (M : ℝ)..(M + K), x ^ (-p)
        = ((M + K : ℝ) ^ (-p + 1) - (M : ℝ) ^ (-p + 1)) / (-p + 1) := by
      apply integral_rpow
      right
      refine ⟨by linarith, ?_⟩
      rw [Set.mem_uIcc]
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · linarith
      · have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        linarith
    refine hsi.trans ?_
    rw [hint]
    have h1 : (0 : ℝ) ≤ (M + K : ℝ) ^ (-p + 1) := by positivity
    have h2 : (M : ℝ) ^ (-p + 1) / (p - 1) = (M : ℝ) ^ (1 - p) / (p - 1) := by
      rw [show -p + 1 = 1 - p by ring]
    have h3 : ((M + K : ℝ) ^ (-p + 1) - (M : ℝ) ^ (-p + 1)) / (-p + 1)
        = ((M : ℝ) ^ (-p + 1) - (M + K : ℝ) ^ (-p + 1)) / (p - 1) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]
      ring
    rw [h3, ← h2]
    gcongr
    linarith
  have hshift : ∀ N : ℕ, ∑ n ∈ Finset.range N, tailSeries p M n
      ≤ (M : ℝ) ^ (1 - p) / (p - 1) := by
    intro N
    calc ∑ n ∈ Finset.range N, tailSeries p M n
        ≤ ∑ n ∈ Finset.range (M + 1 + N), tailSeries p M n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Finset.mem_range] at hx ⊢
            omega
          · intro i _ _
            exact tailSeries_nonneg p M i
      _ ≤ _ := hbound N
  exact ⟨summable_of_sum_range_le (tailSeries_nonneg p M) hshift,
    Real.tsum_le_of_sum_range_le (tailSeries_nonneg p M) hshift⟩

/-- Rewriting `n^(-7/4)`-type terms as `tailSeries`. -/
theorem a_tail_eq {M : ℕ} (hM : 1 ≤ M) :
    (fun n : ℕ => if M < n then a n else 0) = tailSeries (7 / 4) M := by
  funext n
  unfold tailSeries a
  by_cases h : M < n
  · have : 2 ≤ n := by omega
    simp [h, this]
  · simp [h]

theorem a_eq_tail : a = tailSeries (7 / 4) 1 := by
  funext n
  unfold tailSeries a
  by_cases h : 1 < n
  · have : 2 ≤ n := by omega
    simp [h, this]
  · have : ¬ 2 ≤ n := by omega
    simp [h, this]

theorem C_term_eq {M : ℕ} (hM : 1 ≤ M) :
    (fun n : ℕ => if M < n then a n / (2 * Real.pi * (n : ℝ)) ^ 2 else 0)
      = fun n => (1 / (4 * Real.pi ^ 2)) * tailSeries (15 / 4) M n := by
  funext n
  unfold tailSeries
  by_cases h : M < n
  · have h2 : 2 ≤ n := by omega
    have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    simp only [h, ite_true, a, h2]
    rw [mul_pow, mul_pow, show (-(15 / 4 : ℝ)) = -(7 / 4) - 2 by norm_num,
      Real.rpow_sub hn, show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    field_simp
    norm_num
  · simp [h]

theorem tailSeries_tendsto {p : ℝ} (hp : 1 < p) :
    Tendsto (fun M : ℕ => ∑' n, tailSeries p M n) atTop (𝓝 0) := by
  have hb : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 - p) / (p - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := p - 1) (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := this.div_const (p - 1)
    simpa [Function.comp_def, show -(p - 1) = 1 - p by ring] using h2
  refine squeeze_zero' (Eventually.of_forall fun M => tsum_nonneg (tailSeries_nonneg p M)) ?_ hb
  filter_upwards [eventually_ge_atTop 1] with M hM using (tailSeries_bound hp hM).2

/-- The `A_M` tail bound. -/
theorem tailA_eq {M : ℕ} (hM : 1 ≤ M) : tailA M = ∑' n, tailSeries (7 / 4) M n := by
  unfold tailA
  rw [a_tail_eq hM]

theorem tailA_le {M : ℕ} (hM : 1 ≤ M) :
    tailA M ≤ 4 / 3 * (M : ℝ) ^ (-(3 / 4 : ℝ)) := by
  rw [tailA_eq hM]
  have := (tailSeries_bound (p := 7 / 4) (by norm_num) hM).2
  convert this using 1
  rw [show (1 - 7 / 4 : ℝ) = -(3 / 4) by norm_num]
  ring

theorem B_le {M : ℕ} (hM : 1 ≤ M) :
    B M ≤ 2 * Real.pi * (M : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hS := (tailSeries_bound (p := 3 / 2) (by norm_num) hM).2
  have hS' : ∑' n : ℕ, (if M < n then (n : ℝ) ^ (-(3 / 2 : ℝ)) else 0)
      ≤ 2 * (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have e : (fun n : ℕ => if M < n then (n : ℝ) ^ (-(3 / 2 : ℝ)) else 0)
        = tailSeries (3 / 2) M := rfl
    rw [e]
    convert hS using 1
    rw [show (1 - 3 / 2 : ℝ) = -(1 / 2) by norm_num]
    ring
  unfold B
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hsq : ((M : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 = (M : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMpos.le]
    norm_num
  calc 2 * Real.pi ^ 2 * ∑' n : ℕ, (if M < n then (n : ℝ) ^ (-(3 / 2 : ℝ)) else 0)
      ≤ 2 * Real.pi ^ 2 * (2 * (M : ℝ) ^ (-(1 / 2 : ℝ))) := by gcongr
    _ = (2 * Real.pi * (M : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 := by
      rw [mul_pow, hsq]; ring

theorem C_le {M : ℕ} (hM : 1 ≤ M) :
    C M ≤ (M : ℝ) ^ (-(11 / 4 : ℝ)) / (11 * Real.pi ^ 2) := by
  unfold C
  rw [C_term_eq hM, tsum_mul_left]
  have := (tailSeries_bound (p := 15 / 4) (by norm_num) hM).2
  rw [show (1 - 15 / 4 : ℝ) = -(11 / 4) by norm_num] at this
  have hpi : 0 < Real.pi ^ 2 := by positivity
  calc 1 / (4 * Real.pi ^ 2) * ∑' n, tailSeries (15 / 4) M n
      ≤ 1 / (4 * Real.pi ^ 2) * ((M : ℝ) ^ (-(11 / 4 : ℝ)) / (15 / 4 - 1)) := by gcongr
    _ = _ := by field_simp; norm_num

theorem tendsto_tailA : Tendsto tailA atTop (𝓝 0) := by
  have h := tailSeries_tendsto (p := 7 / 4) (by norm_num)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM using (tailA_eq hM).symm

theorem tendsto_B : Tendsto B atTop (𝓝 0) := by
  have h := tailSeries_tendsto (p := 3 / 2) (by norm_num)
  have h2 := ((h.const_mul (2 * Real.pi ^ 2)).sqrt)
  have h3 : Tendsto (fun M : ℕ => Real.sqrt (2 * Real.pi ^ 2 * ∑' n, tailSeries (3 / 2) M n))
      atTop (𝓝 0) := by simpa using h2
  exact h3

theorem tendsto_C : Tendsto C atTop (𝓝 0) := by
  have h := (tailSeries_tendsto (p := 15 / 4) (by norm_num)).const_mul (1 / (4 * Real.pi ^ 2))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  unfold C
  rw [C_term_eq hM, tsum_mul_left]

/-- H1001: Fourier coefficient and tail bounds (exact statement). -/
theorem fourier_coefficient_and_tail_bounds :
    Summable a ∧ A ≤ 4 / 3 ∧ B 1 ≤ 2 * Real.pi ∧
    (∀ M : ℕ, 1 ≤ M →
      Summable (tailSeries (3 / 2) M) ∧
      Summable (fun n : ℕ => if M < n then a n / (2 * Real.pi * (n : ℝ)) ^ 2 else 0)) ∧
    (∀ M : ℕ, 2 ≤ M →
      tailA M ≤ 4 / 3 * (M : ℝ) ^ (-(3 / 4 : ℝ)) ∧
      B M ≤ 2 * Real.pi * (M : ℝ) ^ (-(1 / 4 : ℝ)) ∧
      C M ≤ (M : ℝ) ^ (-(11 / 4 : ℝ)) / (11 * Real.pi ^ 2)) ∧
    Tendsto tailA atTop (𝓝 0) ∧ Tendsto B atTop (𝓝 0) ∧ Tendsto C atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, tendsto_tailA, tendsto_B, tendsto_C⟩
  · rw [a_eq_tail]; exact (tailSeries_bound (by norm_num) le_rfl).1
  · have h := (tailSeries_bound (p := 7 / 4) (by norm_num) (M := 1) le_rfl).2
    unfold A
    rw [a_eq_tail]
    norm_num at h ⊢
    linarith
  · have := B_le (M := 1) le_rfl
    simpa using this
  · intro M hM
    refine ⟨(tailSeries_bound (by norm_num) hM).1, ?_⟩
    rw [C_term_eq hM]
    exact (tailSeries_bound (p := 15 / 4) (by norm_num) hM).1.mul_left _
  · intro M hM
    exact ⟨tailA_le (by omega), B_le (by omega), C_le (by omega)⟩

/-! ### H1002: the uniform Fourier kernel and its exact coefficients

`R(x) = Σ_{n ≥ 2} a_n cos (2π n x)` on the circle `Torus 1`, `cos (2π n x)` being the real part
of the exponential monomial. Reading choices: the sup norm is the real `iSup` over the circle
(valid for every `M`, not only `M ≥ 2`); Fourier coefficients are `DGPS.fourierCoeff`. -/

open MeasureTheory

/-- The cosine mode `x ↦ cos (2π n x)` on the circle `𝕋 = Torus 1`, as the real part of the
exponential monomial `e_n`. -/
noncomputable def cosMode (n : ℕ) (x : Torus 1) : ℝ :=
  (UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) x).re

/-- The Fourier kernel `R(x) = Σ_{n ≥ 2} a_n cos (2π n x)` on the circle. -/
noncomputable def R (x : Torus 1) : ℝ := ∑' n : ℕ, a n * cosMode n x

/-- The finite sum `R_M(x) = Σ_{2 ≤ n ≤ M} a_n cos (2π n x)`. -/
noncomputable def RM (M : ℕ) (x : Torus 1) : ℝ :=
  ∑ n ∈ Finset.Icc 2 M, a n * cosMode n x

theorem torus_exists_lift (x : Torus 1) : ∃ z : ℝ, x = torusLift (fun _ => z) := by
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (x 0)
  refine ⟨z, ?_⟩
  funext i
  rw [Subsingleton.elim i 0]
  exact hz.symm

theorem cosMode_lift (n : ℕ) (z : ℝ) :
    cosMode n (torusLift (fun _ => z)) = Real.cos (2 * Real.pi * n * z) := by
  have h : UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) (torusLift (fun _ => z))
      = Complex.exp (((2 * Real.pi * n * z : ℝ) : ℂ) * Complex.I) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.univ_unique,
      Finset.prod_singleton, torusLift, SharpLSI.liftT]
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [cosMode, h, Complex.exp_ofReal_mul_I_re]

theorem a_nonneg (n : ℕ) : 0 ≤ a n := by
  unfold a; split_ifs
  · positivity
  · exact le_rfl

theorem a_summable : Summable a := fourier_coefficient_and_tail_bounds.1

theorem a_zero_of_lt {n : ℕ} (h : n < 2) : a n = 0 := by
  unfold a; simp [not_le.mpr h]

theorem cosMode_abs_le (n : ℕ) (x : Torus 1) : |cosMode n x| ≤ 1 := by
  obtain ⟨z, rfl⟩ := torus_exists_lift x
  rw [cosMode_lift]
  exact Real.abs_cos_le_one _

theorem cosMode_zero (n : ℕ) : cosMode n 0 = 1 := by
  have : (0 : Torus 1) = torusLift (fun _ => (0 : ℝ)) := by
    funext i; simp [torusLift, SharpLSI.liftT]
  rw [this, cosMode_lift]; simp

theorem cosMode_neg (n : ℕ) (x : Torus 1) : cosMode n (-x) = cosMode n x := by
  obtain ⟨z, rfl⟩ := torus_exists_lift x
  have : -(torusLift (fun _ => z) : Torus 1) = torusLift (fun _ => -z) := by
    funext i; simp [torusLift, SharpLSI.liftT]
  rw [this, cosMode_lift, cosMode_lift, mul_neg, Real.cos_neg]

theorem continuous_cosMode (n : ℕ) : Continuous (cosMode n) := by
  unfold cosMode
  exact Complex.continuous_re.comp (UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ))).continuous

theorem term_abs_le (n : ℕ) (x : Torus 1) : ‖a n * cosMode n x‖ ≤ a n := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (a_nonneg n)]
  calc a n * |cosMode n x| ≤ a n * 1 :=
        mul_le_mul_of_nonneg_left (cosMode_abs_le n x) (a_nonneg n)
    _ = a n := mul_one _

theorem summable_term (x : Torus 1) : Summable fun n => a n * cosMode n x :=
  Summable.of_norm_bounded a_summable (fun n => term_abs_le n x)

theorem continuous_R : Continuous R :=
  continuous_tsum (fun n => continuous_const.mul (continuous_cosMode n)) a_summable term_abs_le

theorem R_neg (x : Torus 1) : R (-x) = R x := by
  unfold R; simp only [cosMode_neg]

theorem R_zero : R 0 = A := by
  unfold R A; simp only [cosMode_zero, mul_one]

theorem R_sub_RM (M : ℕ) (x : Torus 1) :
    R x - RM M x = ∑' n : ℕ, if M < n then a n * cosMode n x else 0 := by
  have hs := summable_term x
  have hsplit : (fun n : ℕ => a n * cosMode n x) =
      (fun n => if n ≤ M then a n * cosMode n x else 0) +
      (fun n => if M < n then a n * cosMode n x else 0) := by
    funext n
    by_cases h : n ≤ M
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have h1 : Summable fun n : ℕ => if n ≤ M then a n * cosMode n x else 0 :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) (fun n hn => by
      have : ¬ n ≤ M := by simpa [Nat.lt_succ_iff] using hn
      simp [this])
  have h2 : Summable fun n : ℕ => if M < n then a n * cosMode n x else 0 := by
    refine Summable.of_norm_bounded a_summable (fun n => ?_)
    split_ifs
    · exact term_abs_le n x
    · simpa using a_nonneg n
  have h1sum : ∑' n : ℕ, (if n ≤ M then a n * cosMode n x else 0) = RM M x := by
    rw [tsum_eq_sum (s := Finset.range (M + 1)) (fun n hn => by
      have : ¬ n ≤ M := by simpa [Nat.lt_succ_iff] using hn
      simp [this])]
    unfold RM
    rw [Finset.sum_congr rfl (g := fun n => a n * cosMode n x) (fun n hn => by
      have : n ≤ M := by simpa [Nat.lt_succ_iff] using hn
      simp [this])]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_range]; omega
    · intro n _ hn
      have : n < 2 := by
        by_contra hc
        apply hn
        simp only [Finset.mem_Icc]
        constructor <;> [omega; (simp only [Finset.mem_range] at *; omega)]
      simp [a_zero_of_lt this]
  have : R x = (∑' n : ℕ, (if n ≤ M then a n * cosMode n x else 0)) +
      ∑' n : ℕ, if M < n then a n * cosMode n x else 0 := by
    unfold R
    rw [hsplit]
    exact h1.tsum_add h2
  linarith

theorem summable_tailA (M : ℕ) : Summable fun n : ℕ => if M < n then a n else 0 :=
  Summable.of_nonneg_of_le (fun n => by split_ifs <;> [exact a_nonneg n; exact le_rfl])
    (fun n => by split_ifs <;> [exact le_rfl; exact a_nonneg n]) a_summable

theorem abs_R_sub_RM_le (M : ℕ) (x : Torus 1) : |R x - RM M x| ≤ tailA M := by
  rw [R_sub_RM]
  have hb : ∀ n : ℕ, ‖if M < n then a n * cosMode n x else 0‖ ≤ if M < n then a n else 0 := by
    intro n
    split_ifs
    · exact term_abs_le n x
    · simp
  have hsum : Summable fun n : ℕ => ‖if M < n then a n * cosMode n x else 0‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (summable_tailA M)
  calc |∑' n : ℕ, if M < n then a n * cosMode n x else 0|
      ≤ ∑' n : ℕ, ‖if M < n then a n * cosMode n x else 0‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, (if M < n then a n else 0) := hsum.tsum_le_tsum hb (summable_tailA M)

theorem R_sub_RM_zero (M : ℕ) : R 0 - RM M 0 = tailA M := by
  rw [R_sub_RM]
  unfold tailA
  simp only [cosMode_zero, mul_one]

theorem tendstoUniformly_RM : TendstoUniformly RM R atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h := (tendsto_tailA).eventually (gt_mem_nhds hε)
  filter_upwards [h] with M hM x
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (abs_R_sub_RM_le M x) hM

theorem iSup_abs_R_sub_RM (M : ℕ) : ⨆ x : Torus 1, |R x - RM M x| = tailA M := by
  refine le_antisymm (ciSup_le fun x => abs_R_sub_RM_le M x) ?_
  have hb : BddAbove (Set.range fun x : Torus 1 => |R x - RM M x|) :=
    ⟨tailA M, by rintro _ ⟨x, rfl⟩; exact abs_R_sub_RM_le M x⟩
  refine le_trans ?_ (le_ciSup hb 0)
  rw [R_sub_RM_zero]
  exact le_abs_self _

theorem integral_mFourier (j : Fin 1 → ℤ) :
    ∫ x, UnitAddTorus.mFourier j x ∂haar 1 = if j = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 1))) 0 j
  simp only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
    ← UnitAddTorus.mFourier_add] at h
  rw [neg_zero, add_zero] at h
  rw [haar_eq_pi_haarAddCircle]
  have h' : ∫ x, UnitAddTorus.mFourier j x ∂(Measure.pi fun _ : Fin 1 =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) = if 0 = j then 1 else 0 := h
  rw [h']
  by_cases hj : j = 0 <;> simp [hj, eq_comm]

theorem fourierCoeff_eq_integral (u : Torus 1 → ℝ) (k : Fin 1 → ℤ) :
    fourierCoeff u k = ∫ x, UnitAddTorus.mFourier (-k) x * (u x : ℂ) ∂haar 1 := by
  rw [haar_eq_pi_haarAddCircle]; simp only [fourierCoeff, UnitAddTorus.mFourierCoeff, smul_eq_mul]; rfl

/-- The frequency `n ∈ ℤ` as a frequency on `𝕋¹`. -/
def freq (n : ℤ) : Fin 1 → ℤ := fun _ => n

theorem cosMode_ofReal (n : ℕ) (x : Torus 1) :
    (cosMode n x : ℂ) = (UnitAddTorus.mFourier (freq n) x + UnitAddTorus.mFourier (-freq n) x) / 2 := by
  rw [UnitAddTorus.mFourier_neg, Complex.add_conj, cosMode]
  unfold freq
  push_cast
  ring

theorem integrable_mFourier (j : Fin 1 → ℤ) :
    Integrable (fun x : Torus 1 => UnitAddTorus.mFourier j x) (haar 1) :=
  Integrable.mono' (integrable_const 1) (UnitAddTorus.mFourier j).continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simp [norm_mFourier_apply])

theorem termCoeff (n : ℕ) (k : Fin 1 → ℤ) :
    ∫ x, UnitAddTorus.mFourier (-k) x * ((a n * cosMode n x : ℝ) : ℂ) ∂haar 1 =
      ((a n / 2 : ℝ) : ℂ) * ((if -k + freq n = 0 then 1 else 0) +
        (if -k + -freq n = 0 then 1 else 0)) := by
  have hfun : ∀ y : Torus 1, UnitAddTorus.mFourier (-k) y * ((a n * cosMode n y : ℝ) : ℂ) =
      ((a n / 2 : ℝ) : ℂ) * (UnitAddTorus.mFourier (-k + freq n) y +
        UnitAddTorus.mFourier (-k + -freq n) y) := by
    intro y
    rw [Complex.ofReal_mul, cosMode_ofReal, UnitAddTorus.mFourier_add,
      UnitAddTorus.mFourier_add]
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_add (integrable_mFourier _) (integrable_mFourier _),
    integral_mFourier, integral_mFourier]

theorem integrable_term (n : ℕ) : Integrable (fun x : Torus 1 => a n * cosMode n x) (haar 1) :=
  Integrable.mono' (integrable_const (a n))
    (continuous_const.mul (continuous_cosMode n)).aestronglyMeasurable
    (Eventually.of_forall fun x => term_abs_le n x)

theorem fourierCoeff_R (k : Fin 1 → ℤ) :
    fourierCoeff R k = ∑' n : ℕ, ((a n / 2 : ℝ) : ℂ) * ((if -k + freq n = 0 then 1 else 0) +
        (if -k + -freq n = 0 then 1 else 0)) := by
  rw [fourierCoeff_eq_integral]
  have h1 : ∀ x : Torus 1, UnitAddTorus.mFourier (-k) x * (R x : ℂ) =
      ∑' n : ℕ, UnitAddTorus.mFourier (-k) x * ((a n * cosMode n x : ℝ) : ℂ) := by
    intro x
    unfold R
    rw [Complex.ofReal_tsum, tsum_mul_left]
  simp_rw [h1]
  have hint : ∀ n : ℕ, Integrable
      (fun x : Torus 1 => UnitAddTorus.mFourier (-k) x * ((a n * cosMode n x : ℝ) : ℂ))
      (haar 1) := fun n => integrable_mFourier_mul (integrable_term n) (-k)
  have hnorm : ∀ n x, ‖UnitAddTorus.mFourier (-k) x * ((a n * cosMode n x : ℝ) : ℂ)‖ ≤ a n := by
    intro n x
    rw [norm_mul, norm_mFourier_apply, one_mul, Complex.norm_real]
    exact term_abs_le n x
  have hsum : Summable fun n : ℕ => ∫ x, ‖UnitAddTorus.mFourier (-k) x *
      ((a n * cosMode n x : ℝ) : ℂ)‖ ∂haar 1 := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) a_summable
    calc ∫ x, ‖UnitAddTorus.mFourier (-k) x * ((a n * cosMode n x : ℝ) : ℂ)‖ ∂haar 1
        ≤ ∫ _x, a n ∂haar 1 :=
          integral_mono (hint n).norm (integrable_const _) (hnorm n)
      _ = a n := by simp
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [termCoeff]

theorem freq_cond1 (m n : ℕ) : -freq m + freq n = 0 ↔ m = n := by
  constructor
  · intro h
    have := congrFun h 0
    simp [freq] at this
    omega
  · rintro rfl; funext i; simp [freq]

theorem freq_cond2 (m n : ℕ) : -freq m + -freq n = 0 ↔ m = 0 ∧ n = 0 := by
  constructor
  · intro h
    have := congrFun h 0
    simp [freq] at this
    omega
  · rintro ⟨rfl, rfl⟩; funext i; simp [freq]

theorem freq_cond3 (m n : ℕ) : freq m + freq n = 0 ↔ m = 0 ∧ n = 0 := by
  constructor
  · intro h
    have := congrFun h 0
    simp [freq] at this
    omega
  · rintro ⟨rfl, rfl⟩; funext i; simp [freq]

theorem freq_cond4 (m n : ℕ) : freq m + -freq n = 0 ↔ m = n := by
  constructor
  · intro h
    have := congrFun h 0
    simp [freq] at this
    omega
  · rintro rfl; funext i; simp [freq]

theorem fourierCoeff_R_pos (m : ℕ) : fourierCoeff R (freq m) = ((a m / 2 : ℝ) : ℂ) := by
  rw [fourierCoeff_R]
  rw [tsum_eq_single m]
  · by_cases hm : m = 0
    · subst hm
      simp [a_zero_of_lt (show 0 < 2 by norm_num)]
    · simp [freq_cond2, hm]
  · intro n hn
    have h1 : ¬ (-freq m + freq n = 0) := fun h => hn ((freq_cond1 m n).1 h).symm
    have h2 : ¬ (-freq m + -freq n = 0) := fun h => hn (by have := (freq_cond2 m n).1 h; omega)
    simp [h1, h2]

theorem fourierCoeff_R_neg (m : ℕ) : fourierCoeff R (-freq m) = ((a m / 2 : ℝ) : ℂ) := by
  rw [fourierCoeff_R]
  rw [tsum_eq_single m]
  · by_cases hm : m = 0
    · subst hm
      simp [a_zero_of_lt (show 0 < 2 by norm_num)]
    · simp [freq_cond3, hm]
  · intro n hn
    have h1 : ¬ (freq m + freq n = 0) := fun h => hn (by
      have := (freq_cond3 m n).1 h; omega)
    have h2 : ¬ (freq m + -freq n = 0) := fun h => hn ((freq_cond4 m n).1 h).symm
    simp [h1, h2]

theorem R_lift (z : ℝ) :
    R (torusLift fun _ => z) = ∑' n : ℕ, a n * Real.cos (2 * Real.pi * n * z) := by
  unfold R; simp only [cosMode_lift]

theorem fourierCoeff_R_zero : fourierCoeff R 0 = 0 := by
  have h : (0 : Fin 1 → ℤ) = freq 0 := by funext i; simp [freq]
  rw [h]
  have := fourierCoeff_R_pos 0
  simpa [a_zero_of_lt (show 0 < 2 by norm_num)] using this

theorem integral_R : ∫ x, R x ∂haar 1 = 0 := by
  have h := fourierCoeff_R_zero
  rw [fourierCoeff_eq_integral] at h
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.coe_one, Pi.one_apply,
    one_mul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- H1002: Uniform Fourier kernel and exact coefficients (exact statement).

`R(x) = Σ_{n ≥ 2} a_n cos (2π n x)` on the circle `Torus 1`; `RM M` is the partial sum over
`2 ≤ n ≤ M`. The Fourier coefficients are those of `DGPS.fourierCoeff` (frequency `k : Fin 1 → ℤ`,
complex valued); the sup norm of `R - R_M` is the real `iSup` over the circle. -/
theorem uniform_fourier_kernel_and_exact_coefficients :
    TendstoUniformly RM R atTop ∧ Continuous R ∧ (∀ x : Torus 1, R (-x) = R x) ∧ R 0 = A ∧
    (∀ z : ℝ, R (torusLift fun _ => z) = ∑' n : ℕ, a n * Real.cos (2 * Real.pi * n * z)) ∧
    ∫ x, R x ∂haar 1 = 0 ∧
    (∀ n : ℕ, 2 ≤ n →
      fourierCoeff R (fun _ => (n : ℤ)) = ((a n / 2 : ℝ) : ℂ) ∧
      fourierCoeff R (fun _ => -(n : ℤ)) = ((a n / 2 : ℝ) : ℂ)) ∧
    fourierCoeff R (fun _ => (0 : ℤ)) = 0 ∧ fourierCoeff R (fun _ => (1 : ℤ)) = 0 ∧
    fourierCoeff R (fun _ => (-1 : ℤ)) = 0 ∧
    (∀ M : ℕ, ⨆ x : Torus 1, |R x - RM M x| = tailA M) := by
  refine ⟨tendstoUniformly_RM, continuous_R, R_neg, R_zero, R_lift, integral_R, ?_, ?_, ?_, ?_,
    iSup_abs_R_sub_RM⟩
  · intro n _
    exact ⟨fourierCoeff_R_pos n, fourierCoeff_R_neg n⟩
  · exact fourierCoeff_R_zero
  · have := fourierCoeff_R_pos 1
    have e : (fun _ : Fin 1 => (1 : ℤ)) = freq (1 : ℕ) := by funext i; simp [freq]
    rw [e]
    simpa [a_zero_of_lt (show 1 < 2 by norm_num)] using this
  · have := fourierCoeff_R_neg 1
    have e : (fun _ : Fin 1 => (-1 : ℤ)) = -freq (1 : ℕ) := by funext i; simp [freq]
    rw [e]
    simpa [a_zero_of_lt (show 1 < 2 by norm_num)] using this

/-! ### H1003: weak derivative of the infinite Fourier kernel -/

/-- The sine mode. -/
noncomputable def sinMode (n : ℕ) (x : Torus 1) : ℝ :=
  (UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) x).im

noncomputable def cosZ (k : ℤ) (x : Torus 1) : ℝ := (UnitAddTorus.mFourier (freq k) x).re

theorem continuous_sinMode (n : ℕ) : Continuous (sinMode n) :=
  Complex.continuous_im.comp (UnitAddTorus.mFourier _).continuous

theorem continuous_cosZ (k : ℤ) : Continuous (cosZ k) :=
  Complex.continuous_re.comp (UnitAddTorus.mFourier _).continuous

theorem integral_cosZ (k : ℤ) : ∫ x, cosZ k x ∂haar 1 = if k = 0 then 1 else 0 := by
  have h := integral_mFourier (freq k)
  have hi := integrable_mFourier (freq k)
  have h3 : ∫ x, cosZ k x ∂haar 1 = (∫ x, UnitAddTorus.mFourier (freq k) x ∂haar 1).re := by
    have := integral_re hi
    simpa [cosZ] using this
  rw [h3, h]
  by_cases hk : k = 0
  · subst hk
    have : freq 0 = 0 := by funext i; simp [freq]
    simp [this]
  · have : freq k ≠ 0 := fun h' => hk (by simpa [freq] using congrFun h' 0)
    simp [this, hk]

theorem sinMode_mul (m n : ℕ) (x : Torus 1) :
    sinMode m x * sinMode n x = (cosZ ((m : ℤ) - n) x - cosZ ((m : ℤ) + n) x) / 2 := by
  have e1 : UnitAddTorus.mFourier (freq ((m : ℤ) - n)) x
      = UnitAddTorus.mFourier (fun _ : Fin 1 => (m : ℤ)) x *
        (starRingEnd ℂ) (UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) x) := by
    rw [← UnitAddTorus.mFourier_neg, ← UnitAddTorus.mFourier_add]
    congr 2
  have e2 : UnitAddTorus.mFourier (freq ((m : ℤ) + n)) x
      = UnitAddTorus.mFourier (fun _ : Fin 1 => (m : ℤ)) x *
        UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) x := by
    rw [← UnitAddTorus.mFourier_add]
    rfl
  unfold cosZ sinMode
  rw [e1, e2]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem integral_sinMode_mul (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∫ x, sinMode m x * sinMode n x ∂haar 1 = if m = n then 1 / 2 else 0 := by
  have hc : ∀ k, Integrable (cosZ k) (haar 1) := fun k =>
    (memLp_two_of_continuous (continuous_cosZ k)).integrable one_le_two
  simp_rw [sinMode_mul]
  rw [integral_div, integral_sub (hc _) (hc _), integral_cosZ, integral_cosZ]
  have h1 : ((m : ℤ) + n = 0) ↔ False := by simp; omega
  have h2 : ((m : ℤ) - n = 0) ↔ m = n := by omega
  simp only [h1, h2]
  by_cases h : m = n <;> simp [h]


theorem integrable_sin_mul (m n : ℕ) :
    Integrable (fun x => sinMode m x * sinMode n x) (haar 1) :=
  (memLp_two_of_continuous ((continuous_sinMode m).mul (continuous_sinMode n))).integrable one_le_two

theorem integral_sq_sum_sin (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    ∫ x, (∑ n ∈ S, c n * sinMode n x) ^ 2 ∂haar 1 = (1 / 2) * ∑ n ∈ S, c n ^ 2 := by
  have e : ∀ x, (∑ n ∈ S, c n * sinMode n x) ^ 2
      = ∑ m ∈ S, ∑ n ∈ S, (c m * c n) * (sinMode m x * sinMode n x) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_sin_mul m n).const_mul _]
  have : ∀ m ∈ S, ∫ x, ∑ n ∈ S, (c m * c n) * (sinMode m x * sinMode n x) ∂haar 1
      = (1 / 2) * c m ^ 2 := by
    intro m hm
    rw [integral_finsetSum _ fun n _ => (integrable_sin_mul m n).const_mul _]
    have : ∀ n ∈ S, ∫ x, (c m * c n) * (sinMode m x * sinMode n x) ∂haar 1
        = if m = n then (1 / 2) * c m ^ 2 else 0 := by
      intro n hn
      rw [integral_const_mul, integral_sinMode_mul m n (hS m hm) (hS n hn)]
      by_cases h : m = n
      · subst h; simp; ring
      · simp [h]
    rw [Finset.sum_congr rfl this]
    simp [hm]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]


/-- `R_M′(x) = -2π Σ_{2 ≤ n ≤ M} n^(-3/4) sin (2π n x)`. -/
noncomputable def dRM (M : ℕ) (x : Torus 1) : ℝ :=
  -(2 * Real.pi) * ∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-(3 / 4 : ℝ)) * sinMode n x

noncomputable def dcoef (n : ℕ) : ℝ := -(2 * Real.pi) * (n : ℝ) ^ (-(3 / 4 : ℝ))

theorem dRM_eq (M : ℕ) (x : Torus 1) :
    dRM M x = ∑ n ∈ Finset.Icc 2 M, dcoef n * sinMode n x := by
  unfold dRM dcoef
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem dcoef_sq (n : ℕ) : dcoef n ^ 2 = 4 * Real.pi ^ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  unfold dcoef
  have h : ((n : ℝ) ^ (-(3 / 4 : ℝ))) ^ 2 = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [mul_pow, neg_sq, mul_pow, h]
  ring

theorem continuous_dRM (M : ℕ) : Continuous (dRM M) := by
  unfold dRM
  exact continuous_const.mul (continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_sinMode n))

theorem memLp_dRM (M : ℕ) : MemLp (dRM M) 2 (haar 1) := memLp_two_of_continuous (continuous_dRM M)

theorem dRM_sub_eq {L M : ℕ} (h : L ≤ M) (x : Torus 1) :
    dRM M x - dRM L x = ∑ n ∈ Finset.Icc 2 M \ Finset.Icc 2 L, dcoef n * sinMode n x := by
  rw [dRM_eq, dRM_eq, ← Finset.sum_sdiff (Finset.Icc_subset_Icc_right h)]
  ring

theorem integral_sq_dRM_sub {L M : ℕ} (hL : 1 ≤ L) (h : L ≤ M) :
    ∫ x, (dRM M x - dRM L x) ^ 2 ∂haar 1
      = 2 * Real.pi ^ 2 * ∑ n ∈ Finset.range (M + 1), tailSeries (3 / 2) L n := by
  simp_rw [dRM_sub_eq h]
  rw [integral_sq_sum_sin _ (fun n hn => by simp at hn; omega)]
  have hS : Finset.Icc 2 M \ Finset.Icc 2 L = (Finset.range (M + 1)).filter (fun n => L < n) := by
    ext n; simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
  rw [hS, Finset.sum_filter]
  simp_rw [dcoef_sq]
  have : ∀ n ∈ Finset.range (M + 1), (if L < n then 4 * Real.pi ^ 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) else 0)
      = 4 * Real.pi ^ 2 * tailSeries (3 / 2) L n := by
    intro n _; unfold tailSeries; split_ifs <;> simp
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  ring


theorem norm_Lp_sq (g : Lp ℝ 2 (haar 1)) : ‖g‖ ^ 2 = ∫ x, (g x) ^ 2 ∂haar 1 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

/-- The `L²` class of `dRM M`. -/
noncomputable def fL (M : ℕ) : Lp ℝ 2 (haar 1) := (memLp_dRM M).toLp (dRM M)

theorem norm_fL_sub_sq {L M : ℕ} (hL : 1 ≤ L) (h : L ≤ M) :
    ‖fL M - fL L‖ ^ 2 = 2 * Real.pi ^ 2 * ∑ n ∈ Finset.range (M + 1), tailSeries (3 / 2) L n := by
  rw [norm_Lp_sq, ← integral_sq_dRM_sub hL h]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (fL M) (fL L), (memLp_dRM M).coeFn_toLp, (memLp_dRM L).coeFn_toLp]
    with x h1 h2 h3
  simp only [fL] at h1 ⊢
  rw [h1]
  simp only [Pi.sub_apply, h2, h3]

theorem tailSeries_anti {p : ℝ} {N n : ℕ} (h : N ≤ n) (k : ℕ) :
    tailSeries p n k ≤ tailSeries p N k := by
  unfold tailSeries
  by_cases h1 : n < k
  · simp [h1, show N < k by omega]
  · simp only [h1, ite_false]
    split_ifs <;> first | exact le_rfl | positivity

theorem tsum_tailSeries_anti {N n : ℕ} (hN : 1 ≤ N) (h : N ≤ n) :
    ∑' k, tailSeries (3 / 2) n k ≤ ∑' k, tailSeries (3 / 2) N k :=
  Summable.tsum_le_tsum (fun k => tailSeries_anti h k)
    (tailSeries_bound (by norm_num) (hN.trans h)).1 (tailSeries_bound (by norm_num) hN).1

theorem B_eq (M : ℕ) : B M = Real.sqrt (2 * Real.pi ^ 2 * ∑' n, tailSeries (3 / 2) M n) := rfl

theorem norm_fL_sub_le {N n m : ℕ} (hn : N + 1 ≤ n) (hnm : n ≤ m) : ‖fL m - fL n‖ ≤ B (N + 1) := by
  have hn1 : 1 ≤ n := by omega
  rw [B_eq]
  apply Real.le_sqrt_of_sq_le
  rw [norm_fL_sub_sq hn1 hnm]
  have hs := (tailSeries_bound (p := 3 / 2) (by norm_num) hn1).1
  have h1 : ∑ k ∈ Finset.range (m + 1), tailSeries (3 / 2) n k ≤ ∑' k, tailSeries (3 / 2) n k :=
    hs.sum_le_tsum _ (fun k _ => tailSeries_nonneg _ _ _)
  have h2 := tsum_tailSeries_anti (N := N + 1) (n := n) (by omega) hn
  have : (0 : ℝ) ≤ 2 * Real.pi ^ 2 := by positivity
  nlinarith

theorem cauchySeq_fL : CauchySeq (fun k : ℕ => fL (k + 1)) := by
  refine cauchySeq_of_le_tendsto_0 (fun N => B (N + 1)) (fun n m N hn hm => ?_) ?_
  · rw [dist_eq_norm]
    rcases le_total n m with h | h
    · rw [← norm_neg, neg_sub]
      exact norm_fL_sub_le (N := N) (n := n + 1) (m := m + 1) (by omega) (by omega)
    · exact norm_fL_sub_le (N := N) (n := m + 1) (m := n + 1) (by omega) (by omega)
  · exact tendsto_B.comp (tendsto_add_atTop_nat 1)


theorem exists_limit_fL : ∃ G : Lp ℝ 2 (haar 1), ∀ L : ℕ, 1 ≤ L → ‖G - fL L‖ = B L := by
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete cauchySeq_fL
  refine ⟨G, fun L hL => ?_⟩
  have h1 : Tendsto (fun k : ℕ => ‖fL (k + 1) - fL L‖ ^ 2) atTop (𝓝 (‖G - fL L‖ ^ 2)) :=
    ((hG.sub_const (fL L)).norm).pow 2
  have hs := (tailSeries_bound (p := 3 / 2) (by norm_num) hL).1
  have h2 : Tendsto (fun k : ℕ => 2 * Real.pi ^ 2 *
      ∑ n ∈ Finset.range (k + 1 + 1), tailSeries (3 / 2) L n) atTop
      (𝓝 (2 * Real.pi ^ 2 * ∑' n, tailSeries (3 / 2) L n)) :=
    ((hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat (1 + 1))).const_mul _
  have h3 : (fun k : ℕ => ‖fL (k + 1) - fL L‖ ^ 2) =ᶠ[atTop] fun k : ℕ => 2 * Real.pi ^ 2 *
      ∑ n ∈ Finset.range (k + 1 + 1), tailSeries (3 / 2) L n := by
    filter_upwards [eventually_ge_atTop L] with k hk
    exact norm_fL_sub_sq hL (by omega)
  have h4 := tendsto_nhds_unique_of_eventuallyEq h1 h2 h3
  rw [B_eq, ← h4, Real.sqrt_sq (norm_nonneg _)]


theorem sinMode_neg (n : ℕ) (x : Torus 1) : sinMode n (-x) = - sinMode n x := by
  have : UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) (-x)
      = (starRingEnd ℂ) (UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) x) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [fourier_apply (x := -x i), smul_neg, fourier_neg']
  unfold sinMode
  rw [this]; simp

theorem dRM_neg (M : ℕ) (x : Torus 1) : dRM M (-x) = - dRM M x := by
  unfold dRM
  simp_rw [sinMode_neg, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The `L²` limit `R′` of the derivatives `R_M′` (a fixed representative). -/
noncomputable def dR : Torus 1 → ℝ := ⇑(Classical.choose exists_limit_fL)

theorem norm_G_sub (L : ℕ) (hL : 1 ≤ L) : ‖Classical.choose exists_limit_fL - fL L‖ = B L :=
  Classical.choose_spec exists_limit_fL L hL

theorem memLp_dR : MemLp dR 2 (haar 1) := Lp.memLp _

theorem integral_sq_dR_sub {L : ℕ} (hL : 1 ≤ L) :
    ∫ x, (dR x - dRM L x) ^ 2 ∂haar 1 = B L ^ 2 := by
  rw [← norm_G_sub L hL, norm_Lp_sq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (Classical.choose exists_limit_fL) (fL L),
    (memLp_dRM L).coeFn_toLp] with x h1 h2
  rw [h1]
  simp only [Pi.sub_apply, fL, h2, dR]

theorem eLpNorm_dR_sub {L : ℕ} (hL : 1 ≤ L) :
    eLpNorm (fun x => dR x - dRM L x) 2 (haar 1) = ENNReal.ofReal (B L) := by
  have h1 := norm_G_sub L hL
  rw [Lp.norm_def] at h1
  have hne := Lp.eLpNorm_ne_top (Classical.choose exists_limit_fL - fL L)
  have h2 : eLpNorm (⇑(Classical.choose exists_limit_fL - fL L)) 2 (haar 1)
      = eLpNorm (fun x => dR x - dRM L x) 2 (haar 1) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (Classical.choose exists_limit_fL) (fL L),
      (memLp_dRM L).coeFn_toLp] with x h1 h2
    rw [h1]
    simp only [Pi.sub_apply, fL, h2, dR]
  rw [h2] at h1 hne
  rw [← h1, ENNReal.ofReal_toReal hne]


theorem dRM_one (x : Torus 1) : dRM 1 x = 0 := by simp [dRM]

theorem integral_sq_dR :
    ∫ x, dR x ^ 2 ∂haar 1
      = 2 * Real.pi ^ 2 * ∑' n : ℕ, if 2 ≤ n then (n : ℝ) ^ (-(3 / 2 : ℝ)) else 0 := by
  have h := integral_sq_dR_sub (L := 1) le_rfl
  simp only [dRM_one, sub_zero] at h
  rw [h, B_eq, Real.sq_sqrt (by
    have : 0 ≤ ∑' n, tailSeries (3 / 2) 1 n := tsum_nonneg fun n => tailSeries_nonneg _ _ _
    positivity)]
  congr 1

theorem dR_odd : ∀ᵐ x ∂haar 1, dR (-x) = - dR x := by
  have : (haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  have hmp : MeasurePreserving (fun x : Torus 1 => -x) (haar 1) (haar 1) :=
    Measure.measurePreserving_neg _
  have hle : ∀ M : ℕ, 1 ≤ M →
      eLpNorm (fun x => dR x + dR (-x)) 2 (haar 1) ≤ 2 * ENNReal.ofReal (B M) := by
    intro M hM
    have hm : AEStronglyMeasurable (fun x => dR x - dRM M x) (haar 1) :=
      (memLp_dR.sub (memLp_dRM M)).aestronglyMeasurable
    have e : (fun x => dR x + dR (-x)) = (fun x => dR x - dRM M x) +
        (fun x => dR x - dRM M x) ∘ (fun x : Torus 1 => -x) := by
      funext x; simp only [Pi.add_apply, Function.comp_apply, dRM_neg]; ring
    rw [e]
    refine (eLpNorm_add_le one_le_two).trans ?_
    rw [eLpNorm_comp_measurePreserving hm hmp, eLpNorm_dR_sub hM, two_mul]
  have hlim : Tendsto (fun M : ℕ => 2 * ENNReal.ofReal (B M)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := 2) (ENNReal.tendsto_ofReal tendsto_B)
      (Or.inr ENNReal.ofNat_ne_top)
    simpa using this
  have h0 : eLpNorm (fun x => dR x + dR (-x)) 2 (haar 1) ≤ 0 :=
    ge_of_tendsto hlim (by filter_upwards [eventually_ge_atTop 1] with M hM using hle M hM)
  have h1 := (eLpNorm_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ 0)).mp (le_antisymm h0 bot_le)
  filter_upwards [h1] with x hx
  simp only [Pi.zero_apply] at hx
  linarith


theorem sinMode_lift (n : ℕ) (z : ℝ) :
    sinMode n (torusLift (fun _ => z)) = Real.sin (2 * Real.pi * n * z) := by
  have h : UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) (torusLift (fun _ => z))
      = Complex.exp (((2 * Real.pi * n * z : ℝ) : ℂ) * Complex.I) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.univ_unique,
      Finset.prod_singleton, torusLift, SharpLSI.liftT]
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [sinMode, h, Complex.exp_ofReal_mul_I_im]

theorem isSmoothPeriodic_cosMode (n : ℕ) : IsSmoothPeriodic (cosMode n) :=
  isSmoothPeriodic_re_mFourier _

theorem coordPartial_cosMode (n : ℕ) (x : Torus 1) :
    coordPartial 0 (cosMode n) x = -(2 * Real.pi * n) * sinMode n x := by
  have h := coordPartial_re_mFourier (d := 1) (fun _ : Fin 1 => (n : ℤ)) 0 x
  have h' : coordPartial 0 (cosMode n) x = _ := h
  rw [h']
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    sinMode]
  simp

theorem isSmoothPeriodic_RM (M : ℕ) : IsSmoothPeriodic (RM M) := by
  unfold IsSmoothPeriodic RM
  have : ((fun x => ∑ n ∈ Finset.Icc 2 M, a n * cosMode n x) ∘ torusLift)
      = fun y => ∑ n ∈ Finset.Icc 2 M, a n * (cosMode n ∘ torusLift) y := by
    funext y; simp
  rw [this]
  exact ContDiff.sum fun n _ => contDiff_const.mul (isSmoothPeriodic_cosMode n)

theorem coordPartial_RM (M : ℕ) (x : Torus 1) : coordPartial 0 (RM M) x = dRM M x := by
  unfold coordPartial RM
  have : ((fun x => ∑ n ∈ Finset.Icc 2 M, a n * cosMode n x) ∘ torusLift)
      = fun y => ∑ n ∈ Finset.Icc 2 M, a n * (cosMode n ∘ torusLift) y := by
    funext y; simp
  rw [this]
  have hd : ∀ n ∈ Finset.Icc 2 M, DifferentiableAt ℝ (fun y => a n * (cosMode n ∘ torusLift) y)
      (SharpLSI.secT x) := fun n _ =>
    (contDiff_const.mul (isSmoothPeriodic_cosMode n)).differentiable (by simp) _
  rw [fderiv_fun_sum hd]
  simp only [sum_apply]
  have e : ∀ n ∈ Finset.Icc 2 M, (fderiv ℝ (fun y => a n * (cosMode n ∘ torusLift) y)
      (SharpLSI.secT x)) (Pi.single 0 1) = a n * coordPartial 0 (cosMode n) x := by
    intro n hn
    rw [fderiv_const_mul ((isSmoothPeriodic_cosMode n).differentiable (by simp) _)]
    rfl
  rw [Finset.sum_congr rfl e]
  unfold dRM
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [coordPartial_cosMode]
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have han : a n * n = (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
    unfold a
    rw [ite_eq_left_iff.mpr (fun h => absurd hn2 h)]
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [show (n : ℝ) ^ (-(7 / 4 : ℝ)) * n = (n : ℝ) ^ (-(7 / 4 : ℝ)) * (n : ℝ) ^ (1 : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add hpos]
    norm_num
  rw [← han]
  ring

theorem continuous_RM (M : ℕ) : Continuous (RM M) := by
  unfold RM
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (isSmoothPeriodic_cosMode n).continuous_torus

theorem ibp_RM (M : ℕ) {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∫ x, RM M x * coordPartial 0 φ x ∂haar 1 = -∫ x, dRM M x * φ x ∂haar 1 := by
  rw [integral_mul_coordPartial_of_smooth (isSmoothPeriodic_RM M) hφ 0]
  simp_rw [coordPartial_RM]

theorem lintegral_RM_sub_le (M : ℕ) :
    ∫⁻ y, ‖RM M y - R y‖ₑ ∂haar 1 ≤ ENNReal.ofReal (tailA M) := by
  calc ∫⁻ y, ‖RM M y - R y‖ₑ ∂haar 1 ≤ ∫⁻ _y, ENNReal.ofReal (tailA M) ∂haar 1 := by
        refine lintegral_mono fun y => ?_
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact abs_R_sub_RM_le M y
    _ = ENNReal.ofReal (tailA M) := by simp

theorem lintegral_dRM_sub_le {M : ℕ} (hM : 1 ≤ M) :
    ∫⁻ y, ‖dRM M y - dR y‖ₑ ∂haar 1 ≤ ENNReal.ofReal (B M) := by
  have h1 : eLpNorm (fun y => dR y - dRM M y) 1 (haar 1)
      ≤ eLpNorm (fun y => dR y - dRM M y) 2 (haar 1) :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  rw [eLpNorm_dR_sub hM, eLpNorm_one_eq_lintegral_enorm] at h1
  · refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun y => ?_
    rw [enorm_sub_rev]
  · exact (memLp_dR.sub (memLp_dRM M)).aestronglyMeasurable

theorem memLp_grad_dR : MemLp (fun x => (EuclideanSpace.single (0 : Fin 1) (dR x) : Tangent 1))
    2 (haar 1) := by
  refine memLp_dR.mono ?_ (Eventually.of_forall fun x => ?_)
  · have hc : Continuous (fun t : ℝ => (EuclideanSpace.single (0 : Fin 1) t : Tangent 1)) :=
      (Isometry.of_dist_eq fun a b => PiLp.dist_single_same 2 (fun _ : Fin 1 => ℝ) 0 a b).continuous
    exact hc.comp_aestronglyMeasurable memLp_dR.aestronglyMeasurable
  · simp

theorem weak_gradient_R :
    IsWeakGradient R (fun x => (EuclideanSpace.single (0 : Fin 1) (dR x) : Tangent 1)) := by
  refine ⟨memLp_two_of_continuous continuous_R, memLp_grad_dR, ?_⟩
  intro φ hφ j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  obtain ⟨C1, hC1⟩ := exists_abs_le_of_continuous (hφ.continuous_coordPartial 0)
  obtain ⟨C2, hC2⟩ := exists_abs_le_of_continuous hφ.continuous_torus
  have hint : ∀ {f : Torus 1 → ℝ}, Continuous f → Integrable f (haar 1) := fun hf =>
    (memLp_two_of_continuous hf).integrable one_le_two
  have hA : Tendsto (fun M => ENNReal.ofReal (tailA M)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_tailA
  have hBt : Tendsto (fun M => ENNReal.ofReal (B M)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_B
  have T1 := tendsto_integral_mul_of_lintegral (l := atTop) (F := fun M => RM M) (f := R)
    (ψ := coordPartial 0 φ) (C := C1) (fun M => hint (continuous_RM M)) (hint continuous_R)
    (hφ.continuous_coordPartial 0) hC1
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA
      (fun _ => bot_le) lintegral_RM_sub_le)
  have T2 := tendsto_integral_mul_of_lintegral (l := atTop) (F := fun M => dRM M) (f := dR)
    (ψ := φ) (C := C2) (fun M => hint (continuous_dRM M))
    (memLp_dR.integrable one_le_two) hφ.continuous_torus hC2
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hBt
      (Eventually.of_forall fun _ => bot_le)
      (Filter.eventually_atTop.2 ⟨1, fun M hM => lintegral_dRM_sub_le hM⟩))
  have e : ∀ M, ∫ x, RM M x * coordPartial 0 φ x ∂haar 1 = -∫ x, dRM M x * φ x ∂haar 1 :=
    fun M => ibp_RM M hφ
  have T2' := T2.neg
  simp_rw [← e] at T2'
  have := tendsto_nhds_unique T1 T2'
  simpa using this

/-- H1003: weak derivative of the infinite Fourier kernel. For `R_M' = -2π Σ_{2≤n≤M} n^(-3/4)
sin(2πnz)` (the classical derivative of `R_M`), there is an `L²` function `R'`, odd a.e., with
`R_M' → R'` in `L²`, `‖R'‖₂² = 2π² Σ_{n≥2} n^(-3/2)`, `‖R' - R_M'‖₂ = B_M` for `M ≥ 1`, and
`R'` is the weak derivative of `R`; in particular `R ∈ H¹(𝕋)`. -/
theorem weak_derivative_of_the_infinite_fourier_kernel :
    (∀ M : ℕ, IsSmoothPeriodic (RM M) ∧ ∀ x, coordPartial 0 (RM M) x = dRM M x) ∧
    (∀ (M : ℕ) (z : ℝ), dRM M (torusLift (fun _ => z)) =
      -(2 * Real.pi) * ∑ n ∈ Finset.Icc 2 M,
        (n : ℝ) ^ (-(3 / 4 : ℝ)) * Real.sin (2 * Real.pi * n * z)) ∧
    ∃ R' : Torus 1 → ℝ, MemLp R' 2 (haar 1) ∧ (∀ᵐ x ∂haar 1, R' (-x) = -R' x) ∧
      Tendsto (fun M => eLpNorm (fun x => R' x - dRM M x) 2 (haar 1)) atTop (𝓝 0) ∧
      ∫ x, R' x ^ 2 ∂haar 1
        = 2 * Real.pi ^ 2 * ∑' n : ℕ, (if 2 ≤ n then (n : ℝ) ^ (-(3 / 2 : ℝ)) else 0) ∧
      (∀ M : ℕ, 1 ≤ M → Real.sqrt (∫ x, (R' x - dRM M x) ^ 2 ∂haar 1) = B M) ∧
      IsWeakGradient R (fun x => (EuclideanSpace.single (0 : Fin 1) (R' x) : Tangent 1)) ∧
      MemH1 R := by
  refine ⟨fun M => ⟨isSmoothPeriodic_RM M, coordPartial_RM M⟩, ?_, dR, memLp_dR, dR_odd, ?_,
    integral_sq_dR, ?_, weak_gradient_R, ⟨_, weak_gradient_R⟩⟩
  · intro M z
    unfold dRM
    simp_rw [sinMode_lift]
  · have hBt : Tendsto (fun M => ENNReal.ofReal (B M)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_B
    refine hBt.congr' (Filter.eventually_atTop.2 ⟨1, fun M hM => ?_⟩)
    exact (eLpNorm_dR_sub hM).symm
  · intro M hM
    rw [integral_sq_dR_sub hM, Real.sqrt_sq]
    exact Real.sqrt_nonneg _

end DGPS.Examples.PositiveH1.Fourier
