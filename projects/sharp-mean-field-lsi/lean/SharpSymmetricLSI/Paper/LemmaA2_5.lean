import SharpSymmetricLSI.Paper.LemmaA2_4

/-!
# R25 (A.9), part 5: series of eigenfunctions with summable `C¹` weights

For a good density with eigenbasis `e` and `C¹` representatives `eC_j` with
`|eC_j| ≤ M_j`, `‖∇(eC_j ∘ liftT)‖ ≤ M'_j`, a series `S = ∑ b_j eC_j` with
`∑ |b_j| (M_j + M'_j) < ∞` is `C¹` (`contDiff_series`), integrates termwise against integrable
functions (`integral_series_mul`), and has `μ`-coefficients `b_i` (`coeff_series`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem summable_of_le_div_sq {x : ℕ → ℝ} (h0 : ∀ j, 0 ≤ x j) {K : ℝ}
    (h : ∀ j, 1 ≤ j → x j ≤ K / (j : ℝ) ^ 2) : Summable x := by
  rw [← summable_nat_add_iff 1]
  have h2 : Summable fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ 2 :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine Summable.of_nonneg_of_le (fun j => h0 _) (fun j => ?_) (h2.mul_left K)
  have := h (j + 1) (by omega)
  rw [mul_one_div]; exact this

theorem norm_fderiv_le_sum {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → ℝ) → ℝ) (w : ι → ℝ) :
    ‖fderiv ℝ F w‖ ≤ ∑ i, |fderiv ℝ F w (Pi.single i 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun h => ?_
  rw [Real.norm_eq_abs, fderiv_apply_eq_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (abs_nonneg _)

theorem fderiv_lift_repTorus {ι : Type} [Fintype ι] [DecidableEq ι] (f : UnitAddTorus ι → ℝ)
    (x : ι → ℝ) : fderiv ℝ (f ∘ liftT) (repTorus (liftT x)) = fderiv ℝ (f ∘ liftT) x := by
  have h1 := fderiv_lift_secT f (repTorus (liftT x))
  rw [liftT_repTorus, fderiv_lift_secT] at h1
  exact h1.symm

section series

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
  {eC : ℕ → Torus d → ℝ} (heC1 : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
  (heCae : ∀ j, eC j =ᵐ[densMeasure ρ] e j)
  {M M' : ℕ → ℝ} (hM : ∀ j x, |eC j x| ≤ M j) (hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j)
  {b : ℕ → ℝ} (hbM : Summable fun j => |b j| * M j) (hbM' : Summable fun j => |b j| * M' j)

/-- The series. -/
noncomputable def series (b : ℕ → ℝ) (eC : ℕ → Torus d → ℝ) (y : Torus d) : ℝ := ∑' j, b j * eC j y

include heC1 hM hM' hbM hbM' in
theorem contDiff_series : ContDiff ℝ 1 (series b eC ∘ liftT) := by
  have h := contDiff_tsum (𝕜 := ℝ) (N := 1) (f := fun j z => b j * eC j (liftT z))
    (v := fun k j => if k = 0 then |b j| * M j else |b j| * M' j)
    (fun j => contDiff_const.mul (heC1 j)) (fun k hk => ?_) (fun k j z hk => ?_)
  · exact h
  · rcases Nat.lt_or_ge k 1 with h | h
    · have : k = 0 := by omega
      subst this; simpa using hbM
    · have : k ≠ 0 := by omega
      simpa [this] using hbM'
  · have hk1 : k ≤ 1 := by exact_mod_cast hk
    rcases Nat.lt_or_ge k 1 with h | h
    · have : k = 0 := by omega
      subst this
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_mul, if_true]
      exact mul_le_mul_of_nonneg_left (hM j _) (abs_nonneg _)
    · have : k = 1 := by omega
      subst this
      simp only [one_ne_zero, if_false, norm_iteratedFDeriv_one]
      have hd : DifferentiableAt ℝ (eC j ∘ liftT) z := (heC1 j).differentiable (by norm_num) z
      rw [show (fun z => b j * eC j (liftT z)) = fun z => b j * (eC j ∘ liftT) z from rfl,
        fderiv_const_mul hd, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM' j z) (abs_nonneg _)

include hM hbM in
theorem summable_series_at (y : Torus d) : Summable fun j => b j * eC j y :=
  Summable.of_norm_bounded hbM fun j => by
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hM j y) (abs_nonneg _)

include heC1 hM hbM in
theorem integral_series_mul {ν : Measure (Torus d)} [IsFiniteMeasure ν] {h : Torus d → ℝ}
    (hh : Integrable h ν) :
    ∫ y, series b eC y * h y ∂ν = ∑' j, b j * ∫ y, eC j y * h y ∂ν := by
  have hcont : ∀ j, Continuous (eC j) := fun j => continuous_of_liftT' (heC1 j).continuous
  have hint : ∀ j, Integrable (fun y => b j * eC j y * h y) ν := fun j =>
    (hh.bdd_mul (c := |b j| * M j) (f := fun y => b j * eC j y)
      ((continuous_const.mul (hcont j)).aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        show |b j * eC j y| ≤ _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM j y) (abs_nonneg _))).congr
      (Eventually.of_forall fun y => by simp only [Pi.mul_apply]; try ring)
  have hsum : Summable fun j => ∫ y, ‖b j * eC j y * h y‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _)
      (fun j => ?_) (hbM.mul_right (∫ y, |h y| ∂ν))
    calc ∫ y, ‖b j * eC j y * h y‖ ∂ν ≤ ∫ y, |b j| * M j * |h y| ∂ν := by
          refine integral_mono (hint j).norm (hh.abs.const_mul _) fun y => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hM j y) (abs_nonneg _)) (abs_nonneg _)
      _ = |b j| * M j * ∫ y, |h y| ∂ν := integral_const_mul _ _
  have e1 := integral_tsum_of_summable_integral_norm hint hsum
  have e2 : ∀ y, series b eC y * h y = ∑' j, b j * eC j y * h y := fun y => by
    rw [series, ← tsum_mul_right]
  simp_rw [e2, ← e1]
  congr 1; funext j
  rw [← integral_const_mul]; congr 1; funext y; ring

include hρ hb heC1 heCae hM hbM in
theorem coeff_series (i : ℕ) : ∫ y, series b eC y * e i y ∂densMeasure ρ = b i := by
  haveI := hρ.isProb
  have hei : Integrable (e i) (densMeasure ρ) :=
    ((hb.memH1 i).2.1).integrable one_le_two
  rw [integral_series_mul heC1 hM hbM hei]
  have e1 : ∀ j, ∫ y, eC j y * e i y ∂densMeasure ρ = if j = i then 1 else 0 := fun j => by
    rw [← hb.orthonormal j i]
    exact integral_congr_ae ((heCae j).mono fun y hy => by simp only [hy])
  simp_rw [e1, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq i b

end series

end SharpLSI
