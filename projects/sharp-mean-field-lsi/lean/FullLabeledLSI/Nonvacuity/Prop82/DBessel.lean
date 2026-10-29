import Mathlib

/-!
# Lane D: the modified Bessel bound `∫₀¹ exp(s cos 2πt) dt ≤ exp(s²/4)`

Pure real analysis (no torus). Used for the Gibbs/entropy-moment bound.
-/

open MeasureTheory intervalIntegral

namespace SharpLSI.FL.Prop82

noncomputable def cosMom (n : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * t) ^ n

lemma cosMom_eq (n : ℕ) :
    cosMom n = (2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos x ^ n := by
  unfold cosMom
  have := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun x => Real.cos x ^ n) (c := 2 * Real.pi) (by positivity)
  simpa using this

lemma cosMom_zero : cosMom 0 = 1 := by simp [cosMom]

lemma cosMom_one : cosMom 1 = 0 := by
  rw [cosMom_eq]; simp

lemma cosMom_add_two (n : ℕ) :
    cosMom (n + 2) = ((n : ℝ) + 1) / ((n : ℝ) + 2) * cosMom n := by
  rw [cosMom_eq, cosMom_eq, integral_cos_pow]
  simp only [Real.cos_two_pi, Real.sin_two_pi, Real.sin_zero, mul_zero, sub_self,
    zero_div, zero_add]
  ring

lemma cosMom_odd (k : ℕ) : cosMom (2 * k + 1) = 0 := by
  induction k with
  | zero => simpa using cosMom_one
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [this, cosMom_add_two, ih, mul_zero]

lemma cosMom_even (k : ℕ) :
    cosMom (2 * k) = ((2 * k).factorial : ℝ) / (4 ^ k * ((k.factorial : ℝ)) ^ 2) := by
  induction k with
  | zero => simp [cosMom_zero]
  | succ k ih =>
    have : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [this, cosMom_add_two, ih]
    have h1 : (2 * k + 2).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring
    have h2 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
    rw [h1, h2]
    push_cast
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

lemma even_term_eq (s : ℝ) (k : ℕ) :
    s ^ (2 * k) / ((2 * k).factorial : ℝ) * cosMom (2 * k) =
      (s ^ 2 / 4) ^ k / ((k.factorial : ℝ)) ^ 2 := by
  rw [cosMom_even]
  have h1 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [pow_mul, div_pow]
  field_simp

lemma hasSum_cos_series (s : ℝ) :
    HasSum (fun n : ℕ => s ^ n / (n.factorial : ℝ) * cosMom n)
      (∫ t in (0 : ℝ)..1, Real.exp (s * Real.cos (2 * Real.pi * t))) := by
  set F : ℕ → ℝ → ℝ := fun n t => (s * Real.cos (2 * Real.pi * t)) ^ n / (n.factorial : ℝ)
    with hF
  have hcont : ∀ n, Continuous (F n) := fun n => by
    simp only [hF]; fun_prop
  have hint : ∀ n, Integrable (F n) (volume.restrict (Set.Ioc (0:ℝ) 1)) := fun n =>
    ((hcont n).continuousOn.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ n t, ‖F n t‖ ≤ |s| ^ n / (n.factorial : ℝ) := by
    intro n t
    simp only [hF]
    rw [norm_div, norm_pow, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_natCast]
    gcongr
    calc |s| * |Real.cos (2 * Real.pi * t)| ≤ |s| * 1 :=
          by gcongr; exact Real.abs_cos_le_one _
      _ = |s| := mul_one _
  have hsum : Summable fun n => ∫ t in Set.Ioc (0:ℝ) 1, ‖F n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
      (fun n => ?_) (Real.summable_pow_div_factorial |s|)
    have := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Ioc (0:ℝ) 1) (C := |s| ^ n / (n.factorial : ℝ)) (by simp)
      (f := fun t => ‖F n t‖) (fun t _ => by simpa using hbound n t)
    simpa using (le_trans (le_abs_self _) this)
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : ∀ n, ∫ t in Set.Ioc (0:ℝ) 1, F n t =
      s ^ n / (n.factorial : ℝ) * cosMom n := by
    intro n
    rw [cosMom, ← intervalIntegral.integral_of_le zero_le_one]
    have : (fun x : ℝ => F n x) =
        fun x => (s ^ n / (n.factorial : ℝ)) * Real.cos (2 * Real.pi * x) ^ n := by
      funext x; simp only [hF, mul_pow]; ring
    rw [this, intervalIntegral.integral_const_mul]
  have e2 : ∀ t, ∑' n, F n t = Real.exp (s * Real.cos (2 * Real.pi * t)) := by
    intro t
    simp only [hF]
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (s * Real.cos (2 * Real.pi * t))).tsum_eq
  simp only [e1, e2] at h
  rwa [← intervalIntegral.integral_of_le zero_le_one] at h

theorem integral_exp_cos_le (s : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.exp (s * Real.cos (2 * Real.pi * t)) ≤ Real.exp (s ^ 2 / 4) := by
  set I := ∫ t in (0 : ℝ)..1, Real.exp (s * Real.cos (2 * Real.pi * t)) with hI
  have hf := hasSum_cos_series s
  set f : ℕ → ℝ := fun n => s ^ n / (n.factorial : ℝ) * cosMom n with hfdef
  have hexp : HasSum (fun k : ℕ => (s ^ 2 / 4) ^ k / (k.factorial : ℝ))
      (Real.exp (s ^ 2 / 4)) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hle : ∀ k : ℕ, (s ^ 2 / 4) ^ k / ((k.factorial : ℝ)) ^ 2 ≤
      (s ^ 2 / 4) ^ k / (k.factorial : ℝ) := by
    intro k
    have h1 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h0 : (0:ℝ) ≤ (s ^ 2 / 4) ^ k := by positivity
    apply div_le_div_of_nonneg_left h0 (by positivity)
    nlinarith
  have hesum : Summable fun k : ℕ => (s ^ 2 / 4) ^ k / ((k.factorial : ℝ)) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle hexp.summable
  have hev : HasSum (fun k => f (2 * k)) (∑' k : ℕ, (s ^ 2 / 4) ^ k / ((k.factorial : ℝ)) ^ 2) := by
    have := hesum.hasSum
    convert this using 1
    funext k
    exact even_term_eq s k
  have hod : HasSum (fun k => f (2 * k + 1)) 0 := by
    have : (fun k => f (2 * k + 1)) = fun _ => 0 := by
      funext k; simp [hfdef, cosMom_odd]
    rw [this]; exact hasSum_zero
  have := hev.even_add_odd hod
  rw [add_zero] at this
  have hIeq := hf.unique this
  rw [hI, hIeq]
  exact hasSum_le hle hesum.hasSum hexp

end SharpLSI.FL.Prop82
