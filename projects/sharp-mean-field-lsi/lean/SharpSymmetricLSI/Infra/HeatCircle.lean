import Mathlib

/-!
# The heat semigroup on the circle `ℝ/ℤ` (Phase 3, lane C; R10 sub-milestone (a))

Functions on the circle are `1`-periodic functions on `ℝ`. For a coefficient family `c : ℤ → ℂ`
with `‖c n‖ ≤ C`,
`heatSeries c j t x = ∑ₙ c n (2πin)^j e^{-4π²n²t} e^{2πinx}`  (`t > 0`).
Then `∂ₓ heatSeries c j = heatSeries c (j+1)` and `∂ₜ heatSeries c j = heatSeries c (j+2)`
(`hasDerivAt_heatSeries_x`, `hasDerivAt_heatSeries_t`), so all mixed partials are explicit
series; they are jointly continuous on `t > 0`.

The heat kernel `heatK t x = ∑ₙ e^{-4π²n²t} cos(2πnx)` is Jacobi's `θ₂(x, 4πit)`; it is positive
(functional equation), has mass one and Fourier multipliers `e^{-4π²n²t}`. For an integrable
`1`-periodic `ρ`, `heat ρ t = heatK t * ρ` is the heat flow.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace SharpLSI

/-- A term of the damped Fourier series. -/
noncomputable def heatTerm (c : ℤ → ℂ) (j : ℕ) (t x : ℝ) (n : ℤ) : ℂ :=
  c n * (2 * π * I * n) ^ j * (Real.exp (-(4 * π ^ 2) * n ^ 2 * t) : ℂ) *
    cexp (2 * π * I * n * x)

/-- The damped Fourier series `∑ₙ c n (2πin)^j e^{-4π²n²t} e^{2πinx}`. -/
noncomputable def heatSeries (c : ℤ → ℂ) (j : ℕ) (t x : ℝ) : ℂ := ∑' n, heatTerm c j t x n

/-- The summable majorant. -/
noncomputable def heatBound (C : ℝ) (j : ℕ) (t : ℝ) (n : ℤ) : ℝ :=
  C * (2 * π) ^ j * ((|n| ^ j : ℝ) * Real.exp (-π * (4 * π * t * n ^ 2 - 2 * 0 * |n|)))

theorem summable_heatBound (C : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (heatBound C j t) :=
  ((summable_pow_mul_jacobiTheta₂_term_bound 0 (by positivity : 0 < 4 * π * t) j).mul_left
    (C * (2 * π) ^ j))

theorem norm_cexp_two_pi_I (n : ℤ) (x : ℝ) : ‖cexp (2 * π * I * n * x)‖ = 1 := by
  rw [show (2 * π * I * n * x : ℂ) = ((2 * π * n * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_heatTerm_le {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) (j : ℕ) {t₁ t : ℝ}
    (ht : t₁ ≤ t) (x : ℝ) (n : ℤ) : ‖heatTerm c j t x n‖ ≤ heatBound C j t₁ n := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hc 0)
  unfold heatTerm heatBound
  rw [norm_mul, norm_mul, norm_mul, norm_cexp_two_pi_I, mul_one, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : ‖(2 * π * I * n : ℂ)‖ = 2 * π * |(n : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, show ((n : ℤ) : ℂ) = (((n : ℤ) : ℝ) : ℂ) by
        push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    ring
  rw [h1, mul_pow]
  have h2 : Real.exp (-(4 * π ^ 2) * n ^ 2 * t) ≤ Real.exp (-π * (4 * π * t₁ * n ^ 2 - 2 * 0 * |n|)) := by
    apply Real.exp_le_exp.mpr
    have h4 : (π ^ 2 * n ^ 2) * t₁ ≤ (π ^ 2 * n ^ 2) * t :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    have e : -π * (4 * π * t₁ * (n : ℝ) ^ 2 - 2 * 0 * ((|n| : ℤ) : ℝ)) =
        -4 * ((π ^ 2 * n ^ 2) * t₁) := by ring
    rw [e]; linarith
  have h3 : |(n : ℝ)| ^ j = ((|n| : ℤ) : ℝ) ^ j := by rw [Int.cast_abs]
  rw [h3]
  calc ‖c n‖ * ((2 * π) ^ j * ((|n| : ℤ) : ℝ) ^ j) * Real.exp (-(4 * π ^ 2) * n ^ 2 * t)
      ≤ C * ((2 * π) ^ j * ((|n| : ℤ) : ℝ) ^ j) *
          Real.exp (-π * (4 * π * t₁ * n ^ 2 - 2 * 0 * |n|)) := by
        gcongr
        exact hc n
    _ = _ := by ring

theorem summable_heatTerm {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) (j : ℕ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) : Summable (heatTerm c j t x) :=
  Summable.of_norm_bounded (summable_heatBound C j ht) (norm_heatTerm_le hc j le_rfl x)

theorem hasDerivAt_heatTerm_x (c : ℤ → ℂ) (j : ℕ) (t x : ℝ) (n : ℤ) :
    HasDerivAt (fun x => heatTerm c j t x n) (heatTerm c (j + 1) t x n) x := by
  have h := ((((hasDerivAt_id x).ofReal_comp).const_mul (2 * π * I * n)).cexp).const_mul
    (c n * (2 * π * I * n) ^ j * (Real.exp (-(4 * π ^ 2) * n ^ 2 * t) : ℂ))
  convert h using 1
  · funext x; simp [heatTerm]
  · simp only [heatTerm, id]; push_cast; ring

theorem hasDerivAt_heatTerm_t (c : ℤ → ℂ) (j : ℕ) (t x : ℝ) (n : ℤ) :
    HasDerivAt (fun t => heatTerm c j t x n) (heatTerm c (j + 2) t x n) t := by
  have he := ((((hasDerivAt_id t).const_mul (-(4 * π ^ 2) * (n : ℝ) ^ 2)).exp).ofReal_comp)
  have h := (he.const_mul (c n * (2 * π * I * n) ^ j)).mul_const (cexp (2 * π * I * n * x))
  convert h using 1
  · funext t; simp [heatTerm]
  · simp only [heatTerm, id]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring

theorem hasDerivAt_heatSeries_x {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) (j : ℕ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x => heatSeries c j t x) (heatSeries c (j + 1) t x) x :=
  hasDerivAt_tsum (summable_heatBound C (j + 1) ht) (fun n y => hasDerivAt_heatTerm_x c j t y n)
    (fun n y => norm_heatTerm_le hc (j + 1) le_rfl y n) (summable_heatTerm hc j ht x) x

theorem hasDerivAt_heatSeries_t {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) (j : ℕ) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun t => heatSeries c j t x) (heatSeries c (j + 2) t x) t := by
  have ht2 : 0 < t / 2 := by positivity
  exact hasDerivAt_tsum_of_isPreconnected (summable_heatBound C (j + 2) ht2) isOpen_Ioi
    isPreconnected_Ioi (fun n y _ => hasDerivAt_heatTerm_t c j y x n)
    (fun n y hy => norm_heatTerm_le hc (j + 2) (le_of_lt hy) x n) (by simp; linarith)
    (summable_heatTerm hc j ht x) (by simp; linarith)

theorem continuousOn_heatSeries {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) (j : ℕ) {t₁ : ℝ}
    (ht₁ : 0 < t₁) :
    ContinuousOn (fun q : ℝ × ℝ => heatSeries c j q.1 q.2) (Ici t₁ ×ˢ univ) := by
  refine continuousOn_tsum (u := heatBound C j t₁) (fun n => ?_) (summable_heatBound C j ht₁)
    (fun n q hq => norm_heatTerm_le hc j hq.1 q.2 n)
  apply Continuous.continuousOn
  unfold heatTerm
  fun_prop

theorem heatSeries_add_one (c : ℤ → ℂ) (j : ℕ) (t x : ℝ) :
    heatSeries c j t (x + 1) = heatSeries c j t x := by
  unfold heatSeries
  congr 1; funext n
  unfold heatTerm
  rw [show (2 * π * I * n * ((x + 1 : ℝ) : ℂ)) = 2 * π * I * n * x + (n : ℂ) * (2 * π * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_heatSeries_le {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) (j : ℕ) {t₁ t : ℝ}
    (ht₁ : 0 < t₁) (ht : t₁ ≤ t) (x : ℝ) :
    ‖heatSeries c j t x‖ ≤ ∑' n, heatBound C j t₁ n :=
  tsum_of_norm_bounded (summable_heatBound C j ht₁).hasSum fun n => norm_heatTerm_le hc j ht x n

/-! ### The heat kernel -/

theorem heatSeries_one_eq_theta (t x : ℝ) :
    heatSeries (fun _ => 1) 0 t x = jacobiTheta₂ x (I * (4 * π * t)) := by
  unfold heatSeries jacobiTheta₂
  congr 1; funext n
  unfold heatTerm jacobiTheta₂_term
  rw [Complex.ofReal_exp, one_mul, pow_zero, one_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem theta_eq_real {t : ℝ} (ht : 0 < t) (x : ℝ) :
    jacobiTheta₂ x (I * (4 * π * t)) =
      ((1 / (4 * π * t) ^ (1 / 2 : ℝ) * Real.exp (-x ^ 2 / (4 * t)) *
        ∑' n : ℤ, Real.exp (n * x / (2 * t) - n ^ 2 / (4 * t)) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [jacobiTheta₂_functional_equation]
  have h1 : -I * (I * (4 * π * t)) = ((4 * π * t : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have h2 : -π * I * (x : ℂ) ^ 2 / (I * (4 * π * t)) = ((-x ^ 2 / (4 * t) : ℝ) : ℂ) := by
    rw [div_eq_iff (by simp [hπ, ht', Complex.I_ne_zero])]
    push_cast
    field_simp
    (try ring_nf)
    (try rw [Complex.I_sq])
    (try ring)
  have h3 : jacobiTheta₂ ((x : ℂ) / (I * (4 * π * t))) (-1 / (I * (4 * π * t))) =
      ((∑' n : ℤ, Real.exp (n * x / (2 * t) - n ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    unfold jacobiTheta₂
    rw [Complex.ofReal_tsum]
    congr 1; funext n
    unfold jacobiTheta₂_term
    rw [Complex.ofReal_exp]
    congr 1
    have hI : (I * (4 * π * t) : ℂ) ≠ 0 := by simp [hπ, ht', Complex.I_ne_zero]
    field_simp
    push_cast
    ring_nf
    (try rw [Complex.I_sq])
    field_simp
  rw [h1, h2, h3, ← Complex.ofReal_exp, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

theorem summable_theta_real {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable fun n : ℤ => Real.exp (n * x / (2 * t) - n ^ 2 / (4 * t)) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have him : 0 < (-1 / (I * (4 * π * t)) : ℂ).im := by
    have : (-1 / (I * (4 * π * t)) : ℂ) = ((1 / (4 * π * t) : ℝ) : ℂ) * I := by
      field_simp; push_cast; ring_nf; (try rw [Complex.I_sq]); field_simp
    rw [this, Complex.mul_I_im, Complex.ofReal_re]; positivity
  have hs := (summable_jacobiTheta₂_term_iff ((x : ℂ) / (I * (4 * π * t))) _).mpr him
  refine Complex.summable_ofReal.mp (hs.congr fun n => ?_)
  unfold jacobiTheta₂_term
  rw [Complex.ofReal_exp]
  congr 1
  field_simp
  push_cast
  ring_nf
  (try rw [Complex.I_sq])
  field_simp

/-- The heat kernel `K_t(x) = ∑ₙ e^{-4π²n²t} cos(2πnx)`. -/
noncomputable def heatK (t x : ℝ) : ℝ := (heatSeries (fun _ => 1) 0 t x).re

theorem heatK_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatK t x := by
  unfold heatK
  rw [heatSeries_one_eq_theta, theta_eq_real ht, Complex.ofReal_re]
  have hS : 0 < ∑' n : ℤ, Real.exp (n * x / (2 * t) - n ^ 2 / (4 * t)) :=
    (summable_theta_real ht x).tsum_pos (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  positivity

theorem heatK_eq_tsum {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatK t x = ∑' n : ℤ, Real.exp (-(4 * π ^ 2) * n ^ 2 * t) * Real.cos (2 * π * n * x) := by
  have hc : ∀ n : ℤ, ‖(fun _ : ℤ => (1 : ℂ)) n‖ ≤ 1 := fun n => by simp
  unfold heatK heatSeries
  rw [Complex.re_tsum (summable_heatTerm hc 0 ht x)]
  congr 1; funext n
  unfold heatTerm
  rw [show (2 * π * I * n * x : ℂ) = ((2 * π * n * x : ℝ) : ℂ) * I by push_cast; ring]
  simp only [pow_zero, mul_one, one_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]

theorem intervalIntegral_cexp_int (n : ℤ) :
    ∫ x in (0 : ℝ)..1, cexp (2 * π * I * n * x) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp
  · have hn' : (2 * π * I * n : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => cexp (2 * π * I * n * x) /
        (2 * π * I * n)) (cexp (2 * π * I * n * x)) x := by
      intro x _
      have := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * π * I * n)).cexp.div_const
        (2 * π * I * n)
      convert this using 1
      · funext y; simp
      · simp only [id_eq]; push_cast; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    rw [show (2 * π * I * n * ((1 : ℝ) : ℂ)) = (n : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- Integrals over `(0,1]` of a damped Fourier series pick out the `0`-th term. -/
theorem integral_heatSeries {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) {t : ℝ} (ht : 0 < t) :
    ∫ x in (0 : ℝ)..1, heatSeries c 0 t x = c 0 := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hc 0)
  rw [intervalIntegral.integral_of_le zero_le_one]
  unfold heatSeries
  rw [← integral_tsum_of_summable_integral_norm (F := fun n x => heatTerm c 0 t x n)
    (fun n => (by unfold heatTerm; fun_prop : Continuous fun x => heatTerm c 0 t x n)
      |>.integrableOn_Ioc)]
  · have : ∀ n : ℤ, ∫ x in Ioc (0 : ℝ) 1, heatTerm c 0 t x n = if n = 0 then c 0 else 0 := by
      intro n
      unfold heatTerm
      rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral_cexp_int]
      split_ifs with hn
      · subst hn; simp
      · simp
    simp_rw [this]
    rw [tsum_ite_eq]
  · refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (summable_heatBound C 0 ht)
    calc ∫ x in Ioc (0 : ℝ) 1, ‖heatTerm c 0 t x n‖ ≤ ∫ x in Ioc (0 : ℝ) 1, heatBound C 0 t n :=
          setIntegral_mono_on ((by unfold heatTerm; fun_prop : Continuous fun x =>
            heatTerm c 0 t x n).norm.integrableOn_Ioc) (integrableOn_const (by simp) (by simp))
            measurableSet_Ioc fun x _ => norm_heatTerm_le hc 0 le_rfl x n
      _ = heatBound C 0 t n := by simp

/-- Mass one. -/
theorem integral_heatK {t : ℝ} (ht : 0 < t) : ∫ x in (0 : ℝ)..1, heatK t x = 1 := by
  have hc : ∀ n : ℤ, ‖(fun _ : ℤ => (1 : ℂ)) n‖ ≤ 1 := fun n => by simp
  have hcont : Continuous fun x => heatSeries (fun _ => (1 : ℂ)) 0 t x :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_heatSeries_x hc 0 ht x).continuousAt
  unfold heatK
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hre := integral_re (μ := volume.restrict (Ioc (0 : ℝ) 1)) (hcont.integrableOn_Ioc)
  simp only [RCLike.re_to_complex] at hre
  rw [hre, ← intervalIntegral.integral_of_le zero_le_one, integral_heatSeries hc ht]
  simp

theorem heatK_add_one (t x : ℝ) : heatK t (x + 1) = heatK t x := by
  unfold heatK; rw [heatSeries_add_one]

theorem continuousOn_heatK {t₁ : ℝ} (ht₁ : 0 < t₁) :
    ContinuousOn (fun q : ℝ × ℝ => heatK q.1 q.2) (Ici t₁ ×ˢ univ) :=
  Complex.continuous_re.comp_continuousOn
    (continuousOn_heatSeries (c := fun _ => 1) (C := 1) (fun n => by simp) 0 ht₁)

theorem periodic_eq_fract {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) = f x) (x : ℝ) :
    f x = f (Int.fract x) := by
  have : ∀ n : ℕ, ∀ y, f (y + n) = f y := by
    intro n; induction n with
    | zero => simp
    | succ k ih => intro y; rw [Nat.cast_succ, ← add_assoc, hf, ih]
  have h' : ∀ n : ℤ, ∀ y, f (y + n) = f y := by
    intro n y
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · simpa using this k y
    · have := this k (y - k)
      simp only [sub_add_cancel] at this
      push_cast
      rw [← sub_eq_add_neg]
      exact this.symm
  conv_lhs => rw [← Int.fract_add_floor x]
  exact h' _ _

/-- A uniform positive lower bound for the kernel on `[t₁,t₂] × ℝ`. -/
theorem heatK_lower {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    ∃ m > 0, ∀ t ∈ Icc t₁ t₂, ∀ x, m ≤ heatK t x := by
  have hK : IsCompact (Icc t₁ t₂ ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hne : (Icc t₁ t₂ ×ˢ Icc (0 : ℝ) 1).Nonempty := ⟨(t₁, 0), ⟨le_rfl, h12⟩, ⟨le_rfl, zero_le_one⟩⟩
  have hc := (continuousOn_heatK ht₁).mono (fun q hq => ⟨mem_Ici.mpr hq.1.1, mem_univ _⟩ :
    Icc t₁ t₂ ×ˢ Icc (0 : ℝ) 1 ⊆ Ici t₁ ×ˢ univ)
  obtain ⟨q₀, hq₀, hmin⟩ := hK.exists_isMinOn hne hc
  refine ⟨heatK q₀.1 q₀.2, heatK_pos (lt_of_lt_of_le ht₁ hq₀.1.1) _, fun t ht x => ?_⟩
  rw [periodic_eq_fract (heatK_add_one t) x]
  exact hmin (show (t, Int.fract x) ∈ Icc t₁ t₂ ×ˢ Icc (0 : ℝ) 1 from
    ⟨ht, Int.fract_nonneg x, (Int.fract_lt_one x).le⟩)

/-! ### The heat flow of a periodic density -/

/-- Fourier coefficients `ρ̂(n) = ∫₀¹ ρ(y) e^{-2πiny} dy`. -/
noncomputable def heatCoeff (ρ : ℝ → ℝ) (n : ℤ) : ℂ :=
  ∫ y in (0 : ℝ)..1, (ρ y : ℂ) * cexp (-(2 * π * I * n * y))

theorem norm_heatCoeff_le (ρ : ℝ → ℝ) (n : ℤ) :
    ‖heatCoeff ρ n‖ ≤ ∫ y in (0 : ℝ)..1, |ρ y| := by
  unfold heatCoeff
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans (le_of_eq ?_)
  congr 1; funext y
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show (-(2 * π * I * n * y) : ℂ) = ((-(2 * π * n * y) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The derivatives `∂ₓʲ` of the heat flow (`j = 0`: the heat flow itself). -/
noncomputable def heatD (ρ : ℝ → ℝ) (j : ℕ) (t x : ℝ) : ℝ := (heatSeries (heatCoeff ρ) j t x).re

/-- The heat flow `p_t = e^{t∂²}ρ`. -/
noncomputable abbrev heat (ρ : ℝ → ℝ) (t x : ℝ) : ℝ := heatD ρ 0 t x

theorem hasDerivAt_re_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => (f x).re) f'.re x := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  exact this

theorem hasDerivAt_heatD_x (ρ : ℝ → ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x => heatD ρ j t x) (heatD ρ (j + 1) t x) x :=
  hasDerivAt_re_comp (hasDerivAt_heatSeries_x (norm_heatCoeff_le ρ) j ht x)

theorem hasDerivAt_heatD_t (ρ : ℝ → ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun t => heatD ρ j t x) (heatD ρ (j + 2) t x) t :=
  hasDerivAt_re_comp (hasDerivAt_heatSeries_t (norm_heatCoeff_le ρ) j ht x)

theorem heatD_add_one (ρ : ℝ → ℝ) (j : ℕ) (t x : ℝ) : heatD ρ j t (x + 1) = heatD ρ j t x := by
  unfold heatD; rw [heatSeries_add_one]

theorem continuousOn_heatD (ρ : ℝ → ℝ) (j : ℕ) {t₁ : ℝ} (ht₁ : 0 < t₁) :
    ContinuousOn (fun q : ℝ × ℝ => heatD ρ j q.1 q.2) (Ici t₁ ×ˢ univ) :=
  Complex.continuous_re.comp_continuousOn (continuousOn_heatSeries (norm_heatCoeff_le ρ) j ht₁)

theorem continuous_heatD (ρ : ℝ → ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    Continuous fun x => heatD ρ j t x :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_heatD_x ρ j ht x).continuousAt

theorem abs_heatD_le (ρ : ℝ → ℝ) (j : ℕ) {t₁ t : ℝ} (ht₁ : 0 < t₁) (ht : t₁ ≤ t) (x : ℝ) :
    |heatD ρ j t x| ≤ ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ y|) j t₁ n :=
  (Complex.abs_re_le_norm _).trans (norm_heatSeries_le (norm_heatCoeff_le ρ) j ht₁ ht x)

/-- Mass conservation. -/
theorem integral_heat (ρ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x in (0 : ℝ)..1, heat ρ t x = ∫ y in (0 : ℝ)..1, ρ y := by
  have hcont : Continuous fun x => heatSeries (heatCoeff ρ) 0 t x :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_heatSeries_x (norm_heatCoeff_le ρ) 0 ht x).continuousAt
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hre := integral_re (μ := volume.restrict (Ioc (0 : ℝ) 1)) (hcont.integrableOn_Ioc)
  simp only [RCLike.re_to_complex] at hre
  simp only [heat, heatD]
  rw [hre, ← intervalIntegral.integral_of_le zero_le_one,
    integral_heatSeries (norm_heatCoeff_le ρ) ht]
  unfold heatCoeff
  simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  rw [integral_complex_ofReal, Complex.ofReal_re]

/-- `p_t = K_t * ρ`. -/
theorem heat_eq_conv {ρ : ℝ → ℝ} (hρ : IntervalIntegrable ρ volume 0 1) {t : ℝ} (ht : 0 < t)
    (x : ℝ) : heat ρ t x = ∫ y in (0 : ℝ)..1, heatK t (x - y) * ρ y := by
  have hc1 : ∀ n : ℤ, ‖(fun _ : ℤ => (1 : ℂ)) n‖ ≤ 1 := fun n => by simp
  have hρi : IntegrableOn ρ (Ioc (0 : ℝ) 1) := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    zero_le_one).mp hρ
  set F : ℤ → ℝ → ℂ := fun n y => (ρ y : ℂ) * heatTerm (fun _ => 1) 0 t (x - y) n with hF
  have hterm : ∀ n, heatTerm (heatCoeff ρ) 0 t x n = ∫ y in Ioc (0 : ℝ) 1, F n y := by
    intro n
    unfold heatTerm heatCoeff
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_mul_const, ← integral_mul_const,
      ← integral_mul_const]
    congr 1; funext y
    simp only [hF, heatTerm, pow_zero, mul_one, one_mul]
    rw [show cexp (2 * π * I * n * ((x - y : ℝ) : ℂ)) =
        cexp (-(2 * π * I * n * y)) * cexp (2 * π * I * n * x) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have hFi : ∀ n, Integrable (F n) (volume.restrict (Ioc (0 : ℝ) 1)) := fun n => by
    refine Integrable.mono' (hρi.norm.mul_const (heatBound 1 0 t n))
      (hρi.ofReal.aestronglyMeasurable.mul ((by unfold heatTerm; fun_prop : Continuous fun y =>
        heatTerm (fun _ => (1 : ℂ)) 0 t (x - y) n).aestronglyMeasurable))
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_heatTerm_le hc1 0 le_rfl _ n) (norm_nonneg _)
  have hsum : Summable fun n => ∫ y in Ioc (0 : ℝ) 1, ‖F n y‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) (fun n => ?_)
      ((summable_heatBound 1 0 ht).mul_left (∫ y in Ioc (0 : ℝ) 1, ‖ρ y‖))
    rw [← integral_mul_const]
    refine integral_mono (hFi n).norm (hρi.norm.mul_const _) fun y => ?_
    simp only [hF, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_heatTerm_le hc1 0 le_rfl (x - y) n) (norm_nonneg (ρ y))
  have hsumF : ∀ y, ∑' n, F n y = (ρ y : ℂ) * heatSeries (fun _ => 1) 0 t (x - y) := fun y => by
    simp only [hF]; rw [tsum_mul_left]; rfl
  have hScont : Continuous fun y => heatSeries (fun _ => (1 : ℂ)) 0 t (x - y) :=
    (continuous_iff_continuousAt.mpr fun z => (hasDerivAt_heatSeries_x hc1 0 ht z).continuousAt).comp
      (continuous_const.sub continuous_id)
  have hint : Integrable (fun y => (ρ y : ℂ) * heatSeries (fun _ => 1) 0 t (x - y))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine Integrable.mono' (hρi.norm.mul_const (∑' n, heatBound 1 0 t n))
      (hρi.ofReal.aestronglyMeasurable.mul hScont.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_heatSeries_le hc1 0 ht le_rfl _) (norm_nonneg _)
  simp only [heat, heatD, heatSeries]
  simp_rw [hterm]
  rw [integral_tsum_of_summable_integral_norm hFi hsum]
  simp_rw [hsumF]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre, intervalIntegral.integral_of_le zero_le_one]
  congr 1; funext y
  rw [Complex.re_ofReal_mul]
  unfold heatK heatSeries
  ring

theorem continuous_heatK {t : ℝ} (ht : 0 < t) : Continuous fun x => heatK t x :=
  Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_heatSeries_x (c := fun _ => 1) (C := 1) (fun n => by simp) 0 ht x).continuousAt)

/-- Positivity of the heat flow, uniformly on `[t₁,t₂]`. -/
theorem heat_lower {ρ : ℝ → ℝ} (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    ∃ m > 0, ∀ t ∈ Icc t₁ t₂, ∀ x, m * ∫ y in (0 : ℝ)..1, ρ y ≤ heat ρ t x := by
  obtain ⟨m, hm, hK⟩ := heatK_lower ht₁ h12
  refine ⟨m, hm, fun t ht x => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht.1
  rw [heat_eq_conv hρ ht0 x, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one (hρ.const_mul m)
    (hρ.continuousOn_mul ((continuous_heatK ht0).comp (continuous_const.sub
      continuous_id)).continuousOn) fun y _ => ?_
  exact mul_le_mul_of_nonneg_right (hK t ht (x - y)) (hρ0 y)

/-! ### Long-time decay -/

theorem heatBound_mono {C : ℝ} (hC : 0 ≤ C) (j : ℕ) {t : ℝ} (ht : 1 ≤ t) {n : ℤ} (hn : n ≠ 0) :
    heatBound C j t n ≤ Real.exp (-(4 * π ^ 2) * (t - 1)) * heatBound C j 1 n := by
  unfold heatBound
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [sq_nonneg n, Int.one_le_abs hn, sq_abs n]
    exact_mod_cast this
  have he : Real.exp (-π * (4 * π * t * n ^ 2 - 2 * 0 * |n|)) ≤
      Real.exp (-(4 * π ^ 2) * (t - 1)) * Real.exp (-π * (4 * π * 1 * n ^ 2 - 2 * 0 * |n|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (4 * π ^ 2) * (t - 1) ≤ (4 * π ^ 2) * ((t - 1) * n ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith
  calc C * (2 * π) ^ j * (((|n| : ℤ) : ℝ) ^ j * Real.exp (-π * (4 * π * t * n ^ 2 - 2 * 0 * |n|)))
      ≤ C * (2 * π) ^ j * (((|n| : ℤ) : ℝ) ^ j * (Real.exp (-(4 * π ^ 2) * (t - 1)) *
          Real.exp (-π * (4 * π * 1 * n ^ 2 - 2 * 0 * |n|)))) := by
        gcongr
    _ = _ := by ring

/-- Long-time decay: `|∂ₓʲ p_t - δ_{j0} ∫ρ| ≤ e^{-4π²(t-1)} K_j` for `t ≥ 1`. -/
theorem abs_heatD_sub_le (ρ : ℝ → ℝ) (j : ℕ) {t : ℝ} (ht : 1 ≤ t) (x : ℝ) :
    |heatD ρ j t x - (if j = 0 then ∫ y in (0 : ℝ)..1, ρ y else 0)| ≤
      Real.exp (-(4 * π ^ 2) * (t - 1)) * ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ y|) j 1 n := by
  set C := ∫ y in (0 : ℝ)..1, |ρ y|
  have hC : 0 ≤ C := intervalIntegral.integral_nonneg zero_le_one fun y _ => abs_nonneg _
  have ht0 : 0 < t := by linarith
  have hs := summable_heatTerm (norm_heatCoeff_le ρ) j ht0 x
  have h0 : heatTerm (heatCoeff ρ) j t x 0 =
      ((if j = 0 then ∫ y in (0 : ℝ)..1, ρ y else 0 : ℝ) : ℂ) := by
    unfold heatTerm heatCoeff
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one,
        pow_zero, ↓reduceIte]
      rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
        integral_complex_ofReal]
      simp
    · simp [hj.ne', zero_pow hj.ne']
  have hsplit := hs.tsum_eq_add_tsum_ite 0
  unfold heatD heatSeries
  rw [hsplit, h0, Complex.add_re, Complex.ofReal_re, add_sub_cancel_left]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hb : ∀ n : ℤ, ‖(if n = 0 then 0 else heatTerm (heatCoeff ρ) j t x n)‖ ≤
      Real.exp (-(4 * π ^ 2) * (t - 1)) * heatBound C j 1 n := by
    intro n
    split_ifs with hn
    · simp only [norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (by
        unfold heatBound; positivity)
    · exact (norm_heatTerm_le (norm_heatCoeff_le ρ) j le_rfl x n).trans (heatBound_mono hC j ht hn)
  refine (tsum_of_norm_bounded (((summable_heatBound C j one_pos).mul_left _).hasSum) hb).trans
    (le_of_eq ?_)
  rw [tsum_mul_left]

/-! ### Fourier coefficients of the flow, reality, and derivative coefficients -/

/-- `∫₀¹ (∑ₙ cₙ e^{-4π²n²t} e^{2πinx}) e^{-2πimx} dx = c_m e^{-4π²m²t}`. -/
theorem heatCoeff_heatSeries {c : ℤ → ℂ} {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) {t : ℝ} (ht : 0 < t)
    (m : ℤ) : ∫ x in (0 : ℝ)..1, heatSeries c 0 t x * cexp (-(2 * π * I * m * x)) =
      c m * (Real.exp (-(4 * π ^ 2) * m ^ 2 * t) : ℂ) := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hc 0)
  have hn1 : ∀ x : ℝ, ‖cexp (-(2 * π * I * m * x))‖ = 1 := fun x => by
    rw [show (-(2 * π * I * m * x) : ℂ) = ((-m : ℤ) : ℂ) * (2 * π * I) * x / 1 * 1 by
      push_cast; ring, mul_one, div_one,
      show ((-m : ℤ) : ℂ) * (2 * π * I) * x = 2 * π * I * ((-m : ℤ) : ℂ) * x by ring]
    exact norm_cexp_two_pi_I _ x
  rw [intervalIntegral.integral_of_le zero_le_one]
  unfold heatSeries
  simp_rw [← tsum_mul_right]
  have hcontF : ∀ n, Continuous fun x : ℝ => heatTerm c 0 t x n * cexp (-(2 * π * I * m * x)) :=
    fun n => by unfold heatTerm; fun_prop
  rw [← integral_tsum_of_summable_integral_norm
    (F := fun n x => heatTerm c 0 t x n * cexp (-(2 * π * I * m * x)))
    (fun n => (hcontF n).integrableOn_Ioc)]
  · have : ∀ n : ℤ, ∫ x in Ioc (0 : ℝ) 1, heatTerm c 0 t x n * cexp (-(2 * π * I * m * x)) =
        if n = m then c m * (Real.exp (-(4 * π ^ 2) * m ^ 2 * t) : ℂ) else 0 := by
      intro n
      have he : ∀ x : ℝ, heatTerm c 0 t x n * cexp (-(2 * π * I * m * x)) =
          (c n * (Real.exp (-(4 * π ^ 2) * n ^ 2 * t) : ℂ)) *
            cexp (2 * π * I * ((n - m : ℤ) : ℂ) * x) := fun x => by
        unfold heatTerm
        rw [mul_assoc _ (cexp _), ← Complex.exp_add]
        push_cast; ring_nf
      simp_rw [he]
      rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral_cexp_int]
      by_cases hnm : n = m
      · subst hnm; simp
      · rw [if_neg (sub_ne_zero.mpr hnm), if_neg hnm, mul_zero]
    simp_rw [this]
    rw [tsum_ite_eq]
  · refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (summable_heatBound C 0 ht)
    calc ∫ x in Ioc (0 : ℝ) 1, ‖heatTerm c 0 t x n * cexp (-(2 * π * I * m * x))‖
          ≤ ∫ x in Ioc (0 : ℝ) 1, heatBound C 0 t n :=
          setIntegral_mono_on (hcontF n).norm.integrableOn_Ioc
            (integrableOn_const (by simp) (by simp))
            measurableSet_Ioc fun x _ => by
              rw [norm_mul, hn1, mul_one]; exact norm_heatTerm_le hc 0 le_rfl x n
      _ = heatBound C 0 t n := by simp

theorem heatCoeff_neg (ρ : ℝ → ℝ) (n : ℤ) : heatCoeff ρ (-n) = (starRingEnd ℂ) (heatCoeff ρ n) := by
  unfold heatCoeff
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    ← integral_conj]
  congr 1; funext y
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  push_cast; ring

/-- The flow of a real density is real: `(p_t : ℂ) = ∑ₙ ...`. -/
theorem heat_coe (ρ : ℝ → ℝ) (t x : ℝ) :
    ((heat ρ t x : ℝ) : ℂ) = heatSeries (heatCoeff ρ) 0 t x := by
  rw [heat, heatD, ← Complex.conj_eq_iff_re]
  unfold heatSeries
  rw [Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq]
  congr 1; funext n
  simp only [Equiv.neg_apply, heatTerm, pow_zero, mul_one, map_mul, heatCoeff_neg,
    Complex.conj_conj, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  · push_cast; ring_nf
  · simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    push_cast; ring

/-- Fourier multipliers of the flow: `\widehat{p_t}(m) = ρ̂(m) e^{-4π²m²t}`. -/
theorem heatCoeff_heat (ρ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (m : ℤ) :
    heatCoeff (heat ρ t) m = heatCoeff ρ m * (Real.exp (-(4 * π ^ 2) * m ^ 2 * t) : ℂ) := by
  rw [← heatCoeff_heatSeries (norm_heatCoeff_le ρ) ht m]
  unfold heatCoeff
  simp_rw [heat_coe]
  rfl

/-- If `ĝ(n) = 2πin ρ̂(n)` then `∂ₓ p_t[ρ] = p_t[g]`. -/
theorem heatD_one_eq_heat {ρ g : ℝ → ℝ} (h : ∀ n : ℤ, heatCoeff g n = 2 * π * I * n * heatCoeff ρ n)
    (t x : ℝ) : heatD ρ 1 t x = heat g t x := by
  simp only [heat, heatD, heatSeries]
  congr 2; funext n
  simp only [heatTerm, h, pow_one, pow_zero, mul_one]
  ring

/-- `∫₀¹ K_t(x - y) dx = 1`. -/
theorem integral_heatK_sub {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∫ x in (0 : ℝ)..1, heatK t (x - y) = 1 := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => heatK t x)]
  have hp : Function.Periodic (fun x => heatK t x) 1 := fun x => heatK_add_one t x
  rw [show (1 : ℝ) - y = -y + 1 by ring, zero_sub, hp.intervalIntegral_add_eq (-y) 0, zero_add]
  exact integral_heatK ht

end SharpLSI
