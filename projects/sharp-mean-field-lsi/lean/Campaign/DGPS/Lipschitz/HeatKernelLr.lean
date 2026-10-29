import DGPS.Lipschitz.DuhamelPotential
import DGPS.Analysis.TorusYoung

/-!
# `L^r` bounds and smoothing for the periodized heat kernel (LIP010c1)

* (a) sup bounds `|Kh t v| ≤ (1 + (π t)^{-1/2})^d ≤ 2^d (1 + t^{-d/2})` and
  `‖∇ Kh t v‖ ≤ 2^d t^{-1/2} (1 + t^{-d/2})` (`heatKernel_sup_bounds`);
* (b) `L^r` bounds on the unit torus by interpolation between sup and `L¹`
  (`eLpNorm_heatKernelT_le`, `eLpNorm_Psi_le`);
* (c) smoothing `L^p → L^q` via Young (`eLpNorm_heatOp_le`, `eLpNorm_kerGrad_le`,
  `eLpNorm_fderiv_Hl_le`).
-/

open MeasureTheory Set
open scoped Real ENNReal

namespace DGPS.Lipschitz
variable {d : ℕ}

theorem gauss1_antitoneOn {t : ℝ} (ht : 0 < t) : AntitoneOn (DGPS.gauss1 t) (Ici 0) := by
  intro a ha b _ hab
  have ha' : 0 ≤ a := ha
  unfold DGPS.gauss1
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have : a ^ 2 ≤ b ^ 2 := by nlinarith
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right this (by positivity)

theorem gauss1_le_sup {t : ℝ} (ht : 0 < t) (s : ℝ) : DGPS.gauss1 t s ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) := by
  unfold DGPS.gauss1
  have h0 : 0 ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) := by positivity
  have : Real.exp (-s ^ 2 / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg s]) (by positivity)
  nlinarith

theorem sum_gauss1_range_le {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ∑ i ∈ Finset.range N, DGPS.gauss1 t (a + i) ≤
      (4 * π * t) ^ (-(1 : ℝ) / 2) + ∫ s in Ioi a, DGPS.gauss1 t s := by
  have hint : IntegrableOn (DGPS.gauss1 t) (Ioi a) := (integrable_gauss1 ht).integrableOn
  have hI0 : 0 ≤ ∫ s in Ioi a, DGPS.gauss1 t s :=
    setIntegral_nonneg measurableSet_Ioi fun s _ => DGPS.gauss1_nonneg t s ht
  have hc0 : 0 ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) := by positivity
  cases N with
  | zero => simp; positivity
  | succ n =>
    rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range n, DGPS.gauss1 t (a + ((i + 1 : ℕ) : ℝ)) ≤
        ∫ s in a..a + n, DGPS.gauss1 t s := by
      refine AntitoneOn.sum_le_integral ?_
      exact (gauss1_antitoneOn ht).mono fun s hs => le_trans ha hs.1
    have h2 : ∫ s in a..a + n, DGPS.gauss1 t s ≤ ∫ s in Ioi a, DGPS.gauss1 t s := by
      rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])]
      refine setIntegral_mono_set hint ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun s _ => DGPS.gauss1_nonneg t s ht)
      · exact Filter.Eventually.of_forall fun s hs => hs.1
    have h3 := gauss1_le_sup ht (a + ((0 : ℕ) : ℝ))
    simp only [Nat.cast_add, Nat.cast_one] at h1 ⊢
    linarith

theorem gauss1_neg (t s : ℝ) : DGPS.gauss1 t (-s) = DGPS.gauss1 t s := by
  unfold DGPS.gauss1; rw [neg_sq]

theorem integral_Ioi_gauss1 {t : ℝ} (ht : 0 < t) : ∫ s in Ioi (0 : ℝ), DGPS.gauss1 t s = 1 / 2 := by
  have h := integral_comp_abs (f := DGPS.gauss1 t)
  have e : (fun x : ℝ => DGPS.gauss1 t |x|) = DGPS.gauss1 t := by
    funext x; unfold DGPS.gauss1; rw [sq_abs]
  rw [e, integral_gauss1 ht] at h
  linarith

theorem integral_Ioi_gauss1_le {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a) :
    ∫ s in Ioi a, DGPS.gauss1 t s ≤ 1 / 2 := by
  rw [← integral_Ioi_gauss1 ht]
  refine setIntegral_mono_set (integrable_gauss1 ht).integrableOn ?_ ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun s _ => DGPS.gauss1_nonneg t s ht)
  · exact Filter.Eventually.of_forall fun s hs => lt_of_le_of_lt ha hs

theorem heatK_le_of_mem {t : ℝ} (ht : 0 < t) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    SharpLSI.heatK t x ≤ 2 * (4 * π * t) ^ (-(1 : ℝ) / 2) + 1 := by
  rw [← DGPS.tsum_gauss1_add_int ht x]
  set F : ℤ → ℝ := fun m => DGPS.gauss1 t (x + (m : ℝ)) with hF
  have hs : Summable F := DGPS.summable_gauss1_add_int ht x
  have hs1 : Summable fun n : ℕ => F n := hs.comp_injective (i := ((↑) : ℕ → ℤ)) Nat.cast_injective
  have hs2 : Summable fun n : ℕ => F (-((n : ℤ) + 1)) :=
    hs.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (by
      intro a b h; simp only [neg_inj, add_left_inj] at h; exact_mod_cast h)
  have hsplit : ∑' m : ℤ, F m = ∑' n : ℕ, F n + ∑' n : ℕ, F (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one hs1 hs2
  have e2 : ∀ n : ℕ, F (-((n : ℤ) + 1)) = DGPS.gauss1 t ((1 - x) + n) := by
    intro n
    simp only [hF]
    rw [← gauss1_neg t (x + _)]
    congr 1
    push_cast
    ring
  have b1 : ∑' n : ℕ, F n ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) + 1 / 2 := by
    refine (Real.tsum_le_of_sum_range_le (fun n => DGPS.gauss1_nonneg t _ ht) fun N => ?_)
    have := sum_gauss1_range_le ht hx0 N
    have h2 := integral_Ioi_gauss1_le ht hx0
    simp only [hF, Int.cast_natCast]
    linarith
  have b2 : ∑' n : ℕ, F (-((n : ℤ) + 1)) ≤ (4 * π * t) ^ (-(1 : ℝ) / 2) + 1 / 2 := by
    simp_rw [e2]
    refine (Real.tsum_le_of_sum_range_le (fun n => DGPS.gauss1_nonneg t _ ht) fun N => ?_)
    have := sum_gauss1_range_le ht (by linarith : 0 ≤ 1 - x) N
    have h2 := integral_Ioi_gauss1_le ht (by linarith : 0 ≤ 1 - x)
    linarith
  rw [hsplit]
  linarith

theorem heatK_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    SharpLSI.heatK t x ≤ 1 + (π * t) ^ (-(1 : ℝ) / 2) := by
  have h := heatK_le_of_mem ht (Int.fract_nonneg x) (Int.fract_lt_one x).le
  have e : SharpLSI.heatK t (Int.fract x) = SharpLSI.heatK t x := by
    conv_rhs => rw [← Int.fract_add_floor x]
    exact (SharpLSI.heatK_add_int t _ _).symm
  rw [e] at h
  have hc : 2 * (4 * π * t) ^ (-(1 : ℝ) / 2) = (π * t) ^ (-(1 : ℝ) / 2) := by
    have : 4 * π * t = 4 * (π * t) := by ring
    rw [this, Real.mul_rpow (by norm_num) (by positivity)]
    have h4 : (4 : ℝ) ^ (-(1 : ℝ) / 2) = 1 / 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h4]; ring
  linarith

theorem heatK_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ SharpLSI.heatK t x := by
  rw [← DGPS.tsum_gauss1_add_int ht x]
  exact tsum_nonneg fun _ => DGPS.gauss1_nonneg t _ ht

theorem Kh_eq_prod (t : ℝ) (v : Tangent d) : Kh t v = ∏ k, SharpLSI.heatK t (v.ofLp k) := rfl

theorem Kh_nonneg {t : ℝ} (ht : 0 < t) (v : Tangent d) : 0 ≤ Kh t v :=
  (Kh_eq_tsum ht v ▸ (tsum_nonneg fun _ => (gE_pos ht _).le))

theorem Kh_le {t : ℝ} (ht : 0 < t) (v : Tangent d) :
    Kh t v ≤ (1 + (π * t) ^ (-(1 : ℝ) / 2)) ^ d := by
  rw [Kh_eq_prod]
  calc _ ≤ ∏ _k : Fin d, (1 + (π * t) ^ (-(1 : ℝ) / 2)) :=
        Finset.prod_le_prod₀ (fun k _ => heatK_nonneg ht _) (fun k _ => heatK_le ht _)
    _ = _ := by simp

theorem heatKernelT_torusLift_eq {t : ℝ} (ht : 0 < t) (u : Tangent d) :
    heatKernelT t (torusLift u.ofLp) = Kh t u := by
  rw [heatKernelT_torusLift ht, DGPS.periodizedGaussian_eq_heatPL ht]
  rfl

theorem heatKernelT_eq_Kh {t : ℝ} (ht : 0 < t) (w : Torus d) : heatKernelT t w = Kh t (secE w) := by
  have : w = torusLift (secE w).ofLp := (SharpLSI.liftT_secT w).symm
  conv_lhs => rw [this]
  exact heatKernelT_torusLift_eq ht _

theorem heatKernelT_le {t : ℝ} (ht : 0 < t) (w : Torus d) :
    |heatKernelT t w| ≤ (1 + (π * t) ^ (-(1 : ℝ) / 2)) ^ d := by
  rw [abs_of_pos (heatKernelT_pos ht w), heatKernelT_eq_Kh ht]
  exact Kh_le ht _

theorem norm_fderiv_Kh_le_sup {τ : ℝ} (hτ : 0 < τ) (v : Tangent d) :
    ‖fderiv ℝ (Kh τ) v‖ ≤ (π * (τ / 2)) ^ (-(1 : ℝ) / 2) *
      (1 + (π * (τ / 2)) ^ (-(1 : ℝ) / 2)) ^ d := by
  have hs : 0 < τ / 2 := by positivity
  have hbd := (periodized_heat_gradient_bounds (d := d) hs).1
    (g := heatKernelT (τ / 2)) (M := (1 + (π * (τ / 2)) ^ (-(1 : ℝ) / 2)) ^ d)
    (continuous_heatKernelT hs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => heatKernelT_le hs w) v
  have hfun : (fun u : Tangent d => heatOp (τ / 2) (heatKernelT (τ / 2)) (torusLift u.ofLp)) = Kh τ := by
    funext u
    have := heatKernelT_conv (d := d) hs hs
    have h2 : τ / 2 + τ / 2 = τ := by ring
    rw [h2] at this
    unfold heatOp
    rw [this]
    exact heatKernelT_torusLift_eq hτ u
  rw [hfun] at hbd
  exact hbd.2

theorem one_add_pow_le (x : ℝ) (hx : 0 ≤ x) (d : ℕ) : (1 + x) ^ d ≤ 2 ^ d * (1 + x ^ d) := by
  rcases le_total x 1 with h | h
  · have h1 : (1 + x) ^ d ≤ 2 ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
    have h2 : 0 ≤ x ^ d := by positivity
    have h3 : (0 : ℝ) ≤ 2 ^ d := by positivity
    nlinarith
  · have h1 : (1 + x) ^ d ≤ (2 * x) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
    rw [mul_pow] at h1
    have h3 : (0 : ℝ) ≤ 2 ^ d := by positivity
    nlinarith [pow_nonneg hx d]

theorem rpow_mul_le {t c : ℝ} (ht : 0 < t) (hc : 1 ≤ c) :
    (c * t) ^ (-(1 : ℝ) / 2) ≤ t ^ (-(1 : ℝ) / 2) := by
  rw [Real.mul_rpow (by linarith) ht.le]
  have : c ^ (-(1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have h2 : 0 ≤ t ^ (-(1 : ℝ) / 2) := by positivity
  nlinarith

theorem rpow_neg_half_pow {t : ℝ} (ht : 0 < t) (d : ℕ) :
    (t ^ (-(1 : ℝ) / 2)) ^ d = t ^ (-(d : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1; ring

/-- Sup bound for the periodized heat kernel: `0 < K_t ≤ 2^d (1 + t^{-d/2})`. -/
theorem Kh_le_clean {t : ℝ} (ht : 0 < t) (v : Tangent d) :
    Kh t v ≤ 2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) := by
  refine (Kh_le ht v).trans ?_
  have h1 : (π * t) ^ (-(1 : ℝ) / 2) ≤ t ^ (-(1 : ℝ) / 2) := rpow_mul_le ht (by linarith [Real.pi_gt_three])
  have h2 : (1 + (π * t) ^ (-(1 : ℝ) / 2)) ^ d ≤ (1 + t ^ (-(1 : ℝ) / 2)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  refine h2.trans ?_
  have := one_add_pow_le (t ^ (-(1 : ℝ) / 2)) (by positivity) d
  rwa [rpow_neg_half_pow ht] at this

/-- Sup bound for the gradient of the periodized heat kernel:
`‖∇K_t‖ ≤ 2^d t^{-1/2} (1 + t^{-d/2})`. -/
theorem norm_fderiv_Kh_le_clean {t : ℝ} (ht : 0 < t) (v : Tangent d) :
    ‖fderiv ℝ (Kh t) v‖ ≤ 2 ^ d * (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2))) := by
  refine (norm_fderiv_Kh_le_sup ht v).trans ?_
  have hp : (π * (t / 2)) = (π / 2) * t := by ring
  have h1 : (π * (t / 2)) ^ (-(1 : ℝ) / 2) ≤ t ^ (-(1 : ℝ) / 2) := by
    rw [hp]; exact rpow_mul_le ht (by linarith [Real.pi_gt_three])
  have h0 : 0 ≤ (π * (t / 2)) ^ (-(1 : ℝ) / 2) := by positivity
  have h2 : (1 + (π * (t / 2)) ^ (-(1 : ℝ) / 2)) ^ d ≤ (1 + t ^ (-(1 : ℝ) / 2)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have h3 := one_add_pow_le (t ^ (-(1 : ℝ) / 2)) (by positivity) d
  rw [rpow_neg_half_pow ht] at h3
  have h4 : 0 ≤ t ^ (-(1 : ℝ) / 2) := by positivity
  calc _ ≤ t ^ (-(1 : ℝ) / 2) * (2 ^ d * (1 + t ^ (-(d : ℝ) / 2))) := by
        refine mul_le_mul h1 (h2.trans h3) (by positivity) h4
    _ = _ := by ring

theorem Psi_le_clean {t : ℝ} (ht : 0 < t) (w : Torus d) :
    Psi t w ≤ 2 ^ d * (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2))) :=
  norm_fderiv_Kh_le_clean ht _

/-- **(a) Sup bounds** for the periodized heat kernel and its gradient, `t > 0`. -/
theorem heatKernel_sup_bounds {t : ℝ} (ht : 0 < t) :
    (∀ v : Tangent d, |Kh t v| ≤ (1 + (π * t) ^ (-(1 : ℝ) / 2)) ^ d ∧
        |Kh t v| ≤ 2 ^ d * (1 + t ^ (-(d : ℝ) / 2))) ∧
      ∀ v : Tangent d, ‖fderiv ℝ (Kh t) v‖ ≤
        2 ^ d * (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2))) :=
  ⟨fun v => by rw [abs_of_nonneg (Kh_nonneg ht v)]; exact ⟨Kh_le ht v, Kh_le_clean ht v⟩,
    fun v => norm_fderiv_Kh_le_clean ht v⟩

/-- Interpolation between `L^∞` and `L¹`: `‖g‖_r ≤ ‖g‖_∞^{1-1/r} ‖g‖_1^{1/r}`. -/
theorem eLpNorm_le_interp {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ} {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hg : AEStronglyMeasurable g μ) (hb : ∀ᵐ x ∂μ, |g x| ≤ M)
    (h1 : eLpNorm g 1 μ ≤ ENNReal.ofReal N) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm g r μ ≤ ENNReal.ofReal (M ^ (1 - r⁻¹).toReal * N ^ (r⁻¹).toReal) := by
  by_cases hrt : r = ⊤
  · subst hrt
    have e : M ^ (1 - (⊤ : ℝ≥0∞)⁻¹).toReal * N ^ ((⊤ : ℝ≥0∞)⁻¹).toReal = M := by simp
    rw [e, eLpNorm_exponent_top]
    · exact eLpNormEssSup_le_of_ae_bound (hb.mono fun x hx => by rwa [Real.norm_eq_abs])
    · exact hg
  · have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    have hρ : 1 ≤ r.toReal := by
      have := ENNReal.toReal_mono hrt hr
      simpa using this
    set ρ := r.toReal with hρdef
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt hg]
    have hpt : ∀ᵐ x ∂μ, ‖g x‖ₑ ^ ρ ≤ ENNReal.ofReal M ^ (ρ - 1) * ‖g x‖ₑ := by
      filter_upwards [hb] with x hx
      have hx' : ‖g x‖ₑ ≤ ENNReal.ofReal M := by
        rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal hx
      have e : ‖g x‖ₑ ^ ρ = ‖g x‖ₑ ^ (ρ - 1) * ‖g x‖ₑ := by
        conv_lhs => rw [show ρ = (ρ - 1) + 1 by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
      rw [e]
      exact mul_le_mul_left (ENNReal.rpow_le_rpow hx' (by linarith)) _
    have hint : ∫⁻ x, ‖g x‖ₑ ^ ρ ∂μ ≤ ENNReal.ofReal (M ^ (ρ - 1) * N) := by
      calc ∫⁻ x, ‖g x‖ₑ ^ ρ ∂μ ≤ ∫⁻ x, ENNReal.ofReal M ^ (ρ - 1) * ‖g x‖ₑ ∂μ :=
            lintegral_mono_ae hpt
        _ = ENNReal.ofReal M ^ (ρ - 1) * ∫⁻ x, ‖g x‖ₑ ∂μ :=
            lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
        _ ≤ ENNReal.ofReal M ^ (ρ - 1) * ENNReal.ofReal N := by
            refine mul_le_mul_right ?_ _
            rw [← eLpNorm_one_eq_lintegral_enorm hg]; exact h1
        _ = ENNReal.ofReal (M ^ (ρ - 1) * N) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg hM (by linarith)]
    have hρ0 : 0 < 1 / ρ := by positivity
    calc (∫⁻ x, ‖g x‖ₑ ^ ρ ∂μ) ^ (1 / ρ) ≤ (ENNReal.ofReal (M ^ (ρ - 1) * N)) ^ (1 / ρ) :=
          ENNReal.rpow_le_rpow hint hρ0.le
      _ = ENNReal.ofReal ((M ^ (ρ - 1) * N) ^ (1 / ρ)) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hρ0.le
      _ = _ := by
          have e1 : (1 - r⁻¹).toReal = 1 - 1 / ρ := by
            rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 hr) ENNReal.one_ne_top,
              ENNReal.toReal_inv, ENNReal.toReal_one, one_div]
          have e2 : (r⁻¹).toReal = 1 / ρ := by rw [ENNReal.toReal_inv, one_div]
          rw [e1, e2, Real.mul_rpow (by positivity) hN, ← Real.rpow_mul hM]
          congr 3
          field_simp

theorem eLpNorm_one_le_of_integral {g : Torus d → ℝ} (hg : Continuous g) (hnn : ∀ x, 0 ≤ g x)
    {N : ℝ} (hN : ∫ x, g x ∂haar d ≤ N) : eLpNorm g 1 (haar d) ≤ ENNReal.ofReal N := by
  have hi : Integrable g (haar d) := integrable_of_continuous_torus hg
  rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
  have : ∫⁻ x, ‖g x‖ₑ ∂haar d = ENNReal.ofReal (∫ x, g x ∂haar d) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (hnn x)]
  rw [this]
  exact ENNReal.ofReal_le_ofReal hN

theorem rpow_le_of_le_one {x θ : ℝ} (hx : 1 ≤ x) (hθ : θ ≤ 1) : x ^ θ ≤ x := by
  calc x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ
    _ = x := Real.rpow_one x

theorem toReal_inv_split {r : ℝ≥0∞} (hr : 1 ≤ r) :
    0 ≤ (1 - r⁻¹).toReal ∧ (1 - r⁻¹).toReal ≤ 1 ∧ (r⁻¹).toReal = 1 - (1 - r⁻¹).toReal := by
  have h1 : r⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hr
  have e : (1 - r⁻¹).toReal = 1 - (r⁻¹).toReal := by
    rw [ENNReal.toReal_sub_of_le h1 ENNReal.one_ne_top, ENNReal.toReal_one]
  have h2 : (r⁻¹).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  have h3 : 0 ≤ (r⁻¹).toReal := ENNReal.toReal_nonneg
  refine ⟨by rw [e]; linarith, by rw [e]; linarith, by rw [e]; ring⟩

/-- **(b)** `L^r` bound for the periodized heat kernel on the torus. -/
theorem eLpNorm_heatKernelT_le {t : ℝ} (ht : 0 < t) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (heatKernelT (d := d) t) r (haar d) ≤
      ENNReal.ofReal (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ (1 - r⁻¹).toReal) := by
  obtain ⟨hθ0, hθ1, -⟩ := toReal_inv_split hr
  have hs : 0 ≤ t ^ (-(d : ℝ) / 2) := by positivity
  have hM : 0 ≤ 2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) := by positivity
  have hk : ∀ w : Torus d, 0 ≤ heatKernelT t w := fun w => by
    rw [heatKernelT_eq_Kh ht]; exact Kh_nonneg ht _
  refine (eLpNorm_le_interp (N := 1) hM zero_le_one
    (continuous_heatKernelT ht).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_) ?_ hr).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [abs_of_nonneg (hk w), heatKernelT_eq_Kh ht]; exact Kh_le_clean ht _
  · exact eLpNorm_one_le_of_integral (continuous_heatKernelT ht) hk (le_of_eq (integral_heatKernelT ht))
  · rw [Real.one_rpow, mul_one, Real.mul_rpow (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_right (rpow_le_of_le_one (one_le_pow₀ (by norm_num)) hθ1)
      (by positivity)

theorem Psi_eq_zero_of_dim_zero (hd : d = 0) (t : ℝ) (w : Torus d) : Psi t w = 0 := by
  subst hd
  unfold Psi
  have : fderiv ℝ (Kh (d := 0) t) (secE w) = 0 := Subsingleton.elim _ _
  rw [this, norm_zero]

theorem grad_interp_aux {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (d : ℕ) {θ φ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hφ : φ = 1 - θ) :
    (2 ^ d * (t ^ (-(1 : ℝ) / 2) * (1 + s))) ^ θ * (Real.sqrt (d / 2) * t ^ (-(1 : ℝ) / 2)) ^ φ ≤
      2 ^ d * (d + 1) * (t ^ (-(1 : ℝ) / 2) * (1 + s) ^ θ) := by
  have hφ0 : 0 ≤ φ := by linarith
  have hφ1 : φ ≤ 1 := by linarith
  have hτ : 0 < t ^ (-(1 : ℝ) / 2) := by positivity
  have hb0 : 0 ≤ Real.sqrt (d / 2) := Real.sqrt_nonneg _
  have hbd : Real.sqrt (d / 2) ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp
    · rw [Real.sqrt_le_left (by positivity)]
      have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  have hbφ : Real.sqrt (d / 2) ^ φ ≤ d + 1 := by
    rcases le_total 1 (Real.sqrt (d / 2)) with h | h
    · exact (rpow_le_of_le_one h hφ1).trans (by linarith)
    · have := Real.rpow_le_one hb0 h hφ0
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
  have hp : ((2 : ℝ) ^ d) ^ θ ≤ 2 ^ d := rpow_le_of_le_one (one_le_pow₀ (by norm_num)) hθ1
  have hτθ : (t ^ (-(1 : ℝ) / 2)) ^ θ * (t ^ (-(1 : ℝ) / 2)) ^ φ = t ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hτ, show θ + φ = 1 by linarith, Real.rpow_one]
  have hs1 : 0 ≤ 1 + s := by linarith
  calc _ = (((2 : ℝ) ^ d) ^ θ * Real.sqrt (d / 2) ^ φ) *
          ((t ^ (-(1 : ℝ) / 2)) ^ θ * (t ^ (-(1 : ℝ) / 2)) ^ φ) * (1 + s) ^ θ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hs1,
          Real.mul_rpow hb0 hτ.le]
        ring
    _ ≤ (2 ^ d * (d + 1)) * t ^ (-(1 : ℝ) / 2) * (1 + s) ^ θ := by
        rw [hτθ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hp hbφ (by positivity) (by positivity)) hτ.le) (by positivity)
    _ = _ := by ring

/-- **(b)** `L^r` bound for the norm of the gradient of the periodized heat kernel. -/
theorem eLpNorm_Psi_le {t : ℝ} (ht : 0 < t) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (Psi (d := d) t) r (haar d) ≤
      ENNReal.ofReal (2 ^ d * (d + 1) *
        (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ (1 - r⁻¹).toReal)) := by
  obtain ⟨hθ0, hθ1, hφ⟩ := toReal_inv_split hr
  have hs : 0 ≤ t ^ (-(d : ℝ) / 2) := by positivity
  have hM : 0 ≤ 2 ^ d * (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2))) := by positivity
  have hN : 0 ≤ Real.sqrt (d / 2) * t ^ (-(1 : ℝ) / 2) := by positivity
  have h1 : eLpNorm (Psi (d := d) t) 1 (haar d) ≤
      ENNReal.ofReal (Real.sqrt (d / 2) * t ^ (-(1 : ℝ) / 2)) := by
    refine eLpNorm_one_le_of_integral (continuous_Psi ht) (Psi_nonneg t) ?_
    rcases Nat.eq_zero_or_pos d with h | h
    · have : ∀ w : Torus d, Psi t w = 0 := Psi_eq_zero_of_dim_zero h t
      simp only [this, integral_zero]; exact hN
    · rw [← sqrt_const_eq ht d]; exact integral_Psi_le ht h
  refine (eLpNorm_le_interp hM hN (continuous_Psi ht).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_) h1 hr).trans (ENNReal.ofReal_le_ofReal ?_)
  · rw [abs_of_nonneg (Psi_nonneg t w)]; exact Psi_le_clean ht w
  · exact grad_interp_aux ht hs d hθ0 hθ1 hφ

/-- The Young exponent `r` with `p⁻¹ + r⁻¹ = 1 + q⁻¹`, for `p ≤ q`. -/
theorem exists_young_exponent {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ r : ℝ≥0∞, 1 ≤ r ∧ p⁻¹ + r⁻¹ = 1 + q⁻¹ ∧
      (1 - r⁻¹).toReal = (p⁻¹).toReal - (q⁻¹).toReal := by
  have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hqp : q⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpq
  have hle : p⁻¹ ≤ 1 + q⁻¹ := hp1.trans le_self_add
  refine ⟨(1 + q⁻¹ - p⁻¹)⁻¹, ?_, ?_, ?_⟩
  · rw [ENNReal.one_le_inv]
    calc 1 + q⁻¹ - p⁻¹ ≤ 1 + p⁻¹ - p⁻¹ := tsub_le_tsub_right (by gcongr) _
      _ = 1 := ENNReal.add_sub_cancel_right (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
  · rw [inv_inv]; exact add_tsub_cancel_of_le hle
  · have e : p⁻¹ + (1 + q⁻¹ - p⁻¹) = 1 + q⁻¹ := add_tsub_cancel_of_le hle
    rw [inv_inv]
    have hr1 : 1 + q⁻¹ - p⁻¹ ≤ 1 := by
      calc 1 + q⁻¹ - p⁻¹ ≤ 1 + p⁻¹ - p⁻¹ := tsub_le_tsub_right (by gcongr) _
        _ = 1 := ENNReal.add_sub_cancel_right (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
    have hfin : ∀ {a : ℝ≥0∞}, a ≤ 1 → a ≠ ⊤ := fun h => ne_top_of_le_ne_top ENNReal.one_ne_top h
    have e2 := congrArg ENNReal.toReal e
    rw [ENNReal.toReal_add (hfin hp1) (hfin hr1),
      ENNReal.toReal_add ENNReal.one_ne_top (hfin (hqp.trans hp1)), ENNReal.toReal_one] at e2
    rw [ENNReal.toReal_sub_of_le hr1 ENNReal.one_ne_top, ENNReal.toReal_one]
    linarith

/-- **(c)** Smoothing of the periodic heat semigroup, `L^p → L^q`, `1 ≤ p ≤ q ≤ ∞`. -/
theorem eLpNorm_heatOp_le {t : ℝ} (ht : 0 < t) {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    eLpNorm (heatOp t F) q (haar d) ≤
      ENNReal.ofReal (2 ^ d * (1 + t ^ (-(d : ℝ) / 2)) ^ ((p⁻¹).toReal - (q⁻¹).toReal)) *
        eLpNorm F p (haar d) := by
  obtain ⟨r, hr, hpqr, hθ⟩ := exists_young_exponent hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  have hY := DGPS.Analysis.torus_young_convolution (d := d) (p := r) (q := q) (r := p) hr hq hp
    (by rw [add_comm]; exact hpqr) (f := heatKernelT t) (continuous_heatKernelT ht).aestronglyMeasurable
    hF
  have hK := eLpNorm_heatKernelT_le (d := d) ht hr
  rw [← hθ]
  exact hY.trans (mul_le_mul_left hK _)

theorem norm_kerGrad_le_conv {t : ℝ} (ht : 0 < t) (F : Torus d → ℝ) (x : Torus d) :
    ‖kerGrad t F x‖ ≤ ∫ y, Psi t (x - y) * ‖F y‖ ∂haar d := by
  unfold kerGrad
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Filter.Eventually.of_forall fun w => ?_)))
  simp only [norm_smul, norm_Dk_eq ht, norm_fderiv_Kh_sub]
  ring

theorem aestronglyMeasurable_kerGrad (τ : ℝ) {F : Torus d → ℝ}
    (hF : AEStronglyMeasurable F (haar d)) : AEStronglyMeasurable (kerGrad τ F) (haar d) := by
  have hm : kerGrad τ F = kerGrad τ (hF.mk F) := by
    funext x
    unfold kerGrad
    refine integral_congr_ae ?_
    filter_upwards [hF.ae_eq_mk] with w hw
    rw [hw]
  rw [hm]
  have h2 : Measurable fun z : Torus d × Torus d =>
      (hF.mk F) z.2 • Dk τ (secE z.1 - secE z.2) :=
    (hF.stronglyMeasurable_mk.measurable.comp measurable_snd).smul
      (measurable_Dk.comp (measurable_const.prodMk
        ((measurable_secE.comp measurable_fst).sub (measurable_secE.comp measurable_snd))))
  exact (h2.stronglyMeasurable.integral_prod_right').aestronglyMeasurable

/-- **(c)** Smoothing for the gradient of the periodic heat semigroup (Riesz vector `kerGrad`),
`L^p → L^q`, `1 ≤ p ≤ q ≤ ∞`. -/
theorem eLpNorm_kerGrad_le {t : ℝ} (ht : 0 < t) {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d)) :
    eLpNorm (kerGrad t F) q (haar d) ≤
      ENNReal.ofReal (2 ^ d * (d + 1) *
        (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ ((p⁻¹).toReal - (q⁻¹).toReal))) *
        eLpNorm F p (haar d) := by
  obtain ⟨r, hr, hpqr, hθ⟩ := exists_young_exponent hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  have hY := DGPS.Analysis.torus_young_convolution (d := d) (p := r) (q := q) (r := p) hr hq hp
    (by rw [add_comm]; exact hpqr) (f := Psi t) (continuous_Psi ht).aestronglyMeasurable
    (g := fun y => ‖F y‖) hF.norm
  have hK := eLpNorm_Psi_le (d := d) ht hr
  rw [← hθ]
  calc eLpNorm (kerGrad t F) q (haar d)
      ≤ eLpNorm (fun x => ∫ y, Psi t (x - y) * ‖F y‖ ∂haar d) q (haar d) :=
        eLpNorm_mono (aestronglyMeasurable_kerGrad t hF)
          fun x => (norm_kerGrad_le_conv ht F x).trans (le_abs_self _)
    _ ≤ eLpNorm (Psi (d := d) t) r (haar d) * eLpNorm (fun y => ‖F y‖) p (haar d) := hY
    _ ≤ _ := by
        rw [eLpNorm_norm F hF]
        exact mul_le_mul_left hK _

/-- **(c)** The same bound for the genuine Fréchet gradient of `x ↦ H_t F` on the tangent
space (for integrable `F`). -/
theorem eLpNorm_fderiv_Hl_le {t : ℝ} (ht : 0 < t) {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    {F : Torus d → ℝ} (hF : Integrable F (haar d)) :
    eLpNorm (fun x : Torus d => fderiv ℝ (Hl t F) (secE x)) q (haar d) ≤
      ENNReal.ofReal (2 ^ d * (d + 1) *
        (t ^ (-(1 : ℝ) / 2) * (1 + t ^ (-(d : ℝ) / 2)) ^ ((p⁻¹).toReal - (q⁻¹).toReal))) *
        eLpNorm F p (haar d) := by
  have hm : AEStronglyMeasurable (fun x : Torus d => fderiv ℝ (Hl t F) (secE x)) (haar d) :=
    ((measurable_fderiv ℝ (Hl t F)).comp measurable_secE).aestronglyMeasurable
  refine le_trans (le_of_eq (eLpNorm_congr_norm_ae hm
    (aestronglyMeasurable_kerGrad t hF.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (norm_kerGrad ht hF x).symm)))
    (eLpNorm_kerGrad_le ht hp hpq hF.aestronglyMeasurable)

end DGPS.Lipschitz
