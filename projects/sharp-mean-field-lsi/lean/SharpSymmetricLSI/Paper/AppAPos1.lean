import Mathlib

/-!
# Positivity (1): a chain rule for indefinite integrals and the truncation `G(r) = (r⁻)⁴`

* `chain_rule_intervalIntegral`: for `g ∈ L¹(a,b)` and `G ∈ C¹`,
  `G(c + ∫_a^b g) - G(c) = ∫_a^b G'(c + ∫_a^u g) g(u) du` (absolute continuity).
* `negPow n r = (min r 0)^n` has derivative `n (min r 0)^{n-1}` for `n ≥ 2`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace SharpLSI

/-- **Chain rule** for `u ↦ c + ∫_a^u g`. -/
theorem chain_rule_intervalIntegral {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) {G G' : ℝ → ℝ} (hG : ∀ r, HasDerivAt G (G' r) r)
    (hG'c : Continuous G') (c : ℝ) :
    G (c + ∫ v in a..b, g v) - G c = ∫ u in a..b, G' (c + ∫ v in a..u, g v) * g u := by
  set F : ℝ → ℝ := fun u => c + ∫ v in a..u, g v with hF
  have hFac : AbsolutelyContinuousOnInterval F a b := by
    have h := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp [hab])
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
      (LipschitzWith.const (α := ℝ) c).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hc.add h
  have hFc : ContinuousOn F (uIcc a b) := hFac.continuousOn
  obtain ⟨R, hR⟩ : ∃ R, ∀ u ∈ uIcc a b, |F u| ≤ R := by
    obtain ⟨R, hR⟩ := (isCompact_uIcc.image_of_continuousOn hFc).isBounded.exists_norm_le
    exact ⟨R, fun u hu => by simpa using hR (F u) ⟨u, hu, rfl⟩⟩
  -- `G` is Lipschitz on `[-R, R]`
  obtain ⟨C, hC⟩ : ∃ C, ∀ r ∈ Icc (-R) R, ‖G' r‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hG'c.continuousOn).isBounded.exists_norm_le
    exact ⟨C, fun r hr => hC _ ⟨r, hr, rfl⟩⟩
  have hLip : LipschitzOnWith (Real.toNNReal C) G (Icc (-R) R) := by
    refine (convex_Icc (-R) R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r _ => (hG r).hasDerivWithinAt) fun r hr => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact (hC r hr).trans (le_max_left _ _)
  have hGF : AbsolutelyContinuousOnInterval (G ∘ F) a b :=
    hLip.comp_absolutelyContinuousOnInterval (fun u hu => abs_le.1 (hR u hu) |> fun h => ⟨h.1, h.2⟩)
      hFac
  have hint := hGF.integral_deriv_eq_sub
  have hFa : F a = c := by simp [hF]
  simp only [Function.comp_apply, hFa] at hint
  rw [← hint]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hg.ae_hasDerivAt_integral] with u hu hmem
  have hmem' : u ∈ uIcc a b := uIoc_subset_uIcc hmem
  have hd := hu hmem' a (by simp [hab])
  have hdF : HasDerivAt F (g u) u := by simpa [hF] using hd.const_add c
  exact ((hG (F u)).comp u hdF).deriv

/-- `(min r 0)^n`. -/
noncomputable def negPow (n : ℕ) (r : ℝ) : ℝ := (min r 0) ^ n

theorem hasDerivAt_negPow {n : ℕ} (hn : 2 ≤ n) (r : ℝ) :
    HasDerivAt (negPow n) (n * negPow (n - 1) r) r := by
  unfold negPow
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have h := hasDerivAt_pow n r
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Iio_mem_nhds hr] with x hx
      rw [min_eq_left (le_of_lt hx)]
    · rw [min_eq_left hr.le]
  · subst hr
    simp only [min_self]
    rw [zero_pow (by omega), mul_zero]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, min_self, zero_pow (show n ≠ 0 by omega), sub_zero, smul_zero]
    have h1 : (fun x : ℝ => x ^ n) =o[𝓝 0] fun x => x := isLittleO_pow_id (by omega)
    refine IsBigO.trans_isLittleO ?_ h1
    refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [one_mul, norm_pow, norm_pow]
    gcongr
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total x 0 with hx | hx
    · rw [min_eq_left hx]
    · rw [min_eq_right hx, abs_zero]; exact abs_nonneg _
  · have h : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 r := hasDerivAt_const r 0
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds hr] with x hx
      rw [min_eq_right (le_of_lt hx), zero_pow (by omega)]
    · rw [min_eq_right hr.le, zero_pow (by omega), mul_zero]

theorem continuous_negPow (n : ℕ) : Continuous (negPow n) := by
  unfold negPow; fun_prop

theorem negPow_nonneg_of_even {n : ℕ} (hn : Even n) (r : ℝ) : 0 ≤ negPow n r :=
  hn.pow_nonneg _

theorem negPow_eq_zero_of_nonneg {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 ≤ r) : negPow n r = 0 := by
  unfold negPow; rw [min_eq_right hr, zero_pow hn]

end SharpLSI
