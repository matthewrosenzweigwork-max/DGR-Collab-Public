import Mathlib
import DGPS.Foundations.Entropy

/-!
# Optional direct radial/angular route for the ordered row (FIN041, FIN044)

* `DGPS.FiniteN.optional_circle_l1_entropy_bound` (FIN041): for a nonnegative absolutely
  continuous `g` on the angle circle `ℝ / 2πℤ` with normalized Haar measure `m`,
  `Ent_m(g) ≤ 2π ∫ |g'| dm`.  The derivative `g'` is the a.e. derivative of the lift to `ℝ`,
  viewed as a function on the circle.
* `DGPS.FiniteN.optional_weighted_radial_moment_entropy_bound` (FIN044): if the probability `σ`
  satisfies `Ent_σ(u²) ≤ L ∫ |u'|² dσ` (smooth `u` of finite energy) and `M = ∫ e^{t r²} dσ < ∞`,
  then `∫∫ r² f² dσ dm ≤ (L/t) E_rad(f) + (log M / t) ‖f‖²`, via the Gibbs variational
  inequality `gibbs_weighted_moment`.
-/

open MeasureTheory AddCircle Set
open scoped ENNReal Real ContDiff

namespace DGPS.FiniteN

instance instFactTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

section Circle

variable {g g' : AddCircle (2 * π) → ℝ}

private theorem circle_lift_sub_eq_integral
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => g (t : AddCircle (2 * π))) a b)
    (hd : ∀ᵐ x : ℝ, deriv (fun t : ℝ => g (t : AddCircle (2 * π))) x = g' (x : AddCircle (2 * π)))
    (a b : ℝ) :
    g (b : AddCircle (2 * π)) - g (a : AddCircle (2 * π))
      = ∫ x in a..b, g' (x : AddCircle (2 * π)) := by
  rw [← (hac a b).integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hd] with x hx _ using hx

private theorem circle_lift_intervalIntegrable
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => g (t : AddCircle (2 * π))) a b)
    (hd : ∀ᵐ x : ℝ, deriv (fun t : ℝ => g (t : AddCircle (2 * π))) x = g' (x : AddCircle (2 * π)))
    (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => g' (x : AddCircle (2 * π))) MeasureTheory.volume a b := by
  refine ((hac a b).intervalIntegrable_deriv).congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hd] with x hx _ using hx

private theorem circle_continuous
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => g (t : AddCircle (2 * π))) a b) :
    Continuous g := by
  have hc : Continuous (fun t : ℝ => g (t : AddCircle (2 * π))) := by
    rw [continuous_iff_continuousAt]
    intro x
    have := (hac (x - 1) (x + 1)).continuousOn
    rw [uIcc_of_le (by linarith)] at this
    exact this.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hq : Topology.IsQuotientMap (QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * π))) :=
    QuotientAddGroup.isQuotientMap_mk _
  exact hq.continuous_iff.2 hc

/-- FIN041.  For a nonnegative absolutely continuous function `g` on the circle `ℝ / 2πℤ`
(its lift to `ℝ` is absolutely continuous on every interval) with a.e. derivative `g'`,
`Ent_m(g) ≤ 2π ∫ |g'| dm` for the normalized Haar measure `m`. -/
theorem optional_circle_l1_entropy_bound
    (hg : ∀ x, 0 ≤ g x)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => g (t : AddCircle (2 * π))) a b)
    (hd : ∀ᵐ x : ℝ, deriv (fun t : ℝ => g (t : AddCircle (2 * π))) x = g' (x : AddCircle (2 * π))) :
    homogeneousEntropy (haarAddCircle (T := 2 * π)) g
      ≤ ENNReal.ofReal (2 * π * ∫ x, |g' x| ∂(haarAddCircle (T := 2 * π))) := by
  set m := ∫ x, g x ∂(haarAddCircle (T := 2 * π)) with hm
  set D := 2 * π * ∫ x, |g' x| ∂(haarAddCircle (T := 2 * π)) with hD
  have hgc : Continuous g := circle_continuous hac
  have hgi : Integrable g (haarAddCircle (T := 2 * π)) := hgc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace g)
  have hm0 : 0 ≤ m := integral_nonneg hg
  have hD0 : 0 ≤ D := by
    refine mul_nonneg Real.two_pi_pos.le (integral_nonneg fun x => abs_nonneg _)
  -- the period integral of |g'|
  have hper : ∀ t : ℝ, ∫ x in t..t + 2 * π, |g' (x : AddCircle (2 * π))| = D := by
    intro t
    rw [AddCircle.intervalIntegral_preimage (2 * π) t (fun x => |g' x|), hD,
      AddCircle.integral_haarAddCircle]
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]
  -- pointwise oscillation bound
  have hosc : ∀ x y : ℝ, g (x : AddCircle (2 * π)) - g (y : AddCircle (2 * π)) ≤ D := by
    intro x y
    set y' := toIocMod Real.two_pi_pos (x - 2 * π) y with hy'
    have hy'mem : y' ∈ Ioc (x - 2 * π) (x - 2 * π + 2 * π) := toIocMod_mem_Ioc _ _ _
    have hyc : (y' : AddCircle (2 * π)) = (y : AddCircle (2 * π)) := by
      have h1 := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (x - 2 * π) y
      conv_rhs => rw [← h1]
      rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
    have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => |g' (t : AddCircle (2 * π))|)
        MeasureTheory.volume a b := fun a b => (circle_lift_intervalIntegrable hac hd a b).abs
    have hle : y' ≤ x := by
      have := hy'mem.2; linarith
    have h2 : g (x : AddCircle (2 * π)) - g (y' : AddCircle (2 * π))
        ≤ ∫ t in y'..x, |g' (t : AddCircle (2 * π))| := by
      rw [circle_lift_sub_eq_integral hac hd]
      refine intervalIntegral.integral_mono_on hle (circle_lift_intervalIntegrable hac hd _ _)
        (hint _ _) fun t _ => le_abs_self _
    have h3 : ∫ t in y'..x, |g' (t : AddCircle (2 * π))|
        ≤ ∫ t in (x - 2 * π)..x, |g' (t : AddCircle (2 * π))| := by
      have h4 := intervalIntegral.integral_add_adjacent_intervals (hint (x - 2 * π) y') (hint y' x)
      have h5 : 0 ≤ ∫ t in (x - 2 * π)..y', |g' (t : AddCircle (2 * π))| :=
        intervalIntegral.integral_nonneg (by linarith [hy'mem.1]) fun _ _ => abs_nonneg _
      linarith
    have h6 := hper (x - 2 * π)
    rw [show x - 2 * π + 2 * π = x by ring] at h6
    rw [← hyc]
    linarith
  -- sup bound
  have hbound : ∀ z : AddCircle (2 * π), g z ≤ m + D := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have : ∫ _y, (g (x : AddCircle (2 * π)) - D) ∂(haarAddCircle (T := 2 * π)) ≤ m := by
      refine integral_mono (integrable_const _) hgi fun y => ?_
      obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective y
      have := hosc x y'
      linarith
    rw [integral_const] at this
    simp only [probReal_univ, one_smul] at this
    linarith
  -- the entropy estimate
  rcases hm0.eq_or_lt with h0 | hpos
  · rw [homogeneousEntropy_of_integral_eq_zero h0.symm]
    exact bot_le
  rw [homogeneousEntropy_of_integral_ne_zero hpos.ne', ← hm]
  set B := m + D with hB
  have hBm : m ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  have hpt : ∀ z, entropyIntegrand m (g z) ≤ g z * Real.log (B / m) - g z + m := by
    intro z
    unfold entropyIntegrand
    have : g z * Real.log (g z / m) ≤ g z * Real.log (B / m) := by
      rcases (hg z).eq_or_lt with h | h
      · rw [← h]; simp
      · refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos h hpos) ?_) h.le
        exact div_le_div_of_nonneg_right (hbound z) hpos.le
    linarith
  set h2 : AddCircle (2 * π) → ℝ := fun z => g z * Real.log (B / m) - g z + m with hh2
  have h2int : Integrable h2 (haarAddCircle (T := 2 * π)) :=
    ((hgi.mul_const _).sub hgi).add (integrable_const _)
  have h2nn : 0 ≤ᵐ[haarAddCircle (T := 2 * π)] h2 := by
    refine Filter.Eventually.of_forall fun z => ?_
    exact (entropyIntegrand_nonneg hpos (hg z)).trans (hpt z)
  have hint2 : ∫ z, h2 z ∂(haarAddCircle (T := 2 * π)) = m * Real.log (B / m) := by
    simp only [hh2]
    have i1 : Integrable (fun z => g z * Real.log (B / m)) (haarAddCircle (T := 2 * π)) :=
      hgi.mul_const _
    have i2 : Integrable (fun z => g z * Real.log (B / m) - g z) (haarAddCircle (T := 2 * π)) :=
      i1.sub hgi
    rw [integral_add i2 (integrable_const _), integral_sub i1 hgi, integral_mul_const,
      integral_const]
    simp [← hm]
  calc ∫⁻ z, ENNReal.ofReal (entropyIntegrand m (g z)) ∂(haarAddCircle (T := 2 * π))
      ≤ ∫⁻ z, ENNReal.ofReal (h2 z) ∂(haarAddCircle (T := 2 * π)) :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hpt z)
    _ = ENNReal.ofReal (∫ z, h2 z ∂(haarAddCircle (T := 2 * π))) :=
        (ofReal_integral_eq_lintegral_ofReal h2int h2nn).symm
    _ ≤ ENNReal.ofReal D := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hint2]
        have := Real.log_le_sub_one_of_pos (div_pos hBpos hpos)
        have h3 : m * Real.log (B / m) ≤ m * (B / m - 1) := mul_le_mul_of_nonneg_left this hpos.le
        have h4 : m * (B / m - 1) = D := by field_simp; rw [hB]; ring
        linarith


end Circle

section Radial

/-- pointwise Gibbs inequality -/
private theorem gibbs_pointwise {a M φ h : ℝ} (ha : 0 < a) (hM : 0 < M) (hh : 0 ≤ h) :
    h * φ ≤ entropyIntegrand a h - a + h * Real.log M + a * Real.exp φ / M := by
  have hex : 0 < a * Real.exp φ / M := by positivity
  rcases hh.eq_or_lt with h0 | h0
  · subst h0
    simp [entropyIntegrand]
    exact hex.le
  · have hx : 0 < a * Real.exp φ / (h * M) := by positivity
    have hl := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul h0.ne' hM.ne', Real.log_exp] at hl
    have h2 : a * Real.exp φ / (h * M) = (a * Real.exp φ / M) / h := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hl h0.le
    have h3 : h * (a * Real.exp φ / M / h - 1) = a * Real.exp φ / M - h := by field_simp
    rw [h2, h3] at hmul
    unfold entropyIntegrand
    rw [Real.log_div h0.ne' ha.ne']
    nlinarith [hmul]

theorem gibbs_weighted_moment {σ : Measure ℝ} [IsProbabilityMeasure σ] {t M : ℝ} (ht : 0 < t)
    (hMi : Integrable (fun r : ℝ => Real.exp (t * r ^ 2)) σ)
    (hM : ∫ r, Real.exp (t * r ^ 2) ∂σ = M) {h : ℝ → ℝ} (hmeas : Measurable h)
    (hh0 : ∀ r, 0 ≤ h r) (hint : Integrable h σ) (hent : homogeneousEntropy σ h ≠ ⊤) :
    Integrable (fun r : ℝ => t * r ^ 2 * h r) σ ∧
      ∫ r, t * r ^ 2 * h r ∂σ
        ≤ (homogeneousEntropy σ h).toReal + (∫ r, h r ∂σ) * Real.log M := by
  set a := ∫ r, h r ∂σ with ha
  have ha0 : 0 ≤ a := integral_nonneg hh0
  rcases ha0.eq_or_lt with h0 | hpos
  · have hz : h =ᵐ[σ] 0 := (integral_eq_zero_iff_of_nonneg hh0 hint).mp h0.symm
    have hz2 : (fun r : ℝ => t * r ^ 2 * h r) =ᵐ[σ] 0 := by
      filter_upwards [hz] with r hr; simp [hr]
    refine ⟨(integrable_zero _ _ _).congr hz2.symm, ?_⟩
    rw [integral_congr_ae hz2, homogeneousEntropy_of_integral_eq_zero h0.symm, ← h0]
    simp
  · have hM1 : 1 ≤ M := by
      rw [← hM]
      have : ∫ _r : ℝ, (1 : ℝ) ∂σ ≤ ∫ r, Real.exp (t * r ^ 2) ∂σ :=
        integral_mono (integrable_const _) hMi fun r => by
          have : 0 ≤ t * r ^ 2 := by positivity
          simpa using Real.one_le_exp this
      simpa using this
    have hMpos : 0 < M := by linarith
    rw [homogeneousEntropy_of_integral_ne_zero hpos.ne', ← ha] at hent ⊢
    set E : ℝ → ℝ := fun r => entropyIntegrand a (h r) with hE
    have hE0 : ∀ r, 0 ≤ E r := fun r => entropyIntegrand_nonneg hpos (hh0 r)
    have hEm : Measurable E := by
      simp only [hE, entropyIntegrand]; fun_prop
    have hEi : Integrable E σ := by
      refine ⟨hEm.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      have : ∀ r, ‖E r‖ₑ = ENNReal.ofReal (E r) := fun r => by
        rw [Real.enorm_eq_ofReal (hE0 r)]
      simp_rw [this]
      exact lt_top_iff_ne_top.2 hent
    have hEint : ∫ r, E r ∂σ = (∫⁻ r, ENNReal.ofReal (E r) ∂σ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hE0) hEm.aestronglyMeasurable
    set R : ℝ → ℝ := fun r => E r - a + h r * Real.log M + a * Real.exp (t * r ^ 2) / M with hR
    have hRi : Integrable R σ :=
      (((hEi.sub (integrable_const a)).add (hint.mul_const _)).add (hMi.const_mul a |>.div_const M))
    have hpt : ∀ r, t * r ^ 2 * h r ≤ R r := fun r => by
      have := gibbs_pointwise (φ := t * r ^ 2) hpos hMpos (hh0 r)
      simp only [hR, hE]; linarith
    have hmeas2 : Measurable (fun r : ℝ => t * r ^ 2 * h r) := by fun_prop
    have hI : Integrable (fun r : ℝ => t * r ^ 2 * h r) σ := by
      refine hRi.mono' hmeas2.aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
      have h1 : 0 ≤ t * r ^ 2 * h r := by have := hh0 r; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact hpt r
    refine ⟨hI, ?_⟩
    calc ∫ r, t * r ^ 2 * h r ∂σ ≤ ∫ r, R r ∂σ := integral_mono hI hRi hpt
      _ = (∫⁻ r, ENNReal.ofReal (E r) ∂σ).toReal + a * Real.log M := by
        have i1 : Integrable (fun r => E r - a) σ := hEi.sub (integrable_const a)
        have i2 : Integrable (fun r => E r - a + h r * Real.log M) σ := i1.add (hint.mul_const _)
        simp only [hR]
        rw [integral_add i2 ((hMi.const_mul a).div_const M), integral_add i1 (hint.mul_const _),
          integral_sub hEi (integrable_const a), integral_div, integral_const_mul, hM,
          integral_mul_const, hEint]
        simp
        field_simp
        ring

/-- FIN044: weighted radial moment entropy bound. -/
theorem optional_weighted_radial_moment_entropy_bound
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {L t M : ℝ} (hL : 0 ≤ L) (ht : 0 < t)
    (hlsi : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → Integrable (fun r => u r ^ 2) σ →
      Integrable (fun r => deriv u r ^ 2) σ →
      homogeneousEntropy σ (fun r => u r ^ 2) ≤ ENNReal.ofReal (L * ∫ r, deriv u r ^ 2 ∂σ))
    (hMi : Integrable (fun r : ℝ => Real.exp (t * r ^ 2)) σ)
    (hM : ∫ r, Real.exp (t * r ^ 2) ∂σ = M)
    {f : ℝ → AddCircle (2 * π) → ℝ} (hf : ∀ θ, ContDiff ℝ ∞ (fun r => f r θ))
    (hfi : Integrable (fun p : AddCircle (2 * π) × ℝ => f p.2 p.1 ^ 2)
      ((haarAddCircle (T := 2 * π)).prod σ))
    (hdi : Integrable (fun p : AddCircle (2 * π) × ℝ => deriv (fun r => f r p.1) p.2 ^ 2)
      ((haarAddCircle (T := 2 * π)).prod σ)) :
    ∫ θ, ∫ r, r ^ 2 * f r θ ^ 2 ∂σ ∂(haarAddCircle (T := 2 * π))
      ≤ (L / t) * ∫ θ, ∫ r, deriv (fun s => f s θ) r ^ 2 ∂σ ∂(haarAddCircle (T := 2 * π))
        + (Real.log M / t) * ∫ θ, ∫ r, f r θ ^ 2 ∂σ ∂(haarAddCircle (T := 2 * π)) := by
  set m := haarAddCircle (T := 2 * π) with hm
  have hAi : Integrable (fun θ => ∫ r, f r θ ^ 2 ∂σ) m := hfi.integral_prod_left
  have hDi : Integrable (fun θ => ∫ r, deriv (fun s => f s θ) r ^ 2 ∂σ) m := hdi.integral_prod_left
  have hBi : Integrable (fun θ => (L / t) * ∫ r, deriv (fun s => f s θ) r ^ 2 ∂σ
      + (Real.log M / t) * ∫ r, f r θ ^ 2 ∂σ) m :=
    (hDi.const_mul _).add (hAi.const_mul _)
  have hfae := hfi.prod_right_ae
  have hdae := hdi.prod_right_ae
  have hmain : ∀ᵐ θ ∂m, ∫ r, r ^ 2 * f r θ ^ 2 ∂σ
      ≤ (L / t) * ∫ r, deriv (fun s => f s θ) r ^ 2 ∂σ
        + (Real.log M / t) * ∫ r, f r θ ^ 2 ∂σ := by
    filter_upwards [hfae, hdae] with θ h1 h2
    have hu := hf θ
    have hcont : Continuous (fun r => f r θ) := hu.continuous
    have hmeas : Measurable (fun r => f r θ ^ 2) := (hcont.pow 2).measurable
    have hent := hlsi _ hu h1 h2
    have hne : homogeneousEntropy σ (fun r => f r θ ^ 2) ≠ ⊤ := ne_top_of_le_ne_top
      ENNReal.ofReal_ne_top hent
    obtain ⟨_, hg⟩ := gibbs_weighted_moment ht hMi hM hmeas (fun r => sq_nonneg _) h1 hne
    have hent' : (homogeneousEntropy σ (fun r => f r θ ^ 2)).toReal
        ≤ L * ∫ r, deriv (fun s => f s θ) r ^ 2 ∂σ :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hent).trans
        (ENNReal.toReal_ofReal (mul_nonneg hL (integral_nonneg fun r => sq_nonneg _))).le
    have e1 : ∫ r, t * r ^ 2 * f r θ ^ 2 ∂σ = t * ∫ r, r ^ 2 * f r θ ^ 2 ∂σ := by
      rw [← integral_const_mul]; congr 1; ext r; ring
    rw [e1] at hg
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, le_div_iff₀ ht]
    linarith
  have hB := integral_mono_of_nonneg
    (f := fun θ => ∫ r, r ^ 2 * f r θ ^ 2 ∂σ) (Filter.Eventually.of_forall fun θ =>
      integral_nonneg fun r => by positivity) hBi hmain
  rw [integral_add (hDi.const_mul _) (hAi.const_mul _), integral_const_mul,
    integral_const_mul] at hB
  exact hB

end Radial

end DGPS.FiniteN
