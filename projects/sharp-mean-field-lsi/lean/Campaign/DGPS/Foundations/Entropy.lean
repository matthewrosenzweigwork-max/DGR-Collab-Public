import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Homogeneous entropy (DEF004)

For a measure `P`, a function `v` and `a = ∫ v dP`, `homogeneousEntropy P v : ℝ≥0∞` is `0` if
`a = 0` and otherwise the extended integral of `v log (v / a) - v + a`
(INTERFACES/definitions.md §2). The integrand is nonnegative for `v ≥ 0`, `a > 0`, with
`0 log 0 = 0` (automatic from `Real.log 0 = 0`). The contract domain is a probability `P` and
an integrable nonnegative `v`; every theorem below states its hypotheses explicitly.

Main results:
* `DGPS.self_mul_log_sub_add_one_nonneg`: `t log t - t + 1 ≥ 0` for `t ≥ 0`.
* `DGPS.entropyIntegrand_nonneg`: the integrand is nonnegative.
* `DGPS.entropy_mass_one`: for mass one, the entropy is `∫ (v log v - v + 1) dP`.
* `DGPS.homogeneousEntropy_eq_formula`: when `v log v` is integrable, the entropy is
  `∫ v log v - a log a`.
* `DGPS.homogeneousEntropy_eq_zero_iff`: for `a > 0`, the entropy vanishes iff `v = a` a.e.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace DGPS

/-- The entropy integrand `t log (t / a) - t + a`. -/
noncomputable def entropyIntegrand (a t : ℝ) : ℝ := t * Real.log (t / a) - t + a

/-- `t log t - t + 1 ≥ 0` for `t ≥ 0`, including `t = 0`. -/
theorem self_mul_log_sub_add_one_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t * Real.log t - t + 1 := by
  have h := klFun_nonneg ht
  rw [klFun_apply] at h
  linarith

theorem entropyIntegrand_eq_mul_klFun {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    entropyIntegrand a t = a * klFun (t / a) := by
  rw [entropyIntegrand, klFun_apply]
  field_simp
  ring

theorem entropyIntegrand_nonneg {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    0 ≤ entropyIntegrand a t := by
  rw [entropyIntegrand_eq_mul_klFun ha.ne']
  exact mul_nonneg ha.le (klFun_nonneg (div_nonneg ht ha.le))

theorem entropyIntegrand_eq_zero_iff {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    entropyIntegrand a t = 0 ↔ t = a := by
  rw [entropyIntegrand_eq_mul_klFun ha.ne', mul_eq_zero, klFun_eq_zero_iff (div_nonneg ht ha.le),
    div_eq_one_iff_eq ha.ne']
  simp [ha.ne']

theorem entropyIntegrand_one (t : ℝ) : entropyIntegrand 1 t = t * Real.log t - t + 1 := by
  simp [entropyIntegrand]

section

variable {α : Type*} [MeasurableSpace α]

open Classical in
/-- Homogeneous entropy `Ent_P(v)` (DEF004), valued in `ℝ≥0∞`: zero when `a = ∫ v dP = 0`,
otherwise `∫⁻ (v log (v / a) - v + a) dP`. -/
noncomputable def homogeneousEntropy (P : Measure α) (v : α → ℝ) : ℝ≥0∞ :=
  if ∫ x, v x ∂P = 0 then 0
  else ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂P) (v x)) ∂P

theorem homogeneousEntropy_of_integral_eq_zero {P : Measure α} {v : α → ℝ}
    (h : ∫ x, v x ∂P = 0) : homogeneousEntropy P v = 0 := by
  simp [homogeneousEntropy, h]

theorem homogeneousEntropy_of_integral_ne_zero {P : Measure α} {v : α → ℝ}
    (h : ∫ x, v x ∂P ≠ 0) :
    homogeneousEntropy P v
      = ∫⁻ x, ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂P) (v x)) ∂P := by
  simp [homogeneousEntropy, h]

/-- The entropy depends on `v` only through its a.e. class. -/
theorem homogeneousEntropy_congr_ae {P : Measure α} {v w : α → ℝ} (h : v =ᵐ[P] w) :
    homogeneousEntropy P v = homogeneousEntropy P w := by
  have hi : ∫ x, v x ∂P = ∫ x, w x ∂P := integral_congr_ae h
  unfold homogeneousEntropy
  rw [hi]
  split_ifs
  · rfl
  · exact lintegral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- DEF004, mass-one case: for `∫ v dP = 1`, `Ent_P(v) = ∫ (v log v - v + 1) dP`. -/
theorem entropy_mass_one {P : Measure α} {v : α → ℝ} (hv : ∫ x, v x ∂P = 1) :
    homogeneousEntropy P v
      = ∫⁻ x, ENNReal.ofReal (v x * Real.log (v x) - v x + 1) ∂P := by
  rw [homogeneousEntropy_of_integral_ne_zero (by rw [hv]; exact one_ne_zero), hv]
  simp_rw [entropyIntegrand_one]

/-- For `a > 0`, the integrand is `a · klFun (v / a)`. -/
theorem homogeneousEntropy_eq_lintegral_klFun {P : Measure α} {v : α → ℝ}
    (ha : ∫ x, v x ∂P ≠ 0) :
    homogeneousEntropy P v
      = ∫⁻ x, ENNReal.ofReal ((∫ y, v y ∂P) * klFun (v x / ∫ y, v y ∂P)) ∂P := by
  rw [homogeneousEntropy_of_integral_ne_zero ha]
  simp_rw [entropyIntegrand_eq_mul_klFun ha]

/-- DEF004 homogeneous formula: for a probability `P`, a nonnegative integrable `v` with
`v log v` integrable, `Ent_P(v) = ∫ v log v - a log a` with `a = ∫ v dP`. -/
theorem homogeneousEntropy_eq_formula {P : Measure α} [IsProbabilityMeasure P] {v : α → ℝ}
    (hv : 0 ≤ᵐ[P] v) (hint : Integrable v P)
    (hlog : Integrable (fun x => v x * Real.log (v x)) P) :
    homogeneousEntropy P v = ENNReal.ofReal (∫ x, v x * Real.log (v x) ∂P
      - (∫ x, v x ∂P) * Real.log (∫ x, v x ∂P)) := by
  set a := ∫ x, v x ∂P with ha
  have ha0 : 0 ≤ a := integral_nonneg_of_ae hv
  rcases ha0.eq_or_lt with h0 | h0
  · rw [homogeneousEntropy_of_integral_eq_zero h0.symm]
    have hz : v =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hv hint).mp h0.symm
    have h1 : ∫ x, v x * Real.log (v x) ∂P = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [hz] with x hx; simp [hx]
    rw [← h0, h1]; simp
  · rw [homogeneousEntropy_of_integral_ne_zero h0.ne', ← ha]
    have hpt : ∀ x, entropyIntegrand a (v x)
        = v x * Real.log (v x) - v x * Real.log a + a - v x := by
      intro x
      unfold entropyIntegrand
      rcases eq_or_ne (v x) 0 with h | h
      · rw [h]; simp
      · rw [Real.log_div h h0.ne']; ring
    simp_rw [hpt]
    have hF : Integrable (fun x => v x * Real.log (v x) - v x * Real.log a + a - v x) P :=
      ((hlog.sub (hint.mul_const _)).add (integrable_const a)).sub hint
    have hnn : 0 ≤ᵐ[P] fun x => v x * Real.log (v x) - v x * Real.log a + a - v x := by
      filter_upwards [hv] with x hx
      simp only [Pi.zero_apply]
      rw [← hpt]; exact entropyIntegrand_nonneg h0 hx
    rw [← ofReal_integral_eq_lintegral_ofReal hF hnn]
    congr 1
    have i1 : Integrable (fun x => v x * Real.log a) P := hint.mul_const _
    have i2 : Integrable (fun x => v x * Real.log (v x) - v x * Real.log a) P := hlog.sub i1
    have i3 : Integrable (fun x => v x * Real.log (v x) - v x * Real.log a + a) P :=
      i2.add (integrable_const a)
    rw [integral_sub i3 hint, integral_add i2 (integrable_const a), integral_sub hlog i1,
      integral_mul_const, integral_const, ← ha]
    simp

/-- For `a = ∫ v dP > 0` and `v ≥ 0` a.e., `Ent_P(v) = 0` iff `v = a` a.e. -/
theorem homogeneousEntropy_eq_zero_iff {P : Measure α} {v : α → ℝ} (hv : 0 ≤ᵐ[P] v)
    (hmeas : AEMeasurable v P) (ha : 0 < ∫ x, v x ∂P) :
    homogeneousEntropy P v = 0 ↔ v =ᵐ[P] fun _ => ∫ y, v y ∂P := by
  rw [homogeneousEntropy_of_integral_ne_zero ha.ne']
  have hm : AEMeasurable (fun x => ENNReal.ofReal (entropyIntegrand (∫ y, v y ∂P) (v x))) P := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    unfold entropyIntegrand
    fun_prop
  rw [lintegral_eq_zero_iff' hm]
  constructor
  · intro h
    filter_upwards [h, hv] with x hx hx0
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
    exact (entropyIntegrand_eq_zero_iff ha hx0).mp
      (le_antisymm hx (entropyIntegrand_nonneg ha hx0))
  · intro h
    filter_upwards [h, hv] with x hx hx0
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
    exact ((entropyIntegrand_eq_zero_iff ha hx0).mpr hx).le

end

end DGPS
