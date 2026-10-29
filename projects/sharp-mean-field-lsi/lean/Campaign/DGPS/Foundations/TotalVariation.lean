import DGPS.Foundations.RelativeEntropy
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Full total-variation normalization (DEF029)

`fullVariation ν η` is the total mass of the variation measure of the signed measure `ν - η`
(INTERFACES/definitions.md §5): the **full** norm, not the half-variation convention. For
probabilities its range is `[0, 2]`, and `fullVariation ν η = ∫ |ρ - p| dm` for densities.

Main results:
* `DGPS.fullVariation_eq_integral_abs`: `‖ν - η‖_TV = ∫ |dν/dμ - dη/dμ| dμ` for any dominating `μ`.
* `DGPS.fullVariation_eq_integral_abs_add`: the same with `μ = ν + η`, no hypotheses.
* `DGPS.fullVariation_le_two`, `DGPS.fullVariation_nonneg`, `DGPS.fullVariation_comm`,
  `DGPS.fullVariation_eq_zero_iff`, `DGPS.fullVariation_self`.
* `DGPS.fullVariation_eq_two_mul_sup`: `‖ν - η‖_TV = 2 sup_A |ν(A) - η(A)|` for probabilities
  (the factor-of-two conversion to the half-variation / sup-over-sets convention).
* `DGPS.pinsker_fullVariation`: `‖ν - P‖_TV² ≤ 2 H(ν | P)` (exact constant, full variation).
-/

open MeasureTheory Set
open scoped ENNReal

namespace DGPS

section Calculus

private theorem hasDerivAt_logMean (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (t + 1) * Real.log t - 2 * (t - 1)) (Real.log t + t⁻¹ - 1) t := by
  have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 t := (hasDerivAt_id t).add_const 1
  have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h3 : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 t := by
    simpa using ((hasDerivAt_id t).sub_const 1).const_mul 2
  convert (h1.mul h2).sub h3 using 1
  field_simp
  ring

private theorem logMean_monotoneOn :
    MonotoneOn (fun t : ℝ => (t + 1) * Real.log t - 2 * (t - 1)) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun t ht => (hasDerivAt_logMean t ht).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun t ht => (hasDerivAt_logMean t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro t ht
    rw [(hasDerivAt_logMean t ht).deriv]
    have := Real.one_sub_inv_le_log_of_pos ht
    linarith

private theorem logMean_nonneg {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ (t + 1) * Real.log t - 2 * (t - 1) := by
  have := logMean_monotoneOn (show (1 : ℝ) ∈ Ioi 0 by simp) (show t ∈ Ioi 0 from by
    simp only [mem_Ioi]; linarith) ht
  simpa using this

private theorem logMean_nonpos {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1) :
    (t + 1) * Real.log t - 2 * (t - 1) ≤ 0 := by
  have := logMean_monotoneOn (show t ∈ Ioi 0 from ht0) (show (1 : ℝ) ∈ Ioi 0 by simp) ht
  simpa using this

/-- The auxiliary function `(4 + 2t)(t log t - t + 1) - 3 (t-1)^2` of the Pinsker proof. -/
private noncomputable def pinskerAux (t : ℝ) : ℝ :=
  (4 + 2 * t) * (t * Real.log t - t + 1) - 3 * (t - 1) ^ 2

private theorem hasDerivAt_pinskerAux (t : ℝ) (ht : 0 < t) :
    HasDerivAt pinskerAux (4 * ((t + 1) * Real.log t - 2 * (t - 1))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 4 + 2 * t) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).const_add 4
  have h2 : HasDerivAt (fun t : ℝ => t * Real.log t - t + 1) (Real.log t) t := by
    have := ((Real.hasDerivAt_mul_log ht.ne').sub (hasDerivAt_id t)).add_const 1
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp)
  have h3 : HasDerivAt (fun t : ℝ => 3 * (t - 1) ^ 2) (3 * (2 * (t - 1))) t := by
    have := ((hasDerivAt_id t).sub_const 1).pow 2
    simpa using this.const_mul 3
  have := (h1.mul h2).sub h3
  unfold pinskerAux
  convert this using 1
  ring

private theorem pinskerAux_continuous : Continuous pinskerAux := by
  unfold pinskerAux
  have := Real.continuous_mul_log
  fun_prop

/-- The elementary inequality behind Pinsker: `3 (t-1)^2 ≤ (4 + 2t)(t log t - t + 1)`. -/
theorem three_mul_sq_le_mul_entropy {t : ℝ} (ht : 0 ≤ t) :
    3 * (t - 1) ^ 2 ≤ (4 + 2 * t) * (t * Real.log t - t + 1) := by
  have hmain : 0 ≤ pinskerAux t := by
    have h1 : pinskerAux 1 = 0 := by simp [pinskerAux]
    rcases le_total 1 t with h | h
    · have hm : MonotoneOn pinskerAux (Ici 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
        · exact pinskerAux_continuous.continuousOn
        · rw [interior_Ici]
          exact fun s hs => (hasDerivAt_pinskerAux s (lt_trans one_pos hs)).differentiableAt.differentiableWithinAt
        · rw [interior_Ici]
          intro s hs
          rw [(hasDerivAt_pinskerAux s (lt_trans one_pos hs)).deriv]
          have := logMean_nonneg (le_of_lt (show (1:ℝ) < s from hs))
          linarith
      have := hm (show (1 : ℝ) ∈ Ici 1 by simp) (show t ∈ Ici 1 from h) h
      linarith
    · have hm : AntitoneOn pinskerAux (Icc 0 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
        · exact pinskerAux_continuous.continuousOn
        · rw [interior_Icc]
          exact fun s hs => (hasDerivAt_pinskerAux s hs.1).differentiableAt.differentiableWithinAt
        · rw [interior_Icc]
          intro s hs
          rw [(hasDerivAt_pinskerAux s hs.1).deriv]
          have := logMean_nonpos hs.1 hs.2.le
          linarith
      have := hm (show t ∈ Icc (0:ℝ) 1 from ⟨ht, h⟩) (show (1 : ℝ) ∈ Icc (0:ℝ) 1 by simp) h
      linarith
  unfold pinskerAux at hmain
  linarith


end Calculus

section Variation

variable {α : Type*} [MeasurableSpace α]

/-- DEF029: the **full** total variation of `ν - η`, i.e. the total mass of the variation measure
of the signed measure `ν - η` (Jordan decomposition `ν - η = (ν - η)⁺ - (ν - η)⁻`,
`‖ν - η‖_TV = (ν - η)⁺(univ) + (ν - η)⁻(univ)`). This is twice the "half-variation" convention. -/
noncomputable def fullVariation (ν η : Measure α) [IsFiniteMeasure ν] [IsFiniteMeasure η] : ℝ :=
  (ν.toSignedMeasure - η.toSignedMeasure).totalVariation.real univ

variable (ν η : Measure α) [IsFiniteMeasure ν] [IsFiniteMeasure η]

theorem signedDiff_apply {E : Set α} (hE : MeasurableSet E) :
    (ν.toSignedMeasure - η.toSignedMeasure) E = ν.real E - η.real E := by
  rw [sub_apply, Measure.toSignedMeasure_apply_measurable hE,
    Measure.toSignedMeasure_apply_measurable hE]

theorem fullVariation_nonneg : 0 ≤ fullVariation ν η := measureReal_nonneg

theorem fullVariation_comm : fullVariation ν η = fullVariation η ν := by
  unfold fullVariation
  rw [← SignedMeasure.totalVariation_neg, neg_sub]

theorem fullVariation_self : fullVariation ν ν = 0 := by
  unfold fullVariation
  rw [sub_self, SignedMeasure.totalVariation_zero]
  simp

/-- The total variation measure of `ν - η` is dominated by `ν + η`. -/
theorem totalVariation_signedDiff_le :
    (ν.toSignedMeasure - η.toSignedMeasure).totalVariation ≤ ν + η := by
  rw [SignedMeasure.totalVariation_eq_variation]
  refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
  rw [signedDiff_apply ν η hE, Measure.coe_add, Pi.add_apply]
  rw [← ofReal_norm, Real.norm_eq_abs]
  have h1 : ν.real E = (ν E).toReal := rfl
  have h2 : η.real E = (η E).toReal := rfl
  calc ENNReal.ofReal |ν.real E - η.real E|
      ≤ ENNReal.ofReal (ν.real E + η.real E) :=
        ENNReal.ofReal_le_ofReal (by
          rw [abs_le]; constructor <;> linarith [measureReal_nonneg (μ := ν) (s := E),
            measureReal_nonneg (μ := η) (s := E)])
    _ = ν E + η E := by
        rw [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg, h1, h2,
          ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The full variation is at most the sum of the total masses; for probabilities it is `≤ 2`. -/
theorem fullVariation_le_add : fullVariation ν η ≤ ν.real univ + η.real univ := by
  unfold fullVariation
  have h := totalVariation_signedDiff_le ν η
  have := (ENNReal.toReal_mono (measure_ne_top _ _) (h univ))
  simpa [Measure.real, ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top η _)] using this

theorem fullVariation_le_two [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    fullVariation ν η ≤ 2 := by
  have := fullVariation_le_add ν η
  simp at this
  linarith

/-- The full variation is bounded below by `|ν(E) - η(E)|`. -/
theorem abs_sub_le_fullVariation {E : Set α} (hE : MeasurableSet E) :
    |ν.real E - η.real E| ≤ (ν.toSignedMeasure - η.toSignedMeasure).totalVariation.real E := by
  have := SignedMeasure.norm_le_totalVariation (ν.toSignedMeasure - η.toSignedMeasure) E
  rwa [signedDiff_apply ν η hE, Real.norm_eq_abs] at this

theorem fullVariation_eq_zero_iff : fullVariation ν η = 0 ↔ ν = η := by
  constructor
  · intro h
    ext E hE
    have h0 : (ν.toSignedMeasure - η.toSignedMeasure).totalVariation univ = 0 := by
      have := (measureReal_eq_zero_iff (μ := (ν.toSignedMeasure - η.toSignedMeasure).totalVariation)
        (s := univ)).mp h
      exact this
    have hE0 : (ν.toSignedMeasure - η.toSignedMeasure).totalVariation E = 0 :=
      le_antisymm (h0 ▸ measure_mono (subset_univ E)) bot_le
    have h1 := abs_sub_le_fullVariation ν η hE
    have h2 : (ν.toSignedMeasure - η.toSignedMeasure).totalVariation.real E = 0 := by
      simp [Measure.real, hE0]
    rw [h2] at h1
    have h3 : ν.real E = η.real E := by
      have := abs_nonneg (ν.real E - η.real E)
      linarith [abs_eq_zero.mp (le_antisymm h1 this)]
    simpa [Measure.real, ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν E)
      (measure_ne_top η E)] using h3
  · rintro rfl
    exact fullVariation_self ν

/-- Density formula for the full variation, for any dominating σ-finite measure `μ`:
`‖ν - η‖_TV = ∫ |dν/dμ - dη/dμ| dμ`. -/
theorem fullVariation_eq_integral_abs (μ : Measure α) [SigmaFinite μ] (hν : ν ≪ μ) (hη : η ≪ μ) :
    fullVariation ν η =
      ∫ x, |(ν.rnDeriv μ x).toReal - (η.rnDeriv μ x).toReal| ∂μ := by
  set u : α → ℝ := fun x => (ν.rnDeriv μ x).toReal - (η.rnDeriv μ x).toReal with hu
  have hum : Measurable u :=
    ((Measure.measurable_rnDeriv ν μ).ennreal_toReal).sub
      ((Measure.measurable_rnDeriv η μ).ennreal_toReal)
  have hui : Integrable u μ :=
    (Measure.integrable_toReal_rnDeriv).sub (Measure.integrable_toReal_rnDeriv)
  have hs : ∀ E, MeasurableSet E →
      (ν.toSignedMeasure - η.toSignedMeasure) E = ∫ x in E, u x ∂μ := by
    intro E hE
    rw [signedDiff_apply ν η hE, hu, integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
      Measure.integrable_toReal_rnDeriv.integrableOn, Measure.setIntegral_toReal_rnDeriv hν,
      Measure.setIntegral_toReal_rnDeriv hη]
  apply le_antisymm
  · -- `≤`
    have hle : (ν.toSignedMeasure - η.toSignedMeasure).totalVariation
        ≤ μ.withDensity (fun x => ‖u x‖ₑ) := by
      rw [SignedMeasure.totalVariation_eq_variation]
      refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
      rw [hs E hE, withDensity_apply _ hE]
      exact enorm_integral_le_lintegral_enorm _
    have h1 := ENNReal.toReal_mono (by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact (hui.norm.lintegral_lt_top |>.ne) |> fun h => by
        simpa [Integrable, HasFiniteIntegral] using hui.2.ne) (hle univ)
    unfold fullVariation
    refine h1.trans_eq ?_
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← integral_norm_eq_lintegral_enorm hui.aestronglyMeasurable]
    simp only [Real.norm_eq_abs]
    rfl
  · -- `≥`
    set E : Set α := {x | 0 < u x} with hE
    have hEm : MeasurableSet E := measurableSet_lt measurable_const hum
    have hEc : MeasurableSet Eᶜ := hEm.compl
    have b1 := abs_sub_le_fullVariation ν η hEm
    have b2 := abs_sub_le_fullVariation ν η hEc
    have hsE : ν.real E - η.real E = ∫ x in E, u x ∂μ := by
      rw [← signedDiff_apply ν η hEm, hs E hEm]
    have hsEc : ν.real Eᶜ - η.real Eᶜ = ∫ x in Eᶜ, u x ∂μ := by
      rw [← signedDiff_apply ν η hEc, hs Eᶜ hEc]
    have i1 : 0 ≤ ∫ x in E, u x ∂μ :=
      setIntegral_nonneg hEm fun x hx => le_of_lt hx
    have i2 : ∫ x in Eᶜ, u x ∂μ ≤ 0 :=
      setIntegral_nonpos hEc fun x hx => not_lt.mp hx
    have hsplit : ∫ x, |u x| ∂μ = (∫ x in E, u x ∂μ) + -∫ x in Eᶜ, u x ∂μ := by
      rw [← integral_add_compl hEm hui.abs, ← integral_neg]
      congr 1
      · exact setIntegral_congr_fun hEm fun x hx => abs_of_pos hx
      · exact setIntegral_congr_fun hEc fun x hx => abs_of_nonpos (not_lt.mp (show ¬ 0 < u x from hx))
    have hadd : (ν.toSignedMeasure - η.toSignedMeasure).totalVariation.real E
        + (ν.toSignedMeasure - η.toSignedMeasure).totalVariation.real Eᶜ
        = fullVariation ν η := by
      unfold fullVariation
      exact measureReal_add_measureReal_compl hEm
    rw [abs_of_nonneg (by rw [hsE]; exact i1)] at b1
    rw [abs_of_nonpos (by rw [hsEc]; exact i2)] at b2
    rw [hsE] at b1
    rw [hsEc] at b2
    rw [hsplit]
    linarith

/-- Density formula without any hypothesis on a dominating measure: take `μ = ν + η`. -/
theorem fullVariation_eq_integral_abs_add :
    fullVariation ν η = ∫ x, |(ν.rnDeriv (ν + η) x).toReal - (η.rnDeriv (ν + η) x).toReal|
      ∂(ν + η) :=
  fullVariation_eq_integral_abs ν η (ν + η)
    (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))
    (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))

/-- The factor-of-two conversion: for probabilities the full variation is twice the supremum over
measurable sets of `|ν(A) - η(A)|` (the "half-variation" / sup-over-sets distance), and the
supremum is attained. -/
theorem fullVariation_eq_two_mul_sup [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    IsGreatest {x : ℝ | ∃ A : Set α, MeasurableSet A ∧ x = |ν.real A - η.real A|}
      (fullVariation ν η / 2) := by
  set s := ν.toSignedMeasure - η.toSignedMeasure with hs
  have hcompl : ∀ A, MeasurableSet A → ν.real Aᶜ - η.real Aᶜ = -(ν.real A - η.real A) := by
    intro A hA
    have h1 := measureReal_add_measureReal_compl (μ := ν) hA
    have h2 := measureReal_add_measureReal_compl (μ := η) hA
    simp at h1 h2
    linarith
  have hadd : ∀ A, MeasurableSet A →
      s.totalVariation.real A + s.totalVariation.real Aᶜ = fullVariation ν η := by
    intro A hA
    unfold fullVariation
    exact measureReal_add_measureReal_compl hA
  constructor
  · -- attained by `E = {u > 0}`, `u = dν/dμ - dη/dμ`, `μ = ν + η`
    set μ := ν + η with hμ
    set u : α → ℝ := fun x => (ν.rnDeriv μ x).toReal - (η.rnDeriv μ x).toReal with hu
    have hum : Measurable u :=
      ((Measure.measurable_rnDeriv ν μ).ennreal_toReal).sub
        ((Measure.measurable_rnDeriv η μ).ennreal_toReal)
    have hui : Integrable u μ :=
      (Measure.integrable_toReal_rnDeriv).sub (Measure.integrable_toReal_rnDeriv)
    have hνμ : ν ≪ μ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
    have hημ : η ≪ μ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
    set E : Set α := {x | 0 < u x} with hE
    have hEm : MeasurableSet E := measurableSet_lt measurable_const hum
    have hEc : MeasurableSet Eᶜ := hEm.compl
    have hsE : ν.real E - η.real E = ∫ x in E, u x ∂μ := by
      rw [hu, integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
        Measure.integrable_toReal_rnDeriv.integrableOn, Measure.setIntegral_toReal_rnDeriv hνμ,
        Measure.setIntegral_toReal_rnDeriv hημ]
    have hsEc : ν.real Eᶜ - η.real Eᶜ = ∫ x in Eᶜ, u x ∂μ := by
      rw [hu, integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
        Measure.integrable_toReal_rnDeriv.integrableOn, Measure.setIntegral_toReal_rnDeriv hνμ,
        Measure.setIntegral_toReal_rnDeriv hημ]
    have i1 : 0 ≤ ∫ x in E, u x ∂μ :=
      setIntegral_nonneg hEm fun x hx => le_of_lt hx
    have hsplit : ∫ x, |u x| ∂μ = (∫ x in E, u x ∂μ) + -∫ x in Eᶜ, u x ∂μ := by
      rw [← integral_add_compl hEm hui.abs, ← integral_neg]
      congr 1
      · exact setIntegral_congr_fun hEm fun x hx => abs_of_pos hx
      · exact setIntegral_congr_fun hEc fun x hx => abs_of_nonpos (not_lt.mp (show ¬ 0 < u x from hx))
    have hF := fullVariation_eq_integral_abs ν η μ hνμ hημ
    refine ⟨E, hEm, ?_⟩
    rw [abs_of_nonneg (by rw [hsE]; exact i1), hsE]
    have := hcompl E hEm
    rw [hsE, hsEc] at this
    rw [hF, hsplit]
    linarith
  · rintro x ⟨A, hA, rfl⟩
    have b1 := abs_sub_le_fullVariation ν η hA
    have b2 := abs_sub_le_fullVariation ν η hA.compl
    rw [hcompl A hA, abs_neg] at b2
    have := hadd A hA
    linarith

end Variation

section Pinsker

variable {α : Type*} [MeasurableSpace α]

/-- Pointwise form of Pinsker's inequality, with a free scale `c > 0`:
`|t - 1| ≤ (t log t - t + 1) / (6c) + c (2 + t)`. -/
theorem abs_sub_one_le_entropy {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    |t - 1| ≤ (t * Real.log t - t + 1) / (6 * c) + c * (2 + t) := by
  have h := three_mul_sq_le_mul_entropy ht
  set k := t * Real.log t - t + 1 with hk
  set m := 2 + t with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have key : 0 ≤ 2 * m * (6 * c ^ 2 * m + k - 6 * c * |t - 1|) := by
    nlinarith [sq_nonneg (2 * c * m - |t - 1|), sq_abs (t - 1)]
  have key2 : 0 ≤ 6 * c ^ 2 * m + k - 6 * c * |t - 1| :=
    nonneg_of_mul_nonneg_right key (by positivity) |> fun h => by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith [mul_pos (mul_pos two_pos hm0) (neg_pos.mpr hneg)]
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  nlinarith

/-- Real-variable core of Pinsker's inequality for a probability density `v`. -/
theorem sq_integral_abs_sub_one_le {P : Measure α} [IsProbabilityMeasure P] {v : α → ℝ}
    (hv0 : ∀ x, 0 ≤ v x) (hvi : Integrable v P) (hv1 : ∫ x, v x ∂P = 1)
    (hki : Integrable (fun x => v x * Real.log (v x) - v x + 1) P) :
    (∫ x, |v x - 1| ∂P) ^ 2 ≤ 2 * ∫ x, (v x * Real.log (v x) - v x + 1) ∂P := by
  set T := ∫ x, |v x - 1| ∂P with hT
  set K := ∫ x, (v x * Real.log (v x) - v x + 1) ∂P with hK
  have hT0 : 0 ≤ T := integral_nonneg fun x => abs_nonneg _
  rcases hT0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have : 0 ≤ K := integral_nonneg fun x => self_mul_log_sub_add_one_nonneg (hv0 x)
    simp; linarith
  · have hc : 0 < T / 6 := by positivity
    have hA : Integrable (fun x => (v x * Real.log (v x) - v x + 1) / (6 * (T / 6))) P :=
      hki.div_const _
    have hB : Integrable (fun x => T / 6 * (2 + v x)) P := by
      have := ((integrable_const (2 : ℝ)).add hvi).const_mul (T / 6)
      simpa using this
    have hmono : T ≤ ∫ x, ((v x * Real.log (v x) - v x + 1) / (6 * (T / 6))
        + (T / 6) * (2 + v x)) ∂P :=
      integral_mono (hvi.sub (integrable_const 1)).abs (hA.add hB) fun x =>
        abs_sub_one_le_entropy (hv0 x) hc
    have hC : ∫ x, (2 + v x) ∂P = 3 := by
      rw [integral_add (integrable_const 2) hvi, hv1]
      simp; norm_num
    have hcalc : ∫ x, ((v x * Real.log (v x) - v x + 1) / (6 * (T / 6))
        + (T / 6) * (2 + v x)) ∂P = K / T + T / 2 := by
      rw [integral_add hA hB, integral_div, integral_const_mul, hC, ← hK]
      field_simp
      ring
    rw [hcalc] at hmono
    have h2 : T / 2 ≤ K / T := by linarith
    rw [le_div_iff₀ hpos] at h2
    nlinarith

/-- **Pinsker's inequality in the full-variation normalization** (DEF029):
`‖ν - P‖_TV² ≤ 2 H(ν | P)`, with the exact constant `2` (not the half-variation constant). -/
theorem pinsker_fullVariation (ν P : Measure α) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure P] :
    ENNReal.ofReal (fullVariation ν P ^ 2) ≤ 2 * relativeEntropy ν P := by
  by_cases hac : ν ≪ P
  swap
  · simp [relativeEntropy_of_not_absolutelyContinuous hac]
  rw [relativeEntropy_of_absolutelyContinuous hac]
  set v : α → ℝ := fun x => (ν.rnDeriv P x).toReal with hv
  have hvm : Measurable v := (Measure.measurable_rnDeriv ν P).ennreal_toReal
  have hv0 : ∀ x, 0 ≤ v x := fun x => ENNReal.toReal_nonneg
  have hvi : Integrable v P := Measure.integrable_toReal_rnDeriv
  have hv1 : ∫ x, v x ∂P = 1 := by
    simp only [hv]
    rw [Measure.integral_toReal_rnDeriv hac]; simp
  have hT : fullVariation ν P = ∫ x, |v x - 1| ∂P := by
    rw [fullVariation_eq_integral_abs ν P P hac Measure.AbsolutelyContinuous.rfl]
    apply integral_congr_ae
    filter_upwards [Measure.rnDeriv_self P] with x hx
    simp [hv, hx]
  rw [entropy_mass_one hv1, hT]
  have hkm : Measurable fun x => v x * Real.log (v x) - v x + 1 := by fun_prop
  have hk0 : ∀ x, 0 ≤ v x * Real.log (v x) - v x + 1 := fun x =>
    self_mul_log_sub_add_one_nonneg (hv0 x)
  by_cases htop : ∫⁻ x, ENNReal.ofReal (v x * Real.log (v x) - v x + 1) ∂P = ⊤
  · rw [htop]; simp
  · have hki : Integrable (fun x => v x * Real.log (v x) - v x + 1) P :=
      (lintegral_ofReal_ne_top_iff_integrable hkm.aestronglyMeasurable
        (Filter.Eventually.of_forall hk0)).mp htop
    rw [← ofReal_integral_eq_lintegral_ofReal hki (Filter.Eventually.of_forall hk0)]
    have hcore := sq_integral_abs_sub_one_le hv0 hvi hv1 hki
    calc ENNReal.ofReal ((∫ x, |v x - 1| ∂P) ^ 2)
        ≤ ENNReal.ofReal (2 * ∫ x, (v x * Real.log (v x) - v x + 1) ∂P) :=
          ENNReal.ofReal_le_ofReal hcore
      _ = 2 * ENNReal.ofReal (∫ x, (v x * Real.log (v x) - v x + 1) ∂P) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp

/-- Pinsker in real form, for finite relative entropy. -/
theorem pinsker_fullVariation_real (ν P : Measure α) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure P] (h : relativeEntropy ν P ≠ ⊤) :
    fullVariation ν P ^ 2 ≤ 2 * (relativeEntropy ν P).toReal := by
  have := pinsker_fullVariation ν P
  have h2 : 2 * relativeEntropy ν P ≠ ⊤ := ENNReal.mul_ne_top (by simp) h
  have := ENNReal.toReal_mono h2 this
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul] at this
  simpa using this

end Pinsker

end DGPS
