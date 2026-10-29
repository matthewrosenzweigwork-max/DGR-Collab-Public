import LeanResearch.PeriodicAttractiveLogGas.CanonicalRowHolder
import Mathlib.Analysis.MeanInequalitiesPow

/-! Actual double centering in source `eq:reference-residual` and the Jensen
step in `lem:residual-kernels`. This generic probability-law prerequisite does
not supply the geometric Green-kernel estimates or the reference fixed point. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.ResidualDoubleCentering

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (K : α → β → ℝ)

/-- The term order is the source order: kernel, right average, left average,
then the double average. Symmetry is not needed for this generic definition. -/
def doubleCenter (x : α) (y : β) : ℝ :=
  K x y - (∫ v, K x v ∂ν) - (∫ u, K u y ∂μ) + ∫ u, ∫ v, K u v ∂ν ∂μ

theorem measurable_doubleCenter (hK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry (doubleCenter μ ν K)) := by
  have hr : Measurable (fun x => ∫ y, K x y ∂ν) :=
    hK.stronglyMeasurable.integral_prod_right.measurable
  have hl : Measurable (fun y => ∫ x, K x y ∂μ) :=
    hK.stronglyMeasurable.integral_prod_left.measurable
  exact ((hK.sub (hr.comp measurable_fst)).sub (hl.comp measurable_snd)).add measurable_const

theorem integrable_doubleCenter (hK : Integrable (Function.uncurry K) (μ.prod ν)) :
    Integrable (Function.uncurry (doubleCenter μ ν K)) (μ.prod ν) :=
  ((hK.sub (hK.integral_prod_left.comp_fst ν)).sub
    (hK.integral_prod_right.comp_snd μ)).add (integrable_const _)

theorem ae_integral_doubleCenter_right_eq_zero
    (hK : Integrable (Function.uncurry K) (μ.prod ν)) :
    ∀ᵐ x ∂μ, (∫ y, doubleCenter μ ν K x y ∂ν) = 0 := by
  filter_upwards [hK.prod_right_ae] with x hx
  change Integrable (fun y => K x y) ν at hx
  have hl : Integrable (fun y => ∫ u, K u y ∂μ) ν := hK.integral_prod_right
  have hs₁ : Integrable (fun y => K x y - ∫ v, K x v ∂ν) ν := hx.sub (integrable_const _)
  have hs₂ : Integrable (fun y => K x y - (∫ v, K x v ∂ν) - ∫ u, K u y ∂μ) ν := hs₁.sub hl
  unfold doubleCenter
  rw [integral_add hs₂ (integrable_const _), integral_sub hs₁ hl,
    integral_sub hx (integrable_const (∫ v, K x v ∂ν))]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_integral_swap hK]
  ring

theorem ae_integral_doubleCenter_left_eq_zero
    (hK : Integrable (Function.uncurry K) (μ.prod ν)) :
    ∀ᵐ y ∂ν, (∫ x, doubleCenter μ ν K x y ∂μ) = 0 := by
  filter_upwards [hK.prod_left_ae] with y hy
  change Integrable (fun x => K x y) μ at hy
  have hr : Integrable (fun x => ∫ v, K x v ∂ν) μ := hK.integral_prod_left
  have hs₁ : Integrable (fun x => K x y - ∫ v, K x v ∂ν) μ := hy.sub hr
  have hs₂ : Integrable (fun x => K x y - (∫ v, K x v ∂ν) - ∫ u, K u y ∂μ) μ :=
    hs₁.sub (integrable_const _)
  unfold doubleCenter
  rw [integral_add hs₂ (integrable_const _),
    integral_sub hs₁ (integrable_const (∫ u, K u y ∂μ)), integral_sub hy hr]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Subtracting a constant before centering leaves the actual residual unchanged. -/
theorem doubleCenter_sub_const (hK : Integrable (Function.uncurry K) (μ.prod ν)) (c : ℝ) :
    ∀ᵐ z ∂μ.prod ν, doubleCenter μ ν (fun x y => K x y - c) z.1 z.2 =
      doubleCenter μ ν K z.1 z.2 := by
  have hright := (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae
    hK.prod_right_ae
  have hleft := (measurePreserving_snd (μ := μ) (ν := ν)).quasiMeasurePreserving.ae
    hK.prod_left_ae
  have hdouble : (∫ u, ∫ v, K u v - c ∂ν ∂μ) =
      (∫ u, ∫ v, K u v ∂ν ∂μ) - c := by
    calc
      _ = ∫ u, (∫ v, K u v ∂ν) - c ∂μ := by
        apply integral_congr_ae
        filter_upwards [hK.prod_right_ae] with u hu
        change Integrable (fun v => K u v) ν at hu
        rw [integral_sub hu (integrable_const c)]
        simp
      _ = _ := by
        have hr : Integrable (fun u => ∫ v, K u v ∂ν) μ := hK.integral_prod_left
        rw [integral_sub hr (integrable_const c)]
        simp
  filter_upwards [hright, hleft] with z hz₁ hz₂
  change Integrable (fun v => K z.1 v) ν at hz₁
  change Integrable (fun u => K u z.2) μ at hz₂
  dsimp only [doubleCenter]
  rw [integral_sub hz₁ (integrable_const c), integral_sub hz₂ (integrable_const c), hdouble]
  simp only [integral_const, probReal_univ, one_smul]
  ring

section MomentTools
variable {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ} [IsProbabilityMeasure ρ]

/-- Extended-norm Jensen is valid before finiteness is inferred from a bound. -/
theorem enorm_integral_pow_le {g : γ → ℝ} (hg : Measurable g) {p : ℕ} (hp : 1 ≤ p) :
    ‖∫ x, g x ∂ρ‖ₑ ^ p ≤ ∫⁻ x, ‖g x‖ₑ ^ p ∂ρ := by
  have hpn : (p : ℝ≥0) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have he : eLpNorm g (p : ℝ≥0∞) ρ ^ p = ∫⁻ x, ‖g x‖ₑ ^ p ∂ρ := by
    simpa only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := ρ) hpn hg.aestronglyMeasurable)
  rw [← he]
  apply pow_le_pow_left'
  calc
    ‖∫ x, g x ∂ρ‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ ∂ρ := enorm_integral_le_lintegral_enorm g
    _ = eLpNorm g 1 ρ := (eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable).symm
    _ ≤ _ := eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hp)

omit [IsProbabilityMeasure ρ] in
/-- The sum of four terms costs exactly 4^p when each p-th moment is bounded by C. -/
theorem lintegral_enorm_sum_four_le (g : Fin 4 → γ → ℝ)
    (hg : ∀ i, Measurable (g i)) {p : ℕ} (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hb : ∀ i, (∫⁻ x, ‖g i x‖ₑ ^ p ∂ρ) ≤ C) :
    (∫⁻ x, ‖∑ i, g i x‖ₑ ^ p ∂ρ) ≤ (4 : ℝ≥0∞) ^ p * C := by
  have hmean (x : γ) : (∑ i : Fin 4, ‖g i x‖ₑ) ^ p ≤
      ∑ i : Fin 4, (4 : ℝ≥0∞)⁻¹ * ((4 : ℝ≥0∞) ^ p * ‖g i x‖ₑ ^ p) := by
    have hh := ENNReal.rpow_arith_mean_le_arith_mean_rpow
      (Finset.univ : Finset (Fin 4)) (fun _ => (4 : ℝ≥0∞)⁻¹)
      (fun i => (4 : ℝ≥0∞) * ‖g i x‖ₑ) (by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num only [Nat.cast_ofNat]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)) (p := (p : ℝ))
      (by exact_mod_cast hp)
    simpa only [ENNReal.rpow_natCast, mul_pow, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul] using hh
  calc
    _ ≤ ∫⁻ x, (∑ i : Fin 4, ‖g i x‖ₑ) ^ p ∂ρ :=
      lintegral_mono fun x => pow_le_pow_left' (enorm_sum_le _ _) _
    _ ≤ ∫⁻ x, ∑ i : Fin 4, (4 : ℝ≥0∞)⁻¹ *
        ((4 : ℝ≥0∞) ^ p * ‖g i x‖ₑ ^ p) ∂ρ := lintegral_mono hmean
    _ = ∑ i : Fin 4, (4 : ℝ≥0∞)⁻¹ *
        ((4 : ℝ≥0∞) ^ p * ∫⁻ x, ‖g i x‖ₑ ^ p ∂ρ) := by
      rw [lintegral_finsetSum _ (fun i _ =>
        (((hg i).enorm.pow_const p).const_mul _).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_const_mul _ (((hg i).enorm.pow_const p).const_mul _),
        lintegral_const_mul _ ((hg i).enorm.pow_const p)]
    _ ≤ ∑ _i : Fin 4, (4 : ℝ≥0∞)⁻¹ * ((4 : ℝ≥0∞) ^ p * C) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact hb i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num only [Nat.cast_ofNat]
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
end MomentTools

/-- A single conditional moment hypothesis controls its centered counterpart.
The other integrations are against probabilities, so no density factor is repeated. -/
theorem ae_left_moment_doubleCenter_le (hK : Measurable (Function.uncurry K))
    {p : ℕ} (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hb : ∀ᵐ y ∂ν, (∫⁻ x, ‖K x y‖ₑ ^ p ∂μ) ≤ C) :
    ∀ᵐ y ∂ν, (∫⁻ x, ‖doubleCenter μ ν K x y‖ₑ ^ p ∂μ) ≤ (4 : ℝ≥0∞) ^ p * C := by
  have hr : Measurable (fun x => ∫ y, K x y ∂ν) :=
    hK.stronglyMeasurable.integral_prod_right.measurable
  have hrow : (∫⁻ x, ‖∫ v, K x v ∂ν‖ₑ ^ p ∂μ) ≤ C := by
    calc
      _ ≤ ∫⁻ x, ∫⁻ v, ‖K x v‖ₑ ^ p ∂ν ∂μ :=
        lintegral_mono fun x => enorm_integral_pow_le
          (hK.comp (measurable_const.prodMk measurable_id)) hp
      _ = ∫⁻ v, ∫⁻ x, ‖K x v‖ₑ ^ p ∂μ ∂ν :=
        lintegral_lintegral_swap (hK.enorm.pow_const p).aemeasurable
      _ ≤ ∫⁻ _v : β, C ∂ν := lintegral_mono_ae hb
      _ = C := by simp
  have hdouble : ‖∫ u, ∫ v, K u v ∂ν ∂μ‖ₑ ^ p ≤ C :=
    (enorm_integral_pow_le hr hp).trans hrow
  filter_upwards [hb] with y hy
  have hleft : ‖∫ u, K u y ∂μ‖ₑ ^ p ≤ C :=
    (enorm_integral_pow_le (hK.comp (measurable_id.prodMk measurable_const)) hp).trans hy
  let g : Fin 4 → α → ℝ := ![fun x => K x y, fun x => -(∫ v, K x v ∂ν),
    fun _ => -(∫ u, K u y ∂μ), fun _ => ∫ u, ∫ v, K u v ∂ν ∂μ]
  have hg : ∀ i, Measurable (g i) := by
    intro i
    fin_cases i <;> dsimp [g]
    · exact hK.comp (measurable_id.prodMk measurable_const)
    · exact hr.neg
    · exact measurable_const
    · exact measurable_const
  have hgb : ∀ i, (∫⁻ x, ‖g i x‖ₑ ^ p ∂μ) ≤ C := by
    intro i
    fin_cases i
    · simpa [g] using hy
    · simpa [g] using hrow
    · simpa [g] using hleft
    · simpa [g] using hdouble
  have he : (fun x => ∑ i, g i x) = fun x => doubleCenter μ ν K x y := by
    funext x
    simp [g, Fin.sum_univ_four, doubleCenter, sub_eq_add_neg]
  have hh := lintegral_enorm_sum_four_le g hg hp hgb
  simp_rw [show ∀ x, (∑ i, g i x) = doubleCenter μ ν K x y from congrFun he] at hh
  exact hh

/-- Swapping the two reference laws only swaps the two arguments of the residual. -/
theorem doubleCenter_swap (hK : Integrable (Function.uncurry K) (μ.prod ν)) (x : α) (y : β) :
    doubleCenter ν μ (fun y x => K x y) y x = doubleCenter μ ν K x y := by
  dsimp only [doubleCenter]
  rw [← integral_integral_swap hK]
  ring

theorem ae_right_moment_doubleCenter_le (hK : Measurable (Function.uncurry K))
    (hi : Integrable (Function.uncurry K) (μ.prod ν)) {p : ℕ} (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hb : ∀ᵐ x ∂μ, (∫⁻ y, ‖K x y‖ₑ ^ p ∂ν) ≤ C) :
    ∀ᵐ x ∂μ, (∫⁻ y, ‖doubleCenter μ ν K x y‖ₑ ^ p ∂ν) ≤ (4 : ℝ≥0∞) ^ p * C := by
  have hh := ae_left_moment_doubleCenter_le ν μ (fun y x => K x y)
    (hK.comp measurable_swap) hp hb
  simpa only [doubleCenter_swap μ ν K hi] using hh

/-- Actual finite extended conditional moments discharge every joint integrability
premise before applying Fubini. Both exceptional sets remain AE, not pointwise. -/
theorem doubleCenter_properties_of_conditional_moments
    (hK : Measurable (Function.uncurry K)) {p : ℕ} (hp : 1 ≤ p)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hl : ∀ᵐ y ∂ν, (∫⁻ x, ‖K x y‖ₑ ^ p ∂μ) ≤ C)
    (hr : ∀ᵐ x ∂μ, (∫⁻ y, ‖K x y‖ₑ ^ p ∂ν) ≤ C) :
    Measurable (Function.uncurry (doubleCenter μ ν K)) ∧
    Integrable (Function.uncurry K) (μ.prod ν) ∧
    Integrable (Function.uncurry (doubleCenter μ ν K)) (μ.prod ν) ∧
    (∀ᵐ y ∂ν, (∫ x, doubleCenter μ ν K x y ∂μ) = 0 ∧
      (∫⁻ x, ‖doubleCenter μ ν K x y‖ₑ ^ p ∂μ) ≤ (4 : ℝ≥0∞) ^ p * C) ∧
    (∀ᵐ x ∂μ, (∫ y, doubleCenter μ ν K x y ∂ν) = 0 ∧
      (∫⁻ y, ‖doubleCenter μ ν K x y‖ₑ ^ p ∂ν) ≤ (4 : ℝ≥0∞) ^ p * C) := by
  have hm := CanonicalRowHolder.memLp_of_ae_leftMoment_le μ ν K p hp hK hC hl
  have hi : Integrable (Function.uncurry K) (μ.prod ν) :=
    hm.integrable (by exact_mod_cast hp)
  refine ⟨measurable_doubleCenter μ ν K hK, hi, integrable_doubleCenter μ ν K hi, ?_, ?_⟩
  · exact (ae_integral_doubleCenter_left_eq_zero μ ν K hi).and
      (ae_left_moment_doubleCenter_le μ ν K hK hp hl)
  · exact (ae_integral_doubleCenter_right_eq_zero μ ν K hi).and
      (ae_right_moment_doubleCenter_le μ ν K hK hi hp hr)

/-- The same genuine extended bounds yield the source essential-supremum form
and actual joint p-integrability of the residual. -/
theorem memLp_and_essSup_moments_doubleCenter
    (hK : Measurable (Function.uncurry K)) {p : ℕ} (hp : 1 ≤ p)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hl : ∀ᵐ y ∂ν, (∫⁻ x, ‖K x y‖ₑ ^ p ∂μ) ≤ C)
    (hr : ∀ᵐ x ∂μ, (∫⁻ y, ‖K x y‖ₑ ^ p ∂ν) ≤ C) :
    MemLp (Function.uncurry (doubleCenter μ ν K)) (p : ℝ≥0∞) (μ.prod ν) ∧
    essSup (CanonicalRowHolder.leftMoment μ (doubleCenter μ ν K) p) ν ≤
      (4 : ℝ≥0∞) ^ p * C ∧
    essSup (CanonicalRowHolder.rightMoment ν (doubleCenter μ ν K) p) μ ≤
      (4 : ℝ≥0∞) ^ p * C := by
  obtain ⟨hm, _, _, hleft, hright⟩ :=
    doubleCenter_properties_of_conditional_moments μ ν K hK hp hC hl hr
  have hbl := hleft.mono fun _ hy => hy.2
  have hbr := hright.mono fun _ hx => hx.2
  have hfin : (4 : ℝ≥0∞) ^ p * C < ∞ := by finiteness
  exact ⟨CanonicalRowHolder.memLp_of_ae_leftMoment_le μ ν (doubleCenter μ ν K) p hp hm hfin hbl,
    essSup_le_of_ae_le _ hbl, essSup_le_of_ae_le _ hbr⟩

section SymmetricKernel
variable {γ : Type*} [MeasurableSpace γ] (ρ σ : Measure γ)
  [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] (H : γ → γ → ℝ)

omit [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] in
/-- For a symmetric kernel, the left average has precisely the source's
one-body-potential orientation. Later Green instantiation uses evenness. -/
theorem doubleCenter_eq_source_order (hH : ∀ x y, H x y = H y x) (x y : γ) :
    doubleCenter ρ σ H x y = H x y - (∫ v, H x v ∂σ) -
      (∫ u, H y u ∂ρ) + ∫ u, ∫ v, H u v ∂σ ∂ρ := by
  unfold doubleCenter
  rw [show (∫ u, H u y ∂ρ) = ∫ u, H y u ∂ρ from
    integral_congr_ae (Eventually.of_forall fun u => hH u y)]
end SymmetricKernel

end PeriodicAttractiveLogGas.ResidualDoubleCentering
