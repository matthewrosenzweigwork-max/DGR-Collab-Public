import LeanResearch.PeriodicAttractiveLogGas.CanonicalWordMoments
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.EssSup

/-! Conditional row Hölder and the extended-integral factorial input for
`thm:canonical-pairs`. No finite Bochner integral is presumed integrable. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.CanonicalRowHolder

section FiniteHolder
variable {β : Type*} [MeasurableSpace β] {μ : Measure β} {a : ℕ}

/-- Finite Hölder with a common bound for each slot-count moment. -/
theorem lintegral_prod_enorm_le (ha : 1 ≤ a) (g : Fin a → β → ℝ)
    (hg : ∀ ℓ, Measurable (g ℓ)) {K : ℝ≥0∞}
    (hK : ∀ ℓ, (∫⁻ x, ‖g ℓ x‖ₑ ^ a ∂μ) ≤ K) :
    (∫⁻ x, ∏ ℓ, ‖g ℓ x‖ₑ ∂μ) ≤ K := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have haN : 0 ≤ (a : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg a)
  have hsum : (∑ _ℓ : Fin a, (a : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ ha0
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := μ) (Finset.univ : Finset (Fin a))
    (f := fun ℓ x => ‖g ℓ x‖ₑ ^ a) (p := fun _ => (a : ℝ)⁻¹)
    (fun ℓ _ => ((hg ℓ).enorm.pow_const a).aemeasurable) hsum (fun _ _ => haN)
  have hroot (z : ℝ≥0∞) : (z ^ a) ^ (a : ℝ)⁻¹ = z := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_inv_cancel₀ ha0, ENNReal.rpow_one]
  simp_rw [hroot] at h
  refine h.trans ?_
  calc
    (∏ ℓ : Fin a, (∫⁻ x, ‖g ℓ x‖ₑ ^ a ∂μ) ^ (a : ℝ)⁻¹) ≤
        ∏ _ℓ : Fin a, K ^ (a : ℝ)⁻¹ :=
      Finset.prod_le_prod (fun ℓ _ => ENNReal.rpow_le_rpow (hK ℓ) haN)
    _ = K := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, inv_mul_cancel₀ ha0, ENNReal.rpow_one]

theorem enorm_finset_prod {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ‖∏ ℓ ∈ s, g ℓ‖ₑ = ∏ ℓ ∈ s, ‖g ℓ‖ₑ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- Hölder yields actual integrability as well as the integral bound. -/
theorem integrable_prod_and_integral_abs_le (ha : 1 ≤ a) (g : Fin a → β → ℝ)
    (hg : ∀ ℓ, Measurable (g ℓ)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ ℓ, (∫⁻ x, ‖g ℓ x‖ₑ ^ a ∂μ) ≤ ENNReal.ofReal K) :
    Integrable (fun x => ∏ ℓ, g ℓ x) μ ∧
      (∫ x, |∏ ℓ, g ℓ x| ∂μ) ≤ K := by
  have hm : Measurable (fun x => ∏ ℓ, g ℓ x) :=
    Finset.measurable_prod _ (fun ℓ _ => hg ℓ)
  have hb : (∫⁻ x, ‖∏ ℓ, g ℓ x‖ₑ ∂μ) ≤ ENNReal.ofReal K := by
    simp_rw [enorm_finset_prod]
    exact lintegral_prod_enorm_le ha g hg hK
  have hi : Integrable (fun x => ∏ ℓ, g ℓ x) μ :=
    ⟨hm.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  have hb' : ENNReal.ofReal (∫ x, ‖∏ ℓ, g ℓ x‖ ∂μ) ≤ ENNReal.ofReal K := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hi]
    exact hb
  simpa only [Real.norm_eq_abs] using (ENNReal.ofReal_le_ofReal_iff hK0).mp hb'
end FiniteHolder

section ConditionalMoments
variable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
  (μ : Measure β) (ρ : Measure γ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
  (h : β → γ → ℝ) (p : ℕ)

def leftMoment (y : γ) : ℝ≥0∞ := ∫⁻ x, ‖h x y‖ₑ ^ p ∂μ
def rightMoment (x : β) : ℝ≥0∞ := ∫⁻ y, ‖h x y‖ₑ ^ p ∂ρ

theorem measurable_leftMoment (hh : Measurable (Function.uncurry h)) :
    Measurable (leftMoment μ h p) :=
  (hh.enorm.pow_const p).lintegral_prod_left'

theorem measurable_rightMoment (hh : Measurable (Function.uncurry h)) :
    Measurable (rightMoment ρ h p) :=
  (hh.enorm.pow_const p).lintegral_prod_right'

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] in
/-- Each nonnegative essential supremum is bounded by their source sum. -/
theorem ae_moments_le_of_essSup_sum_le {K : ℝ≥0∞}
    (hK : essSup (leftMoment μ h p) ρ + essSup (rightMoment ρ h p) μ ≤ K) :
    (∀ᵐ y ∂ρ, leftMoment μ h p y ≤ K) ∧
      (∀ᵐ x ∂μ, rightMoment ρ h p x ≤ K) := by
  constructor
  · filter_upwards [ENNReal.ae_le_essSup (leftMoment μ h p)] with y hy
    exact hy.trans ((le_add_right le_rfl).trans hK)
  · filter_upwards [ENNReal.ae_le_essSup (rightMoment ρ h p)] with x hx
    exact hx.trans ((le_add_left le_rfl).trans hK)

/-- Tonelli converts a genuine conditional extended-moment bound to pairwise MemLp. -/
theorem memLp_of_ae_leftMoment_le (hp : 1 ≤ p)
    (hh : Measurable (Function.uncurry h)) {K : ℝ≥0∞} (hK : K < ∞)
    (hbound : ∀ᵐ y ∂ρ, leftMoment μ h p y ≤ K) :
    MemLp (Function.uncurry h) (p : ℝ≥0∞) (μ.prod ρ) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hb : (∫⁻ z : β × γ, ‖h z.1 z.2‖ₑ ^ p ∂μ.prod ρ) ≤ K := by
    change (∫⁻ z, ‖Function.uncurry h z‖ₑ ^ p ∂μ.prod ρ) ≤ K
    rw [lintegral_prod_symm _ (hh.enorm.pow_const p).aemeasurable]
    calc
      (∫⁻ y, ∫⁻ x, ‖h x y‖ₑ ^ p ∂μ ∂ρ) ≤ ∫⁻ _y : γ, K ∂ρ :=
        lintegral_mono_ae hbound
      _ = K := by simp
  rw [memLp_iff]
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0
    (ENNReal.natCast_ne_top p) hh.aestronglyMeasurable).mpr
  simpa only [ENNReal.toReal_natCast, ENNReal.rpow_natCast, Function.uncurry] using hb.trans_lt hK
end ConditionalMoments

section Rows
variable {m a : ℕ} {α : Fin m → Type*} [∀ i, MeasurableSpace (α i)]
  (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
  (f : ∀ i j, α i → α j → ℝ)

/-- The actual factors belonging to a fixed row, with the primed vector retained. -/
def rowProduct (i : Fin m) (c : Fin a → Fin m) (Y : ∀ j, α j) (x : α i) : ℝ :=
  ∏ ℓ, f i (c ℓ) x (Y (c ℓ))

/-- Finitely many pulled-back exceptional sets suffice even when columns repeat. -/
theorem ae_integrable_rowProduct_and_integral_abs_le (ha : 1 ≤ a)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {K : ℝ} (hK0 : 0 ≤ K)
    (i : Fin m) (c : Fin a → Fin m)
    (hbound : ∀ j, ∀ᵐ y ∂ν j, leftMoment (ν i) (f i j) a y ≤ ENNReal.ofReal K) :
    ∀ᵐ Y ∂Measure.pi ν, Integrable (rowProduct f i c Y) (ν i) ∧
      (∫ x, |rowProduct f i c Y x| ∂ν i) ≤ K := by
  have hslots (ℓ : Fin a) : ∀ᵐ Y ∂Measure.pi ν,
      leftMoment (ν i) (f i (c ℓ)) a (Y (c ℓ)) ≤ ENNReal.ofReal K :=
    (measurePreserving_eval ν (c ℓ)).quasiMeasurePreserving.ae (hbound (c ℓ))
  filter_upwards [ae_all_iff.mpr hslots] with Y hY
  exact integrable_prod_and_integral_abs_le ha (fun ℓ x => f i (c ℓ) x (Y (c ℓ)))
    (fun ℓ => (hf i (c ℓ)).comp (measurable_id.prodMk measurable_const)) hK0 hY

/-- The precise factorial row bound used in the supplied proof. -/
theorem ae_row_factorial_bound (ha : 1 ≤ a)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {L : ℝ} (hL : 0 ≤ L)
    (i : Fin m) (c : Fin a → Fin m)
    (hbound : ∀ j, ∀ᵐ y ∂ν j,
      leftMoment (ν i) (f i j) a y ≤ ENNReal.ofReal (2 * L ^ a * (a.factorial : ℝ))) :
    ∀ᵐ Y ∂Measure.pi ν, Integrable (rowProduct f i c Y) (ν i) ∧
      (∫ x, |rowProduct f i c Y x| ∂ν i) ≤ 2 * L ^ a * (a.factorial : ℝ) :=
  ae_integrable_rowProduct_and_integral_abs_le ν f ha hf
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hL _)) (Nat.cast_nonneg _)) i c hbound

/-- The source sum-of-essential-suprema condition supplies the row bound directly. -/
theorem ae_row_factorial_bound_of_essSup_sum (ha : 1 ≤ a)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {L : ℝ} (hL : 0 ≤ L)
    (i : Fin m) (c : Fin a → Fin m)
    (hsource : ∀ j,
      essSup (leftMoment (ν i) (f i j) a) (ν j) +
        essSup (rightMoment (ν j) (f i j) a) (ν i) ≤
          ENNReal.ofReal (2 * L ^ a * (a.factorial : ℝ))) :
    ∀ᵐ Y ∂Measure.pi ν, Integrable (rowProduct f i c Y) (ν i) ∧
      (∫ x, |rowProduct f i c Y x| ∂ν i) ≤ 2 * L ^ a * (a.factorial : ℝ) := by
  apply ae_row_factorial_bound ν f ha hf hL i c
  intro j
  exact (ae_moments_le_of_essSup_sum_le (ν i) (ν j) (f i j) a (hsource j)).1

/-- No product-space moment integrability is assumed: it follows by Tonelli. -/
theorem pairwise_memLp_of_essSup_sum (ha : 1 ≤ a)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {L : ℝ}
    (hsource : ∀ i j,
      essSup (leftMoment (ν i) (f i j) a) (ν j) +
        essSup (rightMoment (ν j) (f i j) a) (ν i) ≤
          ENNReal.ofReal (2 * L ^ a * (a.factorial : ℝ))) :
    ∀ i j, MemLp (Function.uncurry (f i j)) (a : ℝ≥0∞) ((ν i).prod (ν j)) := by
  intro i j
  apply memLp_of_ae_leftMoment_le (ν i) (ν j) (f i j) a ha (hf i j) ENNReal.ofReal_lt_top
  exact (ae_moments_le_of_essSup_sum_le (ν i) (ν j) (f i j) a (hsource i j)).1
end Rows

end PeriodicAttractiveLogGas.CanonicalRowHolder
