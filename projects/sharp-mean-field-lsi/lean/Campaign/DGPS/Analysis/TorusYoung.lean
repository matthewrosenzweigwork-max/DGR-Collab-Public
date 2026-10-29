import DGPS.Foundations.Torus

/-!
# Young's convolution inequality on the torus (LIP010b)

For `p q r ∈ [1, ∞]` with `p⁻¹ + r⁻¹ = 1 + q⁻¹` and a.e. strongly measurable `f g : 𝕋^d → ℝ`,
the convolution `(f ⋆ g)(x) = ∫ f(x - y) g(y) dm(y)` (Haar probability `haar d`) satisfies
`‖f ⋆ g‖_q ≤ ‖f‖_p ‖g‖_r` in `ℝ≥0∞` (`DGPS.Analysis.torus_young_convolution`); no integrability
hypothesis is needed (non-integrable integrands give the junk value `0`, which is consistent).

Proof: for `q < ∞` the pointwise splitting
`|f(x-y) g(y)| = (|f|^p |g|^r)^{1/q} (|f|^p)^{1/p-1/q} (|g|^r)^{1/r-1/q}`, three-factor Hölder
(`ENNReal.lintegral_mul_prod_norm_pow_le`), then Tonelli and translation invariance of Haar
measure. For `q = ∞` the exponents are Hölder conjugate and Mathlib's `HolderTriple` Hölder is used.
-/
open MeasureTheory
open scoped ENNReal

namespace DGPS.Analysis
variable {d : ℕ}

private instance lip010b_negInv (d : ℕ) : (haar d).IsNegInvariant := Pi.isNegInvariant_volume

private theorem lip010b_key (a b : ℝ≥0∞) {p q r : ℝ} (hp0 : 0 < p) (hr0 : 0 < r) (hq : 0 < q)
    (hα : 0 ≤ 1 / p - 1 / q) (hβ : 0 ≤ 1 / r - 1 / q) :
    a * b = (a ^ p * b ^ r) ^ (1 / q) * (a ^ p) ^ (1 / p - 1 / q) * (b ^ r) ^ (1 / r - 1 / q) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  simp only [← ENNReal.rpow_mul]
  have e1 : a ^ (p * (1 / q)) * a ^ (p * (1 / p - 1 / q)) = a := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by nlinarith)]
    have : p * (1 / q) + p * (1 / p - 1 / q) = 1 := by field_simp; ring
    rw [this, ENNReal.rpow_one]
  have e2 : b ^ (r * (1 / q)) * b ^ (r * (1 / r - 1 / q)) = b := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by nlinarith)]
    have : r * (1 / q) + r * (1 / r - 1 / q) = 1 := by field_simp; ring
    rw [this, ENNReal.rpow_one]
  calc a * b = (a ^ (p * (1 / q)) * a ^ (p * (1 / p - 1 / q))) *
      (b ^ (r * (1 / q)) * b ^ (r * (1 / r - 1 / q))) := by rw [e1, e2]
    _ = _ := by ring

private theorem lip010b_core {F G : Torus d → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    {p q r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hr : 1 ≤ r) (hrq : r ≤ q)
    (h : 1 / p + 1 / r = 1 + 1 / q) :
    ∫⁻ x, (∫⁻ y, F (x - y) * G y ∂haar d) ^ q ∂haar d ≤
      (∫⁻ x, F x ^ p ∂haar d) ^ (q / p) * (∫⁻ x, G x ^ r ∂haar d) ^ (q / r) := by
  set A := ∫⁻ x, F x ^ p ∂haar d with hA
  set B := ∫⁻ x, G x ^ r ∂haar d with hB
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by linarith
  have hq : 0 < q := by linarith
  have hα : 0 ≤ 1 / p - 1 / q := sub_nonneg.2 (one_div_le_one_div_of_le hp0 hpq)
  have hβ : 0 ≤ 1 / r - 1 / q := sub_nonneg.2 (one_div_le_one_div_of_le hr0 hrq)
  have hq1 : 0 ≤ 1 / q := by positivity
  have hsub : (fun x y : Torus d => F (x - y)) = fun x y => F (x - y) := rfl
  have hmeasF : Measurable fun z : Torus d × Torus d => F (z.1 - z.2) :=
    hF.comp (measurable_fst.sub measurable_snd)
  have pt : ∀ x, ∫⁻ y, F (x - y) * G y ∂haar d ≤
      (∫⁻ y, F (x - y) ^ p * G y ^ r ∂haar d) ^ (1 / q) * A ^ (1 / p - 1 / q) *
        B ^ (1 / r - 1 / q) := by
    intro x
    have hsum : 1 / q + ((1 / p - 1 / q) + (1 / r - 1 / q)) = 1 := by linarith
    have hFx : Measurable fun y => F (x - y) := hF.comp (measurable_const.sub measurable_id)
    have hAx : ∫⁻ y, F (x - y) ^ p ∂haar d = A :=
      lintegral_sub_left_eq_self (fun z => F z ^ p) x
    have H := ENNReal.lintegral_mul_prod_norm_pow_le (μ := haar d) (Finset.univ : Finset (Fin 2))
      (g := fun y => F (x - y) ^ p * G y ^ r)
      (f := ![fun y => F (x - y) ^ p, fun y => G y ^ r])
      ((hFx.pow_const p).mul (hG.pow_const r)).aemeasurable
      (by intro i _; fin_cases i
          · exact (hFx.pow_const p).aemeasurable
          · exact (hG.pow_const r).aemeasurable)
      (1 / q) (p := ![1 / p - 1 / q, 1 / r - 1 / q])
      (by simpa [Fin.sum_univ_two] using hsum) hq1
      (by intro i _; fin_cases i
          · exact hα
          · exact hβ)
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.prod_univ_two] at H
    rw [hAx] at H
    calc ∫⁻ y, F (x - y) * G y ∂haar d
        = ∫⁻ y, (F (x - y) ^ p * G y ^ r) ^ (1 / q) * ((F (x - y) ^ p) ^ (1 / p - 1 / q) *
            (G y ^ r) ^ (1 / r - 1 / q)) ∂haar d := by
          refine lintegral_congr fun y => ?_
          rw [← mul_assoc]; exact lip010b_key _ _ hp0 hr0 hq hα hβ
      _ ≤ _ := by simpa [mul_assoc] using H
  have hmeasK : Measurable fun x => ∫⁻ y, F (x - y) ^ p * G y ^ r ∂haar d :=
    Measurable.lintegral_prod_right'
      (f := fun z : Torus d × Torus d => F (z.1 - z.2) ^ p * G z.2 ^ r)
      ((hmeasF.pow_const p).mul ((hG.comp measurable_snd).pow_const r))
  have hK : ∫⁻ x, ∫⁻ y, F (x - y) ^ p * G y ^ r ∂haar d ∂haar d = A * B := by
    rw [lintegral_lintegral_swap
      (((hmeasF.pow_const p).mul ((hG.comp measurable_snd).pow_const r)).aemeasurable)]
    have : ∀ y, ∫⁻ x, F (x - y) ^ p * G y ^ r ∂haar d = A * G y ^ r := by
      intro y
      have hm : Measurable fun x : Torus d => F (x - y) ^ p :=
        (hF.comp (measurable_id.sub_const y)).pow_const p
      rw [lintegral_mul_const _ hm]
      congr 1
      exact lintegral_sub_right_eq_self (fun z => F z ^ p) y
    simp_rw [this]
    rw [lintegral_const_mul _ (hG.pow_const r)]
  have step : ∀ x, (∫⁻ y, F (x - y) * G y ∂haar d) ^ q ≤
      (∫⁻ y, F (x - y) ^ p * G y ^ r ∂haar d) *
        ((A ^ (1 / p - 1 / q)) ^ q * (B ^ (1 / r - 1 / q)) ^ q) := by
    intro x
    calc (∫⁻ y, F (x - y) * G y ∂haar d) ^ q
        ≤ ((∫⁻ y, F (x - y) ^ p * G y ^ r ∂haar d) ^ (1 / q) * A ^ (1 / p - 1 / q) *
          B ^ (1 / r - 1 / q)) ^ q := ENNReal.rpow_le_rpow (pt x) hq.le
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
          ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one, mul_assoc]
  calc ∫⁻ x, (∫⁻ y, F (x - y) * G y ∂haar d) ^ q ∂haar d
      ≤ ∫⁻ x, (∫⁻ y, F (x - y) ^ p * G y ^ r ∂haar d) *
        ((A ^ (1 / p - 1 / q)) ^ q * (B ^ (1 / r - 1 / q)) ^ q) ∂haar d := lintegral_mono step
    _ = A * B * ((A ^ (1 / p - 1 / q)) ^ q * (B ^ (1 / r - 1 / q)) ^ q) := by
        rw [lintegral_mul_const _ hmeasK, hK]
    _ = A ^ (q / p) * B ^ (q / r) := by
        simp only [← ENNReal.rpow_mul]
        have e1 : A ^ (q / p) = A ^ (1 : ℝ) * A ^ ((1 / p - 1 / q) * q) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by nlinarith)]
          congr 1; field_simp; ring
        have e2 : B ^ (q / r) = B ^ (1 : ℝ) * B ^ ((1 / r - 1 / q) * q) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by nlinarith)]
          congr 1; field_simp; ring
        rw [e1, e2, ENNReal.rpow_one, ENNReal.rpow_one]; ring

/-- Measurability of the convolution of strongly measurable functions. -/
private theorem lip010b_meas_sm {f g : Torus d → ℝ} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun x => ∫ y, f (x - y) * g y ∂haar d :=
  StronglyMeasurable.integral_prod_right'
    (f := fun z : Torus d × Torus d => f (z.1 - z.2) * g z.2)
    ((hf.comp_measurable (measurable_fst.sub measurable_snd)).mul
      (hg.comp_measurable measurable_snd))

/-- The convolution only depends on the a.e. classes of the factors. -/
private theorem lip010b_conv_eq {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (haar d)) (hg : AEStronglyMeasurable g (haar d)) :
    (fun x => ∫ y, f (x - y) * g y ∂haar d) =
      fun x => ∫ y, hf.mk f (x - y) * hg.mk g y ∂haar d := by
  funext x
  have hmp : MeasurePreserving (fun y : Torus d => x - y) (haar d) (haar d) :=
    (haar d).measurePreserving_sub_left x
  refine integral_congr_ae ?_
  filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk, hg.ae_eq_mk] with y h1 h2
  simp only [Function.comp] at h1
  rw [h1, h2]

private theorem lip010b_meas {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (haar d)) (hg : AEStronglyMeasurable g (haar d)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x - y) * g y ∂haar d) (haar d) := by
  rw [lip010b_conv_eq hf hg]
  exact (lip010b_meas_sm hf.stronglyMeasurable_mk hg.stronglyMeasurable_mk).aestronglyMeasurable

/-- Pointwise: the norm of the convolution integral is bounded by the `lintegral` of the norms. -/
private theorem lip010b_enorm_conv_le (f g : Torus d → ℝ) (x : Torus d) :
    ‖∫ y, f (x - y) * g y ∂haar d‖ₑ ≤ ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂haar d := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp [enorm_mul]

/-- The case `q = ∞`. -/
private theorem lip010b_top {p r : ℝ≥0∞} (hpr : p⁻¹ + r⁻¹ = 1) {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (haar d)) (hg : AEStronglyMeasurable g (haar d)) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂haar d) ∞ (haar d) ≤
      eLpNorm f p (haar d) * eLpNorm g r (haar d) := by
  have : ENNReal.HolderTriple p r 1 := ⟨by simpa using hpr⟩
  rw [eLpNorm_exponent_top (lip010b_meas hf hg)]
  refine eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x => ?_)
  have hmp : MeasurePreserving (fun y : Torus d => x - y) (haar d) (haar d) :=
    (haar d).measurePreserving_sub_left x
  have hfx : AEStronglyMeasurable (fun y => f (x - y)) (haar d) :=
    hf.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have H := eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (μ := haar d) (p := p) (q := r) (r := 1)
    (f := fun y => f (x - y)) (g := g) (fun a b : ℝ => a * b) 1 (by fun_prop) hfx hg
    (Filter.Eventually.of_forall fun y => by simp [enorm_mul])
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun y => f (x - y) * g y) (hfx.mul hg)] at H
  have e : eLpNorm (fun y => f (x - y)) p (haar d) = eLpNorm f p (haar d) :=
    eLpNorm_comp_measurePreserving hf hmp
  rw [e, one_mul] at H
  refine (lip010b_enorm_conv_le f g x).trans (le_trans (le_of_eq ?_) H)
  simp [enorm_mul]

/-- The finite case for strongly measurable functions. -/
private theorem lip010b_fin {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) (hqt : q ≠ ∞) {f g : Torus d → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂haar d) q (haar d) ≤
      eLpNorm f p (haar d) * eLpNorm g r (haar d) := by
  have hpt : p ≠ ∞ := by
    rintro rfl
    have : (1 : ℝ≥0∞) + q⁻¹ ≤ 1 := by
      rw [← hpqr]; simp only [ENNReal.inv_top, zero_add]; exact ENNReal.inv_le_one.2 hr
    have hq0 : q⁻¹ ≠ 0 := by simpa using hqt
    have h2 : (1 : ℝ≥0∞) < 1 + q⁻¹ := ENNReal.lt_add_right (by simp) hq0
    exact absurd this (not_le.2 h2)
  have hrt : r ≠ ∞ := by
    rintro rfl
    have : (1 : ℝ≥0∞) + q⁻¹ ≤ 1 := by
      rw [← hpqr]; simp only [ENNReal.inv_top, add_zero]; exact ENNReal.inv_le_one.2 hp
    have hq0 : q⁻¹ ≠ 0 := by simpa using hqt
    have h2 : (1 : ℝ≥0∞) < 1 + q⁻¹ := ENNReal.lt_add_right (by simp) hq0
    exact absurd this (not_le.2 h2)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hp1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp
  have hq1 : 1 ≤ q.toReal := by simpa using ENNReal.toReal_mono hqt hq
  have hr1 : 1 ≤ r.toReal := by simpa using ENNReal.toReal_mono hrt hr
  have hrel : 1 / p.toReal + 1 / r.toReal = 1 + 1 / q.toReal := by
    have h := congrArg ENNReal.toReal hpqr
    rw [ENNReal.toReal_add (by simpa using hp0) (by simpa using hr0),
      ENNReal.toReal_add (by simp) (by simpa using hq0), ENNReal.toReal_inv, ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_one] at h
    simpa [one_div] using h
  have hpq : p.toReal ≤ q.toReal := by
    have h1 : 1 / r.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hr1
    have h2 : 1 / q.toReal ≤ 1 / p.toReal := by linarith
    exact (one_div_le_one_div (by linarith) (by linarith)).1 h2
  have hrq : r.toReal ≤ q.toReal := by
    have h1 : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
    have h2 : 1 / q.toReal ≤ 1 / r.toReal := by linarith
    exact (one_div_le_one_div (by linarith) (by linarith)).1 h2
  have hF : Measurable fun x => ‖f x‖ₑ := hf.enorm
  have hG : Measurable fun x => ‖g x‖ₑ := hg.enorm
  have core := lip010b_core hF hG hp1 hpq hr1 hrq hrel
  have hqpos : 0 < q.toReal := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt (lip010b_meas_sm hf.stronglyMeasurable hg.stronglyMeasurable).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt hg.aestronglyMeasurable]
  calc (∫⁻ x, ‖∫ y, f (x - y) * g y ∂haar d‖ₑ ^ q.toReal ∂haar d) ^ (1 / q.toReal)
      ≤ (∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂haar d) ^ q.toReal ∂haar d) ^ (1 / q.toReal) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by positivity)
        exact ENNReal.rpow_le_rpow (lip010b_enorm_conv_le f g x) hqpos.le
    _ ≤ ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂haar d) ^ (q.toReal / p.toReal) *
          (∫⁻ x, ‖g x‖ₑ ^ r.toReal ∂haar d) ^ (q.toReal / r.toReal)) ^ (1 / q.toReal) :=
        ENNReal.rpow_le_rpow core (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        congr 2 <;> field_simp

/-- **Young's convolution inequality on the torus** (LIP010b), `ℝ≥0∞`-valued `Lᵖ` seminorms:
`‖f ⋆ g‖_q ≤ ‖f‖_p ‖g‖_r` for `1 ≤ p, q, r ≤ ∞` with `p⁻¹ + r⁻¹ = 1 + q⁻¹`. -/
theorem torus_young_convolution {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) {f g : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (haar d)) (hg : AEStronglyMeasurable g (haar d)) :
    eLpNorm (fun x => ∫ y, f (x - y) * g y ∂haar d) q (haar d) ≤
      eLpNorm f p (haar d) * eLpNorm g r (haar d) := by
  by_cases hqt : q = ∞
  · subst hqt
    exact lip010b_top (by simpa using hpqr) hf hg
  · have hfm : f =ᵐ[haar d] hf.mk f := hf.ae_eq_mk
    have hgm : g =ᵐ[haar d] hg.mk g := hg.ae_eq_mk
    rw [lip010b_conv_eq hf hg, eLpNorm_congr_ae hfm, eLpNorm_congr_ae hgm]
    exact lip010b_fin hp hq hr hpqr hqt hf.stronglyMeasurable_mk.measurable
      hg.stronglyMeasurable_mk.measurable

end DGPS.Analysis
