import DGPS.Frontier.EX049.T25

/-!
# EX049.33: Fundamental-interval measure transport

Task id: EX049.33 (node EX049, the engineered rank-one sharp species).
Title: Fundamental-interval measure transport.

Let `L = 2π`. Under the binding of EX049.25, integration of a descended measurable periodic real
function `F` against the angular Haar measure `angHaar` equals `(1/L) ∫_0^L F(s) ds`; integrability
on the two sides is equivalent; the same holds for `|F|` and `F ^ 2`; almost-everywhere equality
is equivalent on the circle and on a fundamental interval; and everything is independent of the
base point of the interval.

Provides (every name is in the namespace `DGPS.Frontier.EX049`):
* `ex049_33_fundamental_interval_measure_transport`: the conjunction of the parts below, for a
  measurable `F` (and a second measurable `G` for the almost-everywhere part) and every base
  point `a`.
* `ex049_33_fundamental_interval_measure_transport_measure`: the measure identity
  `angHaar S = L⁻¹ · volume (↑⁻¹' S ∩ (a, a + L])` for measurable `S`, and its form for
  nonnegative measurable functions (lower integrals).
* `ex049_33_fundamental_interval_measure_transport_integral`: integrability equivalence and the
  integral identity, for `F`, `|F|` and `F ^ 2`, on `(a, a + L]`.
* `ex049_33_fundamental_interval_measure_transport_ae`: almost-everywhere equality on the circle
  is equivalent to almost-everywhere equality of the lifts on `(a, a + L]`.
* `ex049_33_fundamental_interval_measure_transport_translate`: the interval integral and the
  interval integrability of the lift do not depend on the base point `a`.
* `ex049_33_fundamental_interval_measure_transport_Ico`: the same transport on the half-open
  fundamental interval `[a, a + L)` (endpoints are null).
* `ex049_33_fundamental_interval_measure_transport_periodic`: the version for a measurable
  `2π`-periodic function on `ℝ` and its descent to the circle.

R5 notes:
* Reading of "descended measurable periodic real function". `F : AngCircle → ℝ` is a function on
  the quotient circle `AngCircle = AddCircle (2π)`; its real-line lift `s ↦ F ↑s` is periodic
  with period `L = 2π` automatically. The hypothesis on `F` is `Measurable F` (the quotient
  sigma-algebra); nothing else is assumed. The second reading, a measurable periodic
  `f : ℝ → ℝ` together with its descent `Function.Periodic.lift`, is the public lemma with suffix
  `_periodic`.
* The integral identity is stated without the proviso "whenever either expression is
  integrable": it holds for every measurable `F`, since the two integrability conditions are
  equivalent and the integral of a function that is not integrable is `0` on both sides. This is
  a strengthening of the literal text, not an additional hypothesis. The factor `1 / L` of the
  specification is written `(2 * π)⁻¹`.
* "Integrable on the two sides" is stated as `Integrable F angHaar` against
  `IntervalIntegrable (fun s => F ↑s) volume a (a + 2π)`; for `a ≤ b` the latter is
  integrability on `Ioc a b`, and the `Ioc` form is in the helper
  `integrable_angHaar_iff_EX04933`.
* The fundamental interval is `(a, a + 2π]` for an arbitrary base point `a` (the form of the
  binding in EX049.25, where `interval integral` means the integral over `Ioc`). The `[a, a + 2π)`
  form is the separate `_Ico` lemma. The specification's `∫_0^L` is the case `a = 0`.
* `|F| ^ 2` is stated as `F ^ 2`, which is the same function for real `F` (`sq_abs`). The
  identities for `|F|` and `F ^ 2` are instances of the general statement for the measurable
  functions `|F|` and `F ^ 2`; they are spelled out because the specification names them.
* Almost-everywhere equality needs measurability of both functions (the set where they differ
  has to be a measurable set of the circle), so the `_ae` statement carries `Measurable F` and
  `Measurable G`. The specification's proof applies the measure identity to that set.
* No positivity or integrability hypothesis is added anywhere. The measure identity is the one
  of EX049.25 (`angHaar` is the pushforward of the normalized Lebesgue measure on `(a, a + 2π]`).
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization

namespace DGPS.Frontier.EX049

/-! ### Constants and the measure identity -/

theorem inv_ofReal_two_pi_ne_zero_EX04933 : (ENNReal.ofReal (2 * π))⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top

theorem inv_ofReal_two_pi_ne_top_EX04933 : (ENNReal.ofReal (2 * π))⁻¹ ≠ ∞ :=
  ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'

theorem angHaar_apply_EX04933 (a : ℝ) {S : Set AngCircle} (hS : MeasurableSet S) :
    angHaar S = (ENNReal.ofReal (2 * π))⁻¹ *
      volume (((↑) : ℝ → AngCircle) ⁻¹' S ∩ Ioc a (a + 2 * π)) := by
  rw [angHaar_eq_map_EX04925 a, Measure.smul_apply, Measure.map_apply AddCircle.measurable_mk' hS,
    Measure.restrict_apply (AddCircle.measurable_mk' hS), smul_eq_mul]

theorem lintegral_angHaar_EX04933 (a : ℝ) {f : AngCircle → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ θ, f θ ∂angHaar =
      (ENNReal.ofReal (2 * π))⁻¹ * ∫⁻ s in Ioc a (a + 2 * π), f (s : AngCircle) := by
  rw [angHaar_eq_map_normalized_EX04925 a, lintegral_map hf AddCircle.measurable_mk',
    lintegral_smul_measure, smul_eq_mul]

theorem ex049_33_fundamental_interval_measure_transport_measure (a : ℝ) :
    (∀ S : Set AngCircle, MeasurableSet S →
      angHaar S = (ENNReal.ofReal (2 * π))⁻¹ *
        volume (((↑) : ℝ → AngCircle) ⁻¹' S ∩ Ioc a (a + 2 * π))) ∧
    (∀ f : AngCircle → ℝ≥0∞, Measurable f →
      ∫⁻ θ, f θ ∂angHaar =
        (ENNReal.ofReal (2 * π))⁻¹ * ∫⁻ s in Ioc a (a + 2 * π), f (s : AngCircle)) :=
  ⟨fun _ hS => angHaar_apply_EX04933 a hS, fun _ hf => lintegral_angHaar_EX04933 a hf⟩

/-! ### Integrability and the integral identity -/

theorem integrable_angHaar_iff_EX04933 (a : ℝ) {F : AngCircle → ℝ} (hF : Measurable F) :
    Integrable F angHaar ↔ IntegrableOn (fun s : ℝ => F (s : AngCircle)) (Ioc a (a + 2 * π)) := by
  rw [angHaar_eq_map_normalized_EX04925 a,
    integrable_map_measure hF.aestronglyMeasurable AddCircle.measurable_mk'.aemeasurable,
    integrable_smul_measure inv_ofReal_two_pi_ne_zero_EX04933 inv_ofReal_two_pi_ne_top_EX04933]
  rfl

theorem intervalIntegrable_iff_EX04933 (a : ℝ) {F : AngCircle → ℝ} (hF : Measurable F) :
    Integrable F angHaar ↔
      IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume a (a + 2 * π) := by
  rw [integrable_angHaar_iff_EX04933 a hF, intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by linarith [Real.two_pi_pos])]

theorem transport_EX04933 (a : ℝ) {F : AngCircle → ℝ} (hF : Measurable F) :
    (Integrable F angHaar ↔
      IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume a (a + 2 * π)) ∧
    ∫ θ, F θ ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, F (s : AngCircle) :=
  ⟨intervalIntegrable_iff_EX04933 a hF, integral_angHaar_interval_EX04925 a F⟩

theorem ex049_33_fundamental_interval_measure_transport_integral (a : ℝ)
    {F : AngCircle → ℝ} (hF : Measurable F) :
    ((Integrable F angHaar ↔
        IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume a (a + 2 * π)) ∧
      ∫ θ, F θ ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, F (s : AngCircle)) ∧
    ((Integrable (fun θ => |F θ|) angHaar ↔
        IntervalIntegrable (fun s : ℝ => |F (s : AngCircle)|) volume a (a + 2 * π)) ∧
      ∫ θ, |F θ| ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, |F (s : AngCircle)|) ∧
    ((Integrable (fun θ => F θ ^ 2) angHaar ↔
        IntervalIntegrable (fun s : ℝ => F (s : AngCircle) ^ 2) volume a (a + 2 * π)) ∧
      ∫ θ, F θ ^ 2 ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, F (s : AngCircle) ^ 2) :=
  ⟨transport_EX04933 a hF,
    transport_EX04933 (F := fun θ => |F θ|) a (continuous_abs.measurable.comp hF),
    transport_EX04933 (F := fun θ => F θ ^ 2) a (hF.pow_const 2)⟩

/-! ### Almost-everywhere equality -/

theorem ae_angHaar_iff_EX04933 (a : ℝ) {F G : AngCircle → ℝ} (hF : Measurable F)
    (hG : Measurable G) :
    F =ᵐ[angHaar] G ↔ (fun s : ℝ => F (s : AngCircle)) =ᵐ[volume.restrict (Ioc a (a + 2 * π))]
      (fun s : ℝ => G (s : AngCircle)) := by
  have hS : MeasurableSet {θ | ¬ F θ = G θ} := (measurableSet_eq_fun hF hG).compl
  rw [Filter.EventuallyEq, Filter.EventuallyEq, ae_iff, ae_iff, angHaar_apply_EX04933 a hS,
    show {s : ℝ | ¬ F (s : AngCircle) = G (s : AngCircle)} =
      ((↑) : ℝ → AngCircle) ⁻¹' {θ | ¬ F θ = G θ} from rfl,
    Measure.restrict_apply (AddCircle.measurable_mk' hS)]
  exact (mul_eq_zero.trans (or_iff_right inv_ofReal_two_pi_ne_zero_EX04933))

theorem ex049_33_fundamental_interval_measure_transport_ae (a : ℝ) {F G : AngCircle → ℝ}
    (hF : Measurable F) (hG : Measurable G) :
    F =ᵐ[angHaar] G ↔ (fun s : ℝ => F (s : AngCircle)) =ᵐ[volume.restrict (Ioc a (a + 2 * π))]
      (fun s : ℝ => G (s : AngCircle)) :=
  ae_angHaar_iff_EX04933 a hF hG

/-! ### Translating the interval -/

theorem periodic_lift_EX04933 (F : AngCircle → ℝ) :
    Function.Periodic (fun s : ℝ => F (s : AngCircle)) (2 * π) := fun s => by
  simp only [AddCircle.coe_add_period]

theorem ex049_33_fundamental_interval_measure_transport_translate (a b : ℝ)
    {F : AngCircle → ℝ} (hF : Measurable F) :
    (IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume a (a + 2 * π) ↔
      IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume b (b + 2 * π)) ∧
    ∫ s in a..a + 2 * π, F (s : AngCircle) = ∫ s in b..b + 2 * π, F (s : AngCircle) :=
  ⟨(intervalIntegrable_iff_EX04933 a hF).symm.trans (intervalIntegrable_iff_EX04933 b hF),
    (periodic_lift_EX04933 F).intervalIntegral_add_eq a b⟩

/-! ### The half-open fundamental interval -/

theorem ex049_33_fundamental_interval_measure_transport_Ico (a : ℝ) {F G : AngCircle → ℝ}
    (hF : Measurable F) (hG : Measurable G) :
    (Integrable F angHaar ↔ IntegrableOn (fun s : ℝ => F (s : AngCircle)) (Ico a (a + 2 * π))) ∧
    ∫ θ, F θ ∂angHaar = (2 * π)⁻¹ * ∫ s in Ico a (a + 2 * π), F (s : AngCircle) ∧
    (F =ᵐ[angHaar] G ↔ (fun s : ℝ => F (s : AngCircle)) =ᵐ[volume.restrict (Ico a (a + 2 * π))]
      (fun s : ℝ => G (s : AngCircle))) := by
  have e : volume.restrict (Ico a (a + 2 * π)) = volume.restrict (Ioc a (a + 2 * π)) :=
    Measure.restrict_congr_set Ico_ae_eq_Ioc
  refine ⟨?_, ?_, ?_⟩
  · rw [integrable_angHaar_iff_EX04933 a hF, IntegrableOn, IntegrableOn, e]
  · rw [integral_angHaar_interval_EX04925 a F,
      intervalIntegral.integral_of_le (by linarith [Real.two_pi_pos]),
      setIntegral_congr_set Ico_ae_eq_Ioc]
  · rw [e]
    exact ae_angHaar_iff_EX04933 a hF hG

/-! ### The main statement -/

theorem ex049_33_fundamental_interval_measure_transport (a : ℝ) {F G : AngCircle → ℝ}
    (hF : Measurable F) (hG : Measurable G) :
    (∀ S : Set AngCircle, MeasurableSet S →
      angHaar S = (ENNReal.ofReal (2 * π))⁻¹ *
        volume (((↑) : ℝ → AngCircle) ⁻¹' S ∩ Ioc a (a + 2 * π))) ∧
    (∀ f : AngCircle → ℝ≥0∞, Measurable f →
      ∫⁻ θ, f θ ∂angHaar =
        (ENNReal.ofReal (2 * π))⁻¹ * ∫⁻ s in Ioc a (a + 2 * π), f (s : AngCircle)) ∧
    ((Integrable F angHaar ↔
        IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume a (a + 2 * π)) ∧
      ∫ θ, F θ ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, F (s : AngCircle)) ∧
    ((Integrable (fun θ => |F θ|) angHaar ↔
        IntervalIntegrable (fun s : ℝ => |F (s : AngCircle)|) volume a (a + 2 * π)) ∧
      ∫ θ, |F θ| ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, |F (s : AngCircle)|) ∧
    ((Integrable (fun θ => F θ ^ 2) angHaar ↔
        IntervalIntegrable (fun s : ℝ => F (s : AngCircle) ^ 2) volume a (a + 2 * π)) ∧
      ∫ θ, F θ ^ 2 ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, F (s : AngCircle) ^ 2) ∧
    (F =ᵐ[angHaar] G ↔ (fun s : ℝ => F (s : AngCircle)) =ᵐ[volume.restrict (Ioc a (a + 2 * π))]
      (fun s : ℝ => G (s : AngCircle))) ∧
    (IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume a (a + 2 * π) ↔
      IntervalIntegrable (fun s : ℝ => F (s : AngCircle)) volume 0 (2 * π)) ∧
    ∫ s in a..a + 2 * π, F (s : AngCircle) = ∫ s in (0:ℝ)..2 * π, F (s : AngCircle) := by
  have hm := ex049_33_fundamental_interval_measure_transport_measure a
  have hi := ex049_33_fundamental_interval_measure_transport_integral a hF
  have ht := ex049_33_fundamental_interval_measure_transport_translate a 0 hF
  rw [zero_add] at ht
  exact ⟨hm.1, hm.2, hi.1, hi.2.1, hi.2.2,
    ex049_33_fundamental_interval_measure_transport_ae a hF hG, ht.1, ht.2⟩

/-! ### Periodic functions on the real line -/

theorem ex049_33_fundamental_interval_measure_transport_periodic (a : ℝ) {f : ℝ → ℝ}
    (hper : Function.Periodic f (2 * π)) (hf : Measurable f) :
    (Integrable (hper.lift : AngCircle → ℝ) angHaar ↔
        IntervalIntegrable f volume a (a + 2 * π)) ∧
      ∫ θ, (hper.lift : AngCircle → ℝ) θ ∂angHaar = (2 * π)⁻¹ * ∫ s in a..a + 2 * π, f s ∧
      ∫ s in a..a + 2 * π, f s = ∫ s in (0:ℝ)..2 * π, f s := by
  have hm : Measurable (hper.lift : AngCircle → ℝ) :=
    QuotientAddGroup.measurable_from_quotient.2 hf
  have h := ex049_33_fundamental_interval_measure_transport_translate a 0 hm
  have e : (fun s : ℝ => (hper.lift : AngCircle → ℝ) (s : AngCircle)) = f := rfl
  rw [e] at h
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e] using intervalIntegrable_iff_EX04933 a hm
  · simpa only [e] using integral_angHaar_interval_EX04925 a (hper.lift : AngCircle → ℝ)
  · simpa using h.2

end DGPS.Frontier.EX049
