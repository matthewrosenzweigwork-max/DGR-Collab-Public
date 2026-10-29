import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.OpenPos
import DGPS.Frontier.EX049.T01
import DGPS.Frontier.EX049.T31

/-!
# EX049.32: Periodic weak pairs have periodic AC representatives

Task id and title: EX049.32, "Periodic weak pairs have periodic AC representatives" (node EX049,
shared infrastructure). Let `L > 0` and let `f, g ∈ L²(0, L)` satisfy `∫ f φ' = -∫ g φ` for every
smooth `L`-periodic real `φ`. For the primitive `V(x) = ∫₀ˣ g` of EX049.31 there is `c : ℝ` with
`f = c + V` almost everywhere on `(0, L)`, and `V(L) = V(0)`. The resulting continuous periodic
representative is unique.

## Provides

* `DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac`: the main statement. For
  `f, g ∈ L²(0, L)` with the periodic weak identity, there is `c` with `f = c + V` a.e. on
  `(0, L)` and `V(L) = V(0)`; moreover there is a continuous, `L`-periodic, locally absolutely
  continuous `F`, equal to `c + V` on `[0, L]` and a.e. equal to `f`, and every continuous
  `L`-periodic function a.e. equal to `f` on `(0, L)` equals `F`.
* `DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac_extension`: for a mean-zero
  `g ∈ L²(0, L)` and any `c`, the periodic extension of `c + V` exists as a continuous, `L`-periodic,
  locally absolutely continuous function equal to `c + V` on `[0, L]`.
* `DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac_unique`: two continuous
  `L`-periodic functions that agree almost everywhere on `(0, L)` with a common `f` are equal.
* `DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac_unique_Icc`: two functions
  continuous on `[0, L]` that agree almost everywhere on `(0, L)` with a common `f` agree on `[0, L]`.

## R5 notes

* Smoothness is read as `C^∞`, written `ContDiff ℝ ∞`. A "smooth `L`-periodic real `φ`" is
  `φ : ℝ → ℝ` with `ContDiff ℝ ∞ φ` and `Function.Periodic φ L`, defined on the whole line, with no
  compact-support requirement. The derivative `φ'` is `deriv φ`.
* `f, g ∈ L²(0, L)` is read, as in EX049.31, as `MemLp · 2 (volume.restrict (Ioo 0 L))` for fixed
  representatives `f g : ℝ → ℝ`. Ordinary Lebesgue `L²`, not a normalized one.
* The weak identity is the set integral over the open interval, `∫ x in Ioo 0 L, f x * deriv φ x =
  -∫ x in Ioo 0 L, g x * φ x`, the same form as the conclusion of EX049.31. It equals the oriented
  interval integral over `0..L`, since `Ioo 0 L` and `Ioc 0 L` differ by a null set.
* `V` is the primitive `fun x => ∫ t in (0:ℝ)..x, g t` of EX049.31. The conclusion `V(L) = V(0)` is
  stated verbatim as `∫ t in 0..L, g t = ∫ t in 0..0, g t`; since `V(0) = 0`, this says `∫₀ᴸ g = 0`.
* "`f = c + V` almost everywhere" is read on `(0, L)`: `f =ᵐ[volume.restrict (Ioo 0 L)] fun x => c +
  ∫ t in 0..x, g t`. Values of `f` and `g` outside `(0, L)` are unconstrained and do not enter.
* Non-literal reading 1 (the representative). "The resulting continuous periodic representative" is
  made explicit: `F : ℝ → ℝ` with `Continuous F`, `Function.Periodic F L`, `AbsolutelyContinuousOnInterval
  F a b` for every `a b` (locally absolutely continuous), `F x = c + V x` on `[0, L]`, and `F =ᵐ f` on
  `(0, L)`. It is built as `x ↦ c + ∫₀ˣ G` with `G` the `L`-periodic extension of `g`, using
  `∫₀ᴸ g = 0`; local absolute continuity then follows from interval integrability of `G`. This is the
  periodic extension of `c + V` of the specification, obtained without gluing translates by hand.
* Non-literal reading 2 (uniqueness). Uniqueness is stated for the class of all functions
  `F' : ℝ → ℝ` that are continuous on `ℝ`, `L`-periodic and a.e. equal to `f` on `(0, L)`; any such
  `F'` equals the `F` above everywhere. The proof uses Mathlib's `Measure.eqOn_open_of_ae_eq`
  (continuous functions a.e. equal on an open set are equal there), which is the specification's
  "positive measure of an interval" argument, then continuity at the endpoints and periodicity.
  Uniqueness uses no weak identity. The `_Icc` variant needs continuity on `[0, L]` only.
* Non-literal reading 3 (EX049.36). The integration by parts for `V` against an interior test is the
  weak-derivative conclusion of EX049.31 (itself proved from EX049.34), so EX049.36 is not imported.
  The dependencies used are EX049.01 and EX049.31.
* Interior test functions: EX049.01 tests against `φ` with `ContDiff ℝ ∞ φ`, `HasCompactSupport φ`
  and `tsupport φ ⊆ Ioo 0 L`. The periodic extension needs only that `φ` vanishes off `(0, L)`,
  which `tsupport φ ⊆ Ioo 0 L` gives. It is `x ↦ φ (toIcoMod hL 0 x)`, and on `((k-1)L, (k+1)L)` it
  equals `φ (x - kL) + φ (x - (k-1)L)`, which is smooth; so it is `C^∞` and `L`-periodic, and it
  agrees with `φ` and `deriv φ` on `(0, L)`. Compact support of `φ` is used only to bound `deriv φ`
  for integrability of `f φ'` and `V φ'`.
* The mean-zero step tests with the constant `φ = 1`, which is smooth and `L`-periodic.
* No hypothesis is added beyond the specification's, and no bound, positivity or normalization is
  imposed on `f` or `g`. Every statement is proved.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- Periodic extension of `φ` from the fundamental interval `[0, L)`. -/
noncomputable def periodicExt_EX04932 {L : ℝ} (hL : 0 < L) (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => φ (toIcoMod hL 0 x)

lemma periodic_periodicExt_EX04932 {L : ℝ} (hL : 0 < L) (φ : ℝ → ℝ) :
    Function.Periodic (periodicExt_EX04932 hL φ) L :=
  (toIcoMod_periodic hL 0).comp φ

lemma periodicExt_eq_EX04932 {L : ℝ} (hL : 0 < L) (φ : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ico 0 L) :
    periodicExt_EX04932 hL φ x = φ x := by
  unfold periodicExt_EX04932
  rw [(toIcoMod_eq_self hL).2 (by simpa using hx)]

/-- On `((k-1)L, (k+1)L)` the periodic extension of a function vanishing off `(0, L)` is a sum of
two translates. -/
lemma periodicExt_eq_add_EX04932 {L : ℝ} (hL : 0 < L) {φ : ℝ → ℝ}
    (h0 : ∀ x, x ∉ Ioo 0 L → φ x = 0) (k : ℤ) {x : ℝ}
    (hx : x ∈ Ioo (((k : ℝ) - 1) * L) (((k : ℝ) + 1) * L)) :
    periodicExt_EX04932 hL φ x = φ (x - k * L) + φ (x - ((k : ℝ) - 1) * L) := by
  unfold periodicExt_EX04932
  rcases lt_or_ge x (k * L) with h | h
  · have hm : toIcoMod hL 0 x = x - ((k : ℝ) - 1) * L := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨by linarith [hx.1], by linarith⟩, k - 1, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_one]
      ring
    rw [hm, h0 (x - k * L) (fun hh => by linarith [hh.1]), zero_add]
  · have hm : toIcoMod hL 0 x = x - k * L := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨by linarith, by linarith [hx.2]⟩, k, ?_⟩
      simp only [zsmul_eq_mul]
      ring
    rw [hm, h0 (x - ((k : ℝ) - 1) * L) (fun hh => by linarith [hh.2]), add_zero]

lemma contDiff_periodicExt_EX04932 {L : ℝ} (hL : 0 < L) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (h0 : ∀ x, x ∉ Ioo 0 L → φ x = 0) : ContDiff ℝ ∞ (periodicExt_EX04932 hL φ) := by
  refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
  set k : ℤ := ⌊x₀ / L⌋ with hk
  have h1 : (k : ℝ) ≤ x₀ / L := Int.floor_le _
  have h2 : x₀ / L < k + 1 := Int.lt_floor_add_one _
  have h1' : (k : ℝ) * L ≤ x₀ := by rwa [le_div_iff₀ hL] at h1
  have h2' : x₀ < ((k : ℝ) + 1) * L := by rwa [div_lt_iff₀ hL] at h2
  have hmem : Ioo (((k : ℝ) - 1) * L) (((k : ℝ) + 1) * L) ∈ 𝓝 x₀ :=
    Ioo_mem_nhds (by nlinarith) h2'
  have hsm : ContDiff ℝ ∞ (fun x => φ (x - k * L) + φ (x - ((k : ℝ) - 1) * L)) :=
    (hφ.comp (contDiff_id.sub contDiff_const)).add (hφ.comp (contDiff_id.sub contDiff_const))
  refine hsm.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with x hx using periodicExt_eq_add_EX04932 hL h0 k hx

/-- An interior test function (smooth, with closed support inside `(0, L)`) has a smooth `L`-periodic
extension that agrees with it, together with its derivative, on `(0, L)`. -/
lemma exists_periodic_extension_EX04932 {L : ℝ} (hL : 0 < L) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hts : tsupport φ ⊆ Ioo 0 L) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Function.Periodic ψ L ∧
      ∀ x ∈ Ioo 0 L, ψ x = φ x ∧ deriv ψ x = deriv φ x := by
  have h0 : ∀ x, x ∉ Ioo 0 L → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hts h))
  refine ⟨periodicExt_EX04932 hL φ, contDiff_periodicExt_EX04932 hL hφ h0,
    periodic_periodicExt_EX04932 hL φ, fun x hx =>
      ⟨periodicExt_eq_EX04932 hL φ ⟨hx.1.le, hx.2⟩, ?_⟩⟩
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using
    periodicExt_eq_EX04932 hL φ ⟨hy.1.le, hy.2⟩

/-- `f - V` has zero weak derivative against interior test functions. -/
lemma weak_diff_zero_EX04932 {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) (hg : MemLp g 2 (volume.restrict (Ioo 0 L)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ L →
      ∫ x in Ioo 0 L, f x * deriv φ x = -∫ x in Ioo 0 L, g x * φ x)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
    (hts : tsupport φ ⊆ Ioo 0 L) :
    ∫ x in (0:ℝ)..L, (f x - ∫ t in (0:ℝ)..x, g t) * deriv φ x = 0 := by
  obtain ⟨-, -, -, -, hVL2, hVweak⟩ := ex049_31_primitive_l2_derivative hL hg
  obtain ⟨ψ, hψ, hper, hψφ⟩ := exists_periodic_extension_EX04932 hL hφ hts
  have e1 : ∫ x in Ioo 0 L, f x * deriv ψ x = ∫ x in Ioo 0 L, f x * deriv φ x :=
    setIntegral_congr_fun measurableSet_Ioo fun x hx => by simp only [(hψφ x hx).2]
  have e2 : ∫ x in Ioo 0 L, g x * ψ x = ∫ x in Ioo 0 L, g x * φ x :=
    setIntegral_congr_fun measurableSet_Ioo fun x hx => by simp only [(hψφ x hx).1]
  have h1 := hweak ψ hψ hper
  rw [e1, e2] at h1
  have hd : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support hcs.deriv
  have hint : ∀ u : ℝ → ℝ, IntegrableOn u (Ioo 0 L) →
      IntegrableOn (fun x => u x * deriv φ x) (Ioo 0 L) := fun u hu =>
    hu.mul_bdd hd.aestronglyMeasurable (Eventually.of_forall hC)
  have hfI : IntegrableOn f (Ioo 0 L) := hf.integrable (by norm_num)
  have hVI : IntegrableOn (fun x => ∫ t in (0:ℝ)..x, g t) (Ioo 0 L) := hVL2.integrable (by norm_num)
  rw [intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo]
  simp only [sub_mul]
  rw [integral_sub (hint f hfI) (hint _ hVI), h1, hVweak φ hφ hcs hts, sub_self]

/-- Uniqueness of the continuous representative on `[0, L]`: two functions continuous on `[0, L]`
that agree almost everywhere on `(0, L)` with the same `f` agree at every point of `[0, L]`. -/
theorem ex049_32_periodic_weak_pairs_have_periodic_ac_unique_Icc {L : ℝ} (hL : 0 < L)
    {F₁ F₂ f : ℝ → ℝ} (h₁ : ContinuousOn F₁ (Icc 0 L)) (h₂ : ContinuousOn F₂ (Icc 0 L))
    (e₁ : F₁ =ᵐ[volume.restrict (Ioo 0 L)] f) (e₂ : F₂ =ᵐ[volume.restrict (Ioo 0 L)] f) :
    EqOn F₁ F₂ (Icc 0 L) :=
  (Measure.eqOn_open_of_ae_eq (e₁.trans e₂.symm) isOpen_Ioo (h₁.mono Ioo_subset_Icc_self)
    (h₂.mono Ioo_subset_Icc_self)).of_subset_closure h₁ h₂ Ioo_subset_Icc_self
    (by rw [closure_Ioo hL.ne])

/-- Uniqueness of the continuous `L`-periodic representative: two continuous `L`-periodic functions
that agree almost everywhere on `(0, L)` with the same `f` are equal everywhere. -/
theorem ex049_32_periodic_weak_pairs_have_periodic_ac_unique {L : ℝ} (hL : 0 < L)
    {F₁ F₂ f : ℝ → ℝ} (h₁ : Continuous F₁) (h₂ : Continuous F₂)
    (p₁ : Function.Periodic F₁ L) (p₂ : Function.Periodic F₂ L)
    (e₁ : F₁ =ᵐ[volume.restrict (Ioo 0 L)] f) (e₂ : F₂ =ᵐ[volume.restrict (Ioo 0 L)] f) :
    F₁ = F₂ := by
  have hI := ex049_32_periodic_weak_pairs_have_periodic_ac_unique_Icc hL h₁.continuousOn
    h₂.continuousOn e₁ e₂
  funext x
  have hmem := toIcoMod_mem_Ico hL 0 x
  rw [← p₁.sub_zsmul_eq (toIcoDiv hL 0 x), ← p₂.sub_zsmul_eq (toIcoDiv hL 0 x),
    self_sub_toIcoDiv_zsmul]
  exact hI ⟨hmem.1, by linarith [hmem.2]⟩

/-- A mean-zero `L²` function `g` has a primitive `c + ∫₀ˣ g` whose `L`-periodic extension is
continuous and locally absolutely continuous. -/
theorem ex049_32_periodic_weak_pairs_have_periodic_ac_extension {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 L))) (hmean : ∫ t in (0:ℝ)..L, g t = 0) (c : ℝ) :
    ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F L ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
      ∀ x ∈ Icc 0 L, F x = c + ∫ t in (0:ℝ)..x, g t := by
  have hGper : Function.Periodic (periodicExt_EX04932 hL g) L := periodic_periodicExt_EX04932 hL g
  have hgI : IntegrableOn g (Ioo 0 L) := hg.integrable (by norm_num)
  have hG0 : IntervalIntegrable (periodicExt_EX04932 hL g) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    exact hgI.congr_fun (fun x hx => (periodicExt_eq_EX04932 hL g ⟨hx.1.le, hx.2⟩).symm)
      measurableSet_Ioo
  have hGint : ∀ a b, IntervalIntegrable (periodicExt_EX04932 hL g) volume a b :=
    hGper.intervalIntegrable₀ hL.ne' hG0
  have hGg : ∀ x ∈ Icc 0 L,
      ∫ t in (0:ℝ)..x, periodicExt_EX04932 hL g t = ∫ t in (0:ℝ)..x, g t := by
    intro x hx
    rw [intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_of_le hx.1,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht =>
      periodicExt_eq_EX04932 hL g ⟨ht.1.le, ht.2.trans_le hx.2⟩
  refine ⟨fun x => c + ∫ t in (0:ℝ)..x, periodicExt_EX04932 hL g t, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.add (intervalIntegral.continuous_primitive hGint 0)
  · intro x
    show c + ∫ t in (0:ℝ)..(x + L), periodicExt_EX04932 hL g t =
      c + ∫ t in (0:ℝ)..x, periodicExt_EX04932 hL g t
    rw [← intervalIntegral.integral_add_adjacent_intervals (hGint 0 x) (hGint x (x + L)),
      hGper.intervalIntegral_add_eq x 0, zero_add, hGg L ⟨hL.le, le_rfl⟩, hmean, add_zero]
  · intro a b
    have hm : AbsolutelyContinuousOnInterval
        (fun x => ∫ t in (0:ℝ)..x, periodicExt_EX04932 hL g t)
        (min (min a b) 0) (max (max a b) 0) :=
      (hGint _ _).absolutelyContinuousOnInterval_intervalIntegral
        (by rw [mem_uIcc]; left; exact ⟨min_le_right _ _, le_max_right _ _⟩)
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) (min (min a b) 0) (max (max a b) 0) :=
      ContDiffOn.absolutelyContinuousOnInterval (contDiff_const (𝕜 := ℝ) (n := 1)).contDiffOn
    refine (hc.fun_add hm).mono (uIcc_subset_uIcc ?_ ?_) <;> rw [mem_uIcc] <;> left
    · exact ⟨(min_le_left _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_left _ _)⟩
    · exact ⟨(min_le_left _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_left _ _)⟩
  · intro x hx
    simp only [hGg x hx]

/-- Periodic weak pairs have periodic AC representatives: if `f, g ∈ L²(0, L)` satisfy
`∫ f φ' = -∫ g φ` for every smooth `L`-periodic `φ`, then `∫₀ᴸ g = 0` (so `V(L) = V(0)` for the
primitive `V(x) = ∫₀ˣ g`), `f = c + V` almost everywhere for some `c`, the `L`-periodic extension
`F` of `c + V` is a continuous, locally absolutely continuous representative of `f`, and every
continuous `L`-periodic representative of `f` equals `F`. -/
theorem ex049_32_periodic_weak_pairs_have_periodic_ac (L : ℝ) (hL : 0 < L) (f g : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) (hg : MemLp g 2 (volume.restrict (Ioo 0 L)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ L →
      ∫ x in Ioo 0 L, f x * deriv φ x = -∫ x in Ioo 0 L, g x * φ x) :
    ∃ c : ℝ, (f =ᵐ[volume.restrict (Ioo 0 L)] fun x => c + ∫ t in (0:ℝ)..x, g t) ∧
      (∫ t in (0:ℝ)..L, g t) = ∫ t in (0:ℝ)..0, g t ∧
      ∃ F : ℝ → ℝ,
        (Continuous F ∧ Function.Periodic F L ∧
          (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
          (∀ x ∈ Icc 0 L, F x = c + ∫ t in (0:ℝ)..x, g t) ∧
          F =ᵐ[volume.restrict (Ioo 0 L)] f) ∧
        ∀ F' : ℝ → ℝ, Continuous F' → Function.Periodic F' L →
          F' =ᵐ[volume.restrict (Ioo 0 L)] f → F' = F := by
  have hfI : IntegrableOn f (Ioo 0 L) := hf.integrable (by norm_num)
  obtain ⟨-, -, -, -, hVL2, -⟩ := ex049_31_primitive_l2_derivative hL hg
  have hVI : IntegrableOn (fun x => ∫ t in (0:ℝ)..x, g t) (Ioo 0 L) :=
    hVL2.integrable (by norm_num)
  have hmean : ∫ t in (0:ℝ)..L, g t = 0 := by
    have h := hweak (fun _ => 1) contDiff_const (fun _ => rfl)
    simp only [deriv_const', mul_zero, integral_zero, mul_one] at h
    rw [intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo]
    linarith
  obtain ⟨c, hc⟩ := ex049_01_zero_weak_derivative_implies_constancy L hL
    (fun x => f x - ∫ t in (0:ℝ)..x, g t) (hfI.sub hVI)
    (fun φ hφ hcs hts => weak_diff_zero_EX04932 hL hf hg hweak hφ hcs hts)
  have hfV : f =ᵐ[volume.restrict (Ioo 0 L)] fun x => c + ∫ t in (0:ℝ)..x, g t := by
    filter_upwards [hc] with x hx
    have hx' : f x - ∫ t in (0:ℝ)..x, g t = c := hx
    linarith
  obtain ⟨F, hFc, hFp, hFac, hFeq⟩ :=
    ex049_32_periodic_weak_pairs_have_periodic_ac_extension hL hg hmean c
  have hFf : F =ᵐ[volume.restrict (Ioo 0 L)] f := by
    filter_upwards [hfV, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx, hFeq x (Ioo_subset_Icc_self hxI)]
  exact ⟨c, hfV, by rw [intervalIntegral.integral_same, hmean], F, ⟨hFc, hFp, hFac, hFeq, hFf⟩,
    fun F' h1 h2 h3 =>
      ex049_32_periodic_weak_pairs_have_periodic_ac_unique hL h1 hFc h2 hFp h3 hFf⟩

end DGPS.Frontier.EX049
