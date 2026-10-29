import DGPS.Frontier.EX049.T26
import DGPS.Frontier.EX049.T28
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Support

/-!
# EX049.29: Recover every interior interval integral

Task id and title: EX049.29, "Recover every interior interval integral" (node EX049, shared
infrastructure). Under the hypotheses of EX049.28 (the weak identity of EX049.01 against
`f ∈ L^1(0,L)`, and a normalized smooth bump `β` supported in `[a₀, b₀]`, `0 < a₀ < b₀ < L`),
every interior interval satisfies `∫_a^b f = c (b - a)` with `c = ∫_0^L f β`.

The proof uses the smooth step `S` of EX049.26 to build the test functions
`ψ_n(x) = S((n+1)(x-a)) S((n+1)(b-x))`, applies EX049.28 to each `ψ_n`, and passes to the limit
by dominated convergence on `(0, L]` (interval integrals).

## Provides
* `DGPS.Frontier.EX049.ex049_29_recover_interior_interval_integral` : the main statement. For
  every `β` with the EX049.28 hypotheses, every `0 < a < b < L` satisfies
  `∫ x in a..b, f x = (∫ x in 0..L, f x * β x) * (b - a)`.
* `DGPS.Frontier.EX049.ex049_29_recover_interior_interval_integral_bump` : the same conclusion for
  the EX049.26 bump, namely some smooth `β` supported in `[L/4, 3L/4]` with `∫ β = 1` (existence
  of such a `β` is part of the conclusion).
* `DGPS.Frontier.EX049.testPsi_EX04929` : the test functions `ψ_n` of the proof.
* `DGPS.Frontier.EX049.testPsi_contDiff_EX04929`, `DGPS.Frontier.EX049.testPsi_eq_zero_EX04929`,
  `DGPS.Frontier.EX049.testPsi_mem_EX04929`, `DGPS.Frontier.EX049.testPsi_eventually_one_EX04929`,
  `DGPS.Frontier.EX049.testPsi_tendsto_EX04929` : smoothness, support in `[a, b]`, values in
  `[0, 1]`, eventual value one on `(a, b)`, and pointwise limit (off `{a, b}`) of `ψ_n`.
* `DGPS.Frontier.EX049.integral_indicator_one_EX04929`, `DGPS.Frontier.EX049.integral_indicator_f_EX04929` :
  the two limit integrals `∫_0^L 1_{(a,b)} = b - a` and `∫_0^L 1_{(a,b)} f = ∫_a^b f`.

## R5 notes
* Smoothness is read as `C^∞`, written `ContDiff ℝ ∞` (the `∞` of `ℕ∞`, not the analytic `ω`).
* `f ∈ L^1(0,L)` is read as `IntegrableOn f (Set.Ioo 0 L)`. The integrals `∫_0^L` and `∫_a^b`
  are oriented interval integrals; since `0 < L` and `a < b`, they are the Lebesgue integrals over
  `Ioc 0 L` and `Ioc a b`, and `f` is interval integrable on `[0, L]`
  (`intervalIntegrable_iff_integrableOn_Ioc_of_le`).
* The weak hypothesis and the test class are read as in EX049.28 (and EX049.01): a test is
  `ContDiff ℝ ∞`, `HasCompactSupport`, with `tsupport ⊆ Set.Ioo 0 L`, and the derivative is `deriv`.
* The constant is `c = ∫_0^L f β`, the EX049.28 constant. The main statement is quantified over
  every `β` satisfying EX049.28's hypotheses (`ContDiff`, support in `Set.Icc a₀ b₀`,
  `0 < a₀ < b₀ < L`, `∫ β = 1`), which is stronger than "choose `β` from EX049.26". The
  EX049.26 bump is recovered in the `_bump` corollary, which also states its existence.
* The interval `(a, b)` is read with `0 < a` and `b < L` as hypotheses of the conclusion, since
  these are exactly the conditions `0 < a < b < L` of the specification. The conclusion is for
  all such `a < b`; no endpoint case is excluded.
* The step `S` is taken from EX049.26 (`ex049_26_smooth_step_normalized_test_bump_step`) as an
  existential witness, not as a specific function, so the proof uses only its stated properties.
* Dominated convergence is applied in interval-integral form
  (`intervalIntegral.tendsto_integral_filter_of_dominated_convergence`), with dominating functions
  `|f|` (interval integrable by `IntervalIntegrable.norm`) and the constant `1`. The pointwise limit
  is established off the null set `{a, b}`, which is what the specification's "two endpoints form
  a null set" refers to.
* The indexing of the sequence is `n : ℕ` with the scale `n + 1`, so the sequence starts at a
  positive scale. The specification's `n` ranges over positive integers; the two indexings give
  the same limit, and the shift avoids a separate positivity case.
* No hypothesis beyond the EX049.28 hypotheses and the stated conclusion is assumed. Every Mathlib
  declaration used was checked by grep at the pinned commit (dominated convergence for interval
  integrals, `setIntegral_indicator`, `setIntegral_const`, `integral_Ioc_eq_integral_Ioo`,
  `measure_eq_zero_iff_ae_notMem`, `tendsto_natCast_atTop_atTop`).
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- The shrinking test functions `ψ_n(x) = S((n+1)(x-a)) S((n+1)(b-x))` of EX049.29. -/
def testPsi_EX04929 (S : ℝ → ℝ) (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  S (((n : ℝ) + 1) * (x - a)) * S (((n : ℝ) + 1) * (b - x))

lemma testPsi_contDiff_EX04929 {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S) (a b : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (testPsi_EX04929 S a b n) := by
  unfold testPsi_EX04929
  exact (hS.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
    (hS.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))

lemma testPsi_eq_zero_EX04929 {S : ℝ → ℝ} (hS0 : ∀ x, x ≤ 0 → S x = 0) {a b : ℝ} (n : ℕ)
    {x : ℝ} (hx : x ∉ Set.Icc a b) : testPsi_EX04929 S a b n x = 0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold testPsi_EX04929
  by_cases h : x < a
  · rw [hS0 (((n : ℝ) + 1) * (x - a)) (by nlinarith), zero_mul]
  · have hb : b < x := by
      by_contra hc
      exact hx ⟨not_lt.mp h, not_lt.mp hc⟩
    rw [hS0 (((n : ℝ) + 1) * (b - x)) (by nlinarith), mul_zero]

lemma mul_le_one_EX04929 {p q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ p * q ∧ p * q ≤ 1 := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  exact ⟨mul_nonneg hp0 hq0, by nlinarith⟩

lemma testPsi_mem_EX04929 {S : ℝ → ℝ} (hS01 : ∀ x, S x ∈ Set.Icc (0 : ℝ) 1) (a b : ℝ)
    (n : ℕ) (x : ℝ) : 0 ≤ testPsi_EX04929 S a b n x ∧ testPsi_EX04929 S a b n x ≤ 1 :=
  mul_le_one_EX04929 (hS01 _) (hS01 _)

lemma testPsi_eventually_one_EX04929 {S : ℝ → ℝ} (hS1 : ∀ x, 1 ≤ x → S x = 1) {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) : ∀ᶠ n : ℕ in atTop, testPsi_EX04929 S a b n x = 1 := by
  have hxa : 0 < x - a := by linarith [hx.1]
  have hbx : 0 < b - x := by linarith [hx.2]
  have h1 : ∀ᶠ n : ℕ in atTop, 1 / (x - a) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have h2 : ∀ᶠ n : ℕ in atTop, 1 / (b - x) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [h1, h2] with n hn1 hn2
  have e1 : 1 ≤ ((n : ℝ) + 1) * (x - a) := by
    have := (div_le_iff₀ hxa).mp hn1
    nlinarith
  have e2 : 1 ≤ ((n : ℝ) + 1) * (b - x) := by
    have := (div_le_iff₀ hbx).mp hn2
    nlinarith
  unfold testPsi_EX04929
  rw [hS1 _ e1, hS1 _ e2, one_mul]

lemma testPsi_tendsto_EX04929 {S : ℝ → ℝ} (hS0 : ∀ x, x ≤ 0 → S x = 0)
    (hS1 : ∀ x, 1 ≤ x → S x = 1) {a b x : ℝ} (hxa : x ≠ a) (hxb : x ≠ b) :
    Tendsto (fun n : ℕ => testPsi_EX04929 S a b n x) atTop
      (𝓝 (Set.indicator (Set.Ioo a b) (fun _ => (1 : ℝ)) x)) := by
  by_cases hin : x ∈ Set.Ioo a b
  · rw [Set.indicator_of_mem hin]
    exact tendsto_const_nhds.congr' ((testPsi_eventually_one_EX04929 hS1 hin).mono fun n hn => hn.symm)
  · rw [Set.indicator_of_notMem hin]
    have hout : x ∉ Set.Icc a b := by
      intro hc
      rcases hc.1.lt_or_eq with h | h
      · rcases hc.2.lt_or_eq with h' | h'
        · exact hin ⟨h, h'⟩
        · exact hxb h'
      · exact hxa h.symm
    exact tendsto_const_nhds.congr (fun n => (testPsi_eq_zero_EX04929 hS0 n hout).symm)

lemma integral_indicator_one_EX04929 {L a b : ℝ} (hL : 0 < L) (hab : a < b) (ha : 0 < a)
    (hbL : b < L) :
    ∫ x in (0 : ℝ)..L, Set.indicator (Set.Ioo a b) (fun _ => (1 : ℝ)) x = b - a := by
  rw [intervalIntegral.integral_of_le hL.le, setIntegral_indicator measurableSet_Ioo]
  have hsub : Set.Ioo a b ⊆ Set.Ioc 0 L := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [Set.inter_eq_right.mpr hsub, setIntegral_const, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]

lemma integral_indicator_f_EX04929 {f : ℝ → ℝ} {L a b : ℝ} (hL : 0 < L) (hab : a < b)
    (ha : 0 < a) (hbL : b < L) :
    ∫ x in (0 : ℝ)..L, Set.indicator (Set.Ioo a b) f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hL.le, setIntegral_indicator measurableSet_Ioo]
  have hsub : Set.Ioo a b ⊆ Set.Ioc 0 L := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [Set.inter_eq_right.mpr hsub, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab.le]

/-- EX049.29: for every `β` as in EX049.28 and every `0 < a < b < L`, `∫_a^b f = c (b - a)` with
`c = ∫_0^L f β`. -/
theorem ex049_29_recover_interior_interval_integral (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioo 0 L))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Set.Ioo 0 L →
      ∫ x in (0:ℝ)..L, f x * deriv φ x = 0)
    (β : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0) (hab0 : a0 < b0) (hb0L : b0 < L)
    (hβ : ContDiff ℝ ∞ β) (hβsupp : Function.support β ⊆ Set.Icc a0 b0)
    (hβint : ∫ x, β x = 1) :
    ∀ a b : ℝ, 0 < a → a < b → b < L →
      ∫ x in a..b, f x = (∫ x in (0:ℝ)..L, f x * β x) * (b - a) := by
  intro a b ha hab hbL
  have hfi : IntervalIntegrable f volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mpr hf
  obtain ⟨S, hSc, hS01, hS0, hS1⟩ := ex049_26_smooth_step_normalized_test_bump_step
  have hpsi := ex049_28_weak_hypothesis_determines_test_integrals L hL f hf hweak β a0 b0 ha0
    hab0 hb0L hβ hβsupp hβint
  -- EX049.28 applied to every test function `ψ_n`.
  have hid : ∀ n : ℕ, ∫ x in (0:ℝ)..L, f x * testPsi_EX04929 S a b n x
      = (∫ x in (0:ℝ)..L, f x * β x) * ∫ x in (0:ℝ)..L, testPsi_EX04929 S a b n x := by
    intro n
    have hsupp : Function.support (testPsi_EX04929 S a b n) ⊆ Set.Icc a b := by
      intro x hx
      by_contra hc
      exact hx (testPsi_eq_zero_EX04929 hS0 n hc)
    have htsub : tsupport (testPsi_EX04929 S a b n) ⊆ Set.Icc a b :=
      closure_minimal hsupp isClosed_Icc
    apply hpsi (testPsi_EX04929 S a b n) (testPsi_contDiff_EX04929 hSc a b n)
      (HasCompactSupport.intro isCompact_Icc (fun x hx => testPsi_eq_zero_EX04929 hS0 n hx))
    intro x hx
    have hx' := htsub hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  -- Almost every point avoids `{a, b}`.
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a ∧ x ≠ b := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((Set.toFinite ({a, b} : Set ℝ)).measure_zero
      (volume : Measure ℝ))] with x hx
    exact ⟨fun h => hx (by simp [h]), fun h => hx (by simp [h])⟩
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x => f x * testPsi_EX04929 S a b n x)
      (volume.restrict (Set.uIoc 0 L)) := fun n => by
    rw [Set.uIoc_of_le hL.le]
    exact hfi.1.aestronglyMeasurable.mul
      (testPsi_contDiff_EX04929 hSc a b n).continuous.aestronglyMeasurable
  have hmeas1 : ∀ n : ℕ, AEStronglyMeasurable (fun x => testPsi_EX04929 S a b n x)
      (volume.restrict (Set.uIoc 0 L)) := fun n => by
    rw [Set.uIoc_of_le hL.le]
    exact (testPsi_contDiff_EX04929 hSc a b n).continuous.aestronglyMeasurable
  -- Dominated convergence for `∫_0^L f ψ_n`.
  have hDf : Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..L, f x * testPsi_EX04929 S a b n x) atTop
      (𝓝 (∫ x in (0:ℝ)..L, Set.indicator (Set.Ioo a b) f x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      (Eventually.of_forall fun n => hmeas n) ?_ hfi.norm ?_
    · refine Eventually.of_forall fun n => Eventually.of_forall fun x _ => ?_
      obtain ⟨h0, h1⟩ := testPsi_mem_EX04929 hS01 a b n x
      rw [norm_mul, Real.norm_of_nonneg h0]
      exact mul_le_of_le_one_right (norm_nonneg _) h1
    · filter_upwards [hae] with x hx _
      have hlim := (tendsto_const_nhds (x := f x)).mul
        (testPsi_tendsto_EX04929 hS0 hS1 hx.1 hx.2)
      have hind : Set.indicator (Set.Ioo a b) f x
          = f x * Set.indicator (Set.Ioo a b) (fun _ => (1 : ℝ)) x := by
        by_cases hin : x ∈ Set.Ioo a b <;> simp [hin]
      rw [hind]
      exact hlim
  -- Dominated convergence for `∫_0^L ψ_n`.
  have hDψ : Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..L, testPsi_EX04929 S a b n x) atTop
      (𝓝 (b - a)) := by
    have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (fun _ : ℝ => (1 : ℝ))
      (Eventually.of_forall fun n => hmeas1 n)
      (Eventually.of_forall fun n => Eventually.of_forall fun x _ => by
        obtain ⟨h0, h1⟩ := testPsi_mem_EX04929 hS01 a b n x
        rw [Real.norm_of_nonneg h0]
        exact h1)
      intervalIntegrable_const
      (by
        filter_upwards [hae] with x hx _
        exact testPsi_tendsto_EX04929 hS0 hS1 hx.1 hx.2)
    rw [integral_indicator_one_EX04929 hL hab ha hbL] at h
    exact h
  have hDf' : Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..L, f x * testPsi_EX04929 S a b n x) atTop
      (𝓝 (∫ x in a..b, f x)) := by
    rw [← integral_indicator_f_EX04929 (f := f) hL hab ha hbL]
    exact hDf
  have hRHS : Tendsto (fun n : ℕ => (∫ x in (0:ℝ)..L, f x * β x) *
      ∫ x in (0:ℝ)..L, testPsi_EX04929 S a b n x) atTop
      (𝓝 ((∫ x in (0:ℝ)..L, f x * β x) * (b - a))) :=
    hDψ.const_mul _
  exact tendsto_nhds_unique hDf' (hRHS.congr (fun n => (hid n).symm))

/-- EX049.29 with the EX049.26 bump: for `0 < L`, `f` and the weak hypothesis of EX049.01, there is
a smooth `β` supported in `[L/4, 3L/4]` with `∫ β = 1`, and for every `0 < a < b < L` we have
`∫_a^b f = (∫_0^L f β)(b - a)`. -/
theorem ex049_29_recover_interior_interval_integral_bump (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioo 0 L))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Set.Ioo 0 L →
      ∫ x in (0:ℝ)..L, f x * deriv φ x = 0) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ Function.support β ⊆ Set.Icc (L / 4) (3 * L / 4) ∧
      ∫ x, β x = 1 ∧
      ∀ a b : ℝ, 0 < a → a < b → b < L →
        ∫ x in a..b, f x = (∫ x in (0:ℝ)..L, f x * β x) * (b - a) := by
  obtain ⟨β, hβ, -, hsupp, hint⟩ :=
    ex049_26_smooth_step_normalized_test_bump_bump (L / 4) (3 * L / 4) L
      (by linarith) (by linarith) (by linarith)
  exact ⟨β, hβ, hsupp, hint,
    ex049_29_recover_interior_interval_integral L hL f hf hweak β (L / 4) (3 * L / 4)
      (by linarith) (by linarith) (by linarith) hβ hsupp hint⟩

end DGPS.Frontier.EX049
