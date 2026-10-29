import DGPS.Circle.AngularNormalization
import DGPS.Frontier.EX049.T02

/-!
# EX049.04: Explicit angular Sobolev supremum estimate

Task id: EX049.04 (node EX049, the engineered rank-one sharp species).
Title: Explicit angular Sobolev supremum estimate.

For every angular `H¹` function `w` on the circle `AngCircle = AddCircle (2π)`, put
`M = ∫ w² dm` and `T = ∫ (w')² dm`, where `m` is the normalized Haar measure `dθ/(2π)`.
Its continuous representative `v` satisfies `(sup |v|)² ≤ 2M + 8π²T ≤ (2 + 8π²)(M + T)`.

Provides (every name is in the namespace `DGPS.Frontier.EX049`):
* `ex049_04_explicit_angular_sobolev_supremum_estimate`: the main statement above. It gives a
  continuous representative `v` of `w`, unique among continuous functions that agree with `w`
  almost everywhere, and for every angular weak derivative `g` of `w` the two displayed bounds.
* `abs_integral_le_EX04904`: the absolute value of an interval integral over `[u, s] ⊆ [0, 2π]`
  is at most the integral of the absolute value over `[0, 2π]`.
* `ftc_ordered_EX04904`: the fundamental theorem of calculus for the absolutely continuous
  representative on `[a, b] ⊆ [0, 2π]` with `a ≤ b`, using its almost-everywhere derivative.
* `abs_sub_le_EX04904`: the increment of the representative between two points of `[0, 2π]` is
  bounded by the `L¹` norm of the derivative over `[0, 2π]`.
* `sq_integral_abs_le_EX04904`: Cauchy-Schwarz on `[0, 2π]` in the form `(∫|f|)² ≤ 2π ∫ f²`.
* `memLp_Ioc_EX04904`: an `L²` function on the circle gives an `L²` function on `(0, 2π]`.
* `intervalIntegrable_EX04904`: an `L²` function on `(0, 2π]` is interval integrable on `[0, 2π]`,
  together with its square.
* `angSec_mem_EX04904`: the representative `angSec θ` of a circle point lies in `[0, 2π]`.
* `angSec_coe_EX04904`: the representative `angSec θ` projects back to the point `θ`.

R5 notes:
* Hypotheses: the only hypothesis is `AngularH1 w`, that is, `w` has an angular weak derivative
  in `L²(angHaar)` with the integration-by-parts identity of `IsAngularWeakDeriv`. No other
  hypothesis is added. The representative, its uniqueness, the absolute continuity on `[0, 2π]`
  and the derivative identity are taken from EX049.02 and are not assumed here.
* Non-literal reading 1 (supremum): the norm `‖w‖∞` is read as `⨆ θ, |v θ|`, the pointwise
  supremum over the whole circle of the absolute value of the continuous representative `v`.
  The supremum is bounded above, so the bound is not vacuous.
* Non-literal reading 2 (minimizer): the minimizer `y` of `v²` is taken on the whole circle, via
  `IsCompact.exists_isMinOn` on `Set.univ`, not on the interval `[0, 2π]` as the wording of the
  specification suggests. The value `v y ²` is at most the probability average `∫ v² dangHaar`.
  The interval representative `angSec y` lies in `(0, 2π]` and gives the same point.
* Non-literal reading 3 (derivative): `w'` is read as an arbitrary angular weak derivative `g` of
  `w`. The statement quantifies over every such `g`, so it does not depend on a choice of `g`.
  `T` is `∫ g² dangHaar` for that `g`. The weak derivative is unique almost everywhere, so this is
  the same `T` as in the specification.
* Design choice (uniqueness conjunct): the conclusion also asserts that the continuous
  representative is unique among continuous functions that agree with `w` almost everywhere. This
  is part of the conclusion, not a hypothesis, and it makes "its continuous representative" a
  well-defined object. It is inherited from EX049.02.
* Design choice (domain restriction): the fundamental theorem and the Cauchy-Schwarz step run on
  the interval `[0, 2π]`. The change of variables of EX049.02 converts `∫ g² dangHaar` into
  `(2π)⁻¹ ∫_0^{2π} g²`. The normalization factor `2π` in `T` is kept in the proof through this
  identity, so the constant `4π²` in front of `T` comes from `(2π)²`.
* Design choice (constants): the second conjunct is the displayed bound
  `2M + 8π²T ≤ (2 + 8π²)(M + T)` with `D = 2 + 8π²` written out. The first conjunct is
  `(sup |v|)² ≤ 2M + 8π²T`. It follows from `|v x| ≤ √M + I` with `I = ∫_0^{2π} |g|`, from
  `(a + b)² ≤ 2a² + 2b²`, and from `I² ≤ 2π ∫_0^{2π} g² = 4π²T`. No division by `M` occurs, so the
  case `M = 0` is covered.
* Design choice (almost-everywhere transfer): the derivative of the representative equals `g` on
  `(0, 2π)`. The point `2π` is a null set, so the endpoint is removed by `compl_mem_ae_iff` and
  `measure_singleton`, and the interval integrals are identified with `integral_congr_ae`.
* Design choice (measure): `M` and `T` are integrals over the normalized Haar probability measure
  `angHaar`. Both integrals of `v²` and `w²` coincide by almost-everywhere equality of `v` and `w`.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory Set Real
open DGPS.Circle.AngularNormalization

/-- The absolute value of an interval integral over `[u, s] ⊆ [0, 2π]` is at most the integral of
the absolute value over `[0, 2π]`. -/
lemma abs_integral_le_EX04904 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (2 * π))
    {u s : ℝ} (hu : u ∈ Icc (0:ℝ) (2 * π)) (hs : s ∈ Icc (0:ℝ) (2 * π)) :
    |∫ x in u..s, f x| ≤ ∫ x in (0:ℝ)..(2 * π), |f x| := by
  have hmono : ∀ a b : ℝ, a ∈ Icc (0:ℝ) (2 * π) → b ∈ Icc (0:ℝ) (2 * π) → a ≤ b →
      |∫ x in a..b, f x| ≤ ∫ x in (0:ℝ)..(2 * π), |f x| := by
    intro a b ha hb hle
    refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
    exact intervalIntegral.integral_mono_interval ha.1 hle hb.2
      (ae_of_all _ fun x => abs_nonneg (f x)) hf.abs
  rcases le_total u s with h | h
  · exact hmono u s hu hs h
  · rw [intervalIntegral.integral_symm s u, abs_neg]
    exact hmono s u hs hu h

/-- Fundamental theorem of calculus for an absolutely continuous representative `F` on `[a, b]`
with `a ≤ b` inside `[0, 2π]`, where the almost-everywhere derivative of `F` is `G`. -/
lemma ftc_ordered_EX04904 {F G : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval F 0 (2 * π))
    (hder : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 (2 * π) → deriv F x = G x)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) (2 * π)) (hb : b ∈ Icc (0:ℝ) (2 * π)) (hab : a ≤ b) :
    F b - F a = ∫ x in a..b, G x := by
  have hsub : uIcc a b ⊆ uIcc (0:ℝ) (2 * π) := by
    rw [Set.uIcc_of_le (show (0:ℝ) ≤ 2 * π by positivity)]
    exact Set.uIcc_subset_Icc ha hb
  have hFTC : ∫ x in a..b, deriv F x = F b - F a := (hac.mono hsub).integral_deriv_eq_sub
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({2 * π} : Set ℝ) :=
    compl_mem_ae_iff.2 (measure_singleton _)
  have hcongr : ∫ x in a..b, deriv F x = ∫ x in a..b, G x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hder, hne] with x hx1 hx2 hxI
    rw [Set.uIoc_of_le hab] at hxI
    have hxne : x ≠ 2 * π := fun h => hx2 (Set.mem_singleton_iff.2 h)
    exact hx1 ⟨lt_of_le_of_lt ha.1 hxI.1, lt_of_le_of_ne (hxI.2.trans hb.2) hxne⟩
  exact hFTC.symm.trans hcongr

/-- The increment of the representative between two points of `[0, 2π]` is bounded by the
`L¹` norm of its derivative `G` over `[0, 2π]`. -/
lemma abs_sub_le_EX04904 {F G : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval F 0 (2 * π))
    (hder : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 (2 * π) → deriv F x = G x)
    (hG : IntervalIntegrable G volume 0 (2 * π)) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) (2 * π))
    (hb : b ∈ Icc (0:ℝ) (2 * π)) :
    |F b - F a| ≤ ∫ x in (0:ℝ)..(2 * π), |G x| := by
  rcases le_total a b with hab | hab
  · rw [ftc_ordered_EX04904 hac hder ha hb hab]
    exact abs_integral_le_EX04904 hG ha hb
  · rw [abs_sub_comm, ftc_ordered_EX04904 hac hder hb ha hab]
    exact abs_integral_le_EX04904 hG hb ha

/-- Cauchy-Schwarz on `[0, 2π]` in the form `(∫|f|)² ≤ 2π ∫ f²`. It is proved from the pointwise
inequality `2c|f| ≤ c² + f²` with `c = (∫|f|)/(2π)`, integrated over `[0, 2π]`. -/
lemma sq_integral_abs_le_EX04904 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (2 * π))
    (hf2 : IntervalIntegrable (fun s => f s ^ 2) volume 0 (2 * π)) :
    (∫ s in (0:ℝ)..(2 * π), |f s|) ^ 2 ≤ 2 * π * ∫ s in (0:ℝ)..(2 * π), f s ^ 2 := by
  have hpi : (0:ℝ) < 2 * π := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in (0:ℝ)..(2 * π), |f s|) / (2 * π) := ⟨_, rfl⟩
  have hI : ∫ s in (0:ℝ)..(2 * π), |f s| = 2 * π * c := by
    rw [hc]
    field_simp
  have key : ∫ s in (0:ℝ)..(2 * π), 2 * c * |f s| ≤
      ∫ s in (0:ℝ)..(2 * π), (c ^ 2 + f s ^ 2) := by
    refine intervalIntegral.integral_mono_on hpi.le ?_ ?_ ?_
    · exact hf.abs.const_mul (2 * c)
    · exact intervalIntegrable_const.add hf2
    · intro x _
      nlinarith [sq_nonneg (|f x| - c), sq_abs (f x)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const hf2,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero, hI] at key
  have key2 : 2 * π * c ^ 2 ≤ ∫ s in (0:ℝ)..(2 * π), f s ^ 2 := by
    nlinarith [key]
  rw [hI]
  nlinarith [mul_le_mul_of_nonneg_left key2 hpi.le]

/-- An `L²` function on the circle gives an `L²` function on `(0, 2π]`. -/
lemma memLp_Ioc_EX04904 {w : AngCircle → ℝ} (hw : MemLp w 2 angHaar) :
    MemLp (fun s : ℝ => w (s : AngCircle)) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  have e : volume.restrict (Ioo 0 (2 * π)) = volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [← e]
  exact memLp_interval_EX04902 hw

/-- An `L²` function on `(0, 2π]` is interval integrable on `[0, 2π]`, and so is its square. -/
lemma intervalIntegrable_EX04904 {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) :
    IntervalIntegrable f volume 0 (2 * π) ∧
      IntervalIntegrable (fun s => f s ^ 2) volume 0 (2 * π) := by
  have hle : (0:ℝ) ≤ 2 * π := by positivity
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 (hf.integrable one_le_two),
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 hf.integrable_sq⟩

/-- The representative `angSec θ` of a circle point lies in `[0, 2π]`. -/
lemma angSec_mem_EX04904 (x : AngCircle) : angSec x ∈ Icc (0:ℝ) (2 * π) := by
  have h := (AddCircle.equivIoc (2 * π) 0 x).2
  rw [Set.mem_Ioc] at h
  rw [angSec, Set.mem_Icc]
  exact ⟨h.1.le, by linarith [h.2]⟩

/-- The representative `angSec θ` projects back to the circle point `θ`. -/
lemma angSec_coe_EX04904 (x : AngCircle) : ((angSec x : ℝ) : AngCircle) = x := by
  simp [angSec]

/-- Main statement. For an angular `H¹` function `w`, its continuous representative `v` is unique
among continuous functions equal to `w` almost everywhere. For every angular weak derivative `g` of
`w`, with `M = ∫ w²` and `T = ∫ g²` over the normalized Haar measure, the supremum of `|v|` satisfies
`(sup |v|)² ≤ 2M + 8π²T ≤ (2 + 8π²)(M + T)`. -/
theorem ex049_04_explicit_angular_sobolev_supremum_estimate (w : AngCircle → ℝ)
    (hw : AngularH1 w) :
    ∃ v : AngCircle → ℝ, Continuous v ∧ v =ᵐ[angHaar] w ∧
      (∀ x : AngCircle → ℝ, Continuous x → x =ᵐ[angHaar] w → x = v) ∧
      ∀ g : AngCircle → ℝ, IsAngularWeakDeriv w g →
        (⨆ θ, |v θ|) ^ 2 ≤ 2 * (∫ θ, w θ ^ 2 ∂angHaar) + 8 * π ^ 2 * (∫ θ, g θ ^ 2 ∂angHaar) ∧
          2 * (∫ θ, w θ ^ 2 ∂angHaar) + 8 * π ^ 2 * (∫ θ, g θ ^ 2 ∂angHaar) ≤
            (2 + 8 * π ^ 2) * ((∫ θ, w θ ^ 2 ∂angHaar) + (∫ θ, g θ ^ 2 ∂angHaar)) := by
  have : Nonempty AngCircle := ⟨((0 : ℝ) : AngCircle)⟩
  obtain ⟨v, hvc, hvw, huniq, hac, -, hall⟩ :=
    ex049_02_angular_h1_has_absolutely_continuous_representative w hw
  refine ⟨v, hvc, hvw, huniq, fun g hg => ?_⟩
  obtain ⟨hder, hint⟩ := hall g hg
  have hgL : MemLp (fun s : ℝ => g (s : AngCircle)) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    memLp_Ioc_EX04904 hg.memLp_deriv
  obtain ⟨hgI, hgI2⟩ := intervalIntegrable_EX04904 hgL
  have hsqw : Integrable (fun θ => w θ ^ 2) angHaar := hg.memLp.integrable_sq
  have hsqg : Integrable (fun θ => g θ ^ 2) angHaar := hg.memLp_deriv.integrable_sq
  -- Change of variables for the derivative energy, from EX049.02.
  have hT : ∫ θ, g θ ^ 2 ∂angHaar = (2 * π)⁻¹ * ∫ s in (0:ℝ)..(2 * π), g (s : AngCircle) ^ 2 :=
    hint (fun _ y => y ^ 2) hsqg
  have hQ : ∫ s in (0:ℝ)..(2 * π), g (s : AngCircle) ^ 2 = 2 * π * ∫ θ, g θ ^ 2 ∂angHaar := by
    rw [hT, ← mul_assoc, mul_inv_cancel₀ (show (2 * π : ℝ) ≠ 0 by positivity), one_mul]
  have hTnn : 0 ≤ ∫ θ, g θ ^ 2 ∂angHaar := integral_nonneg fun θ => sq_nonneg _
  have hMnn : 0 ≤ ∫ θ, w θ ^ 2 ∂angHaar := integral_nonneg fun θ => sq_nonneg _
  -- Cauchy-Schwarz on the fundamental interval: I² ≤ 2π Q = 4π² T.
  have hI2 : (∫ s in (0:ℝ)..(2 * π), |g (s : AngCircle)|) ^ 2 ≤
      4 * π ^ 2 * ∫ θ, g θ ^ 2 ∂angHaar := by
    have h := sq_integral_abs_le_EX04904 hgI hgI2
    rw [hQ] at h
    nlinarith [h]
  -- The representative has the same integrals as w.
  have hMv : ∫ θ, v θ ^ 2 ∂angHaar = ∫ θ, w θ ^ 2 ∂angHaar :=
    integral_congr_ae (hvw.mono fun θ h => by simp only [h])
  have hint2 : Integrable (fun θ => v θ ^ 2) angHaar :=
    hsqw.congr (hvw.mono fun θ h => by simp only [h])
  -- A minimizer of v² on the circle lies below the probability average.
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty (hvc.pow 2).continuousOn
  have hy' : ∀ θ, v y ^ 2 ≤ v θ ^ 2 := fun θ => isMinOn_iff.1 hy θ (Set.mem_univ θ)
  have hyM : v y ^ 2 ≤ ∫ θ, w θ ^ 2 ∂angHaar := by
    rw [← hMv]
    have h1 : ∫ _θ, v y ^ 2 ∂angHaar ≤ ∫ θ, v θ ^ 2 ∂angHaar :=
      integral_mono (integrable_const _) hint2 (fun θ => hy' θ)
    simpa using h1
  have hyabs : |v y| ≤ Real.sqrt (∫ θ, w θ ^ 2 ∂angHaar) := Real.abs_le_sqrt hyM
  -- Pointwise bound |v x| ≤ √M + I on the whole circle.
  have hbound : ∀ x : AngCircle,
      |v x| ≤ Real.sqrt (∫ θ, w θ ^ 2 ∂angHaar) + ∫ s in (0:ℝ)..(2 * π), |g (s : AngCircle)| := by
    intro x
    have h1 : |v x - v y| ≤ ∫ s in (0:ℝ)..(2 * π), |g (s : AngCircle)| := by
      have h := abs_sub_le_EX04904 hac hder hgI (angSec_mem_EX04904 y) (angSec_mem_EX04904 x)
      simpa only [angSec_coe_EX04904] using h
    have h2 := abs_sub_abs_le_abs_sub (v x) (v y)
    linarith
  have hsup : (⨆ θ, |v θ|) ≤
      Real.sqrt (∫ θ, w θ ^ 2 ∂angHaar) + ∫ s in (0:ℝ)..(2 * π), |g (s : AngCircle)| :=
    ciSup_le hbound
  have hsup0 : 0 ≤ ⨆ θ, |v θ| := Real.iSup_nonneg fun θ => abs_nonneg _
  have hsq : (⨆ θ, |v θ|) ^ 2 ≤
      (Real.sqrt (∫ θ, w θ ^ 2 ∂angHaar) + ∫ s in (0:ℝ)..(2 * π), |g (s : AngCircle)|) ^ 2 :=
    pow_le_pow_left₀ hsup0 hsup 2
  have hsqrt : Real.sqrt (∫ θ, w θ ^ 2 ∂angHaar) ^ 2 = ∫ θ, w θ ^ 2 ∂angHaar :=
    Real.sq_sqrt hMnn
  refine ⟨?_, ?_⟩
  · nlinarith [hsq, hsqrt, hI2,
      sq_nonneg (Real.sqrt (∫ θ, w θ ^ 2 ∂angHaar) -
        ∫ s in (0:ℝ)..(2 * π), |g (s : AngCircle)|)]
  · nlinarith [mul_nonneg (sq_nonneg π) hMnn, hTnn]

end DGPS.Frontier.EX049
