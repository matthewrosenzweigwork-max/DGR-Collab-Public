import DGPS.Frontier.EX049.T34
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# EX049.31: Primitive of an L2 derivative

Task id: EX049.31 (node EX049, shared infrastructure). Prerequisite: EX049.34
(`DGPS.Frontier.EX049.T34`), used only for the weak-derivative identity.

Let `L > 0` and `g ∈ L²(0, L)` (Lebesgue measure). Then `V(x) = ∫₀ˣ g` is absolutely continuous
on `[0, L]`, has derivative `g` almost everywhere on `(0, L)`, satisfies
`|V y - V x| ≤ |y - x|^{1/2} ‖g‖_{L²(0,L)}` for `x, y ∈ [0, L]`, is bounded on `[0, L]`, belongs to
`L²(0, L)`, and has weak derivative `g` on `(0, L)`.

## Provides

- `DGPS.Frontier.EX049.ex049_31_primitive_l2_derivative`: the full specification statement, as a
  conjunction of six claims (absolute continuity on `[0, L]`, a.e. derivative equal to `g`, the
  square-root Hölder modulus with `‖g‖_{L²(0,L)}`, boundedness on `[0, L]`, membership in
  `L²(0, L)`, and the weak-derivative identity against test functions supported in `(0, L)`).
- `DGPS.Frontier.EX049.ex049_31_primitive_l2_derivative_holder`: the Hölder modulus claim alone,
  for `x, y ∈ [0, L]` (used by the main theorem and reusable elsewhere).

## R5 notes

- Hypotheses. The only hypotheses are `0 < L` and `g ∈ L²(0, L)`, both as in the specification.
  The helper bound `ex049_31_primitive_l2_derivative_holder` takes only `g ∈ L²(0, L)`; the
  hypothesis `0 < L` is not needed there, since the points are restricted to `[0, L]` by `x, y`.
- Norm. `‖g‖_{L²(0,L)}` is the ordinary Lebesgue norm `eLpNorm g 2 (volume.restrict (Ioo 0 L))`,
  taken as a real number with `.toReal`. It is finite because `g ∈ L²`. It is not a normalized or
  Haar `L²` norm (no probability measure is involved).
- Open versus closed interval. The `L²` space and the weak identity use `Ioo 0 L`, matching
  EX049.34. Since `Ioo 0 L` and `Ioc 0 L` differ by a null set, this is the same space. The
  absolute-continuity conclusion uses Mathlib's `AbsolutelyContinuousOnInterval V 0 L`, which is
  the epsilon-delta condition on `uIcc 0 L`; with `0 < L` this is `[0, L]`.
- Functions are real-valued, `g : ℝ → ℝ`. `g` is a fixed representative. `MemLp` and `eLpNorm`
  depend only on the a.e. class, and the conclusions are representative-independent, except that
  the Hölder modulus and boundedness are statements about the chosen representative `V`, which is
  the integral and so is determined by the class of `g`.
- Derivative. The a.e. derivative is Mathlib's total function `deriv`, and the a.e. claim is
  quantified as `∀ᵐ x, x ∈ Ioo 0 L → deriv V x = g x`. Existence of the derivative a.e. comes
  from the Lebesgue differentiation theorem for interval integrals
  (`IntervalIntegrable.ae_hasDerivAt_integral`), not from the absolute continuity alone.
- Boundedness. The specification says "bounded". It is stated as `∃ M, ∀ x ∈ [0, L], |V x| ≤ M`.
  The proof gives the explicit value `M = L^{1/2} ‖g‖_{L²(0,L)}`, which is not part of the
  statement.
- Weak derivative. Test functions are `φ : ℝ → ℝ` with `ContDiff ℝ ∞ φ`, `HasCompactSupport φ` and
  `tsupport φ ⊆ Ioo 0 L`, the same class as in EX049.34. The identity is
  `∫ V φ' = -∫ g φ` over `Ioo 0 L`. The weak identity is obtained from EX049.34 with the
  constant second factor `v ≡ 1`, so `deriv v = 0`.
- Hölder modulus. The specification's `|y - x|^{1/2}` is `|y - x| ^ (1/2 : ℝ)`. The proof uses
  `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` (`L¹` against `L²` on the interval `(x, y]`) and
  monotonicity of `eLpNorm` in the measure. It does not use a Mathlib Hölder statement on
  normalized measures.
- Imports. Besides EX049.34, the file imports `Mathlib.Analysis.Calculus.ContDiff.Basic` for the
  constant function `v ≡ 1` (smooth, hence absolutely continuous on `[0, L]`); it adds no statement.
- No other campaign theorem and no extra assumption is used. Every statement is proved.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace DGPS.Frontier.EX049

/-- For `0 ≤ x ≤ L`, the function `g` is interval integrable on `0..x` when `g ∈ L²(0, L)`. -/
lemma intervalIntegrable_zero_EX04931 {L : ℝ} {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 L))) {x : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    IntervalIntegrable g volume 0 x := by
  have hgI : IntegrableOn g (Ioo 0 L) volume := hg.integrable (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hx0).mpr
    (hgI.mono_set (Ioo_subset_Ioo le_rfl hxL))

/-- The interval `(x, y]` lies in `(0, L]` when `0 ≤ x` and `y ≤ L`. -/
lemma Ioc_subset_EX04931 {x y L : ℝ} (hx : 0 ≤ x) (hy : y ≤ L) :
    Ioc x y ⊆ Ioc 0 L :=
  fun _ ht => ⟨lt_of_le_of_lt hx ht.1, ht.2.trans hy⟩

/-- Ordered Hölder modulus: for `0 ≤ x ≤ y ≤ L`, `|∫ₓʸ g| ≤ |y - x|^{1/2} ‖g‖_{L²(0,L)}`. -/
lemma abs_integral_le_EX04931 {L : ℝ} {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 L))) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ L) :
    |∫ t in x..y, g t| ≤ |y - x| ^ (1/2 : ℝ) * (eLpNorm g 2 (volume.restrict (Ioo 0 L))).toReal := by
  have hIoc : volume.restrict (Ioo 0 L) = volume.restrict (Ioc 0 L) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hgIoc : MemLp g 2 (volume.restrict (Ioc 0 L)) := by rw [← hIoc]; exact hg
  have hsub : Ioc x y ⊆ Ioc 0 L := Ioc_subset_EX04931 hx hy
  have hmeas : AEStronglyMeasurable g (volume.restrict (Ioc x y)) :=
    hgIoc.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hE : eLpNorm g 2 (volume.restrict (Ioo 0 L)) ≠ ⊤ := hg.eLpNorm_ne_top
  have hmono : eLpNorm g 2 (volume.restrict (Ioc x y)) ≤
      eLpNorm g 2 (volume.restrict (Ioo 0 L)) := by
    rw [hIoc]; exact eLpNorm_mono_measure g (Measure.restrict_mono hsub le_rfl)
  have hvol : (volume.restrict (Ioc x y)) Set.univ = ENNReal.ofReal (y - x) := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  have hle : eLpNorm g 1 (volume.restrict (Ioc x y)) ≤
      eLpNorm g 2 (volume.restrict (Ioo 0 L)) * ENNReal.ofReal (y - x) ^ (1 / 2 : ℝ) := by
    calc eLpNorm g 1 (volume.restrict (Ioc x y))
        ≤ eLpNorm g 2 (volume.restrict (Ioc x y)) *
          (volume.restrict (Ioc x y)) Set.univ
            ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hmeas
      _ ≤ _ := by rw [hexp, hvol]; gcongr
  have hfin : eLpNorm g 2 (volume.restrict (Ioo 0 L)) * ENNReal.ofReal (y - x) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hE (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hyx : 0 ≤ y - x := by linarith
  calc |∫ t in x..y, g t|
      = ‖∫ t in x..y, g t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in x..y, ‖g t‖ := intervalIntegral.norm_integral_le_integral_norm hxy
    _ = ∫ t in Ioc x y, ‖g t‖ := intervalIntegral.integral_of_le hxy
    _ = (∫⁻ t in Ioc x y, ‖g t‖ₑ).toReal := integral_norm_eq_lintegral_enorm hmeas
    _ = (eLpNorm g 1 (volume.restrict (Ioc x y))).toReal := by
          rw [eLpNorm_one_eq_lintegral_enorm hmeas]
    _ ≤ (eLpNorm g 2 (volume.restrict (Ioo 0 L)) * ENNReal.ofReal (y - x) ^ (1 / 2 : ℝ)).toReal :=
          ENNReal.toReal_mono hfin hle
    _ = |y - x| ^ (1 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict (Ioo 0 L))).toReal := by
          rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hyx,
            abs_of_nonneg hyx, mul_comm]

/-- Hölder modulus of the primitive `V(x) = ∫₀ˣ g`: for `x, y ∈ [0, L]`,
`|V y - V x| ≤ |y - x|^{1/2} ‖g‖_{L²(0,L)}`. -/
theorem ex049_31_primitive_l2_derivative_holder {L : ℝ} {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 L))) {x y : ℝ}
    (hx : x ∈ Icc 0 L) (hy : y ∈ Icc 0 L) :
    |(∫ t in (0:ℝ)..y, g t) - ∫ t in (0:ℝ)..x, g t| ≤
      |y - x| ^ (1 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict (Ioo 0 L))).toReal := by
  rw [intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_zero_EX04931 hg hy.1 hy.2) (intervalIntegrable_zero_EX04931 hg hx.1 hx.2)]
  rcases le_total x y with hxy | hyx
  · exact abs_integral_le_EX04931 hg hx.1 hxy hy.2
  · rw [intervalIntegral.integral_symm, abs_neg, abs_sub_comm y x]
    exact abs_integral_le_EX04931 hg hy.1 hyx hx.2

/-- Primitive of an `L²` derivative on `(0, L)`: `V(x) = ∫₀ˣ g` is absolutely continuous on
`[0, L]` with a.e. derivative `g`, satisfies the square-root Hölder modulus with the `L²(0, L)`
norm of `g`, is bounded, lies in `L²(0, L)`, and has weak derivative `g`. -/
theorem ex049_31_primitive_l2_derivative {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 L))) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0:ℝ)..x, g t) 0 L ∧
    (∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 L → deriv (fun x => ∫ t in (0:ℝ)..x, g t) x = g x) ∧
    (∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
      |(∫ t in (0:ℝ)..y, g t) - ∫ t in (0:ℝ)..x, g t| ≤
        |y - x| ^ (1 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict (Ioo 0 L))).toReal) ∧
    (∃ M : ℝ, ∀ x ∈ Icc 0 L, |∫ t in (0:ℝ)..x, g t| ≤ M) ∧
    MemLp (fun x => ∫ t in (0:ℝ)..x, g t) 2 (volume.restrict (Ioo 0 L)) ∧
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 L →
      ∫ x in Ioo 0 L, (∫ t in (0:ℝ)..x, g t) * deriv φ x = -∫ x in Ioo 0 L, g x * φ x) := by
  have hL0 : (0:ℝ) ∈ uIcc 0 L := left_mem_uIcc
  have hI : IntervalIntegrable g volume 0 L := intervalIntegrable_zero_EX04931 hg hL.le le_rfl
  have hAC : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0:ℝ)..x, g t) 0 L :=
    hI.absolutelyContinuousOnInterval_intervalIntegral hL0
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 L →
      deriv (fun x => ∫ t in (0:ℝ)..x, g t) x = g x := by
    filter_upwards [hI.ae_hasDerivAt_integral] with x hx hxI
    have hxu : x ∈ uIcc 0 L := by rw [uIcc_of_le hL.le]; exact Ioo_subset_Icc_self hxI
    exact (hx hxu 0 hL0).deriv
  have hcont := hAC.continuousOn
  rw [uIcc_of_le hL.le] at hcont
  have hmeasV : AEStronglyMeasurable (fun x => ∫ t in (0:ℝ)..x, g t)
      (volume.restrict (Ioo 0 L)) :=
    (hcont.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hbound : ∀ x ∈ Icc 0 L,
      |∫ t in (0:ℝ)..x, g t| ≤ L ^ (1 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict (Ioo 0 L))).toReal := by
    intro x hx
    have h := ex049_31_primitive_l2_derivative_holder hg (x := 0) (y := x) ⟨le_rfl, hL.le⟩ hx
    simp only [intervalIntegral.integral_same, sub_zero] at h
    rw [abs_of_nonneg hx.1] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx.1 hx.2 (by norm_num)) ENNReal.toReal_nonneg)
  have hV : MemLp (fun x => ∫ t in (0:ℝ)..x, g t) 2 (volume.restrict (Ioo 0 L)) := by
    refine MemLp.of_bound hmeasV (L ^ (1 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict (Ioo 0 L))).toReal) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]; exact hbound x (Ioo_subset_Icc_self hx)
  have hV' : MemLp (deriv fun x => ∫ t in (0:ℝ)..x, g t) 2 (volume.restrict (Ioo 0 L)) :=
    hg.ae_eq ((ae_restrict_iff' measurableSet_Ioo).mpr
      (hderiv.mono fun x hx hxI => (hx hxI).symm))
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℝ)) 0 L :=
    ContDiffOn.absolutelyContinuousOnInterval (contDiff_const (𝕜 := ℝ) (n := 1)).contDiffOn
  have hconst' : MemLp (deriv fun _ : ℝ => (1:ℝ)) 2 (volume.restrict (Ioo 0 L)) := by
    rw [deriv_const']; exact memLp_const 0
  obtain ⟨-, -, -, -, hweak⟩ :=
    ex049_34_ac_products_h1_bounds_interval hAC hconst hV' hconst'
  refine ⟨hAC, hderiv, fun x hx y hy => ex049_31_primitive_l2_derivative_holder hg hx hy,
    ⟨L ^ (1 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict (Ioo 0 L))).toReal, hbound⟩, hV,
    fun φ hφ hcs hts => ?_⟩
  have h := hweak φ hφ hcs hts
  simp only [mul_one, deriv_const', mul_zero, add_zero] at h
  rw [h]
  congr 1
  refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioo).mpr ?_)
  filter_upwards [hderiv] with x hx hxI
  rw [hx hxI]

end DGPS.Frontier.EX049
