import LeanResearch.PeriodicAttractiveLogGas.RadialMollifier
import LeanResearch.PeriodicAttractiveLogGas.LaplacianGeometry
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

/-! Harmonic reproduction by the explicit planar radial probability kernel.

The proof uses the pinned Mathlib complex circle mean-value theorem. The
complex-to-Euclidean isometry preserves the actual Lebesgue measures. Polar
Fubini is justified by integrability on a compact rectangle and vanishing
outside its radial range. No radial mean-value theorem is assumed.
-/

noncomputable section

open MeasureTheory InnerProductSpace Metric Set Filter
open scoped ContDiff Topology Convolution

namespace PeriodicAttractiveLogGas

theorem continuous_complex_polar_symm :
    Continuous (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

/-- Compact support in the radial direction supplies actual polar integrability,
despite the unbounded radial target of the change of variables. -/
theorem integrableOn_complex_polar_of_support {q : ℂ → ℝ}
    (hq : Continuous q) (R : ℝ) (hq0 : ∀ z, R ≤ ‖z‖ → q z = 0) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * q (Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) volume := by
  let F : ℝ × ℝ → ℝ := fun p ↦ p.1 * q (Complex.polarCoord.symm p)
  let K : Set (ℝ × ℝ) := Icc 0 R ×ˢ Icc (-Real.pi) Real.pi
  have hF : Continuous F := continuous_fst.mul (hq.comp continuous_complex_polar_symm)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hint : Integrable (K.indicator F) volume :=
    (hF.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  refine hint.integrableOn.congr_fun (fun p hp ↦ ?_)
    (measurableSet_Ioi.prod measurableSet_Ioo)
  by_cases hpK : p ∈ K
  · exact indicator_of_mem hpK F
  · have hRp : R ≤ p.1 := by
      by_contra h
      exact hpK ⟨⟨hp.1.le, (lt_of_not_ge h).le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
    have hnorm : R ≤ ‖Complex.polarCoord.symm p‖ := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      exact hRp
    have hzero : F p = 0 := by
      dsimp only [F]
      rw [hq0 _ hnorm, mul_zero]
    change K.indicator F p = F p
    rw [indicator_of_notMem hpK, hzero]

theorem integral_complex_eq_polar_iterated {q : ℂ → ℝ}
    (hq : Continuous q) (R : ℝ) (hq0 : ∀ z, R ≤ ‖z‖ → q z = 0) :
    (∫ z, q z) = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
      r * q (Complex.polarCoord.symm (r, θ)) := by
  rw [← Complex.integral_comp_polarCoord_symm q]
  simp only [smul_eq_mul]
  exact setIntegral_prod _ (integrableOn_complex_polar_of_support hq R hq0)

theorem integral_Ioo_neg_pi_pi_const (a : ℝ) :
    (∫ _θ in Ioo (-Real.pi) Real.pi, a) = (2 * Real.pi) * a := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Conversion of the pinned normalized circle mean into the angular integral
used by polar coordinates. Endpoints do not contribute to Lebesgue integrals. -/
theorem integral_polar_circle_of_harmonic {h : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hh : HarmonicOnNhd h (closedBall c |r|)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, h (c + Complex.polarCoord.symm (r, θ))) =
      (2 * Real.pi) * h c := by
  have hpolar (θ : ℝ) : c + Complex.polarCoord.symm (r, θ) = circleMap c r θ := by
    simp only [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  simp_rw [hpolar]
  have hp : (fun θ ↦ h (circleMap c r θ)).Periodic (2 * Real.pi) :=
    fun θ ↦ congrArg h (periodic_circleMap c r θ)
  have hangle : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hshift : (∫ θ in -Real.pi..Real.pi, h (circleMap c r θ)) =
      ∫ θ in 0..2 * Real.pi, h (circleMap c r θ) := by
    simpa only [hangle, zero_add] using hp.intervalIntegral_add_eq (-Real.pi) 0
  have hmean := hh.circleAverage_eq
  rw [Real.circleAverage_def, smul_eq_mul] at hmean
  have hfull : (∫ θ in 0..2 * Real.pi, h (circleMap c r θ)) =
      (2 * Real.pi) * h c := by
    simpa only [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),
      one_mul] using congrArg (fun a : ℝ ↦ (2 * Real.pi) * a) hmean
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    hshift, hfull]

/-- Radial harmonic reproduction on the complex plane, with the kernel mass
left explicit. Both polar integrands have independently justified integrability. -/
theorem integral_complex_radial_mul_add {κ h : ℂ → ℝ} {c : ℂ}
    (R : ℝ) (hκ : Continuous κ)
    (hκrad : ∀ {z w : ℂ}, ‖z‖ = ‖w‖ → κ z = κ w)
    (hκ0 : ∀ z, R ≤ ‖z‖ → κ z = 0) (hc : Continuous h)
    (hh : HarmonicOnNhd h (closedBall c R)) :
    (∫ z, κ z * h (c + z)) = (∫ z, κ z) * h c := by
  have hq : Continuous (fun z ↦ κ z * h (c + z)) :=
    hκ.mul (hc.comp (continuous_const.add continuous_id))
  have hq0 : ∀ z, R ≤ ‖z‖ → κ z * h (c + z) = 0 := fun z hz ↦ by
    rw [hκ0 z hz, zero_mul]
  have hinner : ∀ r ∈ Ioi (0 : ℝ),
      (∫ θ in Ioo (-Real.pi) Real.pi,
        r * (κ (Complex.polarCoord.symm (r, θ)) * h (c + Complex.polarCoord.symm (r, θ)))) =
      (∫ θ in Ioo (-Real.pi) Real.pi,
        r * κ (Complex.polarCoord.symm (r, θ))) * h c := by
    intro r hr
    have hrpos : 0 < r := hr
    have hκr (θ : ℝ) : κ (Complex.polarCoord.symm (r, θ)) = κ (r : ℂ) :=
      hκrad (by simp only [Complex.norm_polarCoord_symm, Complex.norm_real, Real.norm_eq_abs])
    by_cases hrR : r ≤ R
    · have hh' : HarmonicOnNhd h (closedBall c |r|) := by
        rw [abs_of_pos hrpos]
        exact fun z hz ↦ hh z (closedBall_subset_closedBall hrR hz)
      simp_rw [hκr, ← mul_assoc]
      rw [integral_const_mul, integral_polar_circle_of_harmonic hh',
        integral_Ioo_neg_pi_pi_const]
      ring
    · have hzero (θ : ℝ) : κ (Complex.polarCoord.symm (r, θ)) = 0 :=
        hκ0 _ (by simpa only [Complex.norm_polarCoord_symm, abs_of_pos hrpos]
          using (lt_of_not_ge hrR).le)
      simp_rw [hzero, zero_mul, mul_zero, integral_zero]
      simp only [zero_mul]
  calc
    (∫ z, κ z * h (c + z)) = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r * (κ (Complex.polarCoord.symm (r, θ)) *
          h (c + Complex.polarCoord.symm (r, θ))) :=
      integral_complex_eq_polar_iterated hq R hq0
    _ = ∫ r in Ioi (0 : ℝ), (∫ θ in Ioo (-Real.pi) Real.pi,
        r * κ (Complex.polarCoord.symm (r, θ))) * h c :=
      setIntegral_congr_fun measurableSet_Ioi hinner
    _ = (∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        r * κ (Complex.polarCoord.symm (r, θ))) * h c := integral_mul_const _ _
    _ = (∫ z, κ z) * h c :=
      congrArg (fun a : ℝ ↦ a * h c) (integral_complex_eq_polar_iterated hκ R hκ0).symm

/-- Actual integrability of a continuous function paired with the translated kernel. -/
theorem integrable_radialMollifier_mul_sub (R : ℝ) (hR : 0 < R)
    {h : PlanarSpace → ℝ} (hc : Continuous h) (x : PlanarSpace) :
    Integrable (fun y ↦ radialMollifier R hR y * h (x - y)) volume :=
  ((contDiff_radialMollifier R hR).continuous.mul
    (hc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hasCompactSupport_radialMollifier R hR).mul_right

theorem integrable_mul_radialMollifier_sub (R : ℝ) (hR : 0 < R)
    {h : PlanarSpace → ℝ} (hc : Continuous h) (x : PlanarSpace) :
    Integrable (fun y ↦ h y * radialMollifier R hR (x - y)) volume :=
  (hc.mul ((contDiff_radialMollifier R hR).continuous.comp
    (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((hasCompactSupport_radialMollifier R hR).comp_homeomorph
        (Homeomorph.subLeft x)).mul_left

theorem integral_radialMollifier_mul_add_eq (R : ℝ) (hR : 0 < R)
    {h : PlanarSpace → ℝ} (hc : Continuous h) {x : PlanarSpace}
    (hh : HarmonicOnNhd h (closedBall x R)) :
    (∫ y, radialMollifier R hR y * h (x + y)) = h x := by
  let l : ℂ ≃ₗᵢ[ℝ] PlanarSpace := Complex.orthonormalBasisOneI.repr
  let c : ℂ := l.symm x
  have hhc : HarmonicOnNhd (h ∘ l) (closedBall c R) := by
    intro z hz
    apply (harmonicAt_comp_linearIsometryEquiv_right_iff l).2
    apply hh
    change dist z c ≤ R at hz
    change dist (l z) x ≤ R
    calc
      dist (l z) x = dist z c := by
        change dist (l z) x = dist z (l.symm x)
        rw [← l.dist_map, l.apply_symm_apply]
      _ ≤ R := hz
  have hmass : (∫ z : ℂ, radialMollifier R hR (l z)) = 1 := by
    rw [l.measurePreserving.integral_comp l.toHomeomorph.measurableEmbedding]
    exact integral_radialMollifier R hR
  have hrep := integral_complex_radial_mul_add
    (κ := fun z : ℂ ↦ radialMollifier R hR (l z)) (h := h ∘ l) (c := c) R
    ((contDiff_radialMollifier R hR).continuous.comp l.continuous)
    (fun {z w} hzw ↦ radialMollifier_eq_of_norm_eq R hR (by simpa only [l.norm_map] using hzw))
    (fun z hz ↦ radialMollifier_eq_zero_of_le_norm R hR
      (by simpa only [l.norm_map] using hz))
    (hc.comp l.continuous) hhc
  rw [hmass, one_mul] at hrep
  have hchange := l.measurePreserving.integral_comp l.toHomeomorph.measurableEmbedding
    (fun y ↦ radialMollifier R hR y * h (x + y))
  rw [← hchange]
  simpa only [Function.comp_apply, c, map_add, l.apply_symm_apply] using hrep

/-- A radial probability kernel reproduces every globally continuous real
function harmonic on a neighborhood of the entire closed support ball. -/
theorem integral_radialMollifier_mul_sub_eq (R : ℝ) (hR : 0 < R)
    {h : PlanarSpace → ℝ} (hc : Continuous h) {x : PlanarSpace}
    (hh : HarmonicOnNhd h (closedBall x R)) :
    (∫ y, radialMollifier R hR y * h (x - y)) = h x := by
  have hneg := integral_neg_eq_self
    (fun y ↦ radialMollifier R hR y * h (x - y)) volume
  have hplus : (∫ y, radialMollifier R hR y * h (x + y)) =
      ∫ y, radialMollifier R hR y * h (x - y) := by
    simpa only [radialMollifier_neg, sub_neg_eq_add] using hneg
  rw [← hplus]
  exact integral_radialMollifier_mul_add_eq R hR hc hh

/-- The explicit radial kernel reproduces harmonic functions by convolution. -/
theorem radialMollifier_convolution_eq (R : ℝ) (hR : 0 < R)
    {h : PlanarSpace → ℝ} (hc : Continuous h) {x : PlanarSpace}
    (hh : HarmonicOnNhd h (closedBall x R)) :
    (radialMollifier R hR ⋆ h) x = h x := by
  simpa only [convolution_lsmul, smul_eq_mul] using
    integral_radialMollifier_mul_sub_eq R hR hc hh

/-- The same normalized reproduction identity with the kernel on the right. -/
theorem convolution_radialMollifier_eq (R : ℝ) (hR : 0 < R)
    {h : PlanarSpace → ℝ} (hc : Continuous h) {x : PlanarSpace}
    (hh : HarmonicOnNhd h (closedBall x R)) :
    (h ⋆ radialMollifier R hR) x = h x := by
  rw [convolution_lsmul_swap]
  simpa only [smul_eq_mul, mul_comm] using integral_radialMollifier_mul_sub_eq R hR hc hh

end PeriodicAttractiveLogGas
