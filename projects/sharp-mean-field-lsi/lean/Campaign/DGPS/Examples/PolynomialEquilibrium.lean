import DGPS.Examples.SixthOrderCentering
import DGPS.Examples.RoughBoundary.SemicontinuityPotential

/-!
# Actual polynomial moving equilibrium (EX054)

The normalized law below is the actual density proportional to
`exp (h cos θ - s P_h θ)` against normalized angular Haar measure.
All helpers carry the EX054 suffix. The scalar root is globally unique. Repeated
differentiation of the actual polynomial tilted expectations gives C² field
regularity. Exact half-turn parity and compactness yield a quadratic field
variance remainder; uniform tilt derivative bounds give a linear tilt remainder.
The scalar mean value theorem then gives the sharp sixth-order coefficient with
a uniform eighth-order remainder. The logarithmic density ratio is controlled in
every fixed angular derivative norm, and reflection and half-turn symmetries are exact.
-/

open MeasureTheory Real Filter Topology Set
open scoped ContDiff
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments
open DGPS.Examples.PolynomialSpecies
open DGPS.Examples.RoughBoundary.Semicontinuity

namespace DGPS.Examples.PolynomialEquilibrium

/-- The feature in angular coordinates, matching EX052. -/
noncomputable def feature_EX054 (h : ℝ) (θ : AngCircle) : ℝ :=
  angMode 2 θ - h / 3 * angCos θ

theorem feature_model_EX054 (h : ℝ) (x : DGPS.Torus 1) :
    feature_EX054 h (angEquiv x) = polyFeature h x :=
  (DGPS.Examples.SixthOrderCentering.polyFeature_eq_ang h x).symm

theorem continuous_feature_EX054 (h : ℝ) : Continuous (feature_EX054 h) :=
  (continuous_angMode 2).sub (continuous_const.mul (continuous_angMode 1))

theorem abs_feature_le_EX054 (h : ℝ) (θ : AngCircle) :
    |feature_EX054 h θ| ≤ 1 + |h| / 3 := by
  unfold feature_EX054
  calc _ ≤ |angMode 2 θ| + |h / 3 * angCos θ| := abs_sub _ _
    _ ≤ 1 + |h| / 3 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      have := abs_angMode_le 2 θ
      have := mul_le_mul_of_nonneg_left (abs_angMode_le 1 θ) (by positivity : 0 ≤ |h| / 3)
      linarith

/-- Unnormalized weight of the actual two-parameter family. -/
noncomputable def weight_EX054 (h s : ℝ) (θ : AngCircle) : ℝ :=
  Real.exp (h * angCos θ - s * feature_EX054 h θ)

/-- Its partition function. -/
noncomputable def partition_EX054 (h s : ℝ) : ℝ :=
  ∫ θ, weight_EX054 h s θ ∂angHaar

/-- The actual normalized density; no selected optimizer enters its definition. -/
noncomputable def density_EX054 (h s : ℝ) (θ : AngCircle) : ℝ :=
  weight_EX054 h s θ / partition_EX054 h s

/-- The actual feature expectation. -/
noncomputable def moment_EX054 (h s : ℝ) : ℝ :=
  (∫ θ, feature_EX054 h θ * weight_EX054 h s θ ∂angHaar) / partition_EX054 h s

/-- Left side minus right side in the scalar equilibrium equation. -/
noncomputable def residual_EX054 (h s : ℝ) : ℝ :=
  s - 2 * eta * (moment_EX054 h s - polyCentering h)

theorem tiltData_EX054 (h : ℝ) :
    TiltData angHaar (fun θ => h * angCos θ) (fun θ => -feature_EX054 h θ)
      (feature_EX054 h) (fun _ => 0) (fun _ => 0) := by
  have hc := continuous_angMode 1
  have hp := continuous_feature_EX054 h
  refine ⟨(continuous_const.mul hc).measurable, hp.neg.measurable, hp.measurable,
    measurable_const, measurable_const, ?_, ?_, ?_, AEBdd.const 0, AEBdd.const 0⟩
  · refine ⟨|h|, Eventually.of_forall fun θ => ?_⟩
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_angMode_le 1 θ) (abs_nonneg h)
  · exact ⟨1 + |h| / 3, Eventually.of_forall fun θ => by
      simpa only [abs_neg] using abs_feature_le_EX054 h θ⟩
  · exact ⟨1 + |h| / 3, Eventually.of_forall (abs_feature_le_EX054 h)⟩

theorem partition_eq_polyZ_EX054 (h s : ℝ) :
    partition_EX054 h s = polyZ angHaar (fun θ => h * angCos θ)
      (fun θ => -feature_EX054 h θ) s := by
  simp only [partition_EX054, weight_EX054, polyZ, mul_neg, sub_eq_add_neg]

theorem partition_pos_EX054 (h s : ℝ) : 0 < partition_EX054 h s := by
  rw [partition_eq_polyZ_EX054]
  have ht := tiltData_EX054 h
  exact polyZ_pos _ _ ht.m0 ht.m1 ht.b0 ht.b1 s

theorem continuous_weight_EX054 (h s : ℝ) : Continuous (weight_EX054 h s) := by
  unfold weight_EX054
  exact Real.continuous_exp.comp ((continuous_const.mul (continuous_angMode 1)).sub
    (continuous_const.mul (continuous_feature_EX054 h)))

theorem integrable_weight_EX054 (h s : ℝ) : Integrable (weight_EX054 h s) angHaar :=
  (continuous_weight_EX054 h s).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_feature_weight_EX054 (h s : ℝ) :
    Integrable (fun θ => feature_EX054 h θ * weight_EX054 h s θ) angHaar :=
  ((continuous_feature_EX054 h).mul (continuous_weight_EX054 h s)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem density_pos_EX054 (h s : ℝ) (θ : AngCircle) : 0 < density_EX054 h s θ :=
  div_pos (Real.exp_pos _) (partition_pos_EX054 h s)

theorem integral_density_EX054 (h s : ℝ) : ∫ θ, density_EX054 h s θ ∂angHaar = 1 := by
  simp only [density_EX054, integral_div]
  change partition_EX054 h s / partition_EX054 h s = 1
  exact div_self (partition_pos_EX054 h s).ne'

theorem moment_eq_integral_EX054 (h s : ℝ) :
    moment_EX054 h s = ∫ θ, feature_EX054 h θ * density_EX054 h s θ ∂angHaar := by
  simp only [density_EX054, ← mul_div_assoc, integral_div, moment_EX054]

theorem abs_moment_le_EX054 (h s : ℝ) : |moment_EX054 h s| ≤ 1 + |h| / 3 := by
  have ht := tiltData_EX054 h
  have key := abs_int_mul_exp_le ht.m0 ht.m1 ht.b0 ht.b1 s
    (Eventually.of_forall (abs_feature_le_EX054 h))
  have hw : ∀ θ, Real.exp (h * angCos θ + s * -feature_EX054 h θ) = weight_EX054 h s θ := by
    intro θ
    simp only [weight_EX054, mul_neg, sub_eq_add_neg]
  simp_rw [hw, ← partition_eq_polyZ_EX054] at key
  rw [moment_EX054, abs_div, abs_of_pos (partition_pos_EX054 h s),
    div_le_iff₀ (partition_pos_EX054 h s)]
  exact key

theorem moment_eq_polyTilt_EX054 (h s : ℝ) :
    moment_EX054 h s = polyTilt angHaar (fun θ => h * angCos θ)
      (fun θ => -feature_EX054 h θ) (feature_EX054 h) (fun _ => 0) (fun _ => 0) s := by
  simp only [moment_EX054, polyTilt, polyNum, ← partition_eq_polyZ_EX054,
    mul_zero, add_zero, weight_EX054, mul_neg, sub_eq_add_neg]

/-- The variance under the actual normalized law. -/
noncomputable def variance_EX054 (h s : ℝ) : ℝ :=
  (∫ θ, feature_EX054 h θ ^ 2 * weight_EX054 h s θ ∂angHaar) /
    partition_EX054 h s - moment_EX054 h s ^ 2

theorem integrable_square_weight_EX054 (h s : ℝ) :
    Integrable (fun θ => feature_EX054 h θ ^ 2 * weight_EX054 h s θ) angHaar :=
  (((continuous_feature_EX054 h).pow 2).mul (continuous_weight_EX054 h s)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem variance_algebra_EX054 (N Q Z : ℝ) (hz : Z ≠ 0) :
    Q / Z - (N / Z) ^ 2 = (Q - 2 * (N / Z) * N + (N / Z) ^ 2 * Z) / Z := by
  field_simp [hz]
  ring

theorem centered_integral_EX054 (p w : AngCircle → ℝ) (m : ℝ)
    (hw : Integrable w angHaar)
    (hp : Integrable (fun θ => p θ * w θ) angHaar)
    (hq : Integrable (fun θ => p θ ^ 2 * w θ) angHaar) :
    (∫ θ, (p θ - m) ^ 2 * w θ ∂angHaar) =
      (∫ θ, p θ ^ 2 * w θ ∂angHaar) -
        2 * m * (∫ θ, p θ * w θ ∂angHaar) + m ^ 2 * (∫ θ, w θ ∂angHaar) := by
  let f : AngCircle → ℝ := fun θ => p θ ^ 2 * w θ
  let g : AngCircle → ℝ := fun θ => (2 * m) * (p θ * w θ)
  let k : AngCircle → ℝ := fun θ => m ^ 2 * w θ
  have hf : Integrable f angHaar := hq
  have hg : Integrable g angHaar := hp.const_mul (2 * m)
  have hk : Integrable k angHaar := hw.const_mul (m ^ 2)
  have hfg : Integrable (f - g) angHaar := hf.sub hg
  have eg : (∫ θ, g θ ∂angHaar) = 2 * m * (∫ θ, p θ * w θ ∂angHaar) := by
    simp only [g, integral_const_mul]
  have ek : (∫ θ, k θ ∂angHaar) = m ^ 2 * (∫ θ, w θ ∂angHaar) := by
    simp only [k, integral_const_mul]
  calc
    _ = ∫ θ, ((f - g) + k) θ ∂angHaar := by
      apply integral_congr_ae
      exact Eventually.of_forall fun θ => by
        change (p θ - m) ^ 2 * w θ = p θ ^ 2 * w θ - (2 * m) * (p θ * w θ) + m ^ 2 * w θ
        ring
    _ = (∫ θ, f θ ∂angHaar) - (∫ θ, g θ ∂angHaar) + (∫ θ, k θ ∂angHaar) := by
      rw [integral_add' hfg hk, integral_sub' hf hg]
    _ = _ := by rw [eg, ek]

theorem variance_integral_EX054 (h s : ℝ) :
    variance_EX054 h s =
      (∫ θ, (feature_EX054 h θ - moment_EX054 h s) ^ 2 *
        weight_EX054 h s θ ∂angHaar) / partition_EX054 h s := by
  conv_rhs => rw [centered_integral_EX054 (feature_EX054 h) (weight_EX054 h s) (moment_EX054 h s)
    (integrable_weight_EX054 h s) (integrable_feature_weight_EX054 h s)
    (integrable_square_weight_EX054 h s)]
  exact variance_algebra_EX054
    (∫ θ, feature_EX054 h θ * weight_EX054 h s θ ∂angHaar)
    (∫ θ, feature_EX054 h θ ^ 2 * weight_EX054 h s θ ∂angHaar)
    (partition_EX054 h s) (partition_pos_EX054 h s).ne'

theorem variance_nonneg_EX054 (h s : ℝ) : 0 ≤ variance_EX054 h s := by
  rw [variance_integral_EX054]
  exact div_nonneg (integral_nonneg fun θ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (partition_pos_EX054 h s).le

/-- Differentiation of the actual expectation, with no derivative assumption. -/
theorem hasDerivAt_moment_EX054 (h s : ℝ) :
    HasDerivAt (moment_EX054 h) (-variance_EX054 h s) s := by
  have hd := hasDerivAt_polyTilt (tiltData_EX054 h) s
  have ep : polyNum angHaar (fun θ => h * angCos θ)
      (fun θ => -feature_EX054 h θ) (feature_EX054 h) (fun _ => 0) (fun _ => 0) s =
      ∫ θ, feature_EX054 h θ * weight_EX054 h s θ ∂angHaar := by
    simp only [polyNum, mul_zero, add_zero, weight_EX054, mul_neg, sub_eq_add_neg]
  have en : (∫ θ, ((0 + 2 * s * 0) +
      (feature_EX054 h θ + s * 0 + s ^ 2 * 0) * -feature_EX054 h θ) *
        Real.exp (h * angCos θ + s * -feature_EX054 h θ) ∂angHaar) =
      -(∫ θ, feature_EX054 h θ ^ 2 * weight_EX054 h s θ ∂angHaar) := by
    rw [← integral_neg]
    congr 1
    funext θ
    simp only [weight_EX054, mul_neg, sub_eq_add_neg]
    ring
  have ez : (∫ θ, -feature_EX054 h θ *
        Real.exp (h * angCos θ + s * -feature_EX054 h θ) ∂angHaar) =
      -(∫ θ, feature_EX054 h θ * weight_EX054 h s θ ∂angHaar) := by
    rw [← integral_neg]
    congr 1
    funext θ
    simp only [weight_EX054, mul_neg, sub_eq_add_neg]
    ring
  rw [en, ez, ep, ← partition_eq_polyZ_EX054] at hd
  have ef : moment_EX054 h = polyTilt angHaar (fun θ => h * angCos θ)
      (fun θ => -feature_EX054 h θ) (feature_EX054 h) (fun _ => 0) (fun _ => 0) :=
    funext (moment_eq_polyTilt_EX054 h)
  rw [ef]
  convert hd using 1
  unfold variance_EX054 moment_EX054
  field_simp [(partition_pos_EX054 h s).ne']
  ring

theorem hasDerivAt_residual_EX054 (h s : ℝ) :
    HasDerivAt (residual_EX054 h) (1 + 2 * eta * variance_EX054 h s) s := by
  have hd : HasDerivAt (residual_EX054 h) (1 - 2 * eta * (-variance_EX054 h s)) s :=
    (hasDerivAt_id s).sub
      (((hasDerivAt_moment_EX054 h s).sub_const (polyCentering h)).const_mul (2 * eta))
  convert hd using 1
  ring

theorem residual_derivative_ge_one_EX054 (h s : ℝ) :
    1 ≤ deriv (residual_EX054 h) s := by
  rw [(hasDerivAt_residual_EX054 h s).deriv]
  nlinarith [mul_nonneg eta_pos.le (variance_nonneg_EX054 h s)]

theorem continuous_residual_EX054 (h : ℝ) : Continuous (residual_EX054 h) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_residual_EX054 h s).continuousAt

theorem strictMono_residual_EX054 (h : ℝ) : StrictMono (residual_EX054 h) := by
  apply strictMono_of_deriv_pos
  intro s
  have := residual_derivative_ge_one_EX054 h s
  linarith

/-- Bounded observables give a root on a finite interval, for every real field. -/
theorem existsUnique_root_EX054 (h : ℝ) : ∃! s : ℝ, residual_EX054 h s = 0 := by
  have hηpos := eta_pos
  let B := 2 * eta * (1 + |h| / 3 + |polyCentering h|) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hb (s : ℝ) :
      |2 * eta * (moment_EX054 h s - polyCentering h)| ≤ B - 1 := by
    have hm : |moment_EX054 h s - polyCentering h| ≤ 1 + |h| / 3 + |polyCentering h| :=
      (abs_sub _ _).trans (add_le_add (abs_moment_le_EX054 h s) (le_refl |polyCentering h|))
    rw [abs_mul, abs_of_pos (mul_pos two_pos eta_pos)]
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hm (mul_pos two_pos eta_pos).le]
  have hl : residual_EX054 h (-B) ≤ 0 := by
    have := (abs_le.mp (hb (-B))).1
    dsimp [residual_EX054]
    linarith
  have hr : 0 ≤ residual_EX054 h B := by
    have := (abs_le.mp (hb B)).2
    dsimp [residual_EX054]
    linarith
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by linarith : -B ≤ B)
    (continuous_residual_EX054 h).continuousOn ⟨hl, hr⟩
  refine ⟨s, hs, fun y hy => ?_⟩
  exact (strictMono_residual_EX054 h).injective (hy.trans hs.symm)

/-- Selection is made only after global existence and uniqueness are proved. -/
noncomputable def root_EX054 (h : ℝ) : ℝ := (existsUnique_root_EX054 h).exists.choose

theorem root_residual_EX054 (h : ℝ) : residual_EX054 h (root_EX054 h) = 0 :=
  (existsUnique_root_EX054 h).exists.choose_spec

theorem root_equation_EX054 (h : ℝ) :
    root_EX054 h = 2 * eta * (moment_EX054 h (root_EX054 h) - polyCentering h) := by
  have := root_residual_EX054 h
  dsimp [residual_EX054] at this
  linarith

theorem root_unique_EX054 (h s : ℝ)
    (hs : s = 2 * eta * (moment_EX054 h s - polyCentering h)) : s = root_EX054 h := by
  apply (strictMono_residual_EX054 h).injective
  rw [root_residual_EX054]
  dsimp [residual_EX054]
  linarith

theorem abs_root_le_residual_zero_EX054 (h : ℝ) :
    |root_EX054 h| ≤ |residual_EX054 h 0| := by
  have hd : Differentiable ℝ (residual_EX054 h) :=
    fun s => (hasDerivAt_residual_EX054 h s).differentiableAt
  by_cases hs : 0 ≤ root_EX054 h
  · have hb := mul_sub_le_image_sub_of_le_deriv hd (residual_derivative_ge_one_EX054 h) hs
    rw [root_residual_EX054] at hb
    rw [abs_of_nonneg hs]
    linarith [neg_le_abs (residual_EX054 h 0)]
  · have hs' : root_EX054 h ≤ 0 := le_of_not_ge hs
    have hb := mul_sub_le_image_sub_of_le_deriv hd (residual_derivative_ge_one_EX054 h) hs'
    rw [root_residual_EX054] at hb
    rw [abs_of_nonpos hs']
    linarith [le_abs_self (residual_EX054 h 0)]

theorem moment_zero_EX054 (h : ℝ) :
    moment_EX054 h 0 = DGPS.Examples.SixthOrderCentering.vonMisesCentering h := by
  have ep : partition_EX054 h 0 = besselI 0 h := by
    simp only [partition_EX054, weight_EX054, zero_mul, sub_zero, besselI, angMode_zero, mul_one]
  rw [moment_eq_integral_EX054]
  simp only [density_EX054, weight_EX054, zero_mul, sub_zero, ep, feature_EX054,
    DGPS.Examples.SixthOrderCentering.vonMisesCentering, besselDensity]

theorem abs_root_le_sixth_EX054 :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ h : ℝ, |h| ≤ δ → |root_EX054 h| ≤ C * h ^ 6 := by
  have hηpos := eta_pos
  obtain ⟨C, δ, hC, hδ, hTaylor⟩ := DGPS.Examples.sixth_order_centering_cancellation.2
  refine ⟨2 * eta * (C + 1 / 9216), min δ 1, by positivity, lt_min hδ one_pos,
    fun h hh => ?_⟩
  have hm := (hTaylor h (hh.trans (min_le_left _ _))).2.2
  have h1 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  have h2 : h ^ 2 ≤ 1 := by nlinarith [abs_nonneg h, sq_abs h]
  have h8le : h ^ 8 ≤ h ^ 6 := by
    have : h ^ 8 = h ^ 6 * h ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) h2
  have hcent : |DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h| ≤
      (C + 1 / 9216) * h ^ 6 := by
    have ht := abs_add_le
      (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - (-h ^ 2 / 24 + h ^ 6 / 9216))
      (h ^ 6 / 9216)
    have e : DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h =
        (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - (-h ^ 2 / 24 + h ^ 6 / 9216)) +
          h ^ 6 / 9216 := by unfold polyCentering; ring
    rw [e]
    rw [abs_of_nonneg (by positivity : 0 ≤ h ^ 6 / 9216)] at ht
    nlinarith [mul_le_mul_of_nonneg_left h8le hC.le]
  apply (abs_root_le_residual_zero_EX054 h).trans
  rw [residual_EX054, zero_sub, abs_neg, abs_mul, moment_zero_EX054,
    abs_of_pos (mul_pos two_pos eta_pos)]
  nlinarith [mul_le_mul_of_nonneg_left hcent (by positivity : 0 ≤ 2 * eta)]

theorem feature_reflection_EX054 (h : ℝ) (θ : AngCircle) :
    feature_EX054 h (-θ) = feature_EX054 h θ := by
  have hn (n : ℕ) : angMode n (-θ) = angMode n θ := by
    induction θ using QuotientAddGroup.induction_on with
    | H t =>
      change angMode n ((-t : ℝ) : AngCircle) = angMode n ((t : ℝ) : AngCircle)
      simp only [angMode_coe, mul_neg, Real.cos_neg]
  simp only [feature_EX054, angCos, hn]

/-- Reflection is exact for every member of the family, not only its equilibrium. -/
theorem density_reflection_EX054 (h s : ℝ) (θ : AngCircle) :
    density_EX054 h s (-θ) = density_EX054 h s θ := by
  have hc : angCos (-θ) = angCos θ := by
    induction θ using QuotientAddGroup.induction_on with
    | H t =>
      change angCos ((-t : ℝ) : AngCircle) = angCos ((t : ℝ) : AngCircle)
      simp only [angCos, angMode_coe, mul_neg, Real.cos_neg]
  simp only [density_EX054, weight_EX054, feature_reflection_EX054, hc]

theorem feature_halfTurn_EX054 (h : ℝ) (θ : AngCircle) :
    feature_EX054 (-h) (θ + ((π : ℝ) : AngCircle)) = feature_EX054 h θ := by
  simp only [feature_EX054, angMode_add_pi]
  norm_num
  ring

theorem weight_halfTurn_EX054 (h s : ℝ) (θ : AngCircle) :
    weight_EX054 (-h) s (θ + ((π : ℝ) : AngCircle)) = weight_EX054 h s θ := by
  simp only [weight_EX054, feature_halfTurn_EX054, angCos_add_pi, neg_mul_neg]

theorem partition_even_EX054 (h s : ℝ) :
    partition_EX054 (-h) s = partition_EX054 h s := by
  have ht := integral_add_right_eq_self (μ := angHaar) (weight_EX054 (-h) s)
    ((π : ℝ) : AngCircle)
  simp_rw [weight_halfTurn_EX054] at ht
  exact ht.symm

theorem moment_even_EX054 (h s : ℝ) : moment_EX054 (-h) s = moment_EX054 h s := by
  have ht := integral_add_right_eq_self (μ := angHaar)
    (fun θ => feature_EX054 (-h) θ * weight_EX054 (-h) s θ) ((π : ℝ) : AngCircle)
  simp_rw [feature_halfTurn_EX054, weight_halfTurn_EX054] at ht
  unfold moment_EX054
  rw [partition_even_EX054, ← ht]

theorem residual_even_EX054 (h s : ℝ) : residual_EX054 (-h) s = residual_EX054 h s := by
  simp only [residual_EX054, moment_even_EX054, polyCentering, neg_sq]

theorem root_even_EX054 (h : ℝ) : root_EX054 (-h) = root_EX054 h := by
  apply (strictMono_residual_EX054 h).injective
  rw [root_residual_EX054, ← residual_even_EX054 h, root_residual_EX054]

theorem equilibrium_halfTurn_EX054 (h : ℝ) (θ : AngCircle) :
    density_EX054 (-h) (root_EX054 (-h)) (θ + ((π : ℝ) : AngCircle)) =
      density_EX054 h (root_EX054 h) θ := by
  simp only [density_EX054, root_even_EX054, weight_halfTurn_EX054, partition_even_EX054]

theorem partition_zero_EX054 (h : ℝ) : partition_EX054 h 0 = besselI 0 h := by
  simp only [partition_EX054, weight_EX054, zero_mul, sub_zero, besselI, angMode_zero, mul_one]

theorem hasDerivAt_log_partition_EX054 (h s : ℝ) :
    HasDerivAt (fun t => Real.log (partition_EX054 h t)) (-moment_EX054 h s) s := by
  have hd := hasDerivAt_log_polyZ (tiltData_EX054 h) s
  have en : (∫ θ, -feature_EX054 h θ *
        Real.exp (h * angCos θ + s * -feature_EX054 h θ) ∂angHaar) =
      -(∫ θ, feature_EX054 h θ * weight_EX054 h s θ ∂angHaar) := by
    rw [← integral_neg]
    congr 1
    funext θ
    simp only [weight_EX054, mul_neg, sub_eq_add_neg]
    ring
  rw [en] at hd
  simpa only [partition_eq_polyZ_EX054, moment_EX054, neg_div] using hd

theorem abs_log_partition_sub_EX054 (h s : ℝ) :
    |Real.log (partition_EX054 h s) - Real.log (partition_EX054 h 0)| ≤
      (1 + |h| / 3) * |s| := by
  have hf (t : ℝ) := hasDerivAt_log_partition_EX054 h t
  have hb : ∀ t ∈ (Set.univ : Set ℝ),
      ‖deriv (fun u => Real.log (partition_EX054 h u)) t‖ ≤ 1 + |h| / 3 := by
    intro t _
    rw [(hf t).deriv, Real.norm_eq_abs, abs_neg]
    exact abs_moment_le_EX054 h t
  have ht := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => (hf t).differentiableAt)
    hb convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ s)
  simpa only [Real.norm_eq_abs, sub_zero] using ht

/-- The logarithmic ratio of the actual normalized density to the von Mises reference. -/
noncomputable def logRatio_EX054 (h s : ℝ) (θ : AngCircle) : ℝ :=
  Real.log (density_EX054 h s θ / besselDensity h θ)

theorem logRatio_eq_EX054 (h s : ℝ) (θ : AngCircle) :
    logRatio_EX054 h s θ = -s * feature_EX054 h θ -
      (Real.log (partition_EX054 h s) - Real.log (partition_EX054 h 0)) := by
  have hd := density_pos_EX054 h s θ
  have hb : 0 < besselDensity h θ := div_pos (Real.exp_pos _) (besselI_zero_pos h)
  rw [logRatio_EX054, Real.log_div hd.ne' hb.ne']
  unfold density_EX054 besselDensity weight_EX054
  rw [Real.log_div (Real.exp_pos _).ne' (partition_pos_EX054 h s).ne',
    Real.log_div (Real.exp_pos _).ne' (besselI_zero_pos h).ne',
    Real.log_exp, Real.log_exp, partition_zero_EX054]
  ring

theorem abs_logRatio_le_EX054 (h s : ℝ) (θ : AngCircle) :
    |logRatio_EX054 h s θ| ≤ 2 * (1 + |h| / 3) * |s| := by
  rw [logRatio_eq_EX054]
  calc _ ≤ |-s * feature_EX054 h θ| +
      |Real.log (partition_EX054 h s) - Real.log (partition_EX054 h 0)| := abs_sub _ _
    _ ≤ |s| * (1 + |h| / 3) + (1 + |h| / 3) * |s| := by
      rw [abs_mul, abs_neg]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_feature_le_EX054 h θ) (abs_nonneg _))
        (abs_log_partition_sub_EX054 h s)
    _ = _ := by ring

theorem abs_iteratedDeriv_cos_EX054 (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n Real.cos θ| ≤ 1 := by
  have hb : ∀ n : ℕ, (∀ θ : ℝ, |iteratedDeriv n Real.sin θ| ≤ 1) ∧
      (∀ θ : ℝ, |iteratedDeriv n Real.cos θ| ≤ 1) := by
    intro n
    induction n with
    | zero => exact ⟨Real.abs_sin_le_one, Real.abs_cos_le_one⟩
    | succ n ih =>
      constructor
      · intro x
        simpa only [Nat.succ_eq_add_one, Real.iteratedDeriv_add_one_sin] using ih.2 x
      · intro x
        simpa only [Nat.succ_eq_add_one, Real.iteratedDeriv_add_one_cos, Pi.neg_apply, abs_neg]
          using ih.1 x
  exact (hb n).2 θ

theorem abs_iteratedDeriv_feature_EX054 (h : ℝ) (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n (fun t : ℝ => feature_EX054 h (t : AngCircle)) θ| ≤
      (2 : ℝ) ^ n + |h| / 3 := by
  have ef : (fun t : ℝ => feature_EX054 h (t : AngCircle)) =
      fun t => Real.cos (2 * t) - h / 3 * Real.cos t := by
    funext t
    simp only [feature_EX054, angCos, angMode_coe, Nat.cast_ofNat, Nat.cast_one, one_mul]
  rw [ef, iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul Real.contDiff_cos]
  have hc := abs_iteratedDeriv_cos_EX054 n (2 * θ)
  have hc' := abs_iteratedDeriv_cos_EX054 n θ
  calc _ ≤ |(2 : ℝ) ^ n * iteratedDeriv n Real.cos (2 * θ)| +
      |h / 3 * iteratedDeriv n Real.cos θ| := abs_sub _ _
    _ ≤ (2 : ℝ) ^ n + |h| / 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n),
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 ^ n),
        mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ |h| / 3)]

theorem abs_iteratedDeriv_logRatio_EX054 (h s : ℝ) (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    |iteratedDeriv n (fun t : ℝ => logRatio_EX054 h s (t : AngCircle)) θ| ≤
      |s| * ((2 : ℝ) ^ n + |h| / 3) := by
  have ef : (fun t : ℝ => logRatio_EX054 h s (t : AngCircle)) =
      fun t : ℝ => -(Real.log (partition_EX054 h s) - Real.log (partition_EX054 h 0)) +
        (-s) * feature_EX054 h (t : AngCircle) := by
    funext t
    rw [logRatio_eq_EX054]
    ring
  rw [ef, iteratedDeriv_const_add hn, iteratedDeriv_const_mul_field, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (abs_iteratedDeriv_feature_EX054 h n θ) (abs_nonneg _)

/-- Uniform bounds for all angular derivatives up to each fixed order. -/
theorem logRatio_fixed_Ck_EX054 (k : ℕ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      ∀ j : ℕ, j ≤ k → ∀ θ : ℝ,
        |iteratedDeriv j (fun t : ℝ => logRatio_EX054 h (root_EX054 h) (t : AngCircle)) θ| ≤
          C * h ^ 6 := by
  obtain ⟨C, δ, hC, hδ, hroot⟩ := abs_root_le_sixth_EX054
  refine ⟨(4 + (2 : ℝ) ^ k) * C, min δ 1, by positivity, lt_min hδ one_pos,
    fun h hh j hj θ => ?_⟩
  have hroot' := hroot h (hh.trans (min_le_left _ _))
  have h1 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  have hk : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  by_cases hj0 : j = 0
  · subst j
    simp only [iteratedDeriv_zero]
    have hc : 2 * (1 + |h| / 3) ≤ 4 + (2 : ℝ) ^ k := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
    calc _ ≤ 2 * (1 + |h| / 3) * |root_EX054 h| :=
          abs_logRatio_le_EX054 h (root_EX054 h) (θ : AngCircle)
      _ ≤ 2 * (1 + |h| / 3) * (C * h ^ 6) :=
          mul_le_mul_of_nonneg_left hroot' (by positivity)
      _ ≤ (4 + (2 : ℝ) ^ k) * (C * h ^ 6) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  · have hc : (2 : ℝ) ^ j + |h| / 3 ≤ 4 + (2 : ℝ) ^ k := by linarith
    calc _ ≤ |root_EX054 h| * ((2 : ℝ) ^ j + |h| / 3) :=
          abs_iteratedDeriv_logRatio_EX054 h (root_EX054 h) j (Nat.pos_of_ne_zero hj0) θ
      _ = ((2 : ℝ) ^ j + |h| / 3) * |root_EX054 h| := by ring
      _ ≤ ((2 : ℝ) ^ j + |h| / 3) * (C * h ^ 6) :=
          mul_le_mul_of_nonneg_left hroot' (by positivity)
      _ ≤ (4 + (2 : ℝ) ^ k) * (C * h ^ 6) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring

theorem variance_origin_EX054 : variance_EX054 0 0 = 1 / 2 := by
  have hw : weight_EX054 0 0 = fun _ => 1 := by funext θ; simp [weight_EX054]
  have hz : partition_EX054 0 0 = 1 := by simp [partition_EX054, hw]
  have hm : moment_EX054 0 0 = 0 := by
    rw [moment_zero_EX054, DGPS.Examples.SixthOrderCentering.vonMisesCentering_eq,
      DGPS.Examples.SixthOrderCentering.besselI_two_eq, besselI1Over_zero]
    have hI : besselI 0 0 = 1 := by simp [besselI, angMode_zero]
    rw [hI]
    norm_num
  have he (θ : AngCircle) : feature_EX054 0 θ ^ 2 =
      4 * angCos θ ^ 4 - 4 * angCos θ ^ 2 + 1 := by
    induction θ using QuotientAddGroup.induction_on with
    | H t =>
      simp only [feature_EX054, zero_div, zero_mul, sub_zero, angMode_coe, angCos,
        Nat.cast_ofNat, Nat.cast_one, one_mul]
      rw [Real.cos_two_mul]
      ring
  have hi (n : ℕ) : Integrable (fun θ => angCos θ ^ n) angHaar :=
    ((continuous_angMode 1).pow n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc2 : cosAvg 2 = 1 / 2 := by simpa [cosAvg_zero] using cosAvg_add_two 0
  have hc4 : cosAvg 4 = 3 / 8 := by
    have ht := cosAvg_add_two 2
    rw [hc2] at ht
    norm_num at ht ⊢
    exact ht
  unfold variance_EX054
  rw [hw, hz, hm]
  simp only [mul_one, div_one, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
  simp_rw [he]
  rw [integral_add (f := fun θ => 4 * angCos θ ^ 4 - 4 * angCos θ ^ 2)
      (g := fun _ => (1 : ℝ))
      ((hi 4).const_mul 4 |>.sub ((hi 2).const_mul 4)) (integrable_const 1),
    integral_sub (f := fun θ => 4 * angCos θ ^ 4) (g := fun θ => 4 * angCos θ ^ 2)
      ((hi 4).const_mul 4) ((hi 2).const_mul 4),
    integral_const_mul, integral_const_mul]
  have hmass : (∫ _ : AngCircle, (1 : ℝ) ∂angHaar) = 1 := by simp
  rw [hmass]
  change 4 * cosAvg 4 - 4 * cosAvg 2 + 1 = 1 / 2
  rw [hc4, hc2]
  norm_num

theorem residual_derivative_origin_EX054 :
    deriv (residual_EX054 0) 0 = 1 + eta := by
  rw [(hasDerivAt_residual_EX054 0 0).deriv, variance_origin_EX054]
  ring

/-! ### Repeated differentiation of actual polynomial tilted expectations -/

noncomputable def next0_EX054 (a1 g0 g1 : AngCircle → ℝ) (θ : AngCircle) : ℝ :=
  g1 θ + g0 θ * a1 θ
noncomputable def next1_EX054 (a1 g1 g2 : AngCircle → ℝ) (θ : AngCircle) : ℝ :=
  2 * g2 θ + g1 θ * a1 θ
noncomputable def next2_EX054 (a1 g2 : AngCircle → ℝ) (θ : AngCircle) : ℝ :=
  g2 θ * a1 θ

theorem nextData_EX054 {a0 a1 g0 g1 g2 : AngCircle → ℝ}
    (H : TiltData angHaar a0 a1 g0 g1 g2) :
    TiltData angHaar a0 a1 (next0_EX054 a1 g0 g1) (next1_EX054 a1 g1 g2)
      (next2_EX054 a1 g2) :=
  ⟨H.m0, H.m1, H.n1.add (H.n0.mul H.m1),
    (measurable_const.mul H.n2).add (H.n1.mul H.m1), H.n2.mul H.m1,
    H.b0, H.b1, H.c1.add (H.c0.mul H.b1),
    ((AEBdd.const 2).mul H.c2).add (H.c1.mul H.b1), H.c2.mul H.b1⟩

theorem slopeData_EX054 {a0 a1 g0 g1 g2 : AngCircle → ℝ}
    (H : TiltData angHaar a0 a1 g0 g1 g2) :
    TiltData angHaar a0 a1 a1 (fun _ => 0) (fun _ => 0) :=
  ⟨H.m0, H.m1, H.m1, measurable_const, measurable_const,
    H.b0, H.b1, H.b1, AEBdd.const 0, AEBdd.const 0⟩

noncomputable def polySlope_EX054 (a0 a1 g0 g1 g2 : AngCircle → ℝ) (t : ℝ) : ℝ :=
  polyTilt angHaar a0 a1 (next0_EX054 a1 g0 g1) (next1_EX054 a1 g1 g2)
      (next2_EX054 a1 g2) t -
    polyTilt angHaar a0 a1 g0 g1 g2 t *
      polyTilt angHaar a0 a1 a1 (fun _ => 0) (fun _ => 0) t

theorem hasDerivAt_polyTilt_next_EX054 {a0 a1 g0 g1 g2 : AngCircle → ℝ}
    (H : TiltData angHaar a0 a1 g0 g1 g2) (t : ℝ) :
    HasDerivAt (polyTilt angHaar a0 a1 g0 g1 g2)
      (polySlope_EX054 a0 a1 g0 g1 g2 t) t := by
  have hd := hasDerivAt_polyTilt H t
  have en : polyNum angHaar a0 a1 (next0_EX054 a1 g0 g1)
      (next1_EX054 a1 g1 g2) (next2_EX054 a1 g2) t =
      ∫ θ, ((g1 θ + 2 * t * g2 θ) +
        (g0 θ + t * g1 θ + t ^ 2 * g2 θ) * a1 θ) *
        Real.exp (a0 θ + t * a1 θ) ∂angHaar := by
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by
      simp only [next0_EX054, next1_EX054, next2_EX054]
      ring
  convert hd using 1
  have eb : polyNum angHaar a0 a1 a1 (fun _ => 0) (fun _ => 0) t =
      ∫ θ, a1 θ * Real.exp (a0 θ + t * a1 θ) ∂angHaar := by
    simp only [polyNum, mul_zero, add_zero]
  unfold polySlope_EX054 polyTilt
  rw [en, eb]
  let J := ∫ θ, ((g1 θ + 2 * t * g2 θ) +
    (g0 θ + t * g1 θ + t ^ 2 * g2 θ) * a1 θ) * Real.exp (a0 θ + t * a1 θ) ∂angHaar
  let U := ∫ θ, a1 θ * Real.exp (a0 θ + t * a1 θ) ∂angHaar
  let N := polyNum angHaar a0 a1 g0 g1 g2 t
  let Z := polyZ angHaar a0 a1 t
  change J / Z - (N / Z) * (U / Z) = (J * Z - N * U) / Z ^ 2
  have hz : Z ≠ 0 := (polyZ_pos a0 a1 H.m0 H.m1 H.b0 H.b1 t).ne'
  field_simp [hz]

theorem continuous_polyTilt_EX054 {a0 a1 g0 g1 g2 : AngCircle → ℝ}
    (H : TiltData angHaar a0 a1 g0 g1 g2) :
    Continuous (polyTilt angHaar a0 a1 g0 g1 g2) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_polyTilt H t).continuousAt

theorem contDiff_one_polyTilt_EX054 {a0 a1 g0 g1 g2 : AngCircle → ℝ}
    (H : TiltData angHaar a0 a1 g0 g1 g2) :
    ContDiff ℝ 1 (polyTilt angHaar a0 a1 g0 g1 g2) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_polyTilt H t).differentiableAt, ?_⟩
  have he : deriv (polyTilt angHaar a0 a1 g0 g1 g2) =
      polySlope_EX054 a0 a1 g0 g1 g2 :=
    funext fun t => (hasDerivAt_polyTilt_next_EX054 H t).deriv
  rw [he]
  exact (continuous_polyTilt_EX054 (nextData_EX054 H)).sub
    ((continuous_polyTilt_EX054 H).mul (continuous_polyTilt_EX054 (slopeData_EX054 H)))

theorem contDiff_two_polyTilt_EX054 {a0 a1 g0 g1 g2 : AngCircle → ℝ}
    (H : TiltData angHaar a0 a1 g0 g1 g2) :
    ContDiff ℝ 2 (polyTilt angHaar a0 a1 g0 g1 g2) := by
  have he : deriv (polyTilt angHaar a0 a1 g0 g1 g2) =
      polySlope_EX054 a0 a1 g0 g1 g2 :=
    funext fun t => (hasDerivAt_polyTilt_next_EX054 H t).deriv
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (hasDerivAt_polyTilt H t).differentiableAt, by simp, ?_⟩
  rw [he]
  exact (contDiff_one_polyTilt_EX054 (nextData_EX054 H)).sub
    ((contDiff_one_polyTilt_EX054 H).mul (contDiff_one_polyTilt_EX054 (slopeData_EX054 H)))

theorem aebdd_continuous_EX054 {f : AngCircle → ℝ} (hf : Continuous f) : AEBdd angHaar f := by
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hf.abs.continuousOn
  exact ⟨M, Eventually.of_forall fun θ => hM ⟨θ, Set.mem_univ _, rfl⟩⟩

theorem continuousData_EX054 {a0 a1 g0 g1 g2 : AngCircle → ℝ}
    (ha0 : Continuous a0) (ha1 : Continuous a1)
    (hg0 : Continuous g0) (hg1 : Continuous g1) (hg2 : Continuous g2) :
    TiltData angHaar a0 a1 g0 g1 g2 :=
  ⟨ha0.measurable, ha1.measurable, hg0.measurable, hg1.measurable, hg2.measurable,
    aebdd_continuous_EX054 ha0, aebdd_continuous_EX054 ha1,
    aebdd_continuous_EX054 hg0, aebdd_continuous_EX054 hg1, aebdd_continuous_EX054 hg2⟩

noncomputable def fieldMean_EX054 : ℝ → ℝ :=
  polyTilt angHaar (fun _ => 0) angCos (angMode 2) (fun θ => -angCos θ / 3) (fun _ => 0)

noncomputable def fieldSecond_EX054 : ℝ → ℝ :=
  polyTilt angHaar (fun _ => 0) angCos (fun θ => angMode 2 θ ^ 2)
    (fun θ => -(2 / 3 : ℝ) * angMode 2 θ * angCos θ) (fun θ => angCos θ ^ 2 / 9)

theorem fieldMeanData_EX054 :
    TiltData angHaar (fun _ => 0) angCos (angMode 2) (fun θ => -angCos θ / 3) (fun _ => 0) := by
  have hc := continuous_angMode 1
  have hp := continuous_angMode 2
  apply continuousData_EX054 <;> fun_prop

theorem fieldSecondData_EX054 :
    TiltData angHaar (fun _ => 0) angCos (fun θ => angMode 2 θ ^ 2)
      (fun θ => -(2 / 3 : ℝ) * angMode 2 θ * angCos θ) (fun θ => angCos θ ^ 2 / 9) := by
  have hc := continuous_angMode 1
  have hp := continuous_angMode 2
  apply continuousData_EX054 <;> fun_prop

theorem fieldMean_eq_EX054 (h : ℝ) : moment_EX054 h 0 = fieldMean_EX054 h := by
  unfold moment_EX054 fieldMean_EX054 polyTilt polyNum polyZ partition_EX054
  congr 1
  all_goals
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by
      simp only [feature_EX054, weight_EX054, zero_mul, sub_zero, zero_add, mul_zero, add_zero]
      <;> ring

theorem variance_zero_eq_EX054 (h : ℝ) :
    variance_EX054 h 0 = fieldSecond_EX054 h - fieldMean_EX054 h ^ 2 := by
  unfold variance_EX054
  rw [fieldMean_eq_EX054]
  congr 1
  unfold fieldSecond_EX054 polyTilt polyNum polyZ partition_EX054
  congr 1
  all_goals
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by
      simp only [feature_EX054, weight_EX054, zero_mul, sub_zero, zero_add]
      <;> ring

theorem contDiff_variance_zero_EX054 :
    ContDiff ℝ 2 (fun h => variance_EX054 h 0) := by
  have he : (fun h => variance_EX054 h 0) =
      fun h => fieldSecond_EX054 h - fieldMean_EX054 h ^ 2 := funext variance_zero_eq_EX054
  rw [he]
  exact (contDiff_two_polyTilt_EX054 fieldSecondData_EX054).sub
    ((contDiff_two_polyTilt_EX054 fieldMeanData_EX054).pow 2)

theorem variance_even_EX054 (h s : ℝ) : variance_EX054 (-h) s = variance_EX054 h s := by
  have ht := integral_add_right_eq_self (μ := angHaar)
    (fun θ => feature_EX054 (-h) θ ^ 2 * weight_EX054 (-h) s θ) ((π : ℝ) : AngCircle)
  simp_rw [feature_halfTurn_EX054, weight_halfTurn_EX054] at ht
  unfold variance_EX054
  rw [partition_even_EX054, moment_even_EX054, ← ht]

/-- A proved scalar Taylor adapter: an even C² function has a uniform quadratic remainder. -/
theorem even_Ctwo_quadratic_EX054 {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (heven : ∀ t, f (-t) = f t) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, |t| ≤ 1 → |f t - f 0| ≤ K * t ^ 2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  have hd1 : Differentiable ℝ (deriv f) := hc1.differentiable (by norm_num)
  have hc2 : Continuous (deriv (deriv f)) := (contDiff_one_iff_deriv.mp hc1).2
  have hzero : deriv f 0 = 0 := by
    have hn := (hd (-(0 : ℝ))).hasDerivAt.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simp only [neg_zero] at hn
    change HasDerivAt (fun t : ℝ => f (-t)) (deriv f 0 * -1) 0 at hn
    have he : (fun t => f (-t)) = f := funext heven
    rw [he] at hn
    have hu := hn.unique (hd 0).hasDerivAt
    linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc2.abs.continuousOn
  let K := |M| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : ∀ x ∈ Icc (-1 : ℝ) 1, ‖deriv (deriv f) x‖ ≤ K := by
    intro x hx
    have hm := hM ⟨x, hx, rfl⟩
    rw [Real.norm_eq_abs]
    dsimp [K]
    linarith [le_abs_self M]
  have hfirst (t : ℝ) (ht : |t| ≤ 1) : |deriv f t| ≤ K * |t| := by
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x ∈ Icc (-1 : ℝ) 1) => hd1 x) hb (convex_Icc _ _)
      (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) (abs_le.mp ht)
    simpa only [Real.norm_eq_abs, hzero, sub_zero] using hm
  refine ⟨K, hK, fun t ht => ?_⟩
  have hbound : ∀ x ∈ Icc (-|t|) |t|, ‖deriv f x‖ ≤ K * |t| := by
    intro x hx
    have hxt : |x| ≤ |t| := abs_le.mpr hx
    rw [Real.norm_eq_abs]
    exact (hfirst x (hxt.trans ht)).trans (mul_le_mul_of_nonneg_left hxt hK.le)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Icc (-|t|) |t|) => hd x) hbound (convex_Icc _ _)
    (by exact ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩)
    (by exact ⟨neg_abs_le t, le_abs_self t⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hm
  nlinarith [sq_abs t]

theorem variance_zero_quadratic_EX054 :
    ∃ K : ℝ, 0 < K ∧ ∀ h : ℝ, |h| ≤ 1 →
      |variance_EX054 h 0 - 1 / 2| ≤ K * h ^ 2 := by
  obtain ⟨K, hK, hb⟩ := even_Ctwo_quadratic_EX054 contDiff_variance_zero_EX054
    (fun h => variance_even_EX054 h 0)
  exact ⟨K, hK, fun h hh => by simpa only [variance_origin_EX054] using hb h hh⟩

theorem abs_deriv_constant_tilt_EX054 {a0 a1 g : AngCircle → ℝ}
    (H : TiltData angHaar a0 a1 g (fun _ => 0) (fun _ => 0))
    {C B : ℝ} (hg : ∀ θ, |g θ| ≤ C) (ha : ∀ θ, |a1 θ| ≤ B) (s : ℝ) :
    |deriv (polyTilt angHaar a0 a1 g (fun _ => 0) (fun _ => 0)) s| ≤ 2 * C * B := by
  rw [(hasDerivAt_polyTilt H s).deriv]
  have hb := abs_deriv_polyTilt_le H s (c := C) (d := 0) (B := B)
    (Eventually.of_forall fun θ => by
      simpa only [mul_zero, add_zero, abs_zero] using And.intro (hg θ) (And.intro le_rfl (ha θ)))
  simpa only [zero_add] using hb

noncomputable def second_EX054 (h : ℝ) : ℝ → ℝ :=
  polyTilt angHaar (fun θ => h * angCos θ) (fun θ => -feature_EX054 h θ)
    (fun θ => feature_EX054 h θ ^ 2) (fun _ => 0) (fun _ => 0)

theorem secondData_EX054 (h : ℝ) :
    TiltData angHaar (fun θ => h * angCos θ) (fun θ => -feature_EX054 h θ)
      (fun θ => feature_EX054 h θ ^ 2) (fun _ => 0) (fun _ => 0) := by
  have hc := continuous_angMode 1
  have hp := continuous_feature_EX054 h
  apply continuousData_EX054 <;> fun_prop

theorem variance_eq_second_EX054 (h s : ℝ) :
    variance_EX054 h s = second_EX054 h s - moment_EX054 h s ^ 2 := by
  simp only [variance_EX054, second_EX054, polyTilt, polyNum, mul_zero, add_zero,
    ← partition_eq_polyZ_EX054, weight_EX054, mul_neg, sub_eq_add_neg]

theorem abs_deriv_variance_EX054 (h s : ℝ) :
    |deriv (variance_EX054 h) s| ≤ 6 * (1 + |h| / 3) ^ 3 := by
  let M := 1 + |h| / 3
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (θ : AngCircle) : |feature_EX054 h θ| ≤ M := abs_feature_le_EX054 h θ
  have ha (θ : AngCircle) : |-feature_EX054 h θ| ≤ M := by simpa only [abs_neg] using hb θ
  have hs := abs_deriv_constant_tilt_EX054 (secondData_EX054 h)
    (fun θ => by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hb θ) 2) ha s
  have hm := abs_deriv_constant_tilt_EX054 (tiltData_EX054 h) hb ha s
  have he : variance_EX054 h = fun t => second_EX054 h t - moment_EX054 h t ^ 2 :=
    funext (variance_eq_second_EX054 h)
  have hdsecond : Differentiable ℝ (second_EX054 h) :=
    fun t => (hasDerivAt_polyTilt (secondData_EX054 h) t).differentiableAt
  have hdmean : Differentiable ℝ (moment_EX054 h) :=
    fun t => (hasDerivAt_moment_EX054 h t).differentiableAt
  have hed : moment_EX054 h = polyTilt angHaar (fun θ => h * angCos θ)
      (fun θ => -feature_EX054 h θ) (feature_EX054 h) (fun _ => 0) (fun _ => 0) :=
    funext (moment_eq_polyTilt_EX054 h)
  rw [← hed] at hm
  have hd := ((hdsecond s).hasDerivAt).sub ((hdmean s).hasDerivAt.pow 2)
  rw [he]
  change |deriv (second_EX054 h - moment_EX054 h ^ 2) s| ≤ _
  rw [hd.deriv]
  have hmoment : |moment_EX054 h s| ≤ M := abs_moment_le_EX054 h s
  change |deriv (second_EX054 h) s -
    2 * moment_EX054 h s ^ (2 - 1) * deriv (moment_EX054 h) s| ≤ 6 * M ^ 3
  norm_num only [show 2 - 1 = 1 by omega, pow_one]
  calc _ ≤ |deriv (second_EX054 h) s| +
      |2 * moment_EX054 h s * deriv (moment_EX054 h) s| := abs_sub _ _
    _ ≤ 2 * M ^ 2 * M + 2 * M * (2 * M * M) := by
      refine add_le_add hs ?_
      rw [abs_mul, abs_mul, abs_of_pos two_pos]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hmoment two_pos.le) hm
        (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem variance_lipschitz_EX054 (h s : ℝ) :
    |variance_EX054 h s - variance_EX054 h 0| ≤ 6 * (1 + |h| / 3) ^ 3 * |s| := by
  have he : variance_EX054 h = fun t => second_EX054 h t - moment_EX054 h t ^ 2 :=
    funext (variance_eq_second_EX054 h)
  have hd : Differentiable ℝ (variance_EX054 h) := by
    rw [he]
    have hs : Differentiable ℝ (second_EX054 h) :=
      fun t => (hasDerivAt_polyTilt (secondData_EX054 h) t).differentiableAt
    have hm : Differentiable ℝ (moment_EX054 h) :=
      fun t => (hasDerivAt_moment_EX054 h t).differentiableAt
    exact hs.sub (hm.pow 2)
  have hb : ∀ t ∈ (Set.univ : Set ℝ),
      ‖deriv (variance_EX054 h) t‖ ≤ 6 * (1 + |h| / 3) ^ 3 := by
    intro t _
    simpa only [Real.norm_eq_abs] using abs_deriv_variance_EX054 h t
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le (fun t (_ : t ∈ (Set.univ : Set ℝ)) => hd t)
    hb convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ s)
  simpa only [Real.norm_eq_abs, sub_zero] using hm

theorem variance_quadratic_linear_EX054 :
    ∃ K : ℝ, 0 < K ∧ ∀ h s : ℝ, |h| ≤ 1 →
      |variance_EX054 h s - 1 / 2| ≤ K * (h ^ 2 + |s|) := by
  obtain ⟨K, hK, hzero⟩ := variance_zero_quadratic_EX054
  refine ⟨K + 48, by positivity, fun h s hh => ?_⟩
  have hM : 1 + |h| / 3 ≤ 2 := by linarith
  have hcube : (1 + |h| / 3) ^ 3 ≤ 8 := by
    have ht := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |h| / 3) hM 3
    norm_num at ht
    exact ht
  have ht := abs_add_le (variance_EX054 h s - variance_EX054 h 0)
    (variance_EX054 h 0 - 1 / 2)
  have he : variance_EX054 h s - 1 / 2 =
      (variance_EX054 h s - variance_EX054 h 0) + (variance_EX054 h 0 - 1 / 2) := by ring
  rw [he]
  have hs := variance_lipschitz_EX054 h s
  have hz := hzero h hh
  have hb := mul_le_mul_of_nonneg_right hcube (abs_nonneg s)
  nlinarith [sq_nonneg h, mul_nonneg hK.le (abs_nonneg s)]

theorem residual_linearization_EX054 {K h s : ℝ} (hK : 0 ≤ K) (hh : |h| ≤ 1)
    (hV : ∀ h s : ℝ, |h| ≤ 1 → |variance_EX054 h s - 1 / 2| ≤ K * (h ^ 2 + |s|)) :
    |residual_EX054 h s - residual_EX054 h 0 - (1 + eta) * s| ≤
      2 * eta * K * (h ^ 2 + |s|) * |s| := by
  let f : ℝ → ℝ := fun t => residual_EX054 h t - (1 + eta) * t
  have hd (t : ℝ) : HasDerivAt f (2 * eta * (variance_EX054 h t - 1 / 2)) t := by
    have ht : HasDerivAt f (1 + 2 * eta * variance_EX054 h t - (1 + eta) * 1) t :=
      (hasDerivAt_residual_EX054 h t).sub ((hasDerivAt_id t).const_mul (1 + eta))
    convert ht using 1
    ring
  have hb : ∀ t ∈ Icc (-|s|) |s|, ‖deriv f t‖ ≤ 2 * eta * K * (h ^ 2 + |s|) := by
    intro t ht
    rw [(hd t).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos two_pos eta_pos)]
    have hv := hV h t hh
    have ht' : |t| ≤ |s| := abs_le.mpr ht
    have hk := mul_le_mul_of_nonneg_left (add_le_add (le_refl (h ^ 2)) ht') hK
    have hm := mul_le_mul_of_nonneg_left (hv.trans hk) (mul_pos two_pos eta_pos).le
    convert hm using 1
    ring
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc (-|s|) |s|) => (hd t).differentiableAt)
    hb (convex_Icc _ _)
    (by exact ⟨neg_nonpos.mpr (abs_nonneg s), abs_nonneg s⟩)
    (by exact ⟨neg_abs_le s, le_abs_self s⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hm
  convert hm using 1
  congr 1
  dsimp [f]
  ring

theorem root_sharp_sixth_EX054 :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      |root_EX054 h - eta * h ^ 6 / (4608 * (1 + eta))| ≤ C * h ^ 8 := by
  have hηpos := eta_pos
  obtain ⟨K, hK, hV⟩ := variance_quadratic_linear_EX054
  obtain ⟨B, δB, hB, hδB, hroot⟩ := abs_root_le_sixth_EX054
  obtain ⟨A, δA, hA, hδA, hcenter⟩ := DGPS.Examples.sixth_order_centering_cancellation.2
  let D := 2 * eta * (K * (1 + B) * B + A) + 1
  refine ⟨D, min 1 (min δB δA), by dsimp [D]; positivity,
    lt_min one_pos (lt_min hδB hδA), fun h hh => ?_⟩
  have hh1 : |h| ≤ 1 := hh.trans (min_le_left _ _)
  have hhb : |h| ≤ δB := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hha : |h| ≤ δA := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr := hroot h hhb
  have hc := (hcenter h hha).2.2
  have h2 : h ^ 2 ≤ 1 := by nlinarith [abs_nonneg h, sq_abs h]
  have h6le : h ^ 6 ≤ h ^ 2 := by
    have ht : (h ^ 2) ^ 2 ≤ (1 : ℝ) := by
      calc (h ^ 2) ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (sq_nonneg h) h2 2
        _ = 1 := by norm_num
    have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg h)
    nlinarith
  have hprod : (h ^ 2 + |root_EX054 h|) * |root_EX054 h| ≤ (1 + B) * B * h ^ 8 := by
    have ht : h ^ 2 + |root_EX054 h| ≤ (1 + B) * h ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h6le hB.le]
    have hm := mul_le_mul ht hr (abs_nonneg _) (by positivity : 0 ≤ (1 + B) * h ^ 2)
    convert hm using 1
    ring
  have hl := residual_linearization_EX054 hK.le hh1 hV (s := root_EX054 h)
  rw [root_residual_EX054, residual_EX054, moment_zero_EX054] at hl
  have hlin :
      |(1 + eta) * root_EX054 h -
        2 * eta * (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h)| ≤
      2 * eta * K * (1 + B) * B * h ^ 8 := by
    have he : (1 + eta) * root_EX054 h -
        2 * eta * (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h) =
        -(0 - (0 - 2 * eta *
          (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h)) -
          (1 + eta) * root_EX054 h) := by ring
    rw [he, abs_neg]
    apply hl.trans
    have ht := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2 * eta * K)
    convert ht using 1 <;> ring
  have hcent :
      |DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h - h ^ 6 / 9216| ≤
        A * h ^ 8 := by
    convert hc using 1
    unfold polyCentering
    congr 1
    ring
  have herr :
      |(1 + eta) * root_EX054 h - eta * h ^ 6 / 4608| ≤
        2 * eta * (K * (1 + B) * B + A) * h ^ 8 := by
    have he : (1 + eta) * root_EX054 h - eta * h ^ 6 / 4608 =
        ((1 + eta) * root_EX054 h -
          2 * eta * (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h)) +
          2 * eta *
            (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h - h ^ 6 / 9216) := by ring
    rw [he]
    have ht := abs_add_le
      ((1 + eta) * root_EX054 h -
        2 * eta * (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h))
      (2 * eta * (DGPS.Examples.SixthOrderCentering.vonMisesCentering h - polyCentering h - h ^ 6 / 9216))
    rw [abs_mul, abs_of_pos (mul_pos two_pos eta_pos)] at ht
    have hb := mul_le_mul_of_nonneg_left hcent (mul_pos two_pos eta_pos).le
    calc _ ≤ _ := ht
      _ ≤ 2 * eta * K * (1 + B) * B * h ^ 8 + 2 * eta * (A * h ^ 8) :=
        add_le_add hlin hb
      _ = _ := by ring
  have hη : 0 < 1 + eta := by positivity
  have he : (1 + eta) *
      (root_EX054 h - eta * h ^ 6 / (4608 * (1 + eta))) =
        (1 + eta) * root_EX054 h - eta * h ^ 6 / 4608 := by
    field_simp [hη.ne']
  rw [← he, abs_mul, abs_of_pos hη] at herr
  dsimp [D]
  nlinarith [mul_nonneg eta_pos.le
    (abs_nonneg (root_EX054 h - eta * h ^ 6 / (4608 * (1 + eta)))),
    pow_nonneg (by positivity : 0 ≤ h ^ 2) 4]

end DGPS.Examples.PolynomialEquilibrium


namespace DGPS.Examples

open DGPS.Examples.PolynomialEquilibrium
open DGPS.Examples.PolynomialSpecies
open DGPS.Circle.AngularNormalization

/-- EX054: the actual normalized exponential family has a unique scalar equilibrium,
with the specified sixth-order coefficient, uniform eighth-order error, all fixed
angular C^k logarithmic ratio bounds, and exact reflection and half-turn symmetries. -/
theorem polynomial_exact_moving_equilibrium :
    (∀ h : ℝ, ∃! s : ℝ, s = 2 * eta * (moment_EX054 h s - polyCentering h)) ∧
    (∀ h : ℝ, root_EX054 h = 2 * eta * (moment_EX054 h (root_EX054 h) - polyCentering h)) ∧
    (∀ h : ℝ, (∫ θ, density_EX054 h (root_EX054 h) θ ∂angHaar) = 1 ∧
      ∀ θ, 0 < density_EX054 h (root_EX054 h) θ) ∧
    (∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      |root_EX054 h - eta * h ^ 6 / (4608 * (1 + eta))| ≤ C * h ^ 8) ∧
    (∀ k : ℕ, ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      ∀ j : ℕ, j ≤ k → ∀ θ : ℝ,
        |iteratedDeriv j (fun t : ℝ => logRatio_EX054 h (root_EX054 h) (t : AngCircle)) θ| ≤
          C * h ^ 6) ∧
    (∀ h : ℝ, ∀ θ : AngCircle,
      density_EX054 h (root_EX054 h) (-θ) = density_EX054 h (root_EX054 h) θ) ∧
    (∀ h : ℝ, root_EX054 (-h) = root_EX054 h) ∧
    (∀ h : ℝ, ∀ θ : AngCircle,
      density_EX054 (-h) (root_EX054 (-h)) (θ + ((Real.pi : ℝ) : AngCircle)) =
        density_EX054 h (root_EX054 h) θ) := by
  refine ⟨?_, root_equation_EX054, ?_, root_sharp_sixth_EX054, logRatio_fixed_Ck_EX054,
    fun h θ => density_reflection_EX054 h (root_EX054 h) θ,
    root_even_EX054, equilibrium_halfTurn_EX054⟩
  · intro h
    exact ⟨root_EX054 h, root_equation_EX054 h, fun s hs => root_unique_EX054 h s hs⟩
  · intro h
    exact ⟨integral_density_EX054 h (root_EX054 h), density_pos_EX054 h (root_EX054 h)⟩

end DGPS.Examples
