import DGPS.Foundations.Torus

/-!
# Explicit threefold circle integrals and centered features (STR023)

For `h > 0`: `I_k(h) = (1/2π) ∫_0^{2π} exp(h cos t) cos(k t) dt` (`besselI`, an explicit integral,
not Mathlib's `Complex.besselJ`), the reference density `q_h(x) = exp(h cos 6πx)/I_0(h)`
(`referenceDensity`), `g_h = I_1/I_0` (`referenceMean`), the features `c_h, s_h, b_h`
(`featureC`, `featureS`, `featureB`) and the probability measure `μ_h = q_h m`
(`threefoldReference`) on the circle `Torus 1`.

* `threefoldReference_integral_properties`: `I_0 > 0`, `q_h` positive, smooth, `∫ q_h dm = 1`,
  `μ_h` is a probability measure, `∫ cos 6πx dμ_h = g_h`, and `g_h = (h/2)(1 - I_2/I_0)`.
* `elementaryFeatures_centered_independent`: the three features are `μ_h`-centered and linearly
  independent (as `μ_h`-a.e. classes, and as functions).

Reading choices: `cos(2πk x)`, `sin(2πk x)` on `Torus 1` are the real and imaginary parts of
Mathlib's `fourier k` on `AddCircle 1` (`cosHarm`, `sinHarm`).
-/
open MeasureTheory
open scoped ContDiff

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The point of `Torus 1` with representative `t`. -/
abbrev pt (t : ℝ) : Torus 1 := torusLift (fun _ => t)

/-- `x ↦ cos(2πk x)` on the circle. -/
noncomputable def cosHarm (k : ℕ) (x : Torus 1) : ℝ := (fourier (k : ℤ) (x 0)).re
/-- `x ↦ sin(2πk x)` on the circle. -/
noncomputable def sinHarm (k : ℕ) (x : Torus 1) : ℝ := (fourier (k : ℤ) (x 0)).im

theorem cosHarm_lift (k : ℕ) (y : Fin 1 → ℝ) :
    cosHarm k (torusLift y) = Real.cos (2 * Real.pi * k * y 0) := by
  show (fourier (k : ℤ) (((y 0 : ℝ) : AddCircle (1:ℝ)))).re = _
  rw [fourier_coe_apply]
  have : (2 * ↑Real.pi * Complex.I * ((k:ℤ):ℂ) * ((y 0 : ℝ):ℂ) / ((1:ℝ):ℂ))
      = ((2 * Real.pi * k * y 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem sinHarm_lift (k : ℕ) (y : Fin 1 → ℝ) :
    sinHarm k (torusLift y) = Real.sin (2 * Real.pi * k * y 0) := by
  show (fourier (k : ℤ) (((y 0 : ℝ) : AddCircle (1:ℝ)))).im = _
  rw [fourier_coe_apply]
  have : (2 * ↑Real.pi * Complex.I * ((k:ℤ):ℂ) * ((y 0 : ℝ):ℂ) / ((1:ℝ):ℂ))
      = ((2 * Real.pi * k * y 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im]

theorem cosHarm_pt (k : ℕ) (t : ℝ) : cosHarm k (pt t) = Real.cos (2 * Real.pi * k * t) :=
  cosHarm_lift k _

theorem sinHarm_pt (k : ℕ) (t : ℝ) : sinHarm k (pt t) = Real.sin (2 * Real.pi * k * t) :=
  sinHarm_lift k _

theorem continuous_cosHarm (k : ℕ) : Continuous (cosHarm k) :=
  Complex.continuous_re.comp ((fourier (k:ℤ)).continuous.comp (continuous_apply 0))

theorem continuous_sinHarm (k : ℕ) : Continuous (sinHarm k) :=
  Complex.continuous_im.comp ((fourier (k:ℤ)).continuous.comp (continuous_apply 0))

theorem integral_haar_one (G : Torus 1 → ℝ) (hG : Continuous G) :
    ∫ x, G x ∂haar 1 = ∫ t in (0:ℝ)..1, G (pt t) := by
  rw [haar_eq_map_unitBox, integral_map (SharpLSI.measurable_liftT).aemeasurable hG.aestronglyMeasurable]
  have := (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding (fun t => G (pt t)) (Set.Ioc 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one, ← this]
  have hs : SharpLSI.unitBox (Fin 1) = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Ioc 0 1 := by
    ext x; simp [SharpLSI.unitBox, MeasurableEquiv.funUnique, Set.mem_pi]
  rw [hs]
  congr 1
  ext x
  congr 1
  funext i
  simp [pt, torusLift, SharpLSI.liftT, MeasurableEquiv.funUnique, Subsingleton.elim i 0]

/-- `I_k(h) = (1/2π) ∫_0^{2π} exp(h cos t) cos(k t) dt`. -/
noncomputable def besselI (k : ℕ) (h : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0:ℝ)..(2 * Real.pi), Real.exp (h * Real.cos t) * Real.cos (k * t)

theorem continuous_expCosMul (h : ℝ) (k : ℕ) :
    Continuous (fun t : ℝ => Real.exp (h * Real.cos t) * Real.cos (k * t)) := by fun_prop

theorem besselI_zero_pos {h : ℝ} : 0 < besselI 0 h := by
  unfold besselI
  have : 0 < ∫ t in (0:ℝ)..(2 * Real.pi), Real.exp (h * Real.cos t) * Real.cos ((0:ℕ) * t) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (continuous_expCosMul h 0).intervalIntegrable _ _
    · intro t _; simp [Real.exp_pos]
    · positivity
  positivity

theorem integral_unit_threePeriods (m : ℕ) (h : ℝ) :
    ∫ t in (0:ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t))
        * Real.cos (2 * Real.pi * (m:ℝ) * (3 * t)) = besselI m h := by
  set f : ℝ → ℝ := fun s => Real.exp (h * Real.cos s) * Real.cos (m * s) with hf
  have hper : Function.Periodic f (2 * Real.pi) := by
    intro s
    simp only [hf]
    have : (m:ℝ) * (s + 2 * Real.pi) = m * s + (m:ℕ) * (2 * Real.pi) := by ring
    rw [this, Real.cos_add_nat_mul_two_pi, Real.cos_add_two_pi]
  have h1 : (fun t : ℝ => Real.exp (h * Real.cos (2 * Real.pi * 3 * t))
        * Real.cos (2 * Real.pi * (m:ℝ) * (3 * t))) = fun t => f ((2 * Real.pi * 3) * t) := by
    funext t; simp only [hf]; congr 2; ring
  rw [h1, intervalIntegral.integral_comp_mul_left (fun s => f s) (by positivity)]
  have h3 := hper.intervalIntegral_add_zsmul_eq 3 0
    (fun a b => (continuous_expCosMul h m).intervalIntegrable a b)
  simp only [zero_add] at h3
  simp only [mul_zero, mul_one]
  have h4 : (2 * Real.pi * 3 : ℝ) = ((3:ℤ) • (2 * Real.pi)) := by simp; ring
  rw [h4, h3]
  unfold besselI
  simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_ofNat, hf]
  field_simp


theorem besselI_recurrence (h : ℝ) : 2 * besselI 1 h = h * (besselI 0 h - besselI 2 h) := by
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun t : ℝ => Real.exp (h * Real.cos t) * Real.sin t)
        (Real.exp (h * Real.cos t) * (Real.cos t - h * Real.sin t ^ 2)) t := by
    intro t _
    have := (((Real.hasDerivAt_cos t).const_mul h).exp).mul (Real.hasDerivAt_sin t)
    convert this using 1
    ring
  have hc : Continuous (fun t : ℝ => Real.exp (h * Real.cos t) * (Real.cos t - h * Real.sin t ^ 2)) := by
    fun_prop
  have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)
  simp only [Real.sin_two_pi, Real.sin_zero, mul_zero, sub_self] at h0
  have hpt : ∀ t : ℝ, Real.exp (h * Real.cos t) * (Real.cos t - h * Real.sin t ^ 2)
      = Real.exp (h * Real.cos t) * Real.cos ((1:ℕ) * t)
        - (h / 2) * (Real.exp (h * Real.cos t) * Real.cos ((0:ℕ) * t)
          - Real.exp (h * Real.cos t) * Real.cos ((2:ℕ) * t)) := by
    intro t
    have h2 : Real.cos ((2:ℕ) * t) = 1 - 2 * Real.sin t ^ 2 := by
      push_cast; rw [Real.cos_two_mul, Real.cos_sq']; ring
    rw [h2]; push_cast; simp only [zero_mul, Real.cos_zero, one_mul]; ring
  simp only [hpt] at h0
  rw [intervalIntegral.integral_sub ((continuous_expCosMul h 1).intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; have := (continuous_expCosMul h 0).sub (continuous_expCosMul h 2); fun_prop),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((continuous_expCosMul h 0).intervalIntegrable _ _)
      ((continuous_expCosMul h 2).intervalIntegrable _ _)] at h0
  unfold besselI
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp
  push_cast at h0 ⊢
  linear_combination 2 * h0

/-- shift invariance over one period for 1-periodic continuous functions -/
theorem integral_shift_unit {φ : ℝ → ℝ} (hφ : Function.Periodic φ 1) (a : ℝ) :
    ∫ t in (0:ℝ)..1, φ (t + a) = ∫ t in (0:ℝ)..1, φ t := by
  rw [intervalIntegral.integral_comp_add_right (fun t => φ t) a]
  have := hφ.intervalIntegral_add_eq a 0
  simpa [add_comm] using this

theorem cos_three_sum (u : ℝ) :
    Real.cos u + Real.cos (u + 2 * Real.pi / 3) + Real.cos (u + 4 * Real.pi / 3) = 0 := by
  have h1 : Real.cos (2 * Real.pi / 3) = -1/2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have h2 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  have h3 : Real.cos (4 * Real.pi / 3) = -1/2 := by
    have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [this, Real.cos_add_pi, Real.cos_pi_div_three]; norm_num
  have h4 : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [this, Real.sin_add_pi, Real.sin_pi_div_three]
  rw [Real.cos_add, Real.cos_add, h1, h2, h3, h4]; ring

theorem sin_three_sum (u : ℝ) :
    Real.sin u + Real.sin (u + 2 * Real.pi / 3) + Real.sin (u + 4 * Real.pi / 3) = 0 := by
  have h1 : Real.cos (2 * Real.pi / 3) = -1/2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have h2 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  have h3 : Real.cos (4 * Real.pi / 3) = -1/2 := by
    have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [this, Real.cos_add_pi, Real.cos_pi_div_three]; norm_num
  have h4 : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
    have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
    rw [this, Real.sin_add_pi, Real.sin_pi_div_three]
  rw [Real.sin_add, Real.sin_add, h1, h2, h3, h4]; ring

/-- first harmonic against the von Mises weight has mean zero (cos and sin together) -/
theorem integral_firstHarmonic (h : ℝ) :
    (∫ t in (0:ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * Real.cos (2 * Real.pi * t)) = 0 ∧
    (∫ t in (0:ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * Real.sin (2 * Real.pi * t)) = 0 := by
  have key : ∀ (T : ℝ → ℝ), Continuous T → Function.Periodic T 1 →
      (∀ u, T u + T (u + 1/3) + T (u + 2/3) = 0) →
      ∫ t in (0:ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T t = 0 := by
    intro T hT hTp hsum
    set φ : ℝ → ℝ := fun t => Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T t with hφ
    have hφc : Continuous φ := by simp only [hφ]; fun_prop
    have hφp : Function.Periodic φ 1 := by
      intro t
      simp only [hφ]
      have : 2 * Real.pi * 3 * (t + 1) = 2 * Real.pi * 3 * t + (3:ℕ) * (2 * Real.pi) := by push_cast; ring
      rw [this, Real.cos_add_nat_mul_two_pi, hTp t]
    have e1 : ∀ t, φ (t + 1/3) = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T (t + 1/3) := by
      intro t; simp only [hφ]
      have : 2 * Real.pi * 3 * (t + 1/3) = 2 * Real.pi * 3 * t + 2 * Real.pi := by ring
      rw [this, Real.cos_add_two_pi]
    have e2 : ∀ t, φ (t + 2/3) = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T (t + 2/3) := by
      intro t; simp only [hφ]
      have : 2 * Real.pi * 3 * (t + 2/3) = 2 * Real.pi * 3 * t + (2:ℕ) * (2 * Real.pi) := by push_cast; ring
      rw [this, Real.cos_add_nat_mul_two_pi]
    have s1 := integral_shift_unit hφp (1/3)
    have s2 := integral_shift_unit hφp (2/3)
    have hsum' : ∫ t in (0:ℝ)..1, (φ t + φ (t + 1/3) + φ (t + 2/3)) = 0 := by
      have : ∀ t, φ t + φ (t + 1/3) + φ (t + 2/3)
          = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * (T t + T (t + 1/3) + T (t + 2/3)) := by
        intro t; rw [e1, e2]; simp only [hφ]; ring
      simp only [this, hsum, mul_zero]; simp
    have hi : ∀ a, IntervalIntegrable (fun t => φ (t + a)) MeasureSpace.volume 0 1 := by
      intro a
      exact (hφc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    have hi0 : IntervalIntegrable φ MeasureSpace.volume 0 1 := hφc.intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hi0.add (hi (1/3))) (hi (2/3)),
      intervalIntegral.integral_add hi0 (hi (1/3)), s1, s2] at hsum'
    simp only [hφ] at hsum' ⊢
    linarith
  constructor
  · refine key (fun t => Real.cos (2 * Real.pi * t)) (by fun_prop) ?_ ?_
    · intro t
      have : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
      simp only [this, Real.cos_add_two_pi]
    · intro u
      have e1 : 2 * Real.pi * (u + 1/3) = 2 * Real.pi * u + 2 * Real.pi / 3 := by ring
      have e2 : 2 * Real.pi * (u + 2/3) = 2 * Real.pi * u + 4 * Real.pi / 3 := by ring
      simp only [e1, e2]; exact cos_three_sum _
  · refine key (fun t => Real.sin (2 * Real.pi * t)) (by fun_prop) ?_ ?_
    · intro t
      have : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
      simp only [this, Real.sin_add_two_pi]
    · intro u
      have e1 : 2 * Real.pi * (u + 1/3) = 2 * Real.pi * u + 2 * Real.pi / 3 := by ring
      have e2 : 2 * Real.pi * (u + 2/3) = 2 * Real.pi * u + 4 * Real.pi / 3 := by ring
      simp only [e1, e2]; exact sin_three_sum _


/-- Von Mises reference density `q_h(x) = exp(h cos 6πx) / I_0(h)`. -/
noncomputable def referenceDensity (h : ℝ) (x : Torus 1) : ℝ :=
  Real.exp (h * cosHarm 3 x) / besselI 0 h

/-- `g_h = I_1(h) / I_0(h)`. -/
noncomputable def referenceMean (h : ℝ) : ℝ := besselI 1 h / besselI 0 h

/-- `c_h(x) = cos(2πx) / h`. -/
noncomputable def featureC (h : ℝ) (x : Torus 1) : ℝ := cosHarm 1 x / h

/-- `s_h(x) = sin(2πx) / h`. -/
noncomputable def featureS (h : ℝ) (x : Torus 1) : ℝ := sinHarm 1 x / h

/-- `b_h(x) = 15 (cos(6πx) - g_h) / (4 h³)`. -/
noncomputable def featureB (h : ℝ) (x : Torus 1) : ℝ :=
  15 * (cosHarm 3 x - referenceMean h) / (4 * h ^ 3)

/-- The probability measure `μ_h = q_h · m` on the circle. -/
noncomputable def threefoldReference (h : ℝ) : Measure (Torus 1) :=
  (haar 1).withDensity (fun x => ENNReal.ofReal (referenceDensity h x))

theorem continuous_referenceDensity (h : ℝ) : Continuous (referenceDensity h) := by
  unfold referenceDensity
  have := continuous_cosHarm 3
  fun_prop

theorem referenceDensity_pos {h : ℝ} (x : Torus 1) : 0 < referenceDensity h x := by
  unfold referenceDensity
  exact div_pos (Real.exp_pos _) besselI_zero_pos

theorem integral_threefoldReference (h : ℝ) (g : Torus 1 → ℝ) :
    ∫ x, g x ∂threefoldReference h = ∫ x, referenceDensity h x * g x ∂haar 1 := by
  unfold threefoldReference
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_referenceDensity h).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (referenceDensity_pos (h := h) x).le]

theorem torusIntegral_density_mul (h : ℝ) (m : ℕ) :
    ∫ x, referenceDensity h x * cosHarm (3 * m) x ∂haar 1 = besselI m h / besselI 0 h := by
  rw [integral_haar_one (fun x => referenceDensity h x * cosHarm (3 * m) x)
    ((continuous_referenceDensity h).mul (continuous_cosHarm _))]
  have : ∀ t : ℝ, referenceDensity h (pt t) * cosHarm (3 * m) (pt t)
      = (Real.exp (h * Real.cos (2 * Real.pi * 3 * t))
          * Real.cos (2 * Real.pi * (m:ℝ) * (3 * t))) / besselI 0 h := by
    intro t
    simp only [referenceDensity, cosHarm_pt]
    rw [div_mul_eq_mul_div]
    push_cast
    congr 3; ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, integral_unit_threePeriods]

theorem cosHarm_zero (x : Torus 1) : cosHarm 0 x = 1 := by
  simp [cosHarm]

theorem integrable_referenceDensity (h : ℝ) : Integrable (referenceDensity h) (haar 1) :=
  (continuous_referenceDensity h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem threefoldReference_integral_properties {h : ℝ} (_hh : 0 < h) :
    0 < besselI 0 h ∧ (∀ x, 0 < referenceDensity h x) ∧ IsSmoothPeriodic (referenceDensity h) ∧
    ∫ x, referenceDensity h x ∂haar 1 = 1 ∧ IsProbabilityMeasure (threefoldReference h) ∧
    ∫ x, cosHarm 3 x ∂threefoldReference h = referenceMean h ∧
    referenceMean h = (h / 2) * (1 - besselI 2 h / besselI 0 h) := by
  have hI0 : 0 < besselI 0 h := besselI_zero_pos
  have hint1 : ∫ x, referenceDensity h x ∂haar 1 = 1 := by
    have := torusIntegral_density_mul h 0
    simp only [mul_zero, cosHarm_zero, mul_one] at this
    rw [this, div_self hI0.ne']
  refine ⟨hI0, fun x => referenceDensity_pos x, ?_, hint1, ?_, ?_, ?_⟩
  · unfold IsSmoothPeriodic
    have : (referenceDensity h ∘ torusLift) = fun y : Fin 1 → ℝ =>
        Real.exp (h * Real.cos (2 * Real.pi * ((3:ℕ):ℝ) * y 0)) / besselI 0 h := by
      funext y; simp only [Function.comp, referenceDensity, cosHarm_lift]
    rw [this]
    fun_prop
  · refine ⟨?_⟩
    unfold threefoldReference
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_referenceDensity h)
        (Filter.Eventually.of_forall fun x => (referenceDensity_pos x).le), hint1]
    simp
  · rw [integral_threefoldReference]
    have := torusIntegral_density_mul h 1
    simpa [referenceMean] using this
  · have := besselI_recurrence h
    unfold referenceMean
    field_simp
    linarith


theorem integrable_of_continuous_torus {f : Torus 1 → ℝ} (hf : Continuous f) :
    Integrable f (haar 1) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem torusIntegral_density_first (h : ℝ) :
    ∫ x, referenceDensity h x * cosHarm 1 x ∂haar 1 = 0 ∧
    ∫ x, referenceDensity h x * sinHarm 1 x ∂haar 1 = 0 := by
  have hc := continuous_referenceDensity h
  obtain ⟨c1, s1⟩ := integral_firstHarmonic h
  constructor
  · rw [integral_haar_one (fun x => referenceDensity h x * cosHarm 1 x)
      (hc.mul (continuous_cosHarm _))]
    have : ∀ t : ℝ, referenceDensity h (pt t) * cosHarm 1 (pt t)
        = (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * Real.cos (2 * Real.pi * t))
            / besselI 0 h := by
      intro t
      simp only [referenceDensity, cosHarm_pt]
      rw [div_mul_eq_mul_div]
      push_cast
      congr 3; ring
    simp_rw [this]
    rw [intervalIntegral.integral_div, c1, zero_div]
  · rw [integral_haar_one (fun x => referenceDensity h x * sinHarm 1 x)
      (hc.mul (continuous_sinHarm _))]
    have : ∀ t : ℝ, referenceDensity h (pt t) * sinHarm 1 (pt t)
        = (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * Real.sin (2 * Real.pi * t))
            / besselI 0 h := by
      intro t
      simp only [referenceDensity, cosHarm_pt, sinHarm_pt]
      rw [div_mul_eq_mul_div]
      push_cast
      congr 3; ring
    simp_rw [this]
    rw [intervalIntegral.integral_div, s1, zero_div]

theorem featureC_continuous (h : ℝ) : Continuous (featureC h) := by
  unfold featureC; have := continuous_cosHarm 1; fun_prop

theorem featureS_continuous (h : ℝ) : Continuous (featureS h) := by
  unfold featureS; have := continuous_sinHarm 1; fun_prop

theorem featureB_continuous (h : ℝ) : Continuous (featureB h) := by
  unfold featureB; have := continuous_cosHarm 3; fun_prop

/-- pointwise independence of the three features -/
theorem features_pointwise_independent {h : ℝ} (hh : 0 < h) (a b c : ℝ)
    (H : ∀ x, a * featureC h x + b * featureS h x + c * featureB h x = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hh0 : h ≠ 0 := hh.ne'
  have ev : ∀ t : ℝ, a * (Real.cos (2 * Real.pi * t) / h) + b * (Real.sin (2 * Real.pi * t) / h)
      + c * (15 * (Real.cos (2 * Real.pi * 3 * t) - referenceMean h) / (4 * h ^ 3)) = 0 := by
    intro t
    have := H (pt t)
    simpa [featureC, featureS, featureB, cosHarm_pt, sinHarm_pt] using this
  have hc : ∀ t : ℝ, c * (Real.cos (2 * Real.pi * 3 * t) - referenceMean h) = 0 := by
    intro t
    have e0 := ev t
    have e1 := ev (t + 1/3)
    have e2 := ev (t + 2/3)
    have p1 : 2 * Real.pi * (t + 1/3) = 2 * Real.pi * t + 2 * Real.pi / 3 := by ring
    have p2 : 2 * Real.pi * (t + 2/3) = 2 * Real.pi * t + 4 * Real.pi / 3 := by ring
    have q1 : 2 * Real.pi * 3 * (t + 1/3) = 2 * Real.pi * 3 * t + 2 * Real.pi := by ring
    have q2 : 2 * Real.pi * 3 * (t + 2/3) = 2 * Real.pi * 3 * t + (2:ℕ) * (2 * Real.pi) := by
      push_cast; ring
    rw [p1, q1, Real.cos_add_two_pi] at e1
    rw [p2, q2, Real.cos_add_nat_mul_two_pi] at e2
    have hs1 := cos_three_sum (2 * Real.pi * t)
    have hs2 := sin_three_sum (2 * Real.pi * t)
    have : 3 * (c * (15 * (Real.cos (2 * Real.pi * 3 * t) - referenceMean h) / (4 * h ^ 3))) = 0 := by
      have : a * (Real.cos (2 * Real.pi * t) / h) + a * (Real.cos (2 * Real.pi * t + 2 * Real.pi / 3) / h)
          + a * (Real.cos (2 * Real.pi * t + 4 * Real.pi / 3) / h) = 0 := by
        have : a * (Real.cos (2 * Real.pi * t) / h) + a * (Real.cos (2 * Real.pi * t + 2 * Real.pi / 3) / h)
          + a * (Real.cos (2 * Real.pi * t + 4 * Real.pi / 3) / h)
          = a / h * (Real.cos (2 * Real.pi * t) + Real.cos (2 * Real.pi * t + 2 * Real.pi / 3)
            + Real.cos (2 * Real.pi * t + 4 * Real.pi / 3)) := by ring
        rw [this, hs1, mul_zero]
      have h' : b * (Real.sin (2 * Real.pi * t) / h) + b * (Real.sin (2 * Real.pi * t + 2 * Real.pi / 3) / h)
          + b * (Real.sin (2 * Real.pi * t + 4 * Real.pi / 3) / h) = 0 := by
        have : b * (Real.sin (2 * Real.pi * t) / h) + b * (Real.sin (2 * Real.pi * t + 2 * Real.pi / 3) / h)
          + b * (Real.sin (2 * Real.pi * t + 4 * Real.pi / 3) / h)
          = b / h * (Real.sin (2 * Real.pi * t) + Real.sin (2 * Real.pi * t + 2 * Real.pi / 3)
            + Real.sin (2 * Real.pi * t + 4 * Real.pi / 3)) := by ring
        rw [this, hs2, mul_zero]
      linarith
    have h4 : (15 : ℝ) / (4 * h ^ 3) ≠ 0 := by positivity
    have : c * (Real.cos (2 * Real.pi * 3 * t) - referenceMean h) * (15 / (4 * h ^ 3)) = 0 := by
      have : c * (Real.cos (2 * Real.pi * 3 * t) - referenceMean h) * (15 / (4 * h ^ 3))
        = c * (15 * (Real.cos (2 * Real.pi * 3 * t) - referenceMean h) / (4 * h ^ 3)) := by ring
      rw [this]; linarith
    rcases mul_eq_zero.1 this with h5 | h5
    · exact h5
    · exact absurd h5 h4
  have c0 := hc 0
  have c1 := hc (1/6)
  have e1 : Real.cos (2 * Real.pi * 3 * (1/6)) = -1 := by
    have : 2 * Real.pi * 3 * (1/6 : ℝ) = Real.pi := by ring
    rw [this, Real.cos_pi]
  simp only [mul_zero, Real.cos_zero] at c0
  rw [e1] at c1
  have hc0 : c = 0 := by nlinarith
  subst hc0
  have a0 := ev 0
  have b0 := ev (1/4)
  have s1 : Real.cos (2 * Real.pi * (1/4)) = 0 := by
    have : 2 * Real.pi * (1/4 : ℝ) = Real.pi / 2 := by ring
    rw [this, Real.cos_pi_div_two]
  have s2 : Real.sin (2 * Real.pi * (1/4)) = 1 := by
    have : 2 * Real.pi * (1/4 : ℝ) = Real.pi / 2 := by ring
    rw [this, Real.sin_pi_div_two]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, zero_mul, add_zero, zero_div] at a0
  rw [s1, s2] at b0
  simp only [zero_div, mul_zero, zero_add] at b0
  refine ⟨?_, ?_, rfl⟩
  · have : a * (1 / h) = 0 := by simpa using a0
    simpa [hh0] using this
  · have : b * (1 / h) = 0 := by simpa using b0
    simpa [hh0] using this

theorem elementaryFeatures_centered_independent {h : ℝ} (hh : 0 < h) :
    ∫ x, featureC h x ∂threefoldReference h = 0 ∧
    ∫ x, featureS h x ∂threefoldReference h = 0 ∧
    ∫ x, featureB h x ∂threefoldReference h = 0 ∧
    (∀ a b c : ℝ, (∀ᵐ x ∂threefoldReference h,
        a * featureC h x + b * featureS h x + c * featureB h x = 0) → a = 0 ∧ b = 0 ∧ c = 0) ∧
    LinearIndependent ℝ ![featureC h, featureS h, featureB h] := by
  have hI0 : 0 < besselI 0 h := besselI_zero_pos
  obtain ⟨f1, f2⟩ := torusIntegral_density_first h
  have hq := continuous_referenceDensity h
  have hint1 : ∫ x, referenceDensity h x ∂haar 1 = 1 :=
    (threefoldReference_integral_properties hh).2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [integral_threefoldReference]
    simp only [featureC, mul_div_assoc', integral_div]
    rw [f1, zero_div]
  · rw [integral_threefoldReference]
    simp only [featureS, mul_div_assoc', integral_div]
    rw [f2, zero_div]
  · rw [integral_threefoldReference]
    have : ∀ x, referenceDensity h x * featureB h x
        = (15 / (4 * h ^ 3)) * (referenceDensity h x * cosHarm 3 x
            - referenceMean h * referenceDensity h x) := by
      intro x; simp only [featureB]; ring
    simp_rw [this]
    have i1 : Integrable (fun x => referenceDensity h x * cosHarm 3 x) (haar 1) :=
      integrable_of_continuous_torus (hq.mul (continuous_cosHarm 3))
    have i2 : Integrable (fun x => referenceMean h * referenceDensity h x) (haar 1) :=
      (integrable_referenceDensity h).const_mul _
    rw [integral_const_mul, integral_sub i1 i2, integral_const_mul, hint1]
    have := torusIntegral_density_mul h 1
    simp only [mul_one] at this
    rw [this]
    unfold referenceMean
    simp
  · intro a b c hae
    have hm : Measurable (fun x => ENNReal.ofReal (referenceDensity h x)) := hq.measurable.ennreal_ofReal
    have hae' := (ae_withDensity_iff hm).1 hae
    have hpos : ∀ x, ENNReal.ofReal (referenceDensity h x) ≠ 0 := fun x => by
      simpa using referenceDensity_pos (h := h) x
    have hF : Continuous (fun x => a * featureC h x + b * featureS h x + c * featureB h x) := by
      have := featureC_continuous h; have := featureS_continuous h; have := featureB_continuous h
      fun_prop
    have hae2 : (fun x => a * featureC h x + b * featureS h x + c * featureB h x) =ᵐ[haar 1]
        fun _ => 0 := by
      filter_upwards [hae'] with x hx using hx (hpos x)
    have := (hF.ae_eq_iff_eq (haar 1) continuous_const).1 hae2
    exact features_pointwise_independent hh a b c (fun x => congrFun this x)
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have H : ∀ x, g 0 * featureC h x + g 1 * featureS h x + g 2 * featureB h x = 0 := by
      intro x
      have := congrFun hg x
      simpa [Fin.sum_univ_three] using this
    obtain ⟨h0, h1, h2⟩ := features_pointwise_independent hh _ _ _ H
    fin_cases i <;> simpa

end DGPS.Examples.ThreeSpeciesCircle
