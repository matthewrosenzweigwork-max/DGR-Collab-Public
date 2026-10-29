import DGPS.Circle.FirstClusterPerturbation
import DGPS.Circle.VonMisesParity

namespace DGPS.Circle.VonMisesSpectrum

open MeasureTheory Real
open scoped InnerProductSpace
open DGPS.Circle.FirstClusterPerturbation DGPS.Circle.FirstClusterFourierEX009
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments
open DGPS.Analysis.CompactResolvent DGPS.Lipschitz.WeightedSpectrum
open DGPS.Circle.VonMisesParity

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Degenerate-cluster Rayleigh estimate: the two-dimensional spectral cluster
`lam 1 = lam 2` is located by a quasimode with a residual pairing. -/
theorem cluster_degenerate_estimate_EX016 (e : HilbertBasis ℕ ℝ E) (lam : ℕ → ℝ)
    (hdeg : lam 2 = lam 1) (m delta : ℝ) (hdelta : 0 < delta)
    (hgap : ∀ j, j ≠ 1 → j ≠ 2 → delta ≤ |lam j - m|)
    (f r : E) (hres : ∀ j, (lam j - m) * ⟪e j, f⟫_ℝ = ⟪e j, r⟫_ℝ) :
    |lam 1 - m| * (‖f‖ ^ 2 - ‖r‖ ^ 2 / delta ^ 2) ≤ |⟪r, f⟫_ℝ| + ‖r‖ ^ 2 / delta := by
  set P := pairProjection_EX009 e f with hP
  have herr := spectral_projection_error_EX009 e lam m delta hdelta.le hgap f r hres
  have hpy := pairProjection_pythagoras_EX009 e f
  have hdelta2 : 0 < delta ^ 2 := by positivity
  have hfP : ‖f - P‖ ^ 2 ≤ ‖r‖ ^ 2 / delta ^ 2 := by
    rw [le_div_iff₀ hdelta2]; linarith
  have hfP1 : ‖f - P‖ ≤ ‖r‖ / delta := by
    rw [le_div_iff₀ hdelta]
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    nlinarith
  have hPsq : ‖P‖ ^ 2 = ⟪e 1, f⟫_ℝ * ⟪e 1, f⟫_ℝ + ⟪e 2, f⟫_ℝ * ⟪e 2, f⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    exact pairProjection_inner_EX009 e f f
  have hrP : ⟪r, P⟫_ℝ = (lam 1 - m) * ‖P‖ ^ 2 := by
    rw [pairProjection_inner_right_EX009, hPsq, ← hres 1, ← hres 2, hdeg]
    ring
  have hrf : ⟪r, P⟫_ℝ = ⟪r, f⟫_ℝ - ⟪r, f - P⟫_ℝ := by
    rw [inner_sub_right]; ring
  have hcs : |⟪r, f - P⟫_ℝ| ≤ ‖r‖ * (‖r‖ / delta) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hfP1 (norm_nonneg _))
  have hmain : |lam 1 - m| * ‖P‖ ^ 2 ≤ |⟪r, f⟫_ℝ| + ‖r‖ ^ 2 / delta := by
    have h1 : |lam 1 - m| * ‖P‖ ^ 2 = |⟪r, P⟫_ℝ| := by
      rw [hrP, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖P‖ ^ 2)]
    rw [h1, hrf]
    calc |⟪r, f⟫_ℝ - ⟪r, f - P⟫_ℝ| ≤ |⟪r, f⟫_ℝ| + |⟪r, f - P⟫_ℝ| := abs_sub _ _
      _ ≤ _ := by
        have : ‖r‖ * (‖r‖ / delta) = ‖r‖ ^ 2 / delta := by ring
        linarith
  have hPlow : ‖f‖ ^ 2 - ‖r‖ ^ 2 / delta ^ 2 ≤ ‖P‖ ^ 2 := by linarith
  exact le_trans (mul_le_mul_of_nonneg_left hPlow (abs_nonneg _)) hmain

end Abstract

section Trig

/-- Even-frequency part of the sine residual coefficient. -/
noncomputable def P0_EX016 (θ : AngCircle) : ℝ :=
  -(cosMode_EX009 1 θ * sinMode_EX009 3 θ) / 192 +
    sinMode_EX009 1 θ ^ 2 * sinMode_EX009 2 θ / 48 - sinMode_EX009 2 θ / 72

/-- The `h`-linear part of the sine residual coefficient. -/
noncomputable def P1_EX016 (θ : AngCircle) : ℝ :=
  (sinMode_EX009 1 θ ^ 2 / 4 - 1 / 6) * sinMode_EX009 3 θ / 96

theorem quasiSin_explicit_EX016 (h : ℝ) (θ : AngCircle) :
    quasiSin_EX009 h 1 0 0 0 θ = sinMode_EX009 1 θ + h * (sinMode_EX009 2 θ / 12) +
      h ^ 2 * (sinMode_EX009 3 θ / 96) := by
  simp [quasiSin_EX009, angularPolynomial_EX009, quasiSinCoefficients_EX009, basis_EX009,
    Fin.sum_univ_succ, secondCosCoefficient_EX009, secondSinCoefficient_EX009]
  ring

theorem residual_explicit_EX016 (h : ℝ) (θ : AngCircle) :
    residualCoefficients_EX009 ![1, 0, 0, 0] h θ 0 1 = P0_EX016 θ + h * P1_EX016 θ := by
  simp [residualCoefficients_EX009, P0_EX016, P1_EX016, secondCosCoefficient_EX009,
    secondSinCoefficient_EX009]
  ring


theorem abs_P0_EX016 (θ : AngCircle) : |P0_EX016 θ| ≤ 1 := by
  have h1 := abs_cosMode_EX009 1 θ
  have h2 := abs_sinMode_EX009 1 θ
  have h3 := abs_sinMode_EX009 3 θ
  have h4 := abs_sinMode_EX009 2 θ
  rw [abs_le] at *
  unfold P0_EX016
  have a1 : |cosMode_EX009 1 θ * sinMode_EX009 3 θ| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (cosMode_EX009 1 θ), abs_nonneg (sinMode_EX009 3 θ),
      abs_cosMode_EX009 1 θ, abs_sinMode_EX009 3 θ]
  have a2 : sinMode_EX009 1 θ ^ 2 ≤ 1 := by nlinarith
  have a3 : 0 ≤ sinMode_EX009 1 θ ^ 2 := sq_nonneg _
  rw [abs_le] at a1
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h4.2 a3, mul_le_mul_of_nonneg_left h4.1 a3]

theorem abs_P1_EX016 (θ : AngCircle) : |P1_EX016 θ| ≤ 1 := by
  have h2 := abs_sinMode_EX009 1 θ
  have h3 := abs_sinMode_EX009 3 θ
  rw [abs_le] at *
  unfold P1_EX016
  have a2 : sinMode_EX009 1 θ ^ 2 ≤ 1 := by nlinarith
  have a3 : 0 ≤ sinMode_EX009 1 θ ^ 2 := sq_nonneg _
  have b1 : |sinMode_EX009 1 θ ^ 2 / 4 - 1 / 6| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have b2 : |(sinMode_EX009 1 θ ^ 2 / 4 - 1 / 6) * sinMode_EX009 3 θ| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (sinMode_EX009 1 θ ^ 2 / 4 - 1 / 6),
      abs_nonneg (sinMode_EX009 3 θ), abs_sinMode_EX009 3 θ]
  rw [abs_le] at b2
  constructor <;> linarith [b2.1, b2.2]

theorem abs_residual_EX016 {h : ℝ} (hh : |h| ≤ 1) (θ : AngCircle) :
    |residualCoefficients_EX009 ![1, 0, 0, 0] h θ 0 1| ≤ 2 := by
  rw [residual_explicit_EX016]
  calc |P0_EX016 θ + h * P1_EX016 θ| ≤ |P0_EX016 θ| + |h| * |P1_EX016 θ| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 + 1 * 1 := by
        gcongr
        · exact abs_P0_EX016 θ
        · exact abs_P1_EX016 θ
    _ = 2 := by norm_num

theorem abs_quasiSin_EX016 {h : ℝ} (hh : |h| ≤ 1) (θ : AngCircle) :
    |quasiSin_EX009 h 1 0 0 0 θ| ≤ 3 := by
  rw [quasiSin_explicit_EX016]
  have h1 := abs_sinMode_EX009 1 θ
  have h2 := abs_sinMode_EX009 2 θ
  have h3 := abs_sinMode_EX009 3 θ
  have hh2 : |h| ^ 2 ≤ 1 := by nlinarith [abs_nonneg h]
  have t2 : |h * (sinMode_EX009 2 θ / 12)| ≤ 1 := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 12)]
    nlinarith [abs_nonneg h, abs_nonneg (sinMode_EX009 2 θ)]
  have t3 : |h ^ 2 * (sinMode_EX009 3 θ / 96)| ≤ 1 := by
    rw [abs_mul, abs_pow, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 96)]
    nlinarith [abs_nonneg h, abs_nonneg (sinMode_EX009 3 θ)]
  have := abs_add_three (sinMode_EX009 1 θ) (h * (sinMode_EX009 2 θ / 12))
    (h ^ 2 * (sinMode_EX009 3 θ / 96))
  linarith

theorem coe_add_pi_EX016 (s : ℝ) :
    (s : AngCircle) + ((π : ℝ) : AngCircle) = ((s + π : ℝ) : AngCircle) := by simp

theorem cos1_add_pi_EX016 (θ : AngCircle) :
    cosMode_EX009 1 (θ + ((π : ℝ) : AngCircle)) = -cosMode_EX009 1 θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    rw [coe_add_pi_EX016, cosMode_coe_EX009, cosMode_coe_EX009]
    simp [Real.cos_add_pi]

theorem sin1_add_pi_EX016 (θ : AngCircle) :
    sinMode_EX009 1 (θ + ((π : ℝ) : AngCircle)) = -sinMode_EX009 1 θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    rw [coe_add_pi_EX016, sinMode_coe_EX009, sinMode_coe_EX009]
    simp [Real.sin_add_pi]

theorem sin2_add_pi_EX016 (θ : AngCircle) :
    sinMode_EX009 2 (θ + ((π : ℝ) : AngCircle)) = sinMode_EX009 2 θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    rw [coe_add_pi_EX016, sinMode_coe_EX009, sinMode_coe_EX009]
    push_cast
    rw [show (2 : ℝ) * (s + π) = 2 * s + 2 * π by ring, Real.sin_add_two_pi]

theorem sin3_add_pi_EX016 (θ : AngCircle) :
    sinMode_EX009 3 (θ + ((π : ℝ) : AngCircle)) = -sinMode_EX009 3 θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H s =>
    rw [coe_add_pi_EX016, sinMode_coe_EX009, sinMode_coe_EX009]
    push_cast
    rw [show (3 : ℝ) * (s + π) = 3 * s + π + 2 * π by ring, Real.sin_add_two_pi,
      Real.sin_add_pi]

theorem integral_P0_sin_EX016 :
    ∫ θ, P0_EX016 θ * sinMode_EX009 1 θ ∂angHaar = 0 := by
  have hshift := integral_add_right_eq_self
    (fun θ => P0_EX016 θ * sinMode_EX009 1 θ) (((π : ℝ) : AngCircle)) (μ := angHaar)
  have hf : (fun θ => P0_EX016 (θ + ((π : ℝ) : AngCircle)) *
      sinMode_EX009 1 (θ + ((π : ℝ) : AngCircle))) =
      fun θ => -(P0_EX016 θ * sinMode_EX009 1 θ) := by
    funext θ
    simp only [P0_EX016, cos1_add_pi_EX016, sin1_add_pi_EX016, sin2_add_pi_EX016,
      sin3_add_pi_EX016]
    ring
  rw [hf, integral_neg] at hshift
  linarith

theorem continuous_P0_EX016 : Continuous P0_EX016 := by
  have h1 := continuous_cosMode_EX009 1
  have h2 := continuous_sinMode_EX009 1
  have h3 := continuous_sinMode_EX009 2
  have h4 := continuous_sinMode_EX009 3
  unfold P0_EX016
  fun_prop

theorem continuous_P1_EX016 : Continuous P1_EX016 := by
  have h2 := continuous_sinMode_EX009 1
  have h4 := continuous_sinMode_EX009 3
  unfold P1_EX016
  fun_prop

theorem continuous_quasiSin_EX016 (h : ℝ) : Continuous (quasiSin_EX009 h 1 0 0 0) := by
  have h2 := continuous_sinMode_EX009 1
  have h3 := continuous_sinMode_EX009 2
  have h4 := continuous_sinMode_EX009 3
  have : quasiSin_EX009 h 1 0 0 0 = fun θ => sinMode_EX009 1 θ + h * (sinMode_EX009 2 θ / 12) +
      h ^ 2 * (sinMode_EX009 3 θ / 96) := funext (quasiSin_explicit_EX016 h)
  rw [this]
  fun_prop

theorem residual_pairing_EX016 {h : ℝ} (hh : |h| ≤ 1) :
    |∫ θ, residualCoefficients_EX009 ![1, 0, 0, 0] h θ 0 1 * quasiSin_EX009 h 1 0 0 0 θ
      ∂angHaar| ≤ 4 * |h| := by
  set E : AngCircle → ℝ := fun θ =>
    P0_EX016 θ * (h * (sinMode_EX009 2 θ / 12) + h ^ 2 * (sinMode_EX009 3 θ / 96)) +
      h * P1_EX016 θ * quasiSin_EX009 h 1 0 0 0 θ with hE
  have hsplit : (fun θ => residualCoefficients_EX009 ![1, 0, 0, 0] h θ 0 1 *
      quasiSin_EX009 h 1 0 0 0 θ) = fun θ => P0_EX016 θ * sinMode_EX009 1 θ + E θ := by
    funext θ
    rw [residual_explicit_EX016, quasiSin_explicit_EX016, hE]
    simp only [quasiSin_explicit_EX016]
    ring
  have hcP0 := continuous_P0_EX016
  have hcP1 := continuous_P1_EX016
  have hcq := continuous_quasiSin_EX016 h
  have hs1 := continuous_sinMode_EX009 1
  have hs2 := continuous_sinMode_EX009 2
  have hs3 := continuous_sinMode_EX009 3
  have hcE : Continuous E := by rw [hE]; fun_prop
  have hEb : ∀ θ, |E θ| ≤ 4 * |h| := by
    intro θ
    have a0 := abs_P0_EX016 θ
    have a1 := abs_P1_EX016 θ
    have a2 := abs_quasiSin_EX016 hh θ
    have b2 := abs_sinMode_EX009 2 θ
    have b3 := abs_sinMode_EX009 3 θ
    have hh2 : |h| ^ 2 ≤ |h| := by nlinarith [abs_nonneg h]
    have t1 : |h * (sinMode_EX009 2 θ / 12) + h ^ 2 * (sinMode_EX009 3 θ / 96)| ≤ |h| := by
      have u2 : |h * (sinMode_EX009 2 θ / 12)| ≤ |h| / 12 := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 12)]
        nlinarith [abs_nonneg h, abs_nonneg (sinMode_EX009 2 θ)]
      have u3 : |h ^ 2 * (sinMode_EX009 3 θ / 96)| ≤ |h| / 96 := by
        rw [abs_mul, abs_pow, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 96)]
        nlinarith [abs_nonneg h, abs_nonneg (sinMode_EX009 3 θ)]
      linarith [abs_add_le (h * (sinMode_EX009 2 θ / 12)) (h ^ 2 * (sinMode_EX009 3 θ / 96)),
        abs_nonneg h]
    have v1 : |P0_EX016 θ * (h * (sinMode_EX009 2 θ / 12) + h ^ 2 * (sinMode_EX009 3 θ / 96))|
        ≤ |h| := by
      rw [abs_mul]
      nlinarith [abs_nonneg (P0_EX016 θ),
        abs_nonneg (h * (sinMode_EX009 2 θ / 12) + h ^ 2 * (sinMode_EX009 3 θ / 96)),
        abs_nonneg h]
    have v2 : |h * P1_EX016 θ * quasiSin_EX009 h 1 0 0 0 θ| ≤ 3 * |h| := by
      rw [abs_mul, abs_mul]
      have : |h| * |P1_EX016 θ| ≤ |h| := by nlinarith [abs_nonneg h, abs_nonneg (P1_EX016 θ)]
      nlinarith [abs_nonneg (quasiSin_EX009 h 1 0 0 0 θ), abs_nonneg h,
        abs_nonneg (P1_EX016 θ), mul_nonneg (abs_nonneg h) (abs_nonneg (P1_EX016 θ))]
    rw [hE]
    linarith [abs_add_le (P0_EX016 θ * (h * (sinMode_EX009 2 θ / 12) + h ^ 2 * (sinMode_EX009 3 θ / 96)))
      (h * P1_EX016 θ * quasiSin_EX009 h 1 0 0 0 θ)]
  have hiE : Integrable E angHaar := integrable_cont hcE _ hEb
  have hiP : Integrable (fun θ => P0_EX016 θ * sinMode_EX009 1 θ) angHaar :=
    integrable_cont (hcP0.mul hs1) 1 (fun θ => by
      rw [abs_mul]
      nlinarith [abs_P0_EX016 θ, abs_sinMode_EX009 1 θ, abs_nonneg (P0_EX016 θ),
        abs_nonneg (sinMode_EX009 1 θ)])
  rw [hsplit, integral_add hiP hiE, integral_P0_sin_EX016, zero_add]
  have := norm_integral_le_of_norm_le_const (μ := angHaar) (f := E) (C := 4 * |h|)
    (Filter.Eventually.of_forall fun θ => by simpa [Real.norm_eq_abs] using hEb θ)
  simpa using this

end Trig

section Bridge

/-- The logarithm of the von Mises density, `h cos`. -/
noncomputable def ell_EX016 (h : ℝ) : AngCircle → ℝ := fun θ => h * angCos θ

theorem ell_coe_EX016 (h s : ℝ) : ell_EX016 h (s : AngCircle) = h * Real.cos s := by
  simp [ell_EX016, angCos, angMode_coe]

theorem ell_eq_harmonic_EX016 (h : ℝ) :
    (fun y : ℝ => ell_EX016 h (y : AngCircle)) = harmonicLog_EX009 h 1 0 0 0 := by
  funext y
  simp [ell_coe_EX016, harmonicLog_EX009]

theorem isSmoothAngular_ell_EX016 (h : ℝ) : IsSmoothAngular (ell_EX016 h) := by
  unfold IsSmoothAngular
  have : (fun s : ℝ => ell_EX016 h (s : AngCircle)) = fun s => h * Real.cos s := by
    funext s; exact ell_coe_EX016 h s
  rw [this]
  exact contDiff_const.mul Real.contDiff_cos

theorem c2Jet_ell_EX016 (h : ℝ) :
    c2JetError_EX009 (ell_EX016 h) h (![1, 0, 0, 0] 0) (![1, 0, 0, 0] 1)
      (![1, 0, 0, 0] 2) (![1, 0, 0, 0] 3) 0 := by
  intro x
  have h1 : ell_EX016 h (x : AngCircle) = harmonicLog_EX009 h 1 0 0 0 x :=
    congrFun (ell_eq_harmonic_EX016 h) x
  rw [ell_eq_harmonic_EX016, h1]
  simp

theorem angularGibbs_ell_EX016 (h : ℝ) : angularGibbs_EX009 (ell_EX016 h) = vmWeight h := by
  funext x
  have hint : ∫ y, Real.exp (-(-ell_EX016 h (angEquiv y))) ∂haar 1 = besselI 0 h := by
    simp only [neg_neg]
    rw [measurePreserving_angEquiv.integral_comp' (f := angEquiv)
      (fun θ => Real.exp (ell_EX016 h θ))]
    unfold besselI
    simp [ell_EX016, angMode_zero]
  unfold angularGibbs_EX009 DGPS.Lipschitz.WeightedGenerator.gibbsW vmWeight besselDensity
  rw [hint]
  simp [ell_EX016]

end Bridge

section Quasimode

/-- The sine-column quasimode of the cos-field Schrodinger operator, transported to
`Hw 1 w`: an approximate eigenvector `f` of the pair `(lam 1, lam 2)` near
`AngularNormalization.a0 * (1 + h^2/6)`, with residual `r` of size `O(h^3)` and `<r, f> = O(h^4)`. -/
theorem sine_quasimode_EX016 {w : Torus 1 → ℝ} {c C Z : ℝ}
    (ell : AngCircle → ℝ) (hell : IsSmoothAngular ell) (hZ : 0 < Z)
    (hwexp : ∀ x, w x = Real.exp (ell (angEquiv x)) / Z)
    (hwd : DGPS.Lipschitz.WeightedGenerator.WData 1 w (smoothGrad (ell ∘ angEquiv)) c C)
    {e : HilbertBasis ℕ ℝ (Hw 1 w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus 1 → Tangent 1} (hsd : SpectralData w e lam G)
    {h : ℝ} (hh : |h| ≤ 1)
    (hpot : ∀ x, schrodingerPotential_EX009 (fun y : ℝ => ell (y : AngCircle)) x =
      h * firstPotential_EX009 1 0 x + h ^ 2 * secondPotential_EX009 1 0 0 0 x +
        h ^ 3 * (fun _ : ℝ => (0 : ℝ)) x) :
    ∃ f r : Hw 1 w,
      (∀ j, (lam j - AngularNormalization.a0 * (1 + h ^ 2 / 6)) * ⟪e j, f⟫_ℝ = ⟪e j, r⟫_ℝ) ∧
      1 / 2 ≤ ‖f‖ ^ 2 ∧ ‖r‖ ≤ 2 * AngularNormalization.a0 * |h| ^ 3 ∧ |⟪r, f⟫_ℝ| ≤ 4 * AngularNormalization.a0 * h ^ 4 := by
  have ha := DGPS.Circle.AngularNormalization.a0_pos
  have hps := smooth_normalized_ground_EX009 Z hell (smooth_quasiSin_EX009 h 1 0 0 0)
  obtain ⟨fs, As, hfs, hAs, hcoeffS⟩ :=
    smooth_test_spectral_coefficients_EX009 ell
      (normalizedGroundAngular_EX009 Z ell (quasiSin_EX009 h 1 0 0 0)) hell hps hwd hsd
  have hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C :=
    Filter.Eventually.of_forall hwd.bound
  have hfsAE : (fs : Torus 1 → ℝ) =ᵐ[haar 1] fun x =>
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) * quasiSin_EX009 h 1 0 0 0 (angEquiv x) := by
    filter_upwards [hfs] with x hx
    rw [hx]; rfl
  have hrsAE : ((As - (AngularNormalization.a0 * (1 + h ^ 2 / 6)) • fs : Hw 1 w) : Torus 1 → ℝ) =ᵐ[haar 1] fun x =>
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) *
        (AngularNormalization.a0 * h ^ 3 * residualCoefficients_EX009 ![1, 0, 0, 0] h (angEquiv x) 0 1) := by
    filter_upwards [ae_eq_haar hwd.pos hwb (Lp.coeFn_sub As ((AngularNormalization.a0 * (1 + h ^ 2 / 6)) • fs)),
      ae_eq_haar hwd.pos hwb (Lp.coeFn_smul (AngularNormalization.a0 * (1 + h ^ 2 / 6)) fs),
      hfs, hAs] with x hb hc hfx hAx
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hb hc
    rw [hb, hc, hfx, hAx]
    have key := (physical_quasi_residual_EX009 Z ell hell (fun _ => 0) h 1 0 0 0 hpot x).2
    simp only [Function.comp_apply]
    linear_combination key
  have hqbound (theta : AngCircle) :
      |AngularNormalization.a0 * h ^ 3 * residualCoefficients_EX009 ![1, 0, 0, 0] h theta 0 1| ≤
        2 * AngularNormalization.a0 * |h| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos ha, abs_pow]
    have he := mul_le_mul_of_nonneg_left (abs_residual_EX016 hh theta)
      (by positivity : 0 ≤ AngularNormalization.a0 * |h| ^ 3)
    nlinarith only [he]
  refine ⟨fs, As - (AngularNormalization.a0 * (1 + h ^ 2 / 6)) • fs, ?_, ?_, ?_, ?_⟩
  · intro j
    have hs := hcoeffS j
    rw [inner_sub_right, inner_smul_right]
    linear_combination hs
  · have he := normalized_tests_inner_EX009 hwd.meas hwd.pos hwb hZ ell
      (quasiSin_EX009 h 1 0 0 0) (quasiSin_EX009 h 1 0 0 0) hwexp fs fs hfsAE hfsAE
    rw [real_inner_self_eq_norm_sq] at he
    rw [he, quasi_gram_sin_EX009]
    exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)) (by positivity)
  · exact normalized_test_norm_bound_EX009 hwd.meas hwd.pos hwb hZ ell _ (by positivity)
      hwexp _ hrsAE hqbound
  · have he := normalized_tests_inner_EX009 hwd.meas hwd.pos hwb hZ ell
      (fun theta => AngularNormalization.a0 * h ^ 3 * residualCoefficients_EX009 ![1, 0, 0, 0] h theta 0 1)
      (quasiSin_EX009 h 1 0 0 0) hwexp _ fs hrsAE hfsAE
    rw [he]
    have hc : ∫ theta, AngularNormalization.a0 * h ^ 3 * residualCoefficients_EX009 ![1, 0, 0, 0] h theta 0 1 *
        quasiSin_EX009 h 1 0 0 0 theta ∂angHaar =
        AngularNormalization.a0 * h ^ 3 * ∫ theta, residualCoefficients_EX009 ![1, 0, 0, 0] h theta 0 1 *
          quasiSin_EX009 h 1 0 0 0 theta ∂angHaar := by
      rw [← integral_const_mul]; congr 1; funext theta; ring
    rw [hc, abs_mul, abs_mul, abs_of_pos ha, abs_pow]
    have hp := residual_pairing_EX016 hh
    have h4 : |h| ^ 3 * |h| = h ^ 4 := by
      calc |h| ^ 3 * |h| = (|h| ^ 2) ^ 2 := by ring
        _ = (h ^ 2) ^ 2 := by rw [sq_abs]
        _ = h ^ 4 := by ring
    have := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ AngularNormalization.a0 * |h| ^ 3)
    nlinarith only [this, h4, ha]

end Quasimode

section Spectrum

open DGPS.Analysis DGPS.Lipschitz.WeightedGenerator

/-- If all but one Hilbert-basis coefficient of `u` vanish, then `u` is a multiple of that
basis vector. -/
theorem eq_single_of_coeff_zero_EX016 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (b : HilbertBasis ℕ ℝ E) (u : E) (k : ℕ)
    (h0 : ∀ j, j ≠ k → ⟪b j, u⟫_ℝ = 0) : u = ⟪b k, u⟫_ℝ • (b k : E) := by
  have hs := b.hasSum_repr u
  have h1 : HasSum (fun i => b.repr u i • (b i : E)) (b.repr u k • (b k : E)) :=
    hasSum_single k (fun i hi => by rw [HilbertBasis.repr_apply_apply, h0 i hi, zero_smul])
  rw [HilbertBasis.repr_apply_apply] at h1
  exact hs.unique h1

/-- If the eigenvalue `lam 1` is simple among the spectral data, every `lam 1`-eigenfunction is
a multiple of `e 1`. -/
theorem eigenfunction_eq_mul_EX016 {P : BoundedPositiveReference 1}
    {e : HilbertBasis ℕ ℝ (Hw 1 P.density)} {lam : ℕ → ℝ} {G : ℕ → Torus 1 → Tangent 1}
    (hS : SpecData P e lam G) (h2 : lam 2 ≠ lam 1) (h3 : lam 1 < lam 3)
    {u : Torus 1 → ℝ} (hu : IsEigenfunction P.density (lam 1) u) :
    ∃ c : ℝ, u =ᵐ[haar 1] fun x => c * ((e 1 : Hw 1 P.density) : Torus 1 → ℝ) x := by
  have hl1 : 0 < lam 1 := by have := hS.lam0; have := hS.lam01; linarith
  obtain ⟨-, Gu, hu⟩ := hu
  have hmem := hu.1.memLp
  have hcoef : ∀ j, lam j * ⟪e j, toHw P hmem⟫_ℝ = lam 1 * ⟪e j, toHw P hmem⟫_ℝ := by
    intro j
    have hUw : IsWeakGradient (toHw P hmem : Torus 1 → ℝ) Gu :=
      hu.1.congr_ae (toHw_ae P hmem).symm Filter.EventuallyEq.rfl
    have h1 := hS.form j (toHw P hmem) Gu hUw
    have h2' := hu.2 _ _ (hS.grad j)
    rw [weightedForm_comm, h2'] at h1
    have h3' : ⟪e j, toHw P hmem⟫_ℝ = ∫ x, u x * (e j : Torus 1 → ℝ) x * P.density x ∂haar 1 := by
      rw [inner_toHw]; congr 1; funext x; ring
    rw [← h3'] at h1
    exact h1.symm
  have hz : ∀ j, j ≠ 1 → ⟪e j, toHw P hmem⟫_ℝ = 0 := by
    intro j hj
    have hne : lam j ≠ lam 1 := by
      rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · interval_cases j
        · rw [hS.lam0]; exact hl1.ne
        · exact absurd rfl hj
        · exact h2
      · exact (lt_of_lt_of_le h3 (hS.mono hj3)).ne'
    rcases mul_eq_mul_right_iff.1 (hcoef j) with h | h
    · exact absurd h hne
    · exact h
  have hU := eq_single_of_coeff_zero_EX016 e (toHw P hmem) 1 hz
  refine ⟨⟪e 1, toHw P hmem⟫_ℝ, ?_⟩
  have h5 := ae_eq_haar P.lower_pos (fou020_hwb P)
    (Lp.coeFn_smul ⟪e 1, toHw P hmem⟫_ℝ (e 1 : Hw 1 P.density))
  refine (toHw_ae P hmem).symm.trans ?_
  filter_upwards [h5] with x hx
  have hx' : (toHw P hmem : Torus 1 → ℝ) x =
      ((⟪e 1, toHw P hmem⟫_ℝ • (e 1 : Hw 1 P.density) : Hw 1 P.density) : Torus 1 → ℝ) x := by
    conv_lhs => rw [hU]
  rw [hx']
  simpa using hx

/-- Parity forces the eigenvalue `lam 1` of the von Mises generator to be (at least) doubly
degenerate, hence `lam 2 = lam 1` as soon as `lam 1 < lam 3`. -/
theorem lam_two_eq_EX016 (h : ℝ) {e : HilbertBasis ℕ ℝ (Hw 1 (vmRef h).density)} {lam : ℕ → ℝ}
    {G : ℕ → Torus 1 → Tangent 1} (hS : SpecData (vmRef h) e lam G) (h3 : lam 1 < lam 3) :
    lam 2 = lam 1 := by
  by_contra h2
  have hl1 : 0 < lam 1 := by have := hS.lam0; have := hS.lam01; linarith
  have e1 := hS.isEigenfunction 1
  obtain ⟨⟨v, hv, hvp⟩, ⟨v', hv', hvp'⟩⟩ := eigen_both_sectors (measurable_vmWeight h)
    (vmRef h).lower_pos (fou020_hwb (vmRef h)) (vmWeight_neg h) (vmWeight_mul_half h) hl1 e1
  obtain ⟨c, hc⟩ := eigenfunction_eq_mul_EX016 hS h2 h3 hv
  obtain ⟨c', hc'⟩ := eigenfunction_eq_mul_EX016 hS h2 h3 hv'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv.1
    filter_upwards [hc] with x hx
    simpa using hx
  have hc0' : c' ≠ 0 := by
    rintro rfl
    apply hv'.1
    filter_upwards [hc'] with x hx
    simpa using hx
  apply e1.1
  filter_upwards [hc, hc', ae_neg hc, ae_neg hc', hvp, hvp'] with x h1 h1' h2' h2'' h3' h3''
  simp only [Pi.zero_apply]
  rw [h2', h1] at h3'
  rw [h2'', h1'] at h3''
  have ha : (e 1 : Torus 1 → ℝ) (-x) = (e 1 : Torus 1 → ℝ) x := by
    apply mul_left_cancel₀ hc0; linarith
  have hb : (e 1 : Torus 1 → ℝ) (-x) = -(e 1 : Torus 1 → ℝ) x := by
    apply mul_left_cancel₀ hc0'; linarith
  linarith

end Spectrum

section Final

theorem hpot_ell_EX016 (h x : ℝ) :
    schrodingerPotential_EX009 (fun y : ℝ => ell_EX016 h (y : AngCircle)) x =
      h * firstPotential_EX009 1 0 x + h ^ 2 * secondPotential_EX009 1 0 0 0 x +
        h ^ 3 * (fun _ : ℝ => (0 : ℝ)) x := by
  rw [ell_eq_harmonic_EX016, harmonic_potential_jet_EX009]
  simp only [firstPotential_EX009, secondPotential_EX009, potentialRemainder_EX009]
  ring

/-- Spectral data of the von Mises generator with the sharp `O(h^4)` location of `lam 1`. -/
theorem expansion_at_EX016 {h F : ℝ} (hh : |h| ≤ 1 / 2)
    (hclu : FirstClusterConclusion_EX009 (angularGibbs_EX009 (ell_EX016 h)) ![1, 0, 0, 0] h F) :
    ∃ (e : HilbertBasis ℕ ℝ (Hw 1 (vmRef h).density)) (lam : ℕ → ℝ)
      (G : ℕ → Torus 1 → Tangent 1), SpecData (vmRef h) e lam G ∧
        |lam 1 - AngularNormalization.a0 * (1 + h ^ 2 / 6)| ≤
          20 * AngularNormalization.a0 * h ^ 4 := by
  have ha := DGPS.Circle.AngularNormalization.a0_pos
  have hh1 : |h| ≤ 1 := hh.trans (by norm_num)
  have hell := isSmoothAngular_ell_EX016 h
  have hbound : ∀ theta, |ell_EX016 h theta| ≤ 1 := by
    intro theta
    unfold ell_EX016
    rw [abs_mul]
    have h2 : |angCos theta| ≤ 1 := abs_angMode_le 1 theta
    calc |h| * |angCos theta| ≤ 1 * 1 := mul_le_mul hh1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  obtain ⟨Z, hZ, hwexp, -, hwd⟩ := angular_gibbs_data_EX009 (ell_EX016 h) hell 1 hbound
  rw [angularGibbs_ell_EX016] at hwexp hwd hclu
  obtain ⟨e, lam, G, hsd, he0, hz, hmono, -, h1, h2lt, h3, -, -⟩ := hclu
  have hS : SpecData (vmRef h) e lam G :=
    ⟨he0, hz, by rw [hz]; linarith, hmono, hsd.grad, hsd.eig, hsd.energy⟩
  have hl12 : lam 1 ≤ lam 2 := hmono (by norm_num)
  have hdeg := lam_two_eq_EX016 h hS (by linarith)
  obtain ⟨f, r, hres, hf, hr, hrf⟩ :=
    sine_quasimode_EX016 (ell_EX016 h) hell hZ hwexp hwd hsd hh1 (hpot_ell_EX016 h)
  have hh2 : h ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs h, abs_nonneg h]
  have hgap : ∀ j, j ≠ 1 → j ≠ 2 →
      AngularNormalization.a0 ≤ |lam j - AngularNormalization.a0 * (1 + h ^ 2 / 6)| := by
    intro j hj1 hj2
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · have : j = 0 := by omega
      subst this
      rw [hz, zero_sub, abs_neg, abs_of_pos (by positivity)]
      nlinarith [sq_nonneg h]
    · have h4 := hmono hj3
      rw [abs_of_pos (by nlinarith)]
      nlinarith
  have hest := cluster_degenerate_estimate_EX016 e lam hdeg
    (AngularNormalization.a0 * (1 + h ^ 2 / 6)) AngularNormalization.a0 ha hgap f r hres
  refine ⟨e, lam, G, hS, ?_⟩
  set A := AngularNormalization.a0 with hA
  have hh4 : 0 ≤ h ^ 4 := by positivity
  have hr2 : ‖r‖ ^ 2 ≤ 4 * A ^ 2 * h ^ 6 := by
    have h0 := pow_le_pow_left₀ (norm_nonneg r) hr 2
    calc ‖r‖ ^ 2 ≤ (2 * A * |h| ^ 3) ^ 2 := h0
      _ = 4 * A ^ 2 * (|h| ^ 2) ^ 3 := by ring
      _ = 4 * A ^ 2 * h ^ 6 := by rw [sq_abs]; ring
  have h6a : h ^ 6 ≤ h ^ 4 / 4 := by nlinarith
  have h6b : h ^ 6 ≤ 1 / 64 := by
    have : (h ^ 2) ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ (sq_nonneg h) hh2 3
    nlinarith
  have hq1 : ‖r‖ ^ 2 / A ^ 2 ≤ 4 * h ^ 6 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hq2 : ‖r‖ ^ 2 / A ≤ A * h ^ 4 := by
    rw [div_le_iff₀ ha]; nlinarith [mul_nonneg ha.le hh4]
  have hK : 1 / 4 ≤ ‖f‖ ^ 2 - ‖r‖ ^ 2 / A ^ 2 := by linarith
  have hX := abs_nonneg (lam 1 - A * (1 + h ^ 2 / 6))
  have := mul_le_mul_of_nonneg_left hK hX
  nlinarith

end Final

end DGPS.Circle.VonMisesSpectrum

namespace DGPS.Examples

open DGPS DGPS.Circle.VonMisesParity DGPS.Circle.BesselMoments

/-- **EX016 (even small-field Poincare expansion).**  For the von Mises law `q_h`, the first
positive eigenvalue `lam_1` of `-L_h`, which is also the least positive odd eigenvalue and the
Poincare rate, satisfies `lam_1 = a0 * (1 + h^2/6 + O(h^4))`: there are constants `C, h0 > 0` with
`|lam_1 - a0 * (1 + h^2/6)| <= C * a0 * h^4` for `|h| < h0`. -/
theorem even_small_field_poincare_expansion :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧ ∀ h : ℝ, |h| < h0 →
      ∃ lam1 : ℝ, 0 < lam1 ∧
        IsLeast {lam : ℝ | 0 < lam ∧ ∃ u, IsEigenfunction (vmWeight h) lam u} lam1 ∧
        IsLeast {lam : ℝ | 0 < lam ∧
          ∃ u, IsEigenfunction (vmWeight h) lam u ∧ ex007_InParitySector (d := 1) (-1) u}
          lam1 ∧
        poincareRate ⟨(vmRef h).measure, (vmRef h).isProbabilityMeasure⟩ =
          ENNReal.ofReal lam1 ∧
        |lam1 - DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 / 6)| ≤
          C * DGPS.Circle.AngularNormalization.a0 * h ^ 4 := by
  obtain ⟨delta, F, hdelta, -, hclu⟩ :=
    DGPS.Circle.FirstClusterPerturbation.uniform_box_cluster_EX009 (M := 1) (R := 0)
      zero_le_one le_rfl
  refine ⟨20, min delta (1 / 2), by norm_num, lt_min hdelta (by norm_num), ?_⟩
  intro h hh
  have hhd : |h| ≤ delta := (hh.trans_le (min_le_left _ _)).le
  have hh2 : |h| ≤ 1 / 2 := (hh.trans_le (min_le_right _ _)).le
  have hp : ∀ i, |(![1, 0, 0, 0] : Fin 4 → ℝ) i| ≤ 1 := by
    intro i; fin_cases i <;> simp
  obtain ⟨e, lam, G, hS, hest⟩ := DGPS.Circle.VonMisesSpectrum.expansion_at_EX016 hh2
    (hclu ![1, 0, 0, 0] (DGPS.Circle.VonMisesSpectrum.ell_EX016 h) h hp
      (DGPS.Circle.VonMisesSpectrum.isSmoothAngular_ell_EX016 h) hhd
      (DGPS.Circle.VonMisesSpectrum.c2Jet_ell_EX016 h))
  have hl1 : 0 < lam 1 := by have := hS.lam0; have := hS.lam01; linarith
  have both : ∀ l : ℝ, 0 < l → (∃ u, IsEigenfunction (vmWeight h) l u) →
      (∃ u, IsEigenfunction (vmWeight h) l u ∧ ex007_InParitySector (d := 1) 1 u) ∧
      (∃ u, IsEigenfunction (vmWeight h) l u ∧ ex007_InParitySector (d := 1) (-1) u) :=
    fun l hl ⟨u, hu⟩ => eigen_both_sectors (measurable_vmWeight h) (vmRef h).lower_pos
      (DGPS.Analysis.fou020_hwb (vmRef h)) (vmWeight_neg h) (vmWeight_mul_half h) hl hu
  have least : ∀ l : ℝ, 0 < l → (∃ u, IsEigenfunction (vmWeight h) l u) → lam 1 ≤ l := by
    rintro l hl ⟨u, hu⟩
    obtain ⟨j, rfl⟩ := hS.eigenvalue_mem hu
    have hj : j ≠ 0 := by
      rintro rfl
      rw [hS.lam0] at hl
      exact lt_irrefl _ hl
    exact hS.mono (Nat.one_le_iff_ne_zero.2 hj)
  have e1 := hS.isEigenfunction 1
  refine ⟨lam 1, hl1, ⟨⟨hl1, _, e1⟩, fun l hl => least l hl.1 hl.2⟩,
    ⟨⟨hl1, (both _ hl1 ⟨_, e1⟩).2⟩, fun l hl => least l hl.1 ⟨hl.2.choose, hl.2.choose_spec.1⟩⟩,
    hS.poincareRate_eq, hest⟩

end DGPS.Examples
