import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentSigns

/-! Actual signed zero-mass root-moment coercivity. The feature and generator
vectors rotate independently under the SAME retained C3 root family. No
probability, positivity or support restriction is imposed on the signed weights. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Signed zero-mass weights have a quantitative nonzero C3 resultant. -/
theorem threefoldResultant_zero_mass_lower (p : Fin 3 → ℝ) (hp : ∑ j, p j = 0) :
    (∑ j, |p j|) ^ 2 / 2 ≤ Complex.normSq (threefoldResultant p) := by
  have hm : (p 0 + p 1 + p 2) ^ 2 = 0 := by
    have hsum : p 0 + p 1 + p 2 = 0 := by simpa only [Fin.sum_univ_three] using hp
    rw [hsum]
    norm_num
  have h01 := sq_nonneg (|p 0| - |p 1|)
  have h02 := sq_nonneg (|p 0| - |p 2|)
  have h12 := sq_nonneg (|p 1| - |p 2|)
  rw [threefoldResultant_normSq, Fin.sum_univ_three]
  nlinarith only [hm, h01, h02, h12, sq_abs (p 0), sq_abs (p 1), sq_abs (p 2)]

/-- The exact native six-observable signed moment, without constructing a
probability law from signed weights. -/
def ordinarySignedRootMoment (h : ℝ) (σ : Fin 3 → AbsoluteDensity 1)
    (p : Fin 3 → ℝ) (i : Fin 6) : ℝ :=
  ∑ j, p j * ∫ x, elementarySixObservable h i x ∂(densityMeasure (σ j) : Measure (Torus 1))

/-- The literal correction-difference polynomial used by the original native
six-moment expansion. This definition does not import a profile-error consumer. -/
def ordinarySignedRootQuadratic (h r : ℝ) (σ : Fin 3 → AbsoluteDensity 1)
    (p : Fin 3 → ℝ) : ℝ :=
  let x := ordinarySignedRootMoment h σ p
  2 * kAlpha * (x 0 * x 3 + x 1 * x 4) - 2 * kBeta * x 2 * x 5 -
    r * (kAlpha * (x 0 ^ 2 + x 1 ^ 2) - kBeta * x 2 ^ 2)

private theorem phase_coordinates (j : Fin 3) :
    (threefoldPhase j).re = Real.cos (2 * Real.pi * ((j : ℕ) / 3)) ∧
      (threefoldPhase j).im = Real.sin (2 * Real.pi * ((j : ℕ) / 3)) := by
  fin_cases j
  · norm_num [threefoldPhase]
  · have he : (-1 / 2 : ℝ) = Real.cos (2 * Real.pi * (1 / 3)) ∧
        Real.sqrt 3 / 2 = Real.sin (2 * Real.pi * (1 / 3)) := by
      rw [show 2 * Real.pi * (1 / 3) = 2 * Real.pi / 3 by ring,
        cos_theta_STR02923, sin_theta_STR02923]
      exact ⟨rfl, rfl⟩
    simpa [threefoldPhase] using he
  · have he : (-1 / 2 : ℝ) = Real.cos (2 * Real.pi * (2 / 3)) ∧
        -(Real.sqrt 3 / 2) = Real.sin (2 * Real.pi * (2 / 3)) := by
      rw [show 2 * Real.pi * (2 / 3) = 2 * (2 * Real.pi / 3) by ring,
        Real.cos_two_mul, Real.sin_two_mul, cos_theta_STR02923, sin_theta_STR02923]
      constructor <;> ring
    simpa [threefoldPhase] using he

private theorem orbit_re (p : Fin 3 → ℝ) (v : ℂ) :
    (threefoldOrbitSum p v).re =
      ∑ j, p j * ((threefoldPhase j).re * v.re - (threefoldPhase j).im * v.im) := by
  simp only [threefoldOrbitSum, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem orbit_im (p : Fin 3 → ℝ) (v : ℂ) :
    (threefoldOrbitSum p v).im =
      ∑ j, p j * ((threefoldPhase j).im * v.re + (threefoldPhase j).re * v.im) := by
  simp only [threefoldOrbitSum, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem orbit_pair (p f g : Fin 3 → ℝ) (v : ℂ)
    (hfg : ∀ j, f j = (threefoldPhase j).re * v.re - (threefoldPhase j).im * v.im ∧
      g j = (threefoldPhase j).im * v.re + (threefoldPhase j).re * v.im) :
    (⟨∑ j, p j * f j, ∑ j, p j * g j⟩ : ℂ) = threefoldOrbitSum p v := by
  apply Complex.ext
  · change (∑ j, p j * f j) = (threefoldOrbitSum p v).re
    rw [orbit_re]
    exact Finset.sum_congr rfl fun j _ => congrArg (p j * ·) (hfg j).1
  · change (∑ j, p j * g j) = (threefoldOrbitSum p v).im
    rw [orbit_im]
    exact Finset.sum_congr rfl fun j _ => congrArg (p j * ·) (hfg j).2

/-- The actual six signed root moments reduce to the SAME root-zero beta
coefficient when total signed mass vanishes. Invariant B/AB moments vanish. -/
theorem ordinarySignedRootQuadratic_zero_mass (D : OrdinaryRootGraphData) (h : ℝ)
    (hhr : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ))
    (r : ℝ) (p : Fin 3 → ℝ) (hp : ∑ j, p j = 0) :
    ordinarySignedRootQuadratic h r σ p =
      ordinaryRootCorrectionBeta h r σ * Complex.normSq (threefoldResultant p) := by
  let x := ordinarySignedRootMoment h σ p
  let v : ℂ := ⟨momC h (densityMeasure (σ 0)), momS h (densityMeasure (σ 0))⟩
  let w : ℂ := ⟨∫ y, elementaryFeatureGenerator h (featureC h) y
    ∂(densityMeasure (σ 0) : Measure (Torus 1)),
    ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure (σ 0) : Measure (Torus 1))⟩
  have hr := ordinaryRoot_six_moment_rotations D h hhr σ hσ
  have hv : (⟨x 0, x 1⟩ : ℂ) = threefoldOrbitSum p v := by
    apply orbit_pair p (fun j => momC h (densityMeasure (σ j)))
      (fun j => momS h (densityMeasure (σ j))) v
    intro j
    rw [(phase_coordinates j).1, (phase_coordinates j).2]
    exact ⟨(hr j).1, (hr j).2.1⟩
  have hw : (⟨x 3, x 4⟩ : ℂ) = threefoldOrbitSum p w := by
    apply orbit_pair p
      (fun j => ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure (σ j) : Measure (Torus 1)))
      (fun j => ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure (σ j) : Measure (Torus 1))) w
    intro j
    rw [(phase_coordinates j).1, (phase_coordinates j).2]
    exact ⟨(hr j).2.2.2.1, (hr j).2.2.2.2.1⟩
  have hB : x 2 = 0 := by
    change (∑ j, p j * momB h (densityMeasure (σ j))) = 0
    have hiB (j : Fin 3) : momB h (densityMeasure (σ j)) = momB h (densityMeasure (σ 0)) :=
      (hr j).2.2.1
    simp_rw [hiB]
    rw [← Finset.sum_mul, hp, zero_mul]
  have hAB : x 5 = 0 := by
    change (∑ j, p j * ∫ y, elementaryFeatureGenerator h (featureB h) y
      ∂(densityMeasure (σ j) : Measure (Torus 1))) = 0
    have hiAB (j : Fin 3) :
        (∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure (σ j) : Measure (Torus 1))) =
        ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure (σ 0) : Measure (Torus 1)) :=
      (hr j).2.2.2.2.2
    simp_rw [hiAB]
    rw [← Finset.sum_mul, hp, zero_mul]
  have hxy : x 0 ^ 2 + x 1 ^ 2 = Complex.normSq (threefoldOrbitSum p v) := by
    rw [← hv]
    change x 0 ^ 2 + x 1 ^ 2 = x 0 * x 0 + x 1 * x 1
    ring
  have hdot : x 0 * x 3 + x 1 * x 4 =
      planeDot (threefoldOrbitSum p v) (threefoldOrbitSum p w) := by
    rw [← hv, ← hw]
    rfl
  change 2 * kAlpha * (x 0 * x 3 + x 1 * x 4) - 2 * kBeta * x 2 * x 5 -
    r * (kAlpha * (x 0 ^ 2 + x 1 ^ 2) - kBeta * x 2 ^ 2) =
      threefoldBeta r v w * Complex.normSq (threefoldResultant p)
  rw [hB, hAB]
  simp only [mul_zero, zero_mul, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [hdot, hxy, threefoldOrbitSum_dot, threefoldOrbitSum_normSq]
  unfold threefoldBeta kAlpha
  ring

private theorem beta_antitone (v w : ℂ) {r a : ℝ} (hra : r ≤ a) :
    threefoldBeta a v w ≤ threefoldBeta r v w := by
  unfold threefoldBeta
  apply div_le_div_of_nonneg_right _ a0_pos.le
  have ht := mul_le_mul_of_nonneg_right hra (Complex.normSq_nonneg v)
  nlinarith only [ht]

/-- A genuine fixed interval precedes h, every SAME-chart absolute root triple,
the subrate and all signed charges. No alpha or desired coercivity is assumed. -/
theorem ordinarySignedRootMoment_lower (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
        ∀ r : ℝ, 0 ≤ r → r ≤ (ordinaryLSRate (ordinaryReference h)).toReal →
          ∀ p : Fin 3 → ℝ, (∑ j, p j = 0) →
            (7 / 2 : ℝ) * (∑ j, |p j|) ^ 2 ≤ ordinarySignedRootQuadratic h r σ p := by
  obtain ⟨δ, hδ, hδD, hsign⟩ := ordinaryRoot_correction_coefficient_signs D
  refine ⟨δ, hδ, hδD, fun h hh hhd σ hσ r hr0 hra p hp => ?_⟩
  have hhr : h ∈ Set.Ioo (-D.radius) D.radius :=
    ⟨by linarith [D.radius_pos], hhd.trans_le hδD⟩
  have hβa := (hsign h hh hhd σ hσ).2.2
  have hβ : 7 ≤ ordinaryRootCorrectionBeta h r σ := by
    refine hβa.le.trans ?_
    exact beta_antitone _ _ hra
  rw [ordinarySignedRootQuadratic_zero_mass D h hhr σ hσ r p hp]
  have hz := threefoldResultant_zero_mass_lower p hp
  have hn := Complex.normSq_nonneg (threefoldResultant p)
  calc
    _ ≤ 7 * Complex.normSq (threefoldResultant p) := by nlinarith only [hz]
    _ ≤ _ := mul_le_mul_of_nonneg_right hβ hn

end DGPS.Examples.ThreeSpeciesCircle
