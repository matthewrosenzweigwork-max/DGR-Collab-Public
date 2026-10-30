import DGPS.Examples.PolynomialSpeciesGraphValueComparison
import DGPS.Examples.PolynomialSpeciesReferenceValueControl
import DGPS.Examples.PolynomialSpeciesFiniteProfileGapExpansion

/-! The ACTUAL same-graph scaled fourth coefficient, with uniform fifth-order
value error. Reference tilt and normalized rate are transported explicitly;
no selected root is differentiated and no value expansion is a premise. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

theorem polynomial_range_graph_scaled_deficit_expansion
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ a b σ α h : ℝ,
      |a| ≤ M → |b| ≤ M → |σ| ≤ M → |α| ≤ M → 0 ≤ h → h ≤ δ →
      |polynomialRangeDeficit (h, h ^ 4 * σ)
          (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * α))
          (polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b)) -
        DGPS.Circle.AngularNormalization.a0 *
          ((a ^ 2 + b ^ 2) / 12 + a * (a ^ 2 + b ^ 2) / 12 +
            (a ^ 4 + b ^ 4) / 24 - α * (a ^ 2 + b ^ 2) / 2) * h ^ 4| ≤ K * h ^ 5 := by
  obtain ⟨δP, CP, hδP, hCP, hprofile⟩ := polynomial_range_graph_finite_profile_value_error
    hU h0U hψ hψ0 hgraph hzero hfirst M hM
  obtain ⟨δF, CF, hδF, hCF, hfinite⟩ := polynomialMixedFiniteProfile_deficit_expansion M hM
  obtain ⟨δG, CG, hδG, hCG, hgap⟩ := polynomialMixedFiniteProfile_gap_expansion M hM
  obtain ⟨δS, CS, hδS, hCS, hreference⟩ := polynomialRangeDeficit_reference_value_error
  let W := fun x : ℝ × ℝ => (1 / 2 : ℝ) •
    (polynomialOriginMixedSecondCorrection x.1 x.2 : PeriodicC2_STR02969)
  have hW : Continuous W := by
    have hs : ContDiff ℝ ∞ W := by
      unfold W polynomialOriginMixedSecondCorrection polynomialOriginSecondCorrection
      fun_prop
    exact hs.continuous
  obtain ⟨BW, hBW⟩ := (isCompact_closedBall (0 : ℝ × ℝ) M).exists_bound_of_continuousOn hW.continuousOn
  let CW := max BW 0 + 1
  let CV := M * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖) + 1
  let L := CV + CW
  let Z := M + L + 1
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCW : 0 < CW := by dsimp only [CW]; positivity
  have hCV : 0 < CV := by dsimp only [CV]; positivity
  have hL : 0 < L := add_pos hCV hCW
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  let K := CP + CS * Z * M + CF + 2 * DGPS.Circle.AngularNormalization.a0 * M * CG
  have hK : 0 < K := by dsimp only [K]; positivity
  let δ := min δP (min δF (min δG (min 1 (δS / (2 * Z)))))
  have hδ : 0 < δ := lt_min hδP (lt_min hδF (lt_min hδG (lt_min zero_lt_one (div_pos hδS (by positivity)))))
  refine ⟨δ, K, hδ, hK, fun a b σ α h ha hb hσ hα hh hhδ => ?_⟩
  have hhP : h ≤ δP := hhδ.trans (min_le_left _ _)
  have hhF : h ≤ δF := hhδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhG : h ≤ δG := hhδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hh1 : h ≤ 1 := hhδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hhS : h ≤ δS / (2 * Z) := hhδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hsize : h * Z < δS := by have he := (le_div_iff₀ (by positivity : 0 < 2 * Z)).1 hhS; nlinarith
  have h2 : h ^ 2 ≤ h := by nlinarith
  have h4 : h ^ 4 ≤ h := by simpa only [pow_one] using pow_le_pow_of_le_one hh hh1 (by norm_num : 1 ≤ 4)
  let V := a • cosC2_STR02915 + b • sinC2_STR02915
  let u := polynomialMixedFiniteProfile a b h
  let S := (a ^ 2 + b ^ 2) / 12 + a * (a ^ 2 + b ^ 2) / 12 + (a ^ 4 + b ^ 4) / 24
  let F := fun s : ℝ => polynomialRangeDeficit (h, s)
    (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * α)) u
  let T := DGPS.Circle.AngularNormalization.a0 * (S - α * (a ^ 2 + b ^ 2) / 2) * h ^ 4
  have hVW : ‖W (a, b)‖ ≤ CW := by
    have hp : (a, b) ∈ Metric.closedBall (0 : ℝ × ℝ) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using max_le ha hb
    exact (hBW _ hp).trans (by dsimp only [CW]; linarith [le_max_left BW 0])
  have hV : ‖V‖ ≤ CV := by
    calc _ ≤ ‖a • cosC2_STR02915‖ + ‖b • sinC2_STR02915‖ := norm_add_le _ _
      _ ≤ M * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
        nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg cosC2_STR02915),
          mul_le_mul_of_nonneg_right hb (norm_nonneg sinC2_STR02915)]
      _ ≤ CV := by dsimp only [CV]; linarith
  have hu : ‖u‖ ≤ h * L := by
    have he : u = h • V + h ^ 2 • W (a, b) := by
      simp only [u, V, W, polynomialMixedFiniteProfile, smul_add, smul_smul]
      congr 1
      congr 1
      ring
    rw [he]
    calc _ ≤ ‖h • V‖ + ‖h ^ 2 • W (a, b)‖ := norm_add_le _ _
      _ ≤ h * CV + h ^ 2 * CW := by
        simp only [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hh]
        exact add_le_add (mul_le_mul_of_nonneg_left hV hh) (mul_le_mul_of_nonneg_left hVW (sq_nonneg h))
      _ ≤ h * L := by dsimp only [L]; nlinarith [mul_le_mul_of_nonneg_right h2 hCW.le]
  have hjoint : ‖(((h, h ^ 4 * σ), h ^ 2 * α, u) : (ℝ × ℝ) × ℝ × PeriodicC2_STR02969)‖ ≤ h * Z := by
    have hMZ : M ≤ Z := by dsimp only [Z]; linarith
    have hLZ : L ≤ Z := by dsimp only [Z]; linarith
    have hs : |h ^ 4 * σ| ≤ h * M := by
      rw [abs_mul, abs_pow, abs_of_nonneg hh]
      exact (mul_le_mul_of_nonneg_left hσ (pow_nonneg hh 4)).trans (mul_le_mul_of_nonneg_right h4 hMp.le)
    have hα' : |h ^ 2 * α| ≤ h * M := by
      rw [abs_mul, abs_pow, abs_of_nonneg hh]
      exact (mul_le_mul_of_nonneg_left hα (sq_nonneg h)).trans (mul_le_mul_of_nonneg_right h2 hMp.le)
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hh]
    exact max_le (max_le ((le_mul_of_one_le_right hh hM).trans (mul_le_mul_of_nonneg_left hMZ hh))
      (hs.trans (mul_le_mul_of_nonneg_left hMZ hh)))
      (max_le (hα'.trans (mul_le_mul_of_nonneg_left hMZ hh)) (hu.trans (mul_le_mul_of_nonneg_left hLZ hh)))
  have er := hreference h (h ^ 4 * σ) (h ^ 2 * α) u (hjoint.trans_lt hsize)
  have er' : |F (h ^ 4 * σ) - F 0| ≤ CS * Z * M * h ^ 5 := by
    calc _ ≤ CS * (h * Z) * (h ^ 4 * M) := er.trans (by
        rw [abs_mul, abs_pow, abs_of_nonneg hh]
        gcongr)
      _ = _ := by ring
  have ef := hfinite a b h ha hb hh hhF
  have eg := hgap a b h ha hb hh hhG
  have hrate : F 0 = polynomialRangeDeficit (h, 0) DGPS.Circle.AngularNormalization.a0 u -
      2 * DGPS.Circle.AngularNormalization.a0 * h ^ 2 * α * polynomialRangeGap (h, 0) u := by
    unfold F polynomialRangeDeficit
    ring
  have hid : F 0 - T =
      (polynomialRangeDeficit (h, 0) DGPS.Circle.AngularNormalization.a0 u -
        DGPS.Circle.AngularNormalization.a0 * S * h ^ 4) -
      2 * DGPS.Circle.AngularNormalization.a0 * h ^ 2 * α *
        (polynomialRangeGap (h, 0) u - (a ^ 2 + b ^ 2) / 4 * h ^ 2) := by
    rw [hrate]
    dsimp only [T]
    ring
  have ef' : |F 0 - T| ≤ (CF + 2 * DGPS.Circle.AngularNormalization.a0 * M * CG) * h ^ 5 := by
    rw [hid]
    have eb : |2 * DGPS.Circle.AngularNormalization.a0 * h ^ 2 * α *
        (polynomialRangeGap (h, 0) u - (a ^ 2 + b ^ 2) / 4 * h ^ 2)| ≤
        2 * DGPS.Circle.AngularNormalization.a0 * M * CG * h ^ 5 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * DGPS.Circle.AngularNormalization.a0),
        abs_pow, abs_of_nonneg hh]
      calc _ ≤ ((2 * DGPS.Circle.AngularNormalization.a0 * h ^ 2) * M) * (CG * h ^ 3) := by gcongr
        _ = _ := by ring
    exact (abs_sub _ _).trans ((add_le_add ef eb).trans (by ring_nf; exact le_rfl))
  have ep := hprofile a b σ α h ha hb hσ hα hh hhP
  have hid' : polynomialRangeDeficit (h, h ^ 4 * σ)
      (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * α))
      (polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b)) - T =
    (polynomialRangeDeficit (h, h ^ 4 * σ)
      (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * α))
      (polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b)) - F (h ^ 4 * σ)) +
      (F (h ^ 4 * σ) - F 0) + (F 0 - T) := by ring
  change |polynomialRangeDeficit (h, h ^ 4 * σ)
    (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * α))
    (polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b)) - T| ≤ _
  rw [hid']
  exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
    ((add_le_add (add_le_add ep er') ef').trans (by dsimp only [K]; ring_nf; exact le_rfl)))

end DGPS.Examples.PolynomialSpecies
