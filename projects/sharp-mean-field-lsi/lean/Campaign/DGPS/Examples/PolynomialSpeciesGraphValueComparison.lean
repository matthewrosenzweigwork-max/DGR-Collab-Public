import DGPS.Examples.PolynomialFullChartHessianControl
import DGPS.Examples.PolynomialSpeciesOriginDeficitHessian
import DGPS.Examples.PolynomialSpeciesMixedFiniteProfile

/-! Uniform actual value comparison between the concrete mixed finite profile
and the SAME implicit graph. The original full-chart Hessian, not a reduced
amplitude Hessian, supplies the first-mode kernel cancellation. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

local instance : NormedAddCommGroup (PeriodicC2_STR02969 →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (PeriodicC2_STR02969 →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (PeriodicC2_STR02969 →L[ℝ] PeriodicC2_STR02969 →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (PeriodicC2_STR02969 →L[ℝ] PeriodicC2_STR02969 →L[ℝ] ℝ) := inferInstance

private theorem kernel_tail_bound
    (H : PeriodicC2_STR02969 →L[ℝ] PeriodicC2_STR02969 →L[ℝ] ℝ)
    (u V : PeriodicC2_STR02969) (h B : ℝ) (hV : H V = 0)
    (hbound : ‖u - h • V‖ ≤ B) : ‖H u‖ ≤ ‖H‖ * B := by
  have he : H (u - h • V) = H u := by
    rw [H.map_sub, H.map_smul, hV, smul_zero, sub_zero]
  rw [← he]
  exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left hbound (norm_nonneg H))

private theorem gradient_segment_bound
    (F : PeriodicC2_STR02969 → ℝ)
    (H0 : PeriodicC2_STR02969 →L[ℝ] PeriodicC2_STR02969 →L[ℝ] ℝ)
    (p : ℝ × ℝ) (γ h M CV CW CG CH L Z D δH : ℝ)
    (V w uf ug u : PeriodicC2_STR02969)
    (hMp : 0 < M) (hh : 0 ≤ h) (h2 : h^2 ≤ h) (h3 : h^3 ≤ h^2)
    (hCW : 0 < CW) (hCG : 0 < CG) (hCH : 0 < CH) (hL : 0 < L)
    (hLdef : L = CV + CW + CG) (hZdef : Z = M + L + 1)
    (hDdef : D = ‖H0‖ * (CW + CG) + CH * Z * L)
    (hV : ‖V‖ ≤ CV) (hVW : ‖w‖ ≤ CW) (huf : uf = h • V + h^2 • w)
    (hH0V : H0 V = 0) (herror : ‖ug - uf‖ ≤ CG * h^3)
    (hparam : ‖(p,γ)‖ ≤ h*M) (hsmall : h*Z < δH)
    (hgradient : ∀ u : PeriodicC2_STR02969, ‖(p,γ,u)‖ < δH →
      ‖fderiv ℝ F u - H0 u‖ ≤ CH * ‖(p,γ,u)‖ * ‖u‖)
    (hu : u ∈ segment ℝ uf ug) : ‖fderiv ℝ F u‖ ≤ (D+1)*h^2 := by
  have hZ : 0 < Z := by rw [hZdef]; positivity
  have hnear : ‖u - uf‖ ≤ CG * h ^ 3 := (norm_sub_le_of_mem_segment hu).trans herror
  have htail : ‖u - h • V‖ ≤ (CW + CG) * h ^ 2 := by
    calc
      _ ≤ ‖u - uf‖ + ‖uf - h • V‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ CG * h ^ 3 + h ^ 2 * CW := by
        rw [huf, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hh]
        exact add_le_add (by simpa only [huf] using hnear) (mul_le_mul_of_nonneg_left hVW (sq_nonneg h))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h3 hCG.le]
  have hun : ‖u‖ ≤ h * L := by
    calc
      _ ≤ ‖u - h • V‖ + ‖h • V‖ := norm_le_norm_sub_add _ _
      _ ≤ (CW + CG) * h ^ 2 + h * CV := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        exact add_le_add htail (mul_le_mul_of_nonneg_left hV hh)
      _ ≤ h * L := by rw [hLdef]; nlinarith [mul_le_mul_of_nonneg_left h2 (add_pos hCW hCG).le]
  have hjoint : ‖(p, γ, u)‖ ≤ h * Z := by
    simp only [Prod.norm_def] at hparam ⊢
    have hp' := le_trans (le_max_left _ _) hparam
    have hg' := le_trans (le_max_right _ _) hparam
    have hMZ : M ≤ Z := by rw [hZdef]; linarith
    have hLZ : L ≤ Z := by rw [hZdef]; linarith
    exact max_le (hp'.trans (mul_le_mul_of_nonneg_left hMZ hh))
      (max_le (hg'.trans (mul_le_mul_of_nonneg_left hMZ hh))
        (hun.trans (mul_le_mul_of_nonneg_left hLZ hh)))
  have hr := hgradient u (hjoint.trans_lt hsmall)
  have hHu : ‖H0 u‖ ≤ ‖H0‖ * ((CW + CG) * h ^ 2) :=
    kernel_tail_bound H0 u V h ((CW + CG) * h ^ 2) hH0V htail
  calc
    _ ≤ ‖fderiv ℝ (F) u - H0 u‖ + ‖H0 u‖ := norm_le_norm_sub_add _ _
    _ ≤ CH * (h * Z) * (h * L) + ‖H0‖ * ((CW + CG) * h ^ 2) := by
      exact add_le_add (hr.trans (by gcongr)) hHu
    _ ≤ (D + 1) * h ^ 2 := by rw [hDdef]; nlinarith [sq_nonneg h]

theorem polynomial_range_graph_finite_profile_value_error
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
        polynomialRangeDeficit (h, h ^ 4 * σ)
          (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * α))
          (polynomialMixedFiniteProfile a b h)| ≤ K * h ^ 5 := by
  obtain ⟨δG, CG, hδG, hCG, hprofile⟩ := polynomial_range_graph_scaled_profile_remainder
    hU h0U hψ hψ0 hgraph hzero hfirst M hM
  obtain ⟨δH, CH, hδH, hCH, hgradient⟩ := polynomialRangeDeficit_full_gradient_remainder
  let W := fun x : ℝ × ℝ => (1 / 2 : ℝ) •
    (polynomialOriginMixedSecondCorrection x.1 x.2 : PeriodicC2_STR02969)
  have hW : Continuous W := by
    have hc : ContDiff ℝ ∞ W := by
      unfold W polynomialOriginMixedSecondCorrection polynomialOriginSecondCorrection
      fun_prop
    exact hc.continuous
  obtain ⟨BW, hBW⟩ := (isCompact_closedBall (0 : ℝ × ℝ) M).exists_bound_of_continuousOn hW.continuousOn
  let CW := max BW 0 + 1
  let CV := M * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖) + 1
  let L := CV + CW + CG
  let Z := M + L + 1
  let H0 : PeriodicC2_STR02969 →L[ℝ] PeriodicC2_STR02969 →L[ℝ] ℝ := polynomialRangeFullHessian 0
  let D := ‖H0‖ * (CW + CG) + CH * Z * L
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCW : 0 < CW := by dsimp only [CW]; positivity
  have hCV : 0 < CV := by dsimp only [CV]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let δ := min δG (min 1 (δH / (2 * Z)))
  have hδ : 0 < δ := lt_min hδG (lt_min zero_lt_one (div_pos hδH (by positivity)))
  refine ⟨δ, (D + 1) * CG, hδ, mul_pos (by positivity) hCG, ?_⟩
  intro a b σ α h ha hb hσ hα hh hhδ
  have hh1 : h ≤ 1 := hhδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : h * Z < δH := by
    have hs : h ≤ δH / (2 * Z) := hhδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hs' := (le_div_iff₀ (by positivity : 0 < 2 * Z)).1 hs
    nlinarith
  have h2 : h ^ 2 ≤ h := by nlinarith
  have h3 : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh hh1 (by norm_num)
  have h4 : h ^ 4 ≤ h := by
    simpa only [pow_one] using pow_le_pow_of_le_one hh hh1 (by norm_num : 1 ≤ 4)
  let V := a • cosC2_STR02915 + b • sinC2_STR02915
  let uf := polynomialMixedFiniteProfile a b h
  let ug := polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b)
  let p : ℝ × ℝ := (h, h ^ 4 * σ)
  let γ := h ^ 2 * α
  have hVW : ‖W (a, b)‖ ≤ CW := by
    have hm : (a, b) ∈ Metric.closedBall (0 : ℝ × ℝ) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using max_le ha hb
    exact (hBW _ hm).trans (by dsimp only [CW]; linarith [le_max_left BW 0])
  have hV : ‖V‖ ≤ CV := by
    calc
      _ ≤ ‖a • cosC2_STR02915‖ + ‖b • sinC2_STR02915‖ := norm_add_le _ _
      _ ≤ M * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
        nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg cosC2_STR02915),
          mul_le_mul_of_nonneg_right hb (norm_nonneg sinC2_STR02915)]
      _ ≤ CV := by dsimp only [CV]; linarith
  have huf : uf = h • V + h ^ 2 • W (a, b) := by
    simp only [uf, V, W, polynomialMixedFiniteProfile, smul_add, smul_smul]
    congr 1
    congr 1
    ring
  obtain ⟨_, herror⟩ := hprofile a b σ α h ha hb hσ hα hh (hhδ.trans (min_le_left _ _))
  have hH0V : H0 V = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    simpa only [H0, polynomialRangeFullHessian, Prod.fst_zero, Prod.snd_zero,
      zero_add, add_zero, mul_one, V, zero_apply, (show (0 : ℝ × ℝ) = (0,0) from rfl)] using polynomialRangeDeficit_first_amplitude_hessian_zero a b w
  have hparam : ‖(p, γ)‖ ≤ h * M := by
    simp only [p, γ, Prod.norm_def, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hh]
    apply max_le
    · exact max_le (le_mul_of_one_le_right hh hM)
        ((mul_le_mul_of_nonneg_left hσ (pow_nonneg hh 4)).trans
          (mul_le_mul_of_nonneg_right h4 hMp.le))
    · exact (mul_le_mul_of_nonneg_left hα (sq_nonneg h)).trans
        (mul_le_mul_of_nonneg_right h2 hMp.le)
  have hdf (u : PeriodicC2_STR02969) (hu : u ∈ segment ℝ uf ug) :
      ‖fderiv ℝ (polynomialRangeDeficit p
        (DGPS.Circle.AngularNormalization.a0 * (1 + γ))) u‖ ≤ (D + 1) * h ^ 2 := by
    exact gradient_segment_bound _ H0 p γ h M CV CW CG CH L Z D δH
      V (W (a,b)) uf ug u hMp hh h2 h3 hCW hCG hCH hL rfl rfl rfl
      hV hVW huf hH0V herror hparam hsmall (hgradient p γ) hu
  have hs : ContDiff ℝ ∞ (polynomialRangeDeficit p
      (DGPS.Circle.AngularNormalization.a0 * (1 + γ))) := by
    have hi : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => ((p, DGPS.Circle.AngularNormalization.a0 * (1 + γ), u) : PolynomialEulerInput)) :=
      contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    have ht := polynomialRangeDeficit_smooth.comp hi
    exact ht
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hs.differentiable (by simp) u) hdf (convex_segment (𝕜 := ℝ) uf ug)
    (left_mem_segment ℝ uf ug) (right_mem_segment ℝ uf ug)
  rw [Real.norm_eq_abs] at hm
  have hmul := mul_le_mul_of_nonneg_left herror (mul_nonneg (by positivity : 0 ≤ D + 1) (sq_nonneg h))
  exact hm.trans (hmul.trans_eq (by ring))

end DGPS.Examples.PolynomialSpecies
