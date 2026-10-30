import DGPS.FiniteN.AnisotropicQuarticExteriorGeometry

/-!
# Actual quartic exterior Dirichlet bounds

The private ground-state argument is the proof of Tools.Exterior's unnormalized
exterior estimate, with its used Laplacian upper bound supplied directly. The actual
quartic covariance identity supplies that bound, so no full Hessian bound is assumed.
-/

open MeasureTheory Real Set
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff ENNReal

namespace DGPS.FiniteN

private theorem laplacian_exterior_lower {k : ℕ}
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (M : ℝ)
    (hM : ∀ x, Laplacian.laplacian ψ x ≤ M)
    (S : Set (EuclideanSpace ℝ (Fin k))) (δ : ℝ) (hδ : 0 < δ)
    (hS : ∀ x ∈ S, δ ≤ ‖fderiv ℝ ψ x‖ ^ 2) (N : ℝ) (hN : 0 < N)
    (hNM : 4 * M / δ ≤ N)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFS : tsupport F ⊆ S) :
    δ / 8 * N ^ 2 * ∫ x, F x ^ 2 * exp (-(N * ψ x)) ≤
      ∫ x, ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x)) := by
  rw [ground_state_weighted_energy_identity_euclidean N ψ F hψ hF hFc]
  set G : EuclideanSpace ℝ (Fin k) → ℝ := fun y => F y * exp (-(N * ψ y) / 2) with hG
  set pot : EuclideanSpace ℝ (Fin k) → ℝ := fun x =>
    N ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 / 4 - N * Laplacian.laplacian ψ x / 2 with hpot
  have hEc : ContDiff ℝ ∞ (fun y => exp (-(N * ψ y) / 2)) :=
    contDiff_exp.comp (((contDiff_const.mul hψ).neg).div_const 2)
  have hGs : ContDiff ℝ ∞ G := hF.mul hEc
  have hGc : HasCompactSupport G := hFc.mul_right
  have hpotc : Continuous pot := by
    refine Continuous.sub ?_ ?_
    · exact ((continuous_const.mul ((hψ.continuous_fderiv (by simp)).norm.pow 2))).div_const 4
    · exact (continuous_const.mul (exterior_continuous_laplacian ψ hψ)).div_const 2
  have hGsq : ∀ x, G x ^ 2 = F x ^ 2 * exp (-(N * ψ x)) := by
    intro x
    simp only [hG]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  -- the right-hand integrand and its compact support
  set I : EuclideanSpace ℝ (Fin k) → ℝ := fun x => ‖fderiv ℝ G x‖ ^ 2 + pot x * (F x * exp (-(N * ψ x) / 2)) ^ 2
    with hI
  have hIc : Continuous I := by
    refine Continuous.add ((hGs.continuous_fderiv (by simp)).norm.pow 2) ?_
    exact hpotc.mul (hGs.continuous.pow 2)
  have hIcs : HasCompactSupport I := by
    refine HasCompactSupport.intro hGc.isCompact fun x hx => ?_
    have hx' : x ∉ tsupport G := hx
    have h0 : G x = 0 := image_eq_zero_of_notMem_tsupport hx'
    have h1 : fderiv ℝ G x = 0 := by
      have : G =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        have := (notMem_tsupport_iff_eventuallyEq.mp hx')
        exact this
      rw [this.fderiv_eq]; simp
    simp only [hI, h1]
    have : F x * exp (-(N * ψ x) / 2) = 0 := h0
    rw [this]; simp
  have hIint : Integrable I := hIc.integrable_of_hasCompactSupport hIcs
  have hLc : Continuous fun x => F x ^ 2 * exp (-(N * ψ x)) :=
    (hF.continuous.pow 2).mul (contDiff_exp.comp (contDiff_const.mul hψ).neg).continuous
  have hLcs : HasCompactSupport fun x => F x ^ 2 * exp (-(N * ψ x)) := by
    have h2 : HasCompactSupport fun x => F x ^ 2 :=
      hFc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact h2.mul_right
  have hLint : Integrable fun x => F x ^ 2 * exp (-(N * ψ x)) :=
    hLc.integrable_of_hasCompactSupport hLcs
  have hpoint : ∀ x, δ / 8 * N ^ 2 * (F x ^ 2 * exp (-(N * ψ x))) ≤ I x := by
    intro x
    by_cases hx : F x = 0
    · simp [hI, hx]
    · have hxS : x ∈ S := hFS (subset_tsupport F hx)
      have hgrad := hS x hxS
      have hlap := hM x
      have hpb : δ / 8 * N ^ 2 ≤ pot x := by
        simp only [hpot]
        have h1 : N ^ 2 * δ / 4 ≤ N ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 / 4 := by
          have := mul_le_mul_of_nonneg_left hgrad (sq_nonneg N)
          linarith
        have h2 : N * Laplacian.laplacian ψ x / 2 ≤ N * (M) / 2 := by
          have := mul_le_mul_of_nonneg_left hlap hN.le
          linarith
        have h3 : N * (M) / 2 ≤ δ / 8 * N ^ 2 := by
          have h4 : 4 * (M) ≤ N * δ := by
            rwa [div_le_iff₀ hδ] at hNM
          have := mul_le_mul_of_nonneg_left h4 hN.le
          nlinarith
        nlinarith
      have hsq : (F x * exp (-(N * ψ x) / 2)) ^ 2 = F x ^ 2 * exp (-(N * ψ x)) := hGsq x
      simp only [hI]
      rw [hsq]
      have : δ / 8 * N ^ 2 * (F x ^ 2 * exp (-(N * ψ x))) ≤
          pot x * (F x ^ 2 * exp (-(N * ψ x))) :=
        mul_le_mul_of_nonneg_right hpb (by positivity)
      have h0 : 0 ≤ ‖fderiv ℝ G x‖ ^ 2 := by positivity
      linarith
  calc δ / 8 * N ^ 2 * ∫ x, F x ^ 2 * exp (-(N * ψ x))
      = ∫ x, δ / 8 * N ^ 2 * (F x ^ 2 * exp (-(N * ψ x))) := by rw [integral_const_mul]
    _ ≤ ∫ x, I x := integral_mono (hLint.const_mul _) hIint hpoint

/-- An actual gradient-level region has a quadratic-in-N Dirichlet lower rate.
The region is defined by the actual derivative, with no assumed spectral inequality. -/
theorem quartic_gradient_level_dirichlet (δ : ℝ) (hδ : 0 < δ) :
    ∃ a : ℝ, 0 < a ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        tsupport F ⊆ {w | δ ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖} →
          a * N ^ 2 * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
            ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
  let M := 1 / Models.quarticKappa + 1 / (Models.quarticKappa * Models.quarticEta)
  let N0 := max 1 (4 * M / δ ^ 2)
  refine ⟨δ ^ 2 / 8, by positivity, N0, le_max_left _ _, fun N hN F hF hFc hFS => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  letI := quartic_imsEta_probability N hNpos
  have hNM : 4 * M / δ ^ 2 ≤ N := (le_max_right _ _).trans hN
  have hS : ∀ w ∈ {w | δ ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖},
      δ ^ 2 ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖ ^ 2 :=
    fun w hw => pow_le_pow_left₀ hδ.le hw 2
  have h := laplacian_exterior_lower quarticPsi_FIN066 quartic_potential_contDiff M
    quartic_laplacian_upper _ (δ ^ 2) (sq_pos_of_pos hδ) hS N hNpos hNM F hF hFc hFS
  rw [TiltedXY.Fin049.imsEta_integral_FIN049 N quarticPsi_FIN066 quartic_potential_contDiff,
    TiltedXY.Fin049.imsEta_integral_FIN049 N quarticPsi_FIN066 quartic_potential_contDiff]
  have hz : 0 ≤ (∫⁻ w, ENNReal.ofReal (exp (-(N * quarticPsi_FIN066 w))))⁻¹.toReal :=
    ENNReal.toReal_nonneg
  have hh := mul_le_mul_of_nonneg_left h hz
  convert hh using 1 <;> ring

/-- Actual far exterior estimate with all constants and the radius fixed before N. -/
theorem quartic_far_exterior_dirichlet :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ a : ℝ, 0 < a ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧
      ∀ N : ℝ, N0 ≤ N → ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ {w | ρ ≤ ‖w‖} →
          a * N ^ 2 * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
            ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
  obtain ⟨ρ, hρ, c, hc, hfar⟩ := quartic_gradient_far_bound
  obtain ⟨a, ha, N0, hN0, hlevel⟩ := quartic_gradient_level_dirichlet (c * ρ) (mul_pos hc hρ)
  refine ⟨ρ, hρ, a, ha, N0, hN0, fun N hN F hF hFc hFS =>
    hlevel N hN F hF hFc fun w hw => ?_⟩
  exact (mul_le_mul_of_nonneg_left (hFS hw) hc.le).trans (hfar w (hFS hw))

end DGPS.FiniteN
