import DGPS.FiniteN.Tools.GroundState
import DGPS.FiniteN.Tools.IMS

open MeasureTheory Real
open scoped ContDiff

/-!
# FIN023: noncritical and far exterior Dirichlet rate

Module `DGPS.FiniteN.Tools.Exterior` (placed in a new file instead of `DGPS/FiniteN/Tools.lean`
to avoid file contention). On `ℝ^k = EuclideanSpace ℝ (Fin k)`, let `ψ` be smooth with bounded
Hessian (`‖D²ψ‖ ≤ M`), `K` a compact set with `‖∇ψ‖ ≥ c > 0` on `K`, and `‖∇ψ(w)‖ ≥ c ‖w‖` for
`‖w‖ ≥ ρ > 0`. Then there are `c' > 0` and `N₀` such that for all `N ≥ N₀` and every smooth
compactly supported `F` with `tsupport F ⊆ K ∪ {‖w‖ ≥ ρ}`,
`∫ ‖∇F‖² dη_N ≥ c' N² ∫ F² dη_N`, with `η_N ∝ e^{-Nψ}` (`imsEta N ψ`).

Proof: the ground-state identity (FIN016) turns the Dirichlet form into
`∫ |∇G|² + (N²|∇ψ|²/4 - NΔψ/2) G²`, and `|Δψ| ≤ kM` is absorbed in `N² δ/8`.
-/

namespace DGPS.FiniteN

section Exterior

variable {k : ℕ}

/-- A bounded Hessian bounds the Laplacian from above by `k M`. -/
theorem exterior_laplacian_le (ψ : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (M : ℝ)
    (hM : ∀ x, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ M) (x : EuclideanSpace ℝ (Fin k)) :
    Laplacian.laplacian ψ x ≤ k * M := by
  rw [groundState_laplacian_eq_sum_basis ψ hψ x]
  have hd : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  calc ∑ i, fderiv ℝ (fun y => fderiv ℝ ψ y (EuclideanSpace.basisFun (Fin k) ℝ i)) x
          (EuclideanSpace.basisFun (Fin k) ℝ i) ≤ ∑ _i : Fin k, M := by
        refine Finset.sum_le_sum fun i _ => ?_
        set e := EuclideanSpace.basisFun (Fin k) ℝ i
        have h1 : fderiv ℝ (fun y => fderiv ℝ ψ y e) x = (fderiv ℝ (fderiv ℝ ψ) x).flip e := by
          rw [fderiv_clm_apply (hd x) (differentiableAt_const e)]
          simp
        rw [h1]
        have h2 : ((fderiv ℝ (fderiv ℝ ψ) x).flip e) e = fderiv ℝ (fderiv ℝ ψ) x e e := rfl
        rw [h2]
        have he : ‖e‖ = 1 := by simp [e]
        calc fderiv ℝ (fderiv ℝ ψ) x e e ≤ ‖fderiv ℝ (fderiv ℝ ψ) x e e‖ := le_abs_self _
          _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) x‖ * ‖e‖ * ‖e‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
          _ ≤ M := by rw [he]; simpa using hM x
    _ = k * M := by simp

/-- Continuity of the Laplacian of a smooth function. -/
theorem exterior_continuous_laplacian (ψ : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (Laplacian.laplacian ψ) := by
  have : Laplacian.laplacian ψ = fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ ψ y
      (EuclideanSpace.basisFun (Fin k) ℝ i)) x (EuclideanSpace.basisFun (Fin k) ℝ i) :=
    funext fun x => groundState_laplacian_eq_sum_basis ψ hψ x
  rw [this]
  refine continuous_finsetSum _ fun i _ => ?_
  have hP : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y (EuclideanSpace.basisFun (Fin k) ℝ i)) :=
    (hψ.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const
  exact (hP.continuous_fderiv (by simp)).clm_apply continuous_const

/-- Unnormalized form of FIN023 (weight `e^{-Nψ}` with Lebesgue measure). -/
theorem exterior_dirichlet_rate_unnormalized (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (M : ℝ) (hM : ∀ x, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ M)
    (S : Set (EuclideanSpace ℝ (Fin k))) (δ : ℝ) (hδ : 0 < δ)
    (hS : ∀ x ∈ S, δ ≤ ‖fderiv ℝ ψ x‖ ^ 2) (N : ℝ) (hN : 0 < N)
    (hNM : 4 * (k * M) / δ ≤ N)
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
      have hlap := exterior_laplacian_le ψ hψ M hM x
      have hpb : δ / 8 * N ^ 2 ≤ pot x := by
        simp only [hpot]
        have h1 : N ^ 2 * δ / 4 ≤ N ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 / 4 := by
          have := mul_le_mul_of_nonneg_left hgrad (sq_nonneg N)
          linarith
        have h2 : N * Laplacian.laplacian ψ x / 2 ≤ N * (k * M) / 2 := by
          have := mul_le_mul_of_nonneg_left hlap hN.le
          linarith
        have h3 : N * (k * M) / 2 ≤ δ / 8 * N ^ 2 := by
          have h4 : 4 * (k * M) ≤ N * δ := by
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

/-- **FIN023** (`DGPS.FiniteN.noncritical_and_far_exterior_dirichlet_rate`). Let `ψ` be smooth on
`ℝ^k` with bounded Hessian, `K` compact with `‖∇ψ‖ ≥ c > 0` on `K`, and `‖∇ψ(w)‖ ≥ c‖w‖` for
`‖w‖ ≥ ρ > 0`. Then there are `c' > 0` and `N₀` such that for every `N ≥ N₀` and every smooth
compactly supported `F` supported in `K ∪ {‖w‖ ≥ ρ}`, the local Dirichlet rate with respect to
`η_N ∝ e^{-Nψ}` is at least `c' N²`. -/
theorem noncritical_and_far_exterior_dirichlet_rate (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (M : ℝ) (hM : ∀ x, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ M)
    (K : Set (EuclideanSpace ℝ (Fin k))) (_hK : IsCompact K) (c : ℝ) (hc : 0 < c)
    (hKc : ∀ x ∈ K, c ≤ ‖fderiv ℝ ψ x‖) (ρ : ℝ) (hρ : 0 < ρ)
    (hfar : ∀ x : EuclideanSpace ℝ (Fin k), ρ ≤ ‖x‖ → c * ‖x‖ ≤ ‖fderiv ℝ ψ x‖) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        tsupport F ⊆ K ∪ {x | ρ ≤ ‖x‖} →
        c' * N ^ 2 * ∫ x, F x ^ 2 ∂(imsEta N ψ) ≤ ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(imsEta N ψ) := by
  set δ : ℝ := c ^ 2 * min 1 (ρ ^ 2) with hδdef
  have hδ : 0 < δ := by positivity
  have hS : ∀ x ∈ K ∪ {x : EuclideanSpace ℝ (Fin k) | ρ ≤ ‖x‖}, δ ≤ ‖fderiv ℝ ψ x‖ ^ 2 := by
    intro x hx
    rcases hx with hx | hx
    · have h1 := hKc x hx
      have : c ^ 2 ≤ ‖fderiv ℝ ψ x‖ ^ 2 := pow_le_pow_left₀ hc.le h1 2
      calc δ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg c)
        _ ≤ _ := by linarith
    · have h1 := hfar x hx
      have h2 : (c * ‖x‖) ^ 2 ≤ ‖fderiv ℝ ψ x‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      have h3 : ρ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hρ.le hx 2
      calc δ ≤ c ^ 2 * ρ ^ 2 := mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg c)
        _ ≤ c ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
        _ = (c * ‖x‖) ^ 2 := by ring
        _ ≤ _ := h2
  refine ⟨δ / 8, by positivity, max 1 (4 * (k * M) / δ), fun N hN F hF hFc hFS => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hNM : 4 * (k * M) / δ ≤ N := (le_max_right _ _).trans hN
  have key := exterior_dirichlet_rate_unnormalized ψ hψ M hM _ δ hδ hS N hN0 hNM F hF hFc hFS
  -- pass from the unnormalized to the normalized measure
  set Z : ENNReal := ∫⁻ x, ENNReal.ofReal (exp (-(N * ψ x))) with hZ
  have hdens : Measurable fun x : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (exp (-(N * ψ x))) :=
    (contDiff_exp.comp (contDiff_const.mul hψ).neg).continuous.measurable.ennreal_ofReal
  have hconv : ∀ g : EuclideanSpace ℝ (Fin k) → ℝ, ∫ x, g x ∂(imsEta N ψ) =
      Z⁻¹.toReal * ∫ x, g x * exp (-(N * ψ x)) := by
    intro g
    unfold imsEta
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (exp_pos _).le]
    ring
  rw [hconv (fun x => F x ^ 2), hconv (fun x => ‖fderiv ℝ F x‖ ^ 2)]
  have hZnn : 0 ≤ Z⁻¹.toReal := ENNReal.toReal_nonneg
  calc δ / 8 * N ^ 2 * (Z⁻¹.toReal * ∫ x, F x ^ 2 * exp (-(N * ψ x)))
      = Z⁻¹.toReal * (δ / 8 * N ^ 2 * ∫ x, F x ^ 2 * exp (-(N * ψ x))) := by ring
    _ ≤ Z⁻¹.toReal * ∫ x, ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x)) :=
        mul_le_mul_of_nonneg_left key hZnn

end Exterior

end DGPS.FiniteN
