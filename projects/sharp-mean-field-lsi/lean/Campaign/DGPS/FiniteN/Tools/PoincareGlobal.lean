import DGPS.FiniteN.Tools.ConditionalPoincareMain
import DGPS.FiniteN.Tools.ConditionalPoincare
import DGPS.FiniteN.Tools.IMS
import DGPS.FiniteN.Tools.GroundState

/-!
# FIN024: auxiliary Poincare globalization with the mean

Module `DGPS.FiniteN.Tools.PoincareGlobal` (placed in a new file instead of
`DGPS/FiniteN/Tools.lean` to avoid file contention).

On `ℝ^k = EuclideanSpace ℝ (Fin k)` let `χ : Option (Fin m) → ℝ^k → ℝ` be a smooth quadratic
partition of unity (the output shape of FIN020), with `χ (some j)` supported in the patch `U j`,
`χ none` supported in the exterior set `X`, and `∑ ‖∇χ_i‖² ≤ C` (the fixed IMS error).
Assume
* the minimum patch `U j₀ = ball w0 r` carries the strong convexity hypothesis of FIN021
  (`D²ψ ≥ c₁ I`), a mass lower bound, and the exponentially small mass of `{χ_{j₀} ≠ 1}`; the
  FIN021 cutoff estimate (with the mean correction) is then *taken from*
  `conditional_minimum_neighborhood_poincare`;
* every other patch has Dirichlet rate `≥ c N^α` (`0 < α ≤ 1`) on smooth compactly supported
  test functions supported in it, and the exterior has rate `≥ c N²` (the form delivered by
  FIN023, `noncritical_and_far_exterior_dirichlet_rate`).
Then there are `c' > 0`, `N₀` such that for `N ≥ N₀` and every smooth compactly supported `F`
with `∫ F dη_N = 0`: `c' N^α ∫ F² dη_N ≤ ∫ ‖∇F‖² dη_N`, where `η_N = imsEta N ψ`.
-/

namespace DGPS.FiniteN

open MeasureTheory ProbabilityTheory Set Metric Real
open DGPS.FiniteN.Tools.ConditionalPoincareMain
open scoped ContDiff

/-- A continuous compactly supported real function has a square integrable against any finite
measure. -/
theorem poincareGlobal_integrable_sq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {g : E → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => g x ^ 2) μ := by
  refine Continuous.integrable_of_hasCompactSupport (hg.pow 2) ?_
  have h := hgc.mul_left (f := g)
  rw [show (fun x => g x ^ 2) = g * g from by ext x; simp [sq]]
  exact h

theorem auxiliary_poincare_globalization_with_the_mean {k m : ℕ}
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (U : Fin m → Set (EuclideanSpace ℝ (Fin k))) (X : Set (EuclideanSpace ℝ (Fin k)))
    (j₀ : Fin m) (χ : Option (Fin m) → EuclideanSpace ℝ (Fin k) → ℝ) (C : ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hsum : ∀ x, ∑ i, χ i x ^ 2 = 1)
    (hC : ∀ x, ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 ≤ C)
    (hU : ∀ j, tsupport (χ (some j)) ⊆ U j) (hX : tsupport (χ none) ⊆ X)
    -- the minimum patch (FIN021 data)
    (w0 : EuclideanSpace ℝ (Fin k)) (r c₁ : ℝ) (hc₁ : 0 < c₁) (hU₀ : U j₀ = ball w0 r)
    (hess : ∀ x ∈ ball w0 r, ∀ v, c₁ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ ψ) x v v)
    (hχ0 : ∀ x, 0 ≤ χ (some j₀) x) (N₁ A b m₀ : ℝ) (hb : 0 < b) (hm₀ : 0 < m₀)
    (hmass : ∀ N : ℝ, N₁ ≤ N → m₀ ≤ (imsEta N ψ (ball w0 r)).toReal)
    (hout : ∀ N : ℝ, N₁ ≤ N →
      (imsEta N ψ {x | χ (some j₀) x ≠ 1}).toReal ≤ A * Real.exp (-(b * N)))
    -- the other patches and the exterior
    (α c : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c)
    (hother : ∀ j, j ≠ j₀ → ∀ N : ℝ, N₁ ≤ N → ∀ G : EuclideanSpace ℝ (Fin k) → ℝ,
      ContDiff ℝ ∞ G → HasCompactSupport G → tsupport G ⊆ U j →
      c * N ^ α * ∫ x, G x ^ 2 ∂(imsEta N ψ) ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(imsEta N ψ))
    (hext : ∀ N : ℝ, N₁ ≤ N → ∀ G : EuclideanSpace ℝ (Fin k) → ℝ,
      ContDiff ℝ ∞ G → HasCompactSupport G → tsupport G ⊆ X →
      c * N ^ 2 * ∫ x, G x ^ 2 ∂(imsEta N ψ) ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(imsEta N ψ)) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        ∫ x, F x ∂(imsEta N ψ) = 0 →
        c' * N ^ α * ∫ x, F x ^ 2 ∂(imsEta N ψ) ≤ ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(imsEta N ψ) := by
  classical
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun i _ => sq_nonneg _).trans (hC 0)
  set cm : ℝ := min c c₁ with hcm
  have hcm0 : 0 < cm := lt_min hc hc₁
  set K : ℝ := c₁ * |A| / m₀ / b with hK
  have hK0 : 0 ≤ K := by positivity
  set T : ℝ := (2 * (K + C + 1) / cm) ^ (1 / α) with hT
  refine ⟨cm / 2, by positivity, max (max N₁ 1) T, fun N hN F hF hFc hF0 => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN1' : 1 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNT : T ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 ≤ N := by linarith
  have := imsEta_finite N ψ
  set μ := imsEta N ψ with hμ
  -- power comparisons
  have hpa1 : N ^ α ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1' hα1
  rw [Real.rpow_one] at hpa1
  have hpa2 : N ^ α ≤ N ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  rw [Real.rpow_two] at hpa2
  have hNα : 2 * (K + C + 1) / cm ≤ N ^ α := by
    have h1 : T ^ α ≤ N ^ α := Real.rpow_le_rpow (by positivity) hNT hα0.le
    have h2 : T ^ α = 2 * (K + C + 1) / cm := by
      rw [hT, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hα0.ne', Real.rpow_one]
    linarith
  have hNαpos : 0 ≤ N ^ α := Real.rpow_nonneg hN0 _
  -- integrability
  have hFcont : Continuous F := hF.continuous
  have hdF : Continuous fun x => fderiv ℝ F x := hF.continuous_fderiv (by simp)
  have hF2i : Integrable (fun x => F x ^ 2) μ := poincareGlobal_integrable_sq μ hFcont hFc
  have hFdc : HasCompactSupport fun x => fderiv ℝ F x := hFc.fderiv ℝ
  have hFdi : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) μ := by
    have := poincareGlobal_integrable_sq μ hdF.norm hFdc.norm
    simpa using this
  -- IMS identity
  obtain ⟨hIMS, hIMS2⟩ := ims_integral_identity χ hχ hsum C hC μ F
    (hF.of_le (by exact_mod_cast le_top)) hFdi hF2i
  -- localized functions
  have hG : ∀ i, ContDiff ℝ ∞ (fun y => χ i y * F y) := fun i => (hχ i).mul hF
  have hGc : ∀ i, HasCompactSupport (fun y => χ i y * F y) := fun i => hFc.mul_left
  have hGi : ∀ i, Integrable (fun x => (χ i x * F x) ^ 2) μ := fun i =>
    poincareGlobal_integrable_sq μ ((hχ i).continuous.mul hFcont) (hGc i)
  have hGsum : ∑ i, ∫ x, (χ i x * F x) ^ 2 ∂μ = ∫ x, F x ^ 2 ∂μ := by
    rw [← integral_finsetSum _ fun i _ => hGi i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_pow, ← Finset.sum_mul, hsum x, one_mul]
  -- the mean correction of the minimum patch
  set κ : ℝ := c₁ * A / m₀ * N * Real.exp (-(b * N)) * ∫ x, F x ^ 2 ∂μ with hκ
  have hI0 : 0 ≤ ∫ x, F x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hκK : κ ≤ K * ∫ x, F x ^ 2 ∂μ := by
    have hexp : N * Real.exp (-(b * N)) ≤ 1 / b := by
      have h1 : b * N + 1 ≤ Real.exp (b * N) := Real.add_one_le_exp _
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hb]
      nlinarith
    have hA : c₁ * A / m₀ ≤ c₁ * |A| / m₀ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self A) hc₁.le) hm₀.le
    have hAnn : 0 ≤ c₁ * |A| / m₀ := by positivity
    calc κ = (c₁ * A / m₀) * (N * Real.exp (-(b * N))) * ∫ x, F x ^ 2 ∂μ := by rw [hκ]; ring
      _ ≤ (c₁ * |A| / m₀) * (1 / b) * ∫ x, F x ^ 2 ∂μ := by
          refine mul_le_mul_of_nonneg_right ?_ hI0
          calc (c₁ * A / m₀) * (N * Real.exp (-(b * N)))
              ≤ (c₁ * |A| / m₀) * (N * Real.exp (-(b * N))) :=
                mul_le_mul_of_nonneg_right hA (by positivity)
            _ ≤ (c₁ * |A| / m₀) * (1 / b) := mul_le_mul_of_nonneg_left hexp hAnn
      _ = K * ∫ x, F x ^ 2 ∂μ := by rw [hK]; ring
  -- the FIN021 estimate for the minimum patch
  obtain ⟨-, hmin⟩ := conditional_minimum_neighborhood_poincare ψ hψ2 w0 r c₁ hc₁ hess
  have hbound : ∀ x, ‖fderiv ℝ (χ (some j₀)) x‖ ≤ C + 1 := by
    intro x
    have h1 : ‖fderiv ℝ (χ (some j₀)) x‖ ^ 2 ≤ C :=
      (Finset.single_le_sum (f := fun i => ‖fderiv ℝ (χ i) x‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ (some j₀))).trans (hC x)
    nlinarith [norm_nonneg (fderiv ℝ (χ (some j₀)) x)]
  have hmin' := hmin (χ (some j₀)) ((hχ _).of_le (by exact_mod_cast le_top)) hχ0
    (fun x => by
      have := (Finset.single_le_sum (f := fun i => χ i x ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ (some j₀))).trans (hsum x).le
      nlinarith [hχ0 x])
    (fun x hx => by
      by_contra h
      exact hx (hU₀ ▸ hU j₀ (subset_tsupport _ h)))
    (C + 1) hbound A b m₀ hm₀ N hN0 (hmass N hN1) (hout N hN1) F
    (hF.of_le (by exact_mod_cast le_top)) hF2i hFdi hF0
  -- per-patch lower bounds
  have hper : ∀ i, cm * N ^ α * ∫ x, (χ i x * F x) ^ 2 ∂μ -
      (if i = some j₀ then κ else 0) ≤ ∫ x, ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2 ∂μ := by
    intro i
    have hIi : 0 ≤ ∫ x, (χ i x * F x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hcmN : cm * N ^ α ≤ c * N ^ α := mul_le_mul_of_nonneg_right (min_le_left _ _) hNαpos
    have hsupp : tsupport (fun y => χ i y * F y) ⊆ tsupport (χ i) := tsupport_mul_subset_left
    rcases i with _ | j
    · have h := hext N hN1 _ (hG none) (hGc none) (hsupp.trans hX)
      simp only [reduceCtorEq, ite_false, sub_zero]
      calc cm * N ^ α * ∫ x, (χ none x * F x) ^ 2 ∂μ
          ≤ c * N ^ 2 * ∫ x, (χ none x * F x) ^ 2 ∂μ := by
            refine mul_le_mul_of_nonneg_right ?_ hIi
            calc cm * N ^ α ≤ c * N ^ α := hcmN
              _ ≤ c * N ^ 2 := mul_le_mul_of_nonneg_left hpa2 hc.le
        _ ≤ _ := h
    · by_cases hj : j = j₀
      · subst hj
        simp only [ite_true]
        calc cm * N ^ α * ∫ x, (χ (some j) x * F x) ^ 2 ∂μ - κ
            ≤ c₁ * N * ∫ x, (χ (some j) x * F x) ^ 2 ∂μ - κ := by
              have : cm * N ^ α ≤ c₁ * N :=
                (mul_le_mul_of_nonneg_right (min_le_right _ _) hNαpos).trans
                  (mul_le_mul_of_nonneg_left hpa1 hc₁.le)
              linarith [mul_le_mul_of_nonneg_right this hIi]
          _ ≤ _ := by rw [hκ]; exact hmin'
      · have h := hother j hj N hN1 _ (hG _) (hGc _) (hsupp.trans (hU j))
        simp only [Option.some.injEq, hj, ite_false, sub_zero]
        exact (mul_le_mul_of_nonneg_right hcmN hIi).trans h
  -- sum
  have hsumper : cm * N ^ α * ∫ x, F x ^ 2 ∂μ - κ ≤
      ∑ i, ∫ x, ‖fderiv ℝ (fun y => χ i y * F y) x‖ ^ 2 ∂μ := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hGsum, Finset.sum_ite_eq' Finset.univ
      (some j₀) (fun _ => κ)] at this
    simpa using this
  rw [hIMS] at hsumper
  have hfin : cm * N ^ α * ∫ x, F x ^ 2 ∂μ - κ - C * ∫ x, F x ^ 2 ∂μ ≤
      ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ := by linarith
  have hlow : cm / 2 * N ^ α ≤ cm * N ^ α - K - C := by
    have : 2 * (K + C + 1) ≤ cm * N ^ α := by
      have := mul_le_mul_of_nonneg_left hNα hcm0.le
      rwa [mul_div_cancel₀ _ hcm0.ne'] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hlow hI0]

end DGPS.FiniteN
