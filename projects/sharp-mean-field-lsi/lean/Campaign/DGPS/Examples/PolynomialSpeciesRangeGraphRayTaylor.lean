import DGPS.Examples.PolynomialSpeciesRangeGraphMixedCoefficient
import Mathlib.Analysis.Calculus.Taylor

/-! Uniform cubic remainder for the actual graph on mixed field/amplitude
rays. The constants precede every bounded amplitude coefficient and every
small nonnegative field. This uses the stock vector-valued Taylor estimate. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

local instance (n : ℕ) : NormedAddCommGroup (PolynomialRangeParameters [×n]→L[ℝ] E_STR02969) := inferInstance
local instance (n : ℕ) : NormedSpace ℝ (PolynomialRangeParameters [×n]→L[ℝ] E_STR02969) := inferInstance

private theorem line_iteratedDeriv {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (d : PolynomialRangeParameters) (t : ℝ)
    (ht : t • d ∈ U) (n : ℕ) :
    iteratedDeriv n (fun z : ℝ => ψ (z • d)) t =
      iteratedFDeriv ℝ n ψ (t • d) (fun _ => d) := by
  let L : ℝ →L[ℝ] PolynomialRangeParameters :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight d
  have hV : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hψ hU.uniqueDiffOn hV.uniqueDiffOn ht
    (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hV ht,
    iteratedFDerivWithin_of_isOpen n hU (show L t ∈ U from ht)] at he
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ n (ψ ∘ L) t) (fun _ => 1) = _
  rw [he]
  simp [L]

/-- On a bounded coefficient box, the actual SAME graph has the mixed second
jet with a uniform cubic remainder. The second-jet identity is derived from
the true moving-reference Euler forcing, not included as an input. -/
theorem polynomial_range_graph_mixed_ray_remainder
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ a b h : ℝ, |a| ≤ M → |b| ≤ M → 0 ≤ h → h ≤ δ →
        h • ((a, b, (1, 0), 0) : PolynomialRangeParameters) ∈ U ∧
        ‖ψ (h • ((a, b, (1, 0), 0) : PolynomialRangeParameters)) -
          (h ^ 2 / 2) • polynomialOriginMixedSecondCorrection a b‖ ≤ K * h ^ 3 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds h0U)
  let ρ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hclosed : Metric.closedBall (0 : PolynomialRangeParameters) ρ ⊆ U := by
    intro p hp
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    have hp' : ‖p‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
    exact hp'.trans_lt (by dsimp [ρ]; linarith)
  have hcont : ContinuousOn (iteratedFDeriv ℝ 3 ψ)
      (Metric.closedBall (0 : PolynomialRangeParameters) ρ) := by
    have hc := hψ.continuousOn_iteratedFDerivWithin (m := 3) (by simp) hU.uniqueDiffOn
    exact (hc.congr (fun p hp => (iteratedFDerivWithin_of_isOpen 3 hU hp).symm)).mono hclosed
  obtain ⟨B, hBraw⟩ := (isCompact_closedBall (0 : PolynomialRangeParameters) ρ).exists_bound_of_continuousOn hcont.norm
  have hB : ∀ p ∈ Metric.closedBall (0 : PolynomialRangeParameters) ρ, ‖iteratedFDeriv ℝ 3 ψ p‖ ≤ B := by
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hBraw p hp
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ρ / M
  have hδ : 0 < δ := div_pos hρ (lt_of_lt_of_le zero_lt_one hM)
  refine ⟨δ, C * M ^ 3, hδ, mul_pos hC (pow_pos (lt_of_lt_of_le zero_lt_one hM) _), ?_⟩
  intro a b h ha hb hh hhδ
  let d : PolynomialRangeParameters := (a, b, (1, 0), 0)
  let F := fun t : ℝ => ψ (t • d)
  have hd : ‖d‖ ≤ M := by
    simp only [d, Prod.norm_def, Real.norm_eq_abs, abs_one, norm_zero, max_eq_left zero_le_one]
    exact max_le ha (max_le hb hM)
  have hpath : ∀ t ∈ Set.Icc (0 : ℝ) δ,
      t • d ∈ Metric.closedBall (0 : PolynomialRangeParameters) ρ := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      t * ‖d‖ ≤ δ * M := mul_le_mul ht.2 hd (norm_nonneg _) hδ.le
      _ = ρ := by dsimp [δ]; field_simp
  have hFs : ∀ t ∈ Set.Icc (0 : ℝ) δ, ContDiffAt ℝ ∞ F t := by
    intro t ht
    exact (hψ.contDiffAt (hU.mem_nhds (hclosed (hpath t ht)))).comp t
      (contDiff_id.smul contDiff_const).contDiffAt
  have hF0 : F 0 = 0 := by simp only [F, zero_smul, hψ0]
  have hF1 : deriv F 0 = 0 := by
    have hD := polynomial_range_graph_full_derivative_zero hU h0U hψ hzero hfirst
    have hp : HasDerivAt (fun t : ℝ => t • d) d 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const d
    have he := ((hψ.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
      (0 : ℝ) hp (by simp)
    change HasDerivAt F _ 0 at he
    simpa only [hD, zero_apply] using he.deriv
  have hF2 : iteratedDeriv 2 F 0 = polynomialOriginMixedSecondCorrection a b :=
    polynomial_range_graph_mixed_second_coefficient hU h0U hψ hψ0 hgraph hfirst hzero a b
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) δ,
      ‖iteratedDerivWithin 3 F (Set.Icc (0 : ℝ) δ) t‖ ≤ C * M ^ 3 := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hδ)
      ((hFs t ht).of_le (by simp)) ht,
      line_iteratedDeriv hU hψ d t (hclosed (hpath t ht)) 3]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 3 ψ (t • d)‖ * ∏ _ : Fin 3, ‖d‖ :=
        (iteratedFDeriv ℝ 3 ψ (t • d)).le_opNorm _
      _ ≤ C * M ^ 3 := by
        have hbnd : ‖iteratedFDeriv ℝ 3 ψ (t • d)‖ ≤ C :=
          (hB _ (hpath t ht)).trans (by dsimp [C]; linarith [le_max_left B 0])
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul hbnd (pow_le_pow_left₀ (norm_nonneg _) hd 3) (by positivity) hC.le
  have hTaylor := taylor_mean_remainder_bound (n := 2) hδ.le
    (fun t ht => (hFs t ht).contDiffWithinAt.of_le (by simp)) ⟨hh, hhδ⟩ hbound
  have hcoeff : taylorWithinEval F 2 (Set.Icc (0 : ℝ) δ) 0 h =
      (h ^ 2 / 2) • polynomialOriginMixedSecondCorrection a b := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hδ)
      ((hFs 0 ⟨le_rfl, hδ.le⟩).of_le (by simp)) ⟨le_rfl, hδ.le⟩,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hδ)
      ((hFs 0 ⟨le_rfl, hδ.le⟩).of_le (by simp)) ⟨le_rfl, hδ.le⟩]
    simp only [iteratedDeriv_one, hF0, hF1, hF2, zero_smul, zero_add, sub_zero]
    congr 1
    norm_num
    ring
  refine ⟨hclosed (hpath h ⟨hh, hhδ⟩), ?_⟩
  rw [hcoeff] at hTaylor
  change ‖F h - (h ^ 2 / 2) • polynomialOriginMixedSecondCorrection a b‖ ≤ _
  exact hTaylor.trans (by norm_num; nlinarith [mul_nonneg hC.le (pow_nonneg (lt_of_lt_of_le zero_lt_one hM).le 3), pow_nonneg hh 3])

end DGPS.Examples.PolynomialSpecies
