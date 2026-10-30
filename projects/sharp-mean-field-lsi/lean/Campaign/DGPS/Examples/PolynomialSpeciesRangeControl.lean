import DGPS.Examples.PolynomialSpeciesRangeDerivative

/-! Quantitative amplitude control of the actual interacting range graph and entry
of the frozen selected root into its neighborhood. No smoothness of that root is assumed. -/

noncomputable section
open Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- The actual selected root tends to zero by its proved sixth-order estimate. -/
theorem polynomial_selected_root_tendsto : Tendsto root_EX054 (𝓝 (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := abs_root_le_sixth_EX054
  have hsmall : ∀ᶠ h : ℝ in 𝓝 0, |h| < δ := by
    have hAbs : Tendsto (fun h : ℝ => |h|) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (show Continuous (fun h : ℝ => |h|) from continuous_abs).tendsto (0 : ℝ)
    exact hAbs.eventually (gt_mem_nhds hδ)
  have hbound : Tendsto (fun h : ℝ => C * h ^ 6) (𝓝 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).pow 6).const_mul C
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hsmall] with h hh
  rw [Real.norm_eq_abs]
  exact hb h hh.le

/-- The frozen actual parameters enter every neighborhood of the independent-chart origin.
This uses only continuity at zero supplied by the actual root estimate. -/
theorem polynomial_selected_parameters_tendsto :
    Tendsto (fun x : ℝ × ℝ × ℝ × ℝ =>
      ((x.1, x.2.1, (x.2.2.1, root_EX054 x.2.2.1), x.2.2.2) : PolynomialRangeParameters))
      (𝓝 0) (𝓝 0) := by
  have ha : Tendsto (fun x : ℝ × ℝ × ℝ × ℝ => x.1) (𝓝 0) (𝓝 0) :=
    (show Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.1) by fun_prop).tendsto 0
  have hb : Tendsto (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) (𝓝 0) (𝓝 0) :=
    (show Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) by fun_prop).tendsto 0
  have hh : Tendsto (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.1) (𝓝 0) (𝓝 0) :=
    (show Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.1) by fun_prop).tendsto 0
  have hγ : Tendsto (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.2) (𝓝 0) (𝓝 0) :=
    (show Continuous (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.2) by fun_prop).tendsto 0
  have ht := ha.prodMk_nhds (hb.prodMk_nhds
    ((hh.prodMk_nhds (polynomial_selected_root_tendsto.comp hh)).prodMk_nhds hγ))
  rw [show ((0, 0, (0, 0), 0) : PolynomialRangeParameters) = 0 by ext <;> rfl] at ht
  exact ht

/-- The concrete graph is bounded by its first-harmonic amplitude uniformly in all small
independent field, tilt and rate parameters. The same graph accepts the frozen actual root. -/
theorem exists_polynomial_range_graph_amplitude_bound :
    ∃ (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
      (ψ : PolynomialRangeParameters → E_STR02969) (δ K : ℝ),
      IsOpen U ∧ (0 : PolynomialRangeParameters) ∈ U ∧
      IsOpen N ∧ (0 : E_STR02969) ∈ N ∧ ContDiffOn ℝ ∞ ψ U ∧
      (∀ p ∈ U, ψ p ∈ N) ∧
      (∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) ∧
      (∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
        ψ (0, 0, (h, s), γ) = 0) ∧
      0 < δ ∧ 0 ≤ K ∧ Metric.ball (0 : PolynomialRangeParameters) δ ⊆ U ∧
      (∀ a b h s γ : ℝ, ‖((a, b, (h, s), γ) : PolynomialRangeParameters)‖ < δ →
        ‖ψ (a, b, (h, s), γ)‖ ≤ K * max |a| |b|) ∧
      ∀ᶠ x : ℝ × ℝ × ℝ × ℝ in 𝓝 0,
        ((x.1, x.2.1, (x.2.2.1, root_EX054 x.2.2.1), x.2.2.2) : PolynomialRangeParameters) ∈ U := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero⟩ := exists_polynomial_range_graph
  have hc : ContDiffAt ℝ 1 ψ (0 : PolynomialRangeParameters) :=
    (hψ.contDiffAt (hU.mem_nhds h0U)).of_le (by simp)
  obtain ⟨K, t, ht, hLip⟩ := hc.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (hU.mem_nhds h0U))
  have hballU : Metric.ball (0 : PolynomialRangeParameters) δ ⊆ U := fun p hp => (hball hp).2
  refine ⟨U, N, ψ, δ, K, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero,
    hδ, K.coe_nonneg, hballU, ?_, ?_⟩
  · intro a b h s γ hp
    let p : PolynomialRangeParameters := (a, b, (h, s), γ)
    let p0 : PolynomialRangeParameters := (0, 0, (h, s), γ)
    have hpp : p ∈ Metric.ball (0 : PolynomialRangeParameters) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hp
    have hnorm : ‖p0‖ ≤ ‖p‖ := by
      dsimp only [p0, p]
      simp only [Prod.norm_def, norm_zero]
      have ht : (0 : ℝ) ≤ max (max ‖h‖ ‖s‖) ‖γ‖ := by positivity
      rw [max_eq_right ht, max_eq_right ht]
      exact le_max_of_le_right (le_max_right _ _)
    have hp0 : p0 ∈ Metric.ball (0 : PolynomialRangeParameters) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hnorm.trans_lt hp
    have hz : ψ p0 = 0 := hzero h s γ (hballU hp0)
    have hd := hLip.dist_le_mul p (hball hpp).1 p0 (hball hp0).1
    rw [hz, dist_zero_right] at hd
    have hdist : dist p p0 = max |a| |b| := by
      simp only [p, p0, Prod.dist_eq, dist_self, dist_zero_right, Real.norm_eq_abs,
        max_self, max_eq_left (abs_nonneg b)]
    rw [hdist] at hd
    exact hd
  · exact polynomial_selected_parameters_tendsto.eventually (hU.mem_nhds h0U)

end DGPS.Examples.PolynomialSpecies
