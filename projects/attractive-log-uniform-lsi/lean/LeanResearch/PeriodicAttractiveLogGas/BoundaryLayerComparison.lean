import LeanResearch.PeriodicAttractiveLogGas.StationaryCutDomain

/-! A sharp first-order comparison between Euclidean neighborhoods and
value layers. The local derivative bound is derived from the actual
boundary gradient, and the global Lipschitz estimate only localizes the
segment before the sharp bound is used. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace PeriodicAttractiveLogGas.BoundaryLayerComparison
open StationaryPeriodDisplacement StationaryLevelGeometry

theorem torus_gradient_norm_eq_fderiv (v : Torus → ℝ) (x : PlanarSpace) :
    ‖torusOrdinaryGradient v (torusQuotient x)‖ =
      ‖fderiv ℝ (fun y : PlanarSpace ↦ v (torusQuotient y)) x‖ := by
  rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient,
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map]

theorem exists_lipschitz_scalar_lift {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x : PlanarSpace ↦ v (torusQuotient x)) := by
  let G : C(Torus, ℝ) := ⟨fun z ↦ ‖torusOrdinaryGradient v z‖, continuous_norm_gradient hv⟩
  refine ⟨‖G‖₊, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hv.differentiable (by norm_num))
  intro x
  have hb := G.norm_coe_le_norm (torusQuotient x)
  have hr : ‖fderiv ℝ (fun y : PlanarSpace ↦ v (torusQuotient y)) x‖ ≤ ‖G‖ := by
    rw [← torus_gradient_norm_eq_fderiv]
    simpa only [G, ContinuousMap.coe_mk, norm_norm] using hb
  exact_mod_cast hr

/-- Compactness makes a boundary derivative bound uniform in a value band. -/
theorem exists_gradient_band {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hzero : ∀ z : Torus, v z = 0 → ‖torusOrdinaryGradient v z‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : Torus, |v z| < r → ‖torusOrdinaryGradient v z‖ ≤ 1 + δ := by
  let B : Set Torus := {z | 1 + δ ≤ ‖torusOrdinaryGradient v z‖}
  have hB : IsCompact B := (isClosed_le continuous_const (continuous_norm_gradient hv)).isCompact
  have hI : IsClosed (v '' B) := (hB.image (continuous_of_contDiff_lift hv)).isClosed
  have hz : (0 : ℝ) ∉ v '' B := by
    rintro ⟨z, hz, he⟩
    have hh := hzero z he
    change 1 + δ ≤ ‖torusOrdinaryGradient v z‖ at hz
    linarith only [hh, hz, hδ]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hI.isOpen_compl.mem_nhds hz)
  refine ⟨r, hr, fun z hzr ↦ ?_⟩
  by_contra hb
  have hmem : z ∈ B := le_of_lt (lt_of_not_ge hb)
  have hnot := hball (show v z ∈ Metric.ball 0 r by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hzr)
  exact hnot ⟨z, hmem, rfl⟩

/-- Small translations of a nonnegative point remain above the indicated
negative value. No tubular parametrization or neighborhood-volume estimate
is a hypothesis. -/
theorem value_layer_of_dist_lt {f : PlanarSpace → ℝ} {L : ℝ≥0} {r K ε : ℝ}
    (hf : Differentiable ℝ f) (hL : LipschitzWith L f)
    (hband : ∀ z : PlanarSpace, |f z| < r → ‖fderiv ℝ f z‖ ≤ K)
    (hK : 0 < K) (hε : 0 < ε) (hsmall : 2 * (L : ℝ) * ε < r)
    {x y : PlanarSpace} (hx : 0 ≤ f x) (hxy : dist y x < ε) :
    -(K * ε) < f y := by
  by_cases hy : 0 ≤ f y
  · exact (neg_neg_of_pos (mul_pos hK hε)).trans_le hy
  have hyneg : f y < 0 := lt_of_not_ge hy
  have hfx : |f x| ≤ (L : ℝ) * ε := by
    rw [abs_of_nonneg hx]
    have hl := hL.dist_le_mul x y
    rw [Real.dist_eq, dist_comm x y] at hl
    have hc := mul_le_mul_of_nonneg_left hxy.le L.coe_nonneg
    have ha := le_abs_self (f x - f y)
    linarith only [hl, hc, ha, hyneg]
  have hlocal (z : PlanarSpace) (hz : z ∈ Metric.closedBall x ε) : ‖fderiv ℝ f z‖ ≤ K := by
    apply hband z
    have hl := hL.dist_le_mul z x
    rw [Real.dist_eq] at hl
    have hc := mul_le_mul_of_nonneg_left (show dist z x ≤ ε from hz) L.coe_nonneg
    have ha : |f z| ≤ |f z - f x| + |f x| := by
      simpa only [Real.norm_eq_abs, sub_add_cancel] using norm_add_le (f z - f x) (f x)
    linarith only [hl, hc, ha, hfx, hsmall]
  have hh := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ ↦ (hf z).hasFDerivAt.hasFDerivWithinAt) hlocal
    (convex_closedBall x ε) (Metric.mem_closedBall_self hε.le) hxy.le
  rw [Real.norm_eq_abs, ← dist_eq_norm] at hh
  have hdist := mul_lt_mul_of_pos_left hxy hK
  have hl := neg_le_abs (f y - f x)
  linarith only [hh, hdist, hl, hx]

end PeriodicAttractiveLogGas.BoundaryLayerComparison
