import DGPS.Examples.PolynomialSpeciesDescentBridge

/-! Actual first three physical spatial log-reference derivatives vanish
uniformly at zero field. Only the amplitude of the selected scalar root is
used; no derivative of that selected root is taken. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.PositiveRankOne DGPS.Examples.PolynomialEquilibrium
open DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private theorem root_tendsto : Tendsto root_EX054 (𝓝 (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, δ, _, hδ, hb⟩ := abs_root_le_sixth_EX054
  have hs : ∀ᶠ h : ℝ in 𝓝 0, |h| < δ := by
    have ht : Tendsto (fun h : ℝ => |h|) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using continuous_abs.tendsto (0 : ℝ)
    exact ht.eventually (gt_mem_nhds hδ)
  have ht : Tendsto (fun h : ℝ => C * h ^ 6) (𝓝 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).pow 6).const_mul C
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [hs] with h hh
  rw [Real.norm_eq_abs]
  exact hb h hh.le

private theorem log_formula (h : ℝ) :
    (fun x => Real.log ((polynomialRankOne h).q x)) = fun x =>
      (h + root_EX054 h * h / 3) * cosT 1 x + (-root_EX054 h) * cosT 2 x +
        (-Real.log (DGPS.Examples.ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h (root_EX054 h)))) := by
  funext x
  have hZ := DGPS.Examples.ThreeSpeciesCircle.gibbsZ_pos
    (isSmooth_polyPot_EX055 h (root_EX054 h))
  change Real.log (Real.exp (-polyPot_EX055 h (root_EX054 h) x) /
    DGPS.Examples.ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h (root_EX054 h))) = _
  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  dsimp only [polyPot_EX055, polyFeature]
  ring

private theorem partial_pair {v w : Torus 1 → ℝ}
    (hv : IsSmoothPeriodic v) (hw : IsSmoothPeriodic w) (a b : ℝ) :
    (fun x => coordPartial 0 (fun y => a * v y + b * w y) x) =
      fun x => a * coordPartial 0 v x + b * coordPartial 0 w x := by
  funext x
  simpa only [add_zero] using RankOneModel.coordPartial_lin hv hw a b 0 x

/-- The actual physical score and its first two physical derivatives are
uniformly small. All 2*pi factors are contained in the true native coordinate
derivatives; the spatial normalization constant contributes nothing. -/
theorem polynomial_log_score_second_derivatives_at_origin :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝 0) (𝓝 0) ∧ ∀ h : ℝ, ∀ x : Torus 1,
      |(polynomialRankOne h).dlogq x| +
        |coordPartial 0 (polynomialRankOne h).dlogq x| +
        |coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dlogq y) x| ≤ ε h := by
  let F1 := coordPartial 0 (cosT 1)
  let F2 := coordPartial 0 F1
  let F3 := coordPartial 0 F2
  let G1 := coordPartial 0 (cosT 2)
  let G2 := coordPartial 0 G1
  let G3 := coordPartial 0 G2
  have hF1 : IsSmoothPeriodic F1 := (isSmooth_cosT_EX055 1).isSmoothPeriodic_coordPartial 0
  have hF2 : IsSmoothPeriodic F2 := hF1.isSmoothPeriodic_coordPartial 0
  have hF3 : IsSmoothPeriodic F3 := hF2.isSmoothPeriodic_coordPartial 0
  have hG1 : IsSmoothPeriodic G1 := (isSmooth_cosT_EX055 2).isSmoothPeriodic_coordPartial 0
  have hG2 : IsSmoothPeriodic G2 := hG1.isSmoothPeriodic_coordPartial 0
  have hG3 : IsSmoothPeriodic G3 := hG2.isSmoothPeriodic_coordPartial 0
  let B := fun x => |F1 x| + |F2 x| + |F3 x| + |G1 x| + |G2 x| + |G3 x|
  have hBc : Continuous B :=
    ((((hF1.continuous_torus.abs.add hF2.continuous_torus.abs).add hF3.continuous_torus.abs).add
      hG1.continuous_torus.abs).add hG2.continuous_torus.abs).add hG3.continuous_torus.abs
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hBc.continuousOn
  have hBK (x : Torus 1) : B x ≤ K := by
    have hh := hK x (Set.mem_univ x)
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [B]; positivity)] at hh
    exact hh
  let a := fun h : ℝ => h + root_EX054 h * h / 3
  let b := fun h : ℝ => -root_EX054 h
  let ε := fun h : ℝ => (|a h| + |b h|) * K
  have ha : Tendsto a (𝓝 0) (𝓝 0) := by
    simpa only [a, id_eq, zero_mul, zero_div, add_zero] using
      ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).add
        ((root_tendsto.mul tendsto_id).div_const 3))
  have hb : Tendsto b (𝓝 0) (𝓝 0) := by simpa only [b, neg_zero] using root_tendsto.neg
  refine ⟨ε, ?_, fun h x => ?_⟩
  · simpa only [ε, abs_zero, zero_add, zero_mul] using (ha.abs.add hb.abs).mul_const K
  · have hσ : (polynomialRankOne h).dlogq = fun y => a h * F1 y + b h * G1 y := by
      funext y
      unfold RankOneModel.dlogq
      rw [log_formula]
      exact RankOneModel.coordPartial_lin (isSmooth_cosT_EX055 1) (isSmooth_cosT_EX055 2) _ _ _ y
    have hσ1 : (fun y => coordPartial 0 (polynomialRankOne h).dlogq y) =
        fun y => a h * F2 y + b h * G2 y := by
      rw [hσ]
      exact partial_pair hF1 hG1 _ _
    have hσ2 : (fun y => coordPartial 0 (fun z => coordPartial 0 (polynomialRankOne h).dlogq z) y) =
        fun y => a h * F3 y + b h * G3 y := by
      rw [hσ1]
      exact partial_pair hF2 hG2 _ _
    change |(polynomialRankOne h).dlogq x| +
      |(fun y => coordPartial 0 (polynomialRankOne h).dlogq y) x| +
      |(fun y => coordPartial 0 (fun z => coordPartial 0 (polynomialRankOne h).dlogq z) y) x| ≤ ε h
    have he0 := congrFun hσ x
    have he1 := congrFun hσ1 x
    have he2 := congrFun hσ2 x
    dsimp only
    rw [he2, he1, he0]
    have hf : |F1 x| + |F2 x| + |F3 x| ≤ K := by
      have hh := hBK x
      dsimp only [B] at hh
      linarith [abs_nonneg (G1 x), abs_nonneg (G2 x), abs_nonneg (G3 x)]
    have hg : |G1 x| + |G2 x| + |G3 x| ≤ K := by
      have hh := hBK x
      dsimp only [B] at hh
      linarith [abs_nonneg (F1 x), abs_nonneg (F2 x), abs_nonneg (F3 x)]
    calc
      _ ≤ (|a h| * |F1 x| + |b h| * |G1 x|) +
          (|a h| * |F2 x| + |b h| * |G2 x|) +
          (|a h| * |F3 x| + |b h| * |G3 x|) := by
        exact add_le_add (add_le_add (by simpa only [abs_mul] using abs_add_le (a h * F1 x) (b h * G1 x))
          (by simpa only [abs_mul] using abs_add_le (a h * F2 x) (b h * G2 x)))
            (by simpa only [abs_mul] using abs_add_le (a h * F3 x) (b h * G3 x))
      _ = |a h| * (|F1 x| + |F2 x| + |F3 x|) + |b h| * (|G1 x| + |G2 x| + |G3 x|) := by ring
      _ ≤ ε h := by
        have h1 := mul_le_mul_of_nonneg_left hf (abs_nonneg (a h))
        have h2 := mul_le_mul_of_nonneg_left hg (abs_nonneg (b h))
        dsimp only [ε]
        nlinarith

end DGPS.Examples.PolynomialSpecies
