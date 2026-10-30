import DGPS.Examples.PolynomialSpeciesDescentBridge

/-! Genuine uniform physical feature derivative bounds near zero field.
The moving centering is spatially constant and is never differentiated in
its field parameter. -/

noncomputable section
open MeasureTheory
open DGPS.PositiveRankOne DGPS.Examples.PolynomialEquilibrium
open DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private theorem partial_pair {v w : Torus 1 → ℝ}
    (hv : IsSmoothPeriodic v) (hw : IsSmoothPeriodic w) (a b : ℝ) :
    (fun x => coordPartial 0 (fun y => a * v y + b * w y) x) =
      fun x => a * coordPartial 0 v x + b * coordPartial 0 w x := by
  funext x
  simpa only [add_zero] using RankOneModel.coordPartial_lin hv hw a b 0 x

/-- One constant precedes every field and point. The derivatives are the
actual physical coordinate derivatives of the actual centered feature. -/
theorem polynomial_uniform_feature_derivative_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ h : ℝ, |h| ≤ 1 → ∀ x : Torus 1,
      |(polynomialRankOne h).dφ x| +
        |coordPartial 0 (polynomialRankOne h).dφ x| +
        |coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x| ≤ K := by
  let F1 := coordPartial 0 (cosT 2)
  let F2 := coordPartial 0 F1
  let F3 := coordPartial 0 F2
  let G1 := coordPartial 0 (cosT 1)
  let G2 := coordPartial 0 G1
  let G3 := coordPartial 0 G2
  have hF1 : IsSmoothPeriodic F1 := (isSmooth_cosT_EX055 2).isSmoothPeriodic_coordPartial 0
  have hF2 : IsSmoothPeriodic F2 := hF1.isSmoothPeriodic_coordPartial 0
  have hF3 : IsSmoothPeriodic F3 := hF2.isSmoothPeriodic_coordPartial 0
  have hG1 : IsSmoothPeriodic G1 := (isSmooth_cosT_EX055 1).isSmoothPeriodic_coordPartial 0
  have hG2 : IsSmoothPeriodic G2 := hG1.isSmoothPeriodic_coordPartial 0
  have hG3 : IsSmoothPeriodic G3 := hG2.isSmoothPeriodic_coordPartial 0
  let B := fun x => |F1 x| + |F2 x| + |F3 x| + |G1 x| + |G2 x| + |G3 x|
  have hBc : Continuous B :=
    ((((hF1.continuous_torus.abs.add hF2.continuous_torus.abs).add hF3.continuous_torus.abs).add
      hG1.continuous_torus.abs).add hG2.continuous_torus.abs).add hG3.continuous_torus.abs
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hBc.continuousOn
  let L := max C 0
  have hL : 0 ≤ L := le_max_right _ _
  have hBL (x : Torus 1) : B x ≤ L := by
    have hh := hC x (Set.mem_univ x)
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [B]; positivity)] at hh
    exact hh.trans (le_max_left _ _)
  let K := (Real.sqrt 2 + Real.sqrt 2 / 3) * L + 1
  refine ⟨K, by dsimp only [K]; positivity, fun h hh x => ?_⟩
  let a : ℝ := Real.sqrt 2
  let b : ℝ := -Real.sqrt 2 * h / 3
  have hb : |b| ≤ Real.sqrt 2 / 3 := by
    dsimp only [b]
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hi := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg 2)
    nlinarith
  have hφ : (polynomialRankOne h).φ = fun y => a * cosT 2 y + b * cosT 1 y +
      (-Real.sqrt 2 * moment_EX054 h (root_EX054 h)) := by
    funext y
    change Real.sqrt 2 * (cosT 2 y - h / 3 * cosT 1 y - moment_EX054 h (root_EX054 h)) = _
    dsimp only [a, b]
    ring
  have hd : (polynomialRankOne h).dφ = fun y => a * F1 y + b * G1 y := by
    funext y
    unfold RankOneModel.dφ
    rw [hφ]
    exact RankOneModel.coordPartial_lin (isSmooth_cosT_EX055 2) (isSmooth_cosT_EX055 1) _ _ _ y
  have hd1 : (fun y => coordPartial 0 (polynomialRankOne h).dφ y) =
      fun y => a * F2 y + b * G2 y := by
    rw [hd]
    exact partial_pair hF1 hG1 _ _
  have hd2 : (fun y => coordPartial 0 (fun z => coordPartial 0 (polynomialRankOne h).dφ z) y) =
      fun y => a * F3 y + b * G3 y := by
    rw [hd1]
    exact partial_pair hF2 hG2 _ _
  have he0 := congrFun hd x
  have he1 := congrFun hd1 x
  have he2 := congrFun hd2 x
  rw [he2, he1, he0]
  have hf : |F1 x| + |F2 x| + |F3 x| ≤ L := by
    have hi := hBL x
    dsimp only [B] at hi
    linarith [abs_nonneg (G1 x), abs_nonneg (G2 x), abs_nonneg (G3 x)]
  have hg : |G1 x| + |G2 x| + |G3 x| ≤ L := by
    have hi := hBL x
    dsimp only [B] at hi
    linarith [abs_nonneg (F1 x), abs_nonneg (F2 x), abs_nonneg (F3 x)]
  calc
    _ ≤ (|a| * |F1 x| + |b| * |G1 x|) + (|a| * |F2 x| + |b| * |G2 x|) +
        (|a| * |F3 x| + |b| * |G3 x|) := by
      exact add_le_add (add_le_add (by simpa only [abs_mul] using abs_add_le (a * F1 x) (b * G1 x))
        (by simpa only [abs_mul] using abs_add_le (a * F2 x) (b * G2 x)))
          (by simpa only [abs_mul] using abs_add_le (a * F3 x) (b * G3 x))
    _ = |a| * (|F1 x| + |F2 x| + |F3 x|) + |b| * (|G1 x| + |G2 x| + |G3 x|) := by ring
    _ ≤ K := by
      have h1 := mul_le_mul_of_nonneg_left hf (abs_nonneg a)
      have h2 := mul_le_mul_of_nonneg_left hg (abs_nonneg b)
      have h3 := mul_le_mul_of_nonneg_right hb hL
      have ha : |a| = Real.sqrt 2 := abs_of_nonneg (Real.sqrt_nonneg 2)
      rw [ha] at h1
      dsimp only [K]
      nlinarith

end DGPS.Examples.PolynomialSpecies
