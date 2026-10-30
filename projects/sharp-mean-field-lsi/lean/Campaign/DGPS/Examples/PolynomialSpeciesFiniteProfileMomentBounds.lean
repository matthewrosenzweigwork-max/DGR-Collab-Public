import DGPS.Examples.PolynomialSpeciesFiniteProfileMoments
import Mathlib.Analysis.Calculus.Taylor

/-! Genuine compact-uniform bounds for the actual nonlocal finite-profile
moments. Stock Taylor estimates are applied only after the actual jets have
been derived; the desired moment remainder is never an input. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Input := (ℝ × ℝ) × ℝ

private theorem compact_taylor (F : Input → ℝ) (hF : ContDiff ℝ ∞ F)
    (M : ℝ) (hM : 1 ≤ M) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b h : ℝ, |a| ≤ M → |b| ≤ M → 0 ≤ h → h ≤ 1 →
      |F ((a, b), h) - taylorWithinEval (fun t : ℝ => F ((a, b), t)) n
        (Set.Icc (0 : ℝ) 1) 0 h| ≤ K * h ^ (n + 1) := by
  have hcont : Continuous (iteratedFDeriv ℝ (n + 1) F) :=
    hF.continuous_iteratedFDeriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Input) M).exists_bound_of_continuousOn hcont.continuousOn
  let K := max B 0 + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun a b h ha hb hh hh1 => ?_⟩
  let f := fun t : ℝ => F ((a, b), t)
  have hf : ContDiff ℝ ∞ f := hF.comp (contDiff_const.prodMk contDiff_id)
  have hbnd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) f (Set.Icc (0 : ℝ) 1) t‖ ≤ K := by
    intro t ht
    let L : ℝ →L[ℝ] Input :=
      (0 : ℝ →L[ℝ] (ℝ × ℝ)).prod (ContinuousLinearMap.id ℝ ℝ)
    let z : Input := ((a, b), 0)
    have hs : ContDiff ℝ ∞ (fun x : Input => F (z + x)) := hF.comp (contDiff_const.add contDiff_id)
    have he := L.iteratedFDeriv_comp_right hs t (i := n + 1) (by simp)
    have hline : f = (fun x : Input => F (z + x)) ∘ L := by
      funext t
      simp [f, z, L]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hf.of_le (by simp)).contDiffAt) ht, iteratedDeriv_eq_iteratedFDeriv, hline, he,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_comp_add_left]
    have hpoint : z + L t ∈ Metric.closedBall (0 : Input) M := by
      rw [Metric.mem_closedBall, dist_zero_right]
      simp only [z, L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.id_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.norm_def,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact max_le (max_le ha hb) (ht.2.trans hM)
    calc
      _ ≤ ‖iteratedFDeriv ℝ (n + 1) F (z + L t)‖ * ∏ _ : Fin (n + 1), ‖L 1‖ :=
        (iteratedFDeriv ℝ (n + 1) F (z + L t)).le_opNorm _
      _ = ‖iteratedFDeriv ℝ (n + 1) F (z + L t)‖ := by simp [L]
      _ ≤ K := (hB _ hpoint).trans (by dsimp only [K]; linarith [le_max_left B 0])
  have he := taylor_mean_remainder_bound (n := n) zero_le_one
    (hf.of_le (by simp)).contDiffOn ⟨hh, hh1⟩ hbnd
  have hfac : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnum : 0 ≤ K * h ^ (n + 1) := mul_nonneg hK.le (pow_nonneg hh _)
  exact he.trans (by simpa only [sub_zero] using div_le_self hnum hfac)

private theorem quadratic_taylor (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 0) (q : ℝ) (h2 : iteratedDeriv 2 f 0 = 2 * q) (h : ℝ) :
    taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 h = q * h ^ 2 := by
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hf.of_le (by simp)).contDiffAt) ⟨le_rfl, zero_le_one⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hf.of_le (by simp)).contDiffAt) ⟨le_rfl, zero_le_one⟩]
  simp only [h0, iteratedDeriv_one, h1, h2, smul_eq_mul, zero_mul, zero_add, sub_zero]
  norm_num
  ring

/-- Actual uniform nonlocal inputs: m has its true h-squared coefficient,
the TRUE generator-expectation residual is cubic, and the squared feature
gradient expectation differs from its origin value by order h. One constant
precedes every bounded coefficient pair and every field in [0,1]. -/
theorem polynomialFiniteProfile_moment_bounds (M : ℝ) (hM : 1 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b h : ℝ, |a| ≤ M → |b| ≤ M → 0 ≤ h → h ≤ 1 →
      |polynomialFiniteMoment a b h - (Real.sqrt 2 * (a ^ 2 - b ^ 2) / 24) * h ^ 2| ≤ K * h ^ 3 ∧
      |polynomialFiniteGeneratorMoment a b h -
        4 * DGPS.Circle.AngularNormalization.a0 * polynomialFiniteMoment a b h| ≤ K * h ^ 3 ∧
      |polynomialFiniteGradientMoment a b h - 4 * DGPS.Circle.AngularNormalization.a0| ≤ K * h := by
  obtain ⟨hm, hA, hJ⟩ := polynomialFiniteMoments_smooth
  obtain ⟨Km, hKm, bm⟩ := compact_taylor _ hm M hM 2
  obtain ⟨KA, hKA, bA⟩ := compact_taylor _ hA M hM 2
  obtain ⟨KJ, hKJ, bJ⟩ := compact_taylor _ hJ M hM 0
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  let K := Km + KA + 4 * DGPS.Circle.AngularNormalization.a0 * Km + KJ
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun a b h ha hb hh hh1 => ?_⟩
  obtain ⟨hm0, hA0, hm1, hA1, hm2, hA2, hJ0⟩ := polynomialFiniteMoments_origin_jets a b
  have hi : ContDiff ℝ ∞ (fun h : ℝ => ((a,b),h)) := contDiff_const.prodMk contDiff_id
  have hms : ContDiff ℝ ∞ (polynomialFiniteMoment a b) := by
    have ht := hm.comp hi
    exact ht
  have hAs : ContDiff ℝ ∞ (polynomialFiniteGeneratorMoment a b) := by
    have ht := hA.comp hi
    exact ht
  let m2 := Real.sqrt 2 * (a ^ 2 - b ^ 2) / 24
  have hmq : iteratedDeriv 2 (polynomialFiniteMoment a b) 0 = 2 * m2 := by rw [hm2]; dsimp only [m2]; ring
  have hAq : iteratedDeriv 2 (polynomialFiniteGeneratorMoment a b) 0 =
      2 * (4 * DGPS.Circle.AngularNormalization.a0 * m2) := by rw [hA2]; dsimp only [m2]; ring
  have em := bm a b h ha hb hh hh1
  have eA := bA a b h ha hb hh hh1
  have eJ := bJ a b h ha hb hh hh1
  rw [quadratic_taylor _ hms hm0 hm1 m2 hmq] at em
  rw [quadratic_taylor _ hAs hA0 hA1 (4 * DGPS.Circle.AngularNormalization.a0 * m2) hAq] at eA
  rw [taylor_within_zero_eval, hJ0] at eJ
  have hprod : 0 ≤ 4 * DGPS.Circle.AngularNormalization.a0 * Km := by positivity
  have hKmK : Km ≤ K := by dsimp only [K]; linarith
  have hKAK : KA + 4 * DGPS.Circle.AngularNormalization.a0 * Km ≤ K := by dsimp only [K]; linarith
  have hKJK : KJ ≤ K := by dsimp only [K]; linarith
  refine ⟨em.trans (mul_le_mul_of_nonneg_right hKmK (pow_nonneg hh _)), ?_, ?_⟩
  · have hid : polynomialFiniteGeneratorMoment a b h -
        4 * DGPS.Circle.AngularNormalization.a0 * polynomialFiniteMoment a b h =
      (polynomialFiniteGeneratorMoment a b h - (4 * DGPS.Circle.AngularNormalization.a0 * m2) * h ^ 2) -
        4 * DGPS.Circle.AngularNormalization.a0 * (polynomialFiniteMoment a b h - m2 * h ^ 2) := by ring
    rw [hid]
    calc
      _ ≤ |polynomialFiniteGeneratorMoment a b h - (4 * DGPS.Circle.AngularNormalization.a0 * m2) * h ^ 2| +
          |4 * DGPS.Circle.AngularNormalization.a0 * (polynomialFiniteMoment a b h - m2 * h ^ 2)| := abs_sub _ _
      _ ≤ KA * h ^ 3 + 4 * DGPS.Circle.AngularNormalization.a0 * (Km * h ^ 3) := by
        rw [abs_mul, abs_of_pos (mul_pos (by norm_num) DGPS.Circle.AngularNormalization.a0_pos)]
        exact add_le_add eA (mul_le_mul_of_nonneg_left em (by positivity))
      _ ≤ K * h ^ 3 := by
        calc
          _ = (KA + 4 * DGPS.Circle.AngularNormalization.a0 * Km) * h ^ 3 := by ring
          _ ≤ K * h ^ 3 := mul_le_mul_of_nonneg_right hKAK (pow_nonneg hh 3)
  · simp only [Nat.zero_add, pow_one] at eJ
    exact eJ.trans (mul_le_mul_of_nonneg_right hKJK hh)

end DGPS.Examples.PolynomialSpecies
