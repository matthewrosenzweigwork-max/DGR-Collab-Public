import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarWeakEuler

/-! Uniform fixed-field bounds for the actual nonlinear score correction.
All coefficients are genuine bounded probability moments, including generator
features. No information bound or optimizer assumption is required. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

private def fs (h : ℝ) : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]

private theorem fs_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (fs h i) := by
  fin_cases i
  · exact isSmooth_featureC h
  · exact isSmooth_featureS h
  · exact isSmooth_featureB h

private theorem nine_bounds (h : ℝ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ i : Fin 3, ∀ x : Torus 1,
    |fs h i x| ≤ B ∧ |coordPartial 0 (fs h i) x| ≤ B ∧
      |elementaryFeatureGenerator h (fs h i) x| ≤ B := by
  let F := fun x : Torus 1 => ∑ i : Fin 3,
    (|fs h i x| + |coordPartial 0 (fs h i) x| + |elementaryFeatureGenerator h (fs h i) x|)
  have hF : Continuous F := continuous_finsetSum _ fun i _ =>
    (((fs_smooth h i).continuous_torus.abs).add
      ((fs_smooth h i).continuous_coordPartial 0).abs).add
        (continuous_elementaryFeatureGenerator h _ (fs_smooth h i)).abs
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hF.continuousOn
  have hF0 : 0 ≤ F x0 := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨1 + F x0, by linarith, fun i x => ?_⟩
  have hi : |fs h i x| + |coordPartial 0 (fs h i) x| +
      |elementaryFeatureGenerator h (fs h i) x| ≤ F x :=
    Finset.single_le_sum
      (f := fun j : Fin 3 => |fs h j x| + |coordPartial 0 (fs h j) x| +
        |elementaryFeatureGenerator h (fs h j) x|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hx : F x ≤ F x0 := hx0 (Set.mem_univ x)
  exact ⟨by linarith [abs_nonneg (coordPartial 0 (fs h i) x),
      abs_nonneg (elementaryFeatureGenerator h (fs h i) x)],
    by linarith [abs_nonneg (fs h i x), abs_nonneg (elementaryFeatureGenerator h (fs h i) x)],
    by linarith [abs_nonneg (fs h i x), abs_nonneg (coordPartial 0 (fs h i) x)]⟩

private theorem moment_bound (ν : ProbabilityMeasure (Torus 1)) {f : Torus 1 → ℝ}
    {B : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂(ν : Measure (Torus 1))| ≤ B := by
  have hi : Integrable f (ν : Measure (Torus 1)) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, |f x| ∂(ν : Measure (Torus 1)) := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := (ν : Measure (Torus 1))) f)
    _ ≤ ∫ _ : Torus 1, B ∂(ν : Measure (Torus 1)) :=
      integral_mono hi.abs (integrable_const B) hb
    _ = B := by simp

private theorem triple_bound (α β M N a b c x y z : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M)
    (hx : |x| ≤ N) (hy : |y| ≤ N) (hz : |z| ≤ N) :
    |α * (a * x + b * y) - β * c * z| ≤ (2 * |α| + |β|) * M * N := by
  calc
    _ ≤ |α| * (|a| * |x| + |b| * |y|) + |β| * |c| * |z| := by
      calc
        _ ≤ |α * (a * x + b * y)| + |β * c * z| := abs_sub _ _
        _ ≤ _ := by
          simp only [abs_mul]
          have ht : |a * x + b * y| ≤ |a| * |x| + |b| * |y| := by
            simpa only [abs_mul] using abs_add_le (a * x) (b * y)
          exact add_le_add (mul_le_mul_of_nonneg_left ht (abs_nonneg α)) le_rfl
    _ ≤ |α| * (M * N + M * N) + |β| * M * N := by gcongr
    _ = _ := by ring

/-- Uniformity is over ALL original absolute densities. The bound is fixed
after h and a real rate bound R, before the coupling or competitor. In particular
the nonlinear Euler correction and its mass multiplier vanish at least linearly
with the actual coupling. -/
theorem elementaryEulerCorrection_uniform_bound (h R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : AbsoluteDensity 1, ∀ r : ℝ, |r| ≤ R →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        (∀ x, |elementaryEulerCorrection h ε r ρ x| ≤ K * ε) ∧
          |elementaryEulerMultiplier h ε r ρ| ≤ K * ε := by
  obtain ⟨B, hB, hbounds⟩ := nine_bounds h
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans hB
  let D := (2 * |kAlpha| + |kBeta|) * B * B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let K := 1 + 2 * (2 + R) * D + 3 * D ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun ρ r hr ε hε he => ?_⟩
  let ν := densityMeasure ρ
  have hm (i : Fin 3) : |∫ x, fs h i x ∂(ν : Measure (Torus 1))| ≤ B :=
    moment_bound ν (fs_smooth h i).continuous_torus fun x => (hbounds i x).1
  have ha (i : Fin 3) : |∫ x, elementaryFeatureGenerator h (fs h i) x
      ∂(ν : Measure (Torus 1))| ≤ B :=
    moment_bound ν (continuous_elementaryFeatureGenerator h _ (fs_smooth h i))
      fun x => (hbounds i x).2.2
  have hfeat (x : Torus 1) : |featureC h x| ≤ B ∧ |featureS h x| ≤ B ∧ |featureB h x| ≤ B :=
    ⟨(hbounds 0 x).1, (hbounds 1 x).1, (hbounds 2 x).1⟩
  have hgrad (x : Torus 1) : |coordPartial 0 (featureC h) x| ≤ B ∧
      |coordPartial 0 (featureS h) x| ≤ B ∧ |coordPartial 0 (featureB h) x| ≤ B :=
    ⟨(hbounds 0 x).2.1, (hbounds 1 x).2.1, (hbounds 2 x).2.1⟩
  have hgen (x : Torus 1) : |elementaryFeatureGenerator h (featureC h) x| ≤ B ∧
      |elementaryFeatureGenerator h (featureS h) x| ≤ B ∧
        |elementaryFeatureGenerator h (featureB h) x| ≤ B :=
    ⟨(hbounds 0 x).2.2, (hbounds 1 x).2.2, (hbounds 2 x).2.2⟩
  have hmC : |momC h ν| ≤ B := hm 0
  have hmS : |momS h ν| ≤ B := hm 1
  have hmB : |momB h ν| ≤ B := hm 2
  have hκ (x : Torus 1) : |elementaryKprime h ν x| ≤ D := by
    rw [elementaryKprime_three_features]
    exact triple_bound kAlpha kBeta B B _ _ _ _ _ _ hB0 hB0 hmC hmS hmB
      (hgrad x).1 (hgrad x).2.1 (hgrad x).2.2
  have hAK (x : Torus 1) : |elementaryAK h ν x| ≤ D := by
    rw [elementaryAK_moments]
    exact triple_bound kAlpha kBeta B B _ _ _ _ _ _ hB0 hB0 hmC hmS hmB
      (hgen x).1 (hgen x).2.1 (hgen x).2.2
  have hKm (x : Torus 1) : |elementaryKernelMean h ν x| ≤ D := by
    simpa only [D, elementaryKernelMean, mul_assoc] using
      (triple_bound kAlpha kBeta B B _ _ _ _ _ _ hB0 hB0 hmC hmS hmB
        (hfeat x).1 (hfeat x).2.1 (hfeat x).2.2)
  have hLA (x : Torus 1) : |elementaryGeneratorFeedback h ρ x| ≤ D := by
    simpa [D, elementaryGeneratorFeedback, fs, ν, mul_assoc] using
      (triple_bound kAlpha kBeta B B _ _ _ _ _ _ hB0 hB0 (ha 0) (ha 1) (ha 2)
        (hfeat x).1 (hfeat x).2.1 (hfeat x).2.2)
  have hκc : Continuous (elementaryKprime h ν) :=
    (isSmooth_elementaryKernelMean h ν).continuous_coordPartial 0
  have hforce (i : Fin 3) : |∫ x, elementaryKprime h ν x * coordPartial 0 (fs h i) x
      ∂(ν : Measure (Torus 1))| ≤ D * B := by
    apply moment_bound ν (hκc.mul ((fs_smooth h i).continuous_coordPartial 0))
    intro x
    change |elementaryKprime h ν x * coordPartial 0 (fs h i) x| ≤ D * B
    rw [abs_mul]
    exact mul_le_mul (hκ x) (hbounds i x).2.1 (abs_nonneg _) hD
  have hLP (x : Torus 1) : |elementaryForceFeedback h ρ x| ≤ D ^ 2 := by
    have hb := triple_bound kAlpha kBeta (D * B) B _ _ _ _ _ _ (mul_nonneg hD hB0) hB0
      (hforce 0) (hforce 1) (hforce 2) (hfeat x).1 (hfeat x).2.1 (hfeat x).2.2
    have hb' : |elementaryForceFeedback h ρ x| ≤
        (2 * |kAlpha| + |kBeta|) * (D * B) * B := by
      simpa [elementaryForceFeedback, fs, ν, mul_assoc] using hb
    calc _ ≤ (2 * |kAlpha| + |kBeta|) * (D * B) * B := hb'
      _ = D ^ 2 := by dsimp only [D]; ring
  let FC := fun x => elementaryAK h ν x + elementaryGeneratorFeedback h ρ x - r * elementaryKernelMean h ν x
  let FJ := fun x => elementaryKprime h ν x ^ 2 + 2 * elementaryForceFeedback h ρ x
  have hFC (x : Torus 1) : |FC x| ≤ (2 + R) * D := by
    calc
      _ ≤ |elementaryAK h ν x| + |elementaryGeneratorFeedback h ρ x| +
          |r| * |elementaryKernelMean h ν x| := by
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (by rw [abs_mul]))
      _ ≤ D + D + R * D := add_le_add (add_le_add (hAK x) (hLA x))
        (mul_le_mul hr (hKm x) (abs_nonneg _) hR)
      _ = _ := by ring
  have hFJ (x : Torus 1) : |FJ x| ≤ 3 * D ^ 2 := by
    have hκ2 : |elementaryKprime h ν x ^ 2| ≤ D ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hκ x, sq_abs (elementaryKprime h ν x), abs_nonneg (elementaryKprime h ν x)]
    calc
      _ ≤ |elementaryKprime h ν x ^ 2| + 2 * |elementaryForceFeedback h ρ x| := by
        simpa only [abs_mul, abs_two] using abs_add_le (elementaryKprime h ν x ^ 2)
          (2 * elementaryForceFeedback h ρ x)
      _ ≤ 3 * D ^ 2 := by linarith [hLP x]
  have hC : |elementaryC h r ρ| ≤ (2 + R) * D := by
    rw [← elementaryC_feedback_mean]
    exact moment_bound ν
      (((continuous_elementaryAK h ν).add
        (isSmooth_elementaryGeneratorFeedback h ρ).continuous_torus).sub
          ((isSmooth_elementaryKernelMean h ν).continuous_torus.const_mul r)) hFC
  have hJ : |elementaryJ h ρ| ≤ D ^ 2 := by
    unfold elementaryJ
    rw [← Structural.budget_integral_densityMeasure]
    apply moment_bound ν (f := fun x => elementaryKprime h ν x ^ 2) (hκc.pow 2)
    intro x
    change |elementaryKprime h ν x ^ 2| ≤ D ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (elementaryKprime h ν x)) hD).2 (hκ x)
  have he2 : ε ^ 2 ≤ ε := by nlinarith
  constructor
  · intro x
    calc
      _ ≤ (2 * ε) * |FC x| + ε ^ 2 * |FJ x| := by
        change |(2 * ε) * FC x + ε ^ 2 * FJ x| ≤ _
        have ht := abs_add_le ((2 * ε) * FC x) (ε ^ 2 * FJ x)
        have h2ε : 0 ≤ 2 * ε := mul_nonneg (by norm_num) hε
        rw [abs_mul, abs_of_nonneg h2ε,
          show |ε ^ 2 * FJ x| = ε ^ 2 * |FJ x| by
            rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]] at ht
        exact ht
      _ ≤ (2 * ε) * ((2 + R) * D) + ε * (3 * D ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hFC x) (by positivity))
          (mul_le_mul he2 (hFJ x) (abs_nonneg _) hε)
      _ ≤ K * ε := by dsimp only [K]; nlinarith only [hε]
  · calc
      _ ≤ ε * |elementaryC h r ρ| + 2 * ε ^ 2 * |elementaryJ h ρ| := by
        change |ε * elementaryC h r ρ + (2 * ε ^ 2) * elementaryJ h ρ| ≤ _
        have ht := abs_add_le (ε * elementaryC h r ρ) ((2 * ε ^ 2) * elementaryJ h ρ)
        have h2ε : 0 ≤ 2 * ε ^ 2 := mul_nonneg (by norm_num) (sq_nonneg ε)
        rw [abs_mul, abs_of_nonneg hε,
          show |(2 * ε ^ 2) * elementaryJ h ρ| = (2 * ε ^ 2) * |elementaryJ h ρ| by
            rw [abs_mul, abs_of_nonneg h2ε]] at ht
        exact ht
      _ ≤ ε * ((2 + R) * D) + 2 * ε * D ^ 2 := by
        have ht := mul_le_mul he2 hJ (abs_nonneg _) hε
        have ht2 := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add (mul_le_mul_of_nonneg_left hC hε) (by simpa only [mul_assoc] using ht2)
      _ ≤ K * ε := by
        have hrem : 0 ≤ ε * (1 + (2 + R) * D + D ^ 2) := mul_nonneg hε (by positivity)
        dsimp only [K]
        nlinarith only [hrem]

end DGPS.Examples.ThreeSpeciesCircle
