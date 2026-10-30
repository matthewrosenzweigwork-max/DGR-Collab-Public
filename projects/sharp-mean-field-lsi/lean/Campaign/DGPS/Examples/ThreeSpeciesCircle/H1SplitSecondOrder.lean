import DGPS.Examples.ThreeSpeciesCircle.H1FixedBarycenterIdentities

/-! Genuine two-sided second-order ingredients for bounded continuous H1
relative tangents. Their weak gradients need only be square integrable. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The scalar KL Taylor error used for linear density, rather than a linear
square-root perturbation. The estimate holds for both signs. -/
theorem relativeSplit_kl_taylor {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |InformationTheory.klFun (1 + z) - z ^ 2 / 2| ≤ 4 * |z| ^ 3 := by
  have hz1 : |-z| < 1 := by rw [abs_neg]; linarith
  have ht := Real.abs_log_sub_add_sum_range_le hz1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at ht
  let e := Real.log (1 + z) - (z - z ^ 2 / 2)
  have he : |e| ≤ 2 * |z| ^ 3 := by
    have hb : |-z| ^ (2 + 1) / (1 - |-z|) ≤ 2 * |z| ^ 3 := by
      rw [abs_neg]
      apply (div_le_iff₀ (by linarith : 0 < 1 - |z|)).2
      change |z| ^ 3 ≤ 2 * |z| ^ 3 * (1 - |z|)
      have hhalf : 0 ≤ 1 - 2 * |z| := by linarith only [hz]
      have hprod := mul_nonneg (pow_nonneg (abs_nonneg z) 3) hhalf
      nlinarith only [hprod]
    apply le_trans _ hb
    convert ht using 2
    dsimp only [e]
    ring_nf
  have hid : InformationTheory.klFun (1 + z) - z ^ 2 / 2 =
      -(z ^ 3 / 2) + (1 + z) * e := by
    dsimp only [InformationTheory.klFun, e]
    ring
  have h1 : |1 + z| ≤ 3 / 2 := by
    exact (abs_add_le 1 z).trans (by norm_num; linarith)
  have hprod : |(1 + z) * e| ≤ 3 * |z| ^ 3 := by
    rw [abs_mul]
    nlinarith [abs_nonneg e]
  rw [hid]
  calc _ ≤ |-(z ^ 3 / 2)| + |(1 + z) * e| := abs_add_le _ _
    _ ≤ 4 * |z| ^ 3 := by
      rw [abs_neg, abs_div, abs_pow, abs_two]
      nlinarith [pow_nonneg (abs_nonneg z) 3]

/-- Integrated second-order entropy estimate on the actual base probability.
The constant depends only on the chosen tangent bound, and works for both signs. -/
theorem relativeSplit_entropy_taylor (μ : ProbabilityMeasure (Torus 1))
    (g : Torus 1 → ℝ) (hc : Continuous g) {B t : ℝ}
    (hB : ∀ x, |g x| ≤ B) (ht : |t| * B ≤ 1 / 2) :
    |(∫ x, InformationTheory.klFun (1 + t * g x) ∂(μ : Measure (Torus 1))) -
      t ^ 2 / 2 * ∫ x, g x ^ 2 ∂(μ : Measure (Torus 1))| ≤ 4 * B ^ 3 * |t| ^ 3 := by
  have hB0 : 0 ≤ B := (abs_nonneg (g 0)).trans (hB 0)
  have hiK : Integrable (fun x => InformationTheory.klFun (1 + t * g x))
      (μ : Measure (Torus 1)) :=
    (InformationTheory.continuous_klFun.comp
      (continuous_const.add (continuous_const.mul hc))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hiV : Integrable (fun x => t ^ 2 / 2 * g x ^ 2) (μ : Measure (Torus 1)) :=
    (((hc.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul (t ^ 2 / 2))
  have hb : ∀ᵐ x ∂(μ : Measure (Torus 1)),
      ‖InformationTheory.klFun (1 + t * g x) - t ^ 2 / 2 * g x ^ 2‖ ≤
        4 * B ^ 3 * |t| ^ 3 := Eventually.of_forall fun x => by
    have hz : |t * g x| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)).trans ht
    have h := relativeSplit_kl_taylor hz
    rw [Real.norm_eq_abs]
    have he : t ^ 2 / 2 * g x ^ 2 = (t * g x) ^ 2 / 2 := by ring
    rw [he]
    apply h.trans
    rw [abs_mul, mul_pow]
    have hx := pow_le_pow_left₀ (abs_nonneg (g x)) (hB x) 3
    nlinarith [pow_nonneg (abs_nonneg t) 3]
  have hh := norm_integral_le_of_norm_le_const hb
  rw [integral_sub hiK hiV, integral_const_mul, Real.norm_eq_abs] at hh
  simpa using hh

/-- The information coefficient converges using only the genuine weighted L2
gradient. The spatial gradient is not assumed continuous or smooth. -/
theorem relativeSplit_information_coefficient_tendsto
    (μ : ProbabilityMeasure (Torus 1)) (g : Torus 1 → ℝ) (hc : Continuous g)
    (G : Torus 1 → Tangent 1) (hG : MemLp G 2 (μ : Measure (Torus 1))) :
    Tendsto (fun t : ℝ => ∫ x, ‖G x‖ ^ 2 / (1 + t * g x) ∂(μ : Measure (Torus 1)))
      (𝓝 0) (𝓝 (∫ x, ‖G x‖ ^ 2 ∂(μ : Measure (Torus 1)))) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have ht : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const B
  have he : ∀ᶠ t : ℝ in 𝓝 0, |t| * B ≤ 1 / 2 :=
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hi : Integrable (fun x => 2 * ‖G x‖ ^ 2) (μ : Measure (Torus 1)) :=
    hG.norm.integrable_sq.const_mul 2
  have hm (t : ℝ) : AEStronglyMeasurable
      (fun x => ‖G x‖ ^ 2 / (1 + t * g x)) (μ : Measure (Torus 1)) := by
    have hnum : AEMeasurable (fun x => ‖G x‖ ^ 2) (μ : Measure (Torus 1)) :=
      (hG.aestronglyMeasurable.norm.pow 2).aemeasurable
    have hden : AEMeasurable (fun x => (1 : ℝ) + t * g x) (μ : Measure (Torus 1)) :=
      (continuous_const.add (continuous_const.mul hc)).aemeasurable
    have hquot := (hnum.div hden).aestronglyMeasurable
    have heq : ((fun x : Torus 1 => ‖G x‖ ^ 2) / (fun x => 1 + t * g x)) =
        (fun x => ‖G x‖ ^ 2 / (1 + t * g x)) := by
      funext x
      rfl
    rw [heq] at hquot
    exact hquot
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => 2 * ‖G x‖ ^ 2) (Eventually.of_forall hm) ?_ hi ?_
  · filter_upwards [he] with t ht
    exact Eventually.of_forall fun x => by
      have hx : |g x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x)
      have htg : |t * g x| ≤ 1 / 2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hx (abs_nonneg t)).trans ht
      have hden : 0 < 1 + t * g x := by linarith [(abs_le.mp htg).1]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg ‖G x‖, (abs_le.mp htg).1]
  · exact Eventually.of_forall fun x => by
      have hcden : Continuous (fun t : ℝ => (1 : ℝ) + t * g x) :=
        continuous_const.add (continuous_id.mul continuous_const)
      have hd : Tendsto (fun t : ℝ => 1 + t * g x) (𝓝 0) (𝓝 (1 : ℝ)) := by
        simpa only [zero_mul, add_zero] using hcden.tendsto (0 : ℝ)
      have hn : Tendsto (fun _ : ℝ => ‖G x‖ ^ 2) (𝓝 (0 : ℝ)) (𝓝 (‖G x‖ ^ 2)) :=
        tendsto_const_nhds
      have hquot := hn.div hd one_ne_zero
      have heq : ((fun _ : ℝ => ‖G x‖ ^ 2) / (fun t => 1 + t * g x)) =
          (fun t => ‖G x‖ ^ 2 / (1 + t * g x)) := by
        funext t
        rfl
      rw [heq] at hquot
      simpa only [div_one] using hquot

/-- The exact finite split's quadratic coefficient is strictly positive for
EVERY actual scalar minimizer and EVERY nontrivial finite family of centered
native H1 tangents. No smoothness or weight lower bound is imposed. -/
theorem elementaryModel_minimizer_split_quadratic_positive :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ∀ (q : ℕ+) (θ : Fin q → ℝ), (∀ s, 0 < θ s) →
              ∀ f : Fin q → WeakH1Test (densityMeasure ρ),
                (∀ s, ∫ x, (f s).fn x ∂(densityMeasure ρ : Measure (Torus 1)) = 0) →
                0 < (∑ s, θ s * ∫ x, (f s).fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) →
                0 < ((∑ s, θ s * ∫ x, ((f s).grad x 0) ^ 2
                    ∂(densityMeasure ρ : Measure (Torus 1))) -
                  (scalarRate (modelData h ε) b).toReal *
                    (∑ s, θ s * ∫ x, (f s).fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)))) /
                  (2 * (scalarGap (modelData h ε) ρ : ℝ)) := by
  obtain ⟨δ, hδ, hmain⟩ := elementaryModel_minimizer_poincare_gap
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  obtain ⟨ε0, κ, hε0, hεmax, hκ, hgap⟩ := hmain h hh hhd
  refine ⟨ε0, hε0, hεmax, fun ε hε hεsmall b ρ hG hmin q θ hθ f hm hB => ?_⟩
  have hPC := (hgap ε hε hεsmall b ρ hG hmin).1
  let r := (scalarRate (modelData h ε) b).toReal
  let B := ∑ s, θ s * ∫ x, (f s).fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
  have hper (s : Fin q) :
      (r + κ) * (∫ x, (f s).fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) ≤
        ∫ x, ((f s).grad x 0) ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := by
    have ht := ordinaryRoot_poincare_real (densityMeasure ρ)
      (show 0 ≤ r + κ by dsimp only [r]; positivity) hPC (f s)
    simpa only [weightedVariance, hm s, sub_zero] using ht
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => mul_le_mul_of_nonneg_left (hper s) (hθ s).le)
  have he : (∑ s, θ s * ((r + κ) *
      ∫ x, (f s).fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)))) = (r + κ) * B := by
    dsimp only [B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he] at hsum
  apply div_pos _ (mul_pos (by norm_num) (show 0 < (scalarGap (modelData h ε) ρ : ℝ) from hG))
  change 0 < _ - r * B
  change 0 < B at hB
  nlinarith [mul_pos hκ hB]

end DGPS.Examples.ThreeSpeciesCircle
