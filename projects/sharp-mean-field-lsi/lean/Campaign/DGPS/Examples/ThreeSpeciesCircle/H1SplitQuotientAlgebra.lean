import DGPS.Examples.ThreeSpeciesCircle.H1SplitRealInformation

/-! Two-sided quotient remainder algebra, to be applied to the exact split
entropy and information identities. The remainder is defined from the quotient. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

theorem relativeSplit_entropy_coefficient_tendsto (μ : ProbabilityMeasure (Torus 1))
    (g : Torus 1 → ℝ) (hc : Continuous g) :
    Tendsto (fun t : ℝ =>
        (∫ x, InformationTheory.klFun (1 + t * g x) ∂(μ : Measure (Torus 1))) / t ^ 2)
      (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 ((∫ x, g x ^ 2 ∂(μ : Measure (Torus 1))) / 2)) := by
  obtain ⟨B, hBb⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hB (x : Torus 1) : |g x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hBb x (Set.mem_univ x)
  have hB0 : 0 ≤ B := (abs_nonneg (g 0)).trans (hB 0)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * B ≤ 1 / 2 := by
    have ht : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const B
    exact (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hne : ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0, t ≠ 0 := self_mem_nhdsWithin
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0,
      ‖(∫ x, InformationTheory.klFun (1 + t * g x) ∂(μ : Measure (Torus 1))) / t ^ 2 -
        (∫ x, g x ^ 2 ∂(μ : Measure (Torus 1))) / 2‖ ≤ 4 * B ^ 3 * |t| := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, hne] with t ht htn
    have hs : 0 < t ^ 2 := sq_pos_of_ne_zero htn
    have hh := relativeSplit_entropy_taylor μ g hc hB ht
    have he : (∫ x, InformationTheory.klFun (1 + t * g x) ∂(μ : Measure (Torus 1))) / t ^ 2 -
        (∫ x, g x ^ 2 ∂(μ : Measure (Torus 1))) / 2 =
        ((∫ x, InformationTheory.klFun (1 + t * g x) ∂(μ : Measure (Torus 1))) -
          t ^ 2 / 2 * ∫ x, g x ^ 2 ∂(μ : Measure (Torus 1))) / t ^ 2 := by
      field_simp [htn]
      <;> ring
    rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).2
    convert hh using 1
    rw [← sq_abs t]
    ring
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  have ha : Tendsto (fun t : ℝ => |t|)
      (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := {t : ℝ | t ≠ 0}))
  simpa only [mul_zero] using ha.const_mul (4 * B ^ 3)

/-- Exact rational quotient expansion from its proved entropy and information
coefficients. This is algebra only; actual split identities discharge its inputs. -/
theorem splitQuotient_remainder {G r B E : ℝ} (hG : 0 < G)
    (H I : ℝ → ℝ)
    (hH : Tendsto (fun t => H t / t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 (B / 2)))
    (hI : Tendsto I (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 E)) :
    let Q := fun t : ℝ => (2 * r * G + t ^ 2 * I t) / (2 * (G + H t))
    let c := (E - r * B) / (2 * G)
    Tendsto (fun t => (Q t - r - c * t ^ 2) / t ^ 2)
      (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0) := by
  dsimp only
  have ht : Tendsto (fun t : ℝ => t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => t)
        (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left (nhdsWithin_le_nhds (s := {t : ℝ | t ≠ 0}))
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hi.pow 2
  have hne : ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0, t ≠ 0 := self_mem_nhdsWithin
  have hHz : Tendsto H (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0) := by
    have hh := hH.mul ht
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hne] with t htn
    exact div_mul_cancel₀ (H t) (pow_ne_zero 2 htn)
  have hden : Tendsto (fun t => 2 * (G + H t))
      (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 (2 * G)) := by
    simpa using (tendsto_const_nhds.add hHz).const_mul 2
  have hdenpos : ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0, 0 < G + H t := by
    have hh : Tendsto (fun t => G + H t) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 G) := by
      simpa using tendsto_const_nhds.add hHz
    exact hh.eventually (lt_mem_nhds hG)
  have hnum := hI.sub (hH.const_mul (2 * r))
  have hlimit := (hnum.div hden (by positivity : 2 * G ≠ 0)).sub
    (tendsto_const_nhds (x := (E - r * B) / (2 * G)))
  have heq : (E - 2 * r * (B / 2)) / (2 * G) - (E - r * B) / (2 * G) = 0 := by ring
  rw [heq] at hlimit
  apply hlimit.congr'
  filter_upwards [hne, hdenpos] with t htn hdp
  simp only [Pi.div_apply]
  field_simp [htn, hdp.ne', hG.ne']
  <;> ring

/-- A positive actual quadratic coefficient and a two-sided little-o remainder
give strict increase for every sufficiently small nonzero parameter, both signs. -/
theorem splitQuotient_eventually_strict {r c : ℝ} (hc : 0 < c) (Q : ℝ → ℝ)
    (hrem : Tendsto (fun t => (Q t - r - c * t ^ 2) / t ^ 2)
      (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0)) :
    ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0, r < Q t := by
  have he := hrem.eventually (lt_mem_nhds (show -c / 2 < (0 : ℝ) by linarith))
  have hne : ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0, t ≠ 0 := self_mem_nhdsWithin
  filter_upwards [he, hne] with t ht htn
  have hs : 0 < t ^ 2 := sq_pos_of_ne_zero htn
  have hh := (lt_div_iff₀ hs).1 ht
  nlinarith [mul_pos hc hs]

end DGPS.Examples.ThreeSpeciesCircle
