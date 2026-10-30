import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootDensitySegmentStrongJensen
import DGPS.Structural.CircleDensityRatio

/-! Fixed-field stability of actual global one-body minimizers in a common
ordinary-root density tube. No classification or desired density bound is assumed. -/

noncomputable section
open MeasureTheory Filter Topology Set
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem stability_integrable_cont_mul {μ : Measure (Torus 1)} {c f : Torus 1 → ℝ}
    (hc : Continuous c) (hf : Integrable f μ) : Integrable (fun x => c x * f x) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact hf.bdd_mul (c := C) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

def h1DensityCost (h r : ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal

private theorem stability_field_segment_integral (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (V : Torus 1 → ℝ) (hV : Continuous V) :
    (∫ x, V x ∂(densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht) : Measure (Torus 1))) =
      (1 - t) * (∫ x, V x ∂(densityMeasure ρ : Measure (Torus 1))) +
        t * (∫ x, V x ∂(densityMeasure σ : Measure (Torus 1))) := by
  have hiρ : Integrable (fun x => ρ.density x * V x) (haar 1) := by
    simpa only [mul_comm] using stability_integrable_cont_mul hV ρ.integrable_density
  have hiσ : Integrable (fun x => σ.density x * V x) (haar 1) := by
    simpa only [mul_comm] using stability_integrable_cont_mul hV σ.integrable_density
  rw [Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure,
    Structural.budget_integral_densityMeasure]
  have he := h1DensitySegment_density_ae ρ σ u v hu hv hup hvp hρ hσ t ht
  calc
    _ = ∫ x, (1 - t) * (ρ.density x * V x) + t * (σ.density x * V x) ∂haar 1 := by
      apply integral_congr_ae
      exact he.mono fun x hx => by dsimp only at hx ⊢; rw [hx]; ring
    _ = _ := by
      rw [integral_add (hiρ.const_mul (1 - t)) (hiσ.const_mul t), integral_const_mul, integral_const_mul]

private theorem stability_midpoint_globalMin (h r c : ℝ) (hc : 0 < c)
    (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (V1 V2 : Torus 1 → ℝ) (hV1 : Continuous V1) (hV2 : Continuous V2)
    (L : ℝ) (hL : 0 ≤ L) (hVL : ∀ x, |V1 x - V2 x| ≤ L)
    (hmin1 : ∀ τ : AbsoluteDensity 1,
      h1DensityCost h r ρ + (∫ x, V1 x ∂(densityMeasure ρ : Measure (Torus 1))) ≤
        h1DensityCost h r τ + ∫ x, V1 x ∂(densityMeasure τ : Measure (Torus 1)))
    (hmin2 : ∀ τ : AbsoluteDensity 1,
      h1DensityCost h r σ + (∫ x, V2 x ∂(densityMeasure σ : Measure (Torus 1))) ≤
        h1DensityCost h r τ + ∫ x, V2 x ∂(densityMeasure τ : Measure (Torus 1)))
    (hstrong :
      let ht : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
      let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ (1 / 2) ht
      h1DensityCost h r τ ≤ (1 - (1 / 2 : ℝ)) * h1DensityCost h r ρ +
        (1 / 2 : ℝ) * h1DensityCost h r σ -
          c * (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) * ∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1) :
    c * (∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1) ≤
        (∫ x, (V1 x - V2 x) * (σ.density x - ρ.density x) ∂haar 1) ∧
      Real.sqrt (∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1) ≤ L / c ∧
        (∫ x, |σ.density x - ρ.density x| ∂haar 1) ≤ L / c := by
  have ht : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ (1 / 2) ht
  have hm1 := hmin1 τ
  have hm2 := hmin2 τ
  rw [stability_field_segment_integral ρ σ u v hu hv hup hvp hρ hσ (1 / 2) ht V1 hV1] at hm1
  rw [stability_field_segment_integral ρ σ u v hu hv hup hvp hρ hσ (1 / 2) ht V2 hV2] at hm2
  let d := fun x => σ.density x - ρ.density x
  have hdAE : d =ᵐ[haar 1] (fun x => v x ^ 2 - u x ^ 2) := by
    filter_upwards [hρ, hσ] with x hx hy
    change σ.sqrt x ^ 2 - ρ.sqrt x ^ 2 = _
    rw [hx, hy]
  have hd2 : MemLp d 2 (haar 1) :=
    (memLp_congr_ae hdAE).mpr (memLp_two_of_continuous ((hv.pow 2).sub (hu.pow 2)))
  have hi1ρ : Integrable (fun x => ρ.density x * V1 x) (haar 1) := by
    simpa only [mul_comm] using stability_integrable_cont_mul hV1 ρ.integrable_density
  have hi1σ : Integrable (fun x => σ.density x * V1 x) (haar 1) := by
    simpa only [mul_comm] using stability_integrable_cont_mul hV1 σ.integrable_density
  have hi2ρ : Integrable (fun x => ρ.density x * V2 x) (haar 1) := by
    simpa only [mul_comm] using stability_integrable_cont_mul hV2 ρ.integrable_density
  have hi2σ : Integrable (fun x => σ.density x * V2 x) (haar 1) := by
    simpa only [mul_comm] using stability_integrable_cont_mul hV2 σ.integrable_density
  have hcrossEq : (∫ x, (V1 x - V2 x) * d x ∂haar 1) =
      (∫ x, V1 x ∂(densityMeasure σ : Measure (Torus 1))) -
        (∫ x, V1 x ∂(densityMeasure ρ : Measure (Torus 1))) +
        (∫ x, V2 x ∂(densityMeasure ρ : Measure (Torus 1))) -
          (∫ x, V2 x ∂(densityMeasure σ : Measure (Torus 1))) := by
    have he (x : Torus 1) : (V1 x - V2 x) * d x =
        σ.density x * V1 x - ρ.density x * V1 x + ρ.density x * V2 x - σ.density x * V2 x := by
      dsimp only [d]
      ring
    simp_rw [he]
    have hs := integral_sub ((hi1σ.sub hi1ρ).add hi2ρ) hi2σ
    have ha := integral_add (hi1σ.sub hi1ρ) hi2ρ
    have hb := integral_sub hi1σ hi1ρ
    simp only [Pi.sub_apply, Pi.add_apply] at hs ha hb
    rw [hs, ha, hb,
      ← Structural.budget_integral_densityMeasure σ V1,
      ← Structural.budget_integral_densityMeasure ρ V1,
      ← Structural.budget_integral_densityMeasure ρ V2,
      ← Structural.budget_integral_densityMeasure σ V2]
  have hmono : c * (∫ x, d x ^ 2 ∂haar 1) ≤ ∫ x, (V1 x - V2 x) * d x ∂haar 1 := by
    rw [hcrossEq]
    change h1DensityCost h r τ ≤ _ at hstrong
    change c * (∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1) ≤ _
    nlinarith only [hm1, hm2, hstrong]
  have hiCross : Integrable (fun x => (V1 x - V2 x) * d x) (haar 1) :=
    stability_integrable_cont_mul (hV1.sub hV2) (hd2.integrable one_le_two)
  have hCrossUpper : (∫ x, (V1 x - V2 x) * d x ∂haar 1) ≤ L * ∫ x, |d x| ∂haar 1 := by
    rw [← integral_const_mul]
    apply integral_mono hiCross ((hd2.integrable one_le_two).abs.const_mul L)
    intro x
    calc
      _ ≤ |V1 x - V2 x| * |d x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hVL x) (abs_nonneg _)
  have hL1 := Structural.integral_abs_le_sqrt hd2
  let N := ∫ x, d x ^ 2 ∂haar 1
  have hN : 0 ≤ N := integral_nonneg fun _ => sq_nonneg _
  have hCN : c * N ≤ L * Real.sqrt N :=
    (hmono.trans hCrossUpper).trans (mul_le_mul_of_nonneg_left hL1 hL)
  have hS : Real.sqrt N ≤ L / c := by
    by_cases hz : Real.sqrt N = 0
    · rw [hz]
      exact div_nonneg hL hc.le
    · have hs : 0 < Real.sqrt N := lt_of_le_of_ne (Real.sqrt_nonneg N) (Ne.symm hz)
      have hm : (c * Real.sqrt N) * Real.sqrt N ≤ L * Real.sqrt N := by
        calc
          _ = c * N := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hN]
          _ ≤ _ := hCN
      have hcS := (mul_le_mul_iff_left₀ hs).mp hm
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcS)
  exact ⟨hmono, hS, hL1.trans hS⟩

/-- Actual same-graph fixed-field stability. Only the factual GLOBAL
one-body minimality conditions and actual field difference bound are supplied;
the common strong-Jensen/PC constants are derived from the actual root graph. -/
theorem ordinaryGraph_globalMin_density_stability (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ S : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (S j).density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
      ∃ w : Fin 3 → Torus 1 → ℝ, ∃ q c : ℝ,
        (∀ j, Continuous (w j)) ∧ (∀ j x, 0 < w j x) ∧
        (∀ j, (S j).sqrt =ᵐ[haar 1] w j) ∧ 0 < q ∧ q ≤ 1 / 4 ∧ 0 < c ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ (ordinaryLSRate (ordinaryReference h)).toReal →
          ∀ j : Fin 3, ∀ (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ),
            ∀ (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x),
            ∀ (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v),
            (∀ x, (1 - q) ^ 2 * w j x ^ 2 ≤ u x ^ 2) →
            (∀ x, u x ^ 2 ≤ (1 + q) ^ 2 * w j x ^ 2) →
            (∀ x, (1 - q) ^ 2 * w j x ^ 2 ≤ v x ^ 2) →
            (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w j x ^ 2) →
            ∀ V1 V2 : Torus 1 → ℝ, Continuous V1 → Continuous V2 →
            ∀ L : ℝ, 0 ≤ L → (∀ x, |V1 x - V2 x| ≤ L) →
            (∀ τ : AbsoluteDensity 1,
              h1DensityCost h r ρ + (∫ x, V1 x ∂(densityMeasure ρ : Measure (Torus 1))) ≤
                h1DensityCost h r τ + ∫ x, V1 x ∂(densityMeasure τ : Measure (Torus 1))) →
            (∀ τ : AbsoluteDensity 1,
              h1DensityCost h r σ + (∫ x, V2 x ∂(densityMeasure σ : Measure (Torus 1))) ≤
                h1DensityCost h r τ + ∫ x, V2 x ∂(densityMeasure τ : Measure (Torus 1))) →
            c * (∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1) ≤
                (∫ x, (V1 x - V2 x) * (σ.density x - ρ.density x) ∂haar 1) ∧
              Real.sqrt (∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1) ≤ L / c ∧
                (∫ x, |σ.density x - ρ.density x| ∂haar 1) ≤ L / c := by
  obtain ⟨δ, hδ, hδr, hmain⟩ := ordinaryGraph_densitySegment_common_strongJensen D
  refine ⟨δ, hδ, hδr, fun h hh hhd S hS => ?_⟩
  obtain ⟨w, q, c, hw, hwp, hrep, hq, hq4, hc, hstrong⟩ := hmain h hh hhd S hS
  refine ⟨w, q, c, hw, hwp, hrep, hq, hq4, hc,
    fun r hr hra j ρ σ u v hu hv hup hvp hρ hσ hulo huhi hvlo hvhi V1 V2 hV1 hV2 L hL hVL hmin1 hmin2 => ?_⟩
  have ht : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hmid := hstrong r hr hra j ρ σ u v hu hv hup hvp hρ hσ hulo huhi hvlo hvhi (1 / 2) ht
  exact stability_midpoint_globalMin h r c hc ρ σ u v hu hv hup hvp hρ hσ
    V1 V2 hV1 hV2 L hL hVL hmin1 hmin2 hmid

end DGPS.Examples.ThreeSpeciesCircle
