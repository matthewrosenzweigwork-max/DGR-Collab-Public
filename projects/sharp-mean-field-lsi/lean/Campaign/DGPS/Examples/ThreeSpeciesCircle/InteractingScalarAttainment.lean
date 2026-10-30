import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarPositiveGapCompactness
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarLimitPassage

/-! Actual scalar-rate attainment. The minimizing-sequence construction remains below
an actual positive-gap trial, so the proved positive-gap compactness applies.
The actual limiting gap is proved positive before passing the actual dissipation
and denominator to the limit. No compactness or attainment conclusion is a premise. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem scalar_trial_or_minimizing_sequence (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (σ : AbsoluteDensity 1)
    (hσ : 0 < scalarGap (modelData h ε) σ) :
    scalarQuotient (modelData h ε) b σ = scalarRate (modelData h ε) b ∨
      ∃ ρ : ℕ → AbsoluteDensity 1,
        (∀ n, 0 < scalarGap (modelData h ε) (ρ n)) ∧
        (∀ n, scalarQuotient (modelData h ε) b (ρ n) ≤ scalarQuotient (modelData h ε) b σ) ∧
        Tendsto (fun n => scalarQuotient (modelData h ε) b (ρ n)) atTop
          (𝓝 (scalarRate (modelData h ε) b)) := by
  by_cases he : scalarQuotient (modelData h ε) b σ = scalarRate (modelData h ε) b
  · exact Or.inl he
  let r := scalarRate (modelData h ε) b
  have hrle : r ≤ scalarQuotient (modelData h ε) b σ :=
    scalarRate_le_quotient (modelData h ε) b σ hσ
  have hrt : r < scalarQuotient (modelData h ε) b σ := by
    by_contra hn
    exact he (le_antisymm (not_lt.mp hn) hrle)
  have hrfin : r ≠ ⊤ := (hrt.trans_le le_top).ne
  have hex : ∀ n : ℕ, ∃ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ ∧
      scalarQuotient (modelData h ε) b ρ <
        min (scalarQuotient (modelData h ε) b σ) (r + ((n : ℝ≥0∞) + 1)⁻¹) := by
    intro n
    have ht : r < min (scalarQuotient (modelData h ε) b σ)
        (r + ((n : ℝ≥0∞) + 1)⁻¹) :=
      lt_min hrt (ENNReal.lt_add_right hrfin (by simp))
    change (⨅ ρ : {ρ : AbsoluteDensity 1 // 0 < scalarGap (modelData h ε) ρ},
      scalarQuotient (modelData h ε) b ρ.1) < _ at ht
    obtain ⟨⟨ρ, hρ⟩, hq⟩ := iInf_lt_iff.1 ht
    exact ⟨ρ, hρ, hq⟩
  choose ρ hpos hq using hex
  have hδ : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    refine ht.congr (fun n => ?_)
    simp [Function.comp]
  have hupper : Tendsto (fun n : ℕ => r + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add hδ
  refine Or.inr ⟨ρ, hpos, fun n => (lt_min_iff.mp (hq n)).1.le, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => scalarRate_le_quotient (modelData h ε) b (ρ n) (hpos n))
    (fun n => (lt_min_iff.mp (hq n)).2.le)

private theorem root_bound_of_fisher (ρ : ℕ → AbsoluteDensity 1) {B : ℝ}
    (hB : ∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B) :
    ∃ R : ℝ, ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R := by
  let Γ := Real.sqrt (B / 4)
  refine ⟨1 + Γ, fun n => ?_⟩
  have hW := isWeakGradient_weakGradient (ρ n).sqrt_mem
  have hgrad : (eLpNorm (weakGradient (ρ n).sqrt (ρ n).sqrt_mem) 2 (haar 1)).toReal ≤ Γ := by
    rw [toReal_eLpNorm_two_vec hW.memLp_grad]
    apply Real.sqrt_le_sqrt
    have hb := hB n
    rw [circleFisher_eq_four_mul] at hb
    linarith
  have hroot : (eLpNorm (ρ n).sqrt 2 (haar 1)).toReal = 1 := by
    rw [toReal_eLpNorm_two (ρ n).memLp_sqrt, (ρ n).mass_one, Real.sqrt_one]
  obtain ⟨v, _, hvae, _, hv⟩ := exists_continuous_rep_one hW
  filter_upwards [hvae] with x hx
  rw [← hx]
  have hb := hv x
  rw [hroot] at hb
  linarith

/-- Actual scalar-rate attainment on the full original absolute H1 domain for the
fixed small-h/small-coupling model. Every analytic input is discharged by its actual
producer, with the ordinary graph selected once. -/
theorem elementaryModel_scalar_attainment_of_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), ∃ ρ : AbsoluteDensity 1,
          0 < scalarGap (modelData h ε) ρ ∧
          scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b := by
  obtain ⟨δ, hδ, hδr, hcompact⟩ := elementaryModel_scalar_sublevel_positiveGap_compactness D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨σ, ε0, hε0, hεmax, hC⟩ := hcompact h hh hhd
  refine ⟨ε0, hε0, hεmax, fun ε hε hεsmall b => ?_⟩
  obtain ⟨hσG, hsublevel⟩ := hC ε hε hεsmall b
  rcases scalar_trial_or_minimizing_sequence h ε b σ hσG with he | ⟨ρ, hpos, hq, hQconv⟩
  · exact ⟨σ, hσG, he⟩
  · obtain ⟨B, _, hBn, φ, ρL, η, hφ, hη, hae, _, hGpos⟩ := hsublevel ρ hpos hq
    obtain ⟨R, hR⟩ := root_bound_of_fisher ρ (fun n => (hBn n).1)
    have hGconv := elementaryModel_scalarGap_ennreal_tendsto hh hε
      (hεsmall.trans_le hεmax) (fun n => ρ (φ n)) ρL hη hae R (fun n => hR (φ n))
    have hDlsc := elementaryModel_scalarDissipation_le_liminf h ε b
      (fun n => ρ (φ n)) ρL hη hae R (fun n => hR (φ n))
    have hσDfin := (elementaryModel_scalarDissipation_real h ε b σ).1
    have hσQfin : scalarQuotient (modelData h ε) b σ ≠ ⊤ :=
      ((scalarQuotient_lt_top_iff (modelData h ε) b σ hσG).2 (lt_top_iff_ne_top.mpr hσDfin)).ne
    have hrfin : scalarRate (modelData h ε) b ≠ ⊤ := by
      intro ht
      have hl := scalarRate_le_quotient (modelData h ε) b σ hσG
      rw [ht, top_le_iff] at hl
      exact hσQfin hl
    have hprod : Tendsto (fun n => scalarQuotient (modelData h ε) b (ρ (φ n)) *
        (2 * (scalarGap (modelData h ε) (ρ (φ n)) : ℝ≥0∞))) atTop
        (𝓝 (scalarRate (modelData h ε) b * (2 * (scalarGap (modelData h ε) ρL : ℝ≥0∞)))) :=
      ENNReal.Tendsto.mul (hQconv.comp hφ.tendsto_atTop)
        (Or.inr (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top))
        (ENNReal.Tendsto.const_mul hGconv (Or.inr (by norm_num))) (Or.inr hrfin)
    have hN (n : ℕ) : scalarDissipation (modelData h ε) b (ρ (φ n)) ≤
        scalarQuotient (modelData h ε) b (ρ (φ n)) *
          (2 * (scalarGap (modelData h ε) (ρ (φ n)) : ℝ≥0∞)) := by
      have hden0 : 2 * (scalarGap (modelData h ε) (ρ (φ n)) : ℝ≥0∞) ≠ 0 :=
        mul_ne_zero (by norm_num) (by exact_mod_cast (hpos (φ n)).ne')
      have hdent : 2 * (scalarGap (modelData h ε) (ρ (φ n)) : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
      exact (ENNReal.div_le_iff hden0 hdent).1 le_rfl
    have hDlim : scalarDissipation (modelData h ε) b ρL ≤ scalarRate (modelData h ε) b *
        (2 * (scalarGap (modelData h ε) ρL : ℝ≥0∞)) := by
      refine hDlsc.trans ?_
      calc _ ≤ liminf (fun n => scalarQuotient (modelData h ε) b (ρ (φ n)) *
            (2 * (scalarGap (modelData h ε) (ρ (φ n)) : ℝ≥0∞))) atTop :=
              liminf_le_liminf (Eventually.of_forall hN)
        _ = _ := hprod.liminf_eq
    have hQlim : scalarQuotient (modelData h ε) b ρL ≤ scalarRate (modelData h ε) b :=
      ENNReal.div_le_of_le_mul hDlim
    exact ⟨ρL, hGpos, le_antisymm hQlim (scalarRate_le_quotient (modelData h ε) b ρL hGpos)⟩

/-- The concrete interacting scalar rate is attained for each fixed sufficiently small
positive h and sufficiently small h-dependent positive coupling. No graph or analytic
provider is a premise of this actual public factory. -/
theorem elementaryModel_scalar_attainment :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), ∃ ρ : AbsoluteDensity 1,
          0 < scalarGap (modelData h ε) ρ ∧
          scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨δ, hδ, _, hmain⟩ := elementaryModel_scalar_attainment_of_graph D
  exact ⟨δ, hδ, hmain⟩

end DGPS.Examples.ThreeSpeciesCircle
