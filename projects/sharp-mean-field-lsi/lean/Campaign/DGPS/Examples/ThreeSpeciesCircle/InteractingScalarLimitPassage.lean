import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarLimits
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarCompactness

/-! Actual scalar gap continuity and dissipation lower semicontinuity from
the original a.e.-uniform square-root compactness output. No positive limiting
gap or desired lower-semicontinuity conclusion is an input. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem root_pointwise_limit (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n) :
    ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
  filter_upwards [ae_all_iff.mpr hae] with x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]
    exact hx n) hη

/-- Every bounded continuous moment of the actual probabilities converges from
the genuine original-root compactness output. -/
theorem elementaryModel_moments_of_uniform_roots (ρ : ℕ → AbsoluteDensity 1)
    (ρL : AbsoluteDensity 1) {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) :
    ∀ g : Torus 1 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, g x ∂(densityMeasure (ρ n) : Measure (Torus 1))) atTop
        (𝓝 (∫ x, g x ∂(densityMeasure ρL : Measure (Torus 1)))) := by
  intro g
  have ht := tendsto_integral_comp_mul (T := fun t : ℝ => t ^ 2) (continuous_pow 2)
    g.continuous (Cc := ‖g‖) (fun x => by
      simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x)
    (fun n => (ρ n).memLp_sqrt.aestronglyMeasurable) hub (root_pointwise_limit ρ ρL hη hae)
  simpa only [Structural.budget_integral_densityMeasure, AbsoluteDensity.density] using ht

private theorem eventually_lower_real {f : ℕ → ℝ≥0∞} {F : ℝ≥0∞}
    (hf : ∀ n, f n ≠ ⊤) (hF : F ≠ ⊤) (hl : F ≤ liminf f atTop)
    {r : ℝ} (hr : r < F.toReal) : ∀ᶠ n in atTop, r < (f n).toReal := by
  by_cases hr0 : r < 0
  · exact Eventually.of_forall fun _ => hr0.trans_le ENNReal.toReal_nonneg
  have hnonneg : 0 ≤ r := le_of_not_gt hr0
  have he := eventually_lt_of_lt_liminf
    (((ENNReal.ofReal_lt_iff_lt_toReal hnonneg hF).2 hr).trans_le hl)
  exact he.mono fun n hn => (ENNReal.ofReal_lt_iff_lt_toReal hnonneg (hf n)).1 hn

private theorem correction_liminf {f : ℕ → ℝ≥0∞} {F : ℝ≥0∞}
    (hf : ∀ n, f n ≠ ⊤) (hF : F ≠ ⊤) (hl : F ≤ liminf f atTop)
    {c : ℕ → ℝ} {C : ℝ} (hc : Tendsto c atTop (𝓝 C)) :
    ENNReal.ofReal (F.toReal + C) ≤
      liminf (fun n => ENNReal.ofReal ((f n).toReal + c n)) atTop := by
  apply (Filter.le_liminf_iff').2
  intro b hb
  have hbfin : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb.le
  have hbr : b.toReal < F.toReal + C := (ENNReal.lt_ofReal_iff_toReal_lt hbfin).1 hb
  let δ := (F.toReal + C - b.toReal) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have he := eventually_lower_real hf hF hl
    (show F.toReal - δ < F.toReal by linarith)
  filter_upwards [he, hc.eventually (lt_mem_nhds (show C - δ < C by linarith))] with n hn hcn
  apply le_of_lt
  apply (ENNReal.lt_ofReal_iff_toReal_lt hbfin).2
  dsimp only [δ] at hn hcn
  linarith

/-- The genuine current scalar gap converges, including when its limit is zero.
Ordinary entropy continuity is proved from the original roots, not assumed. -/
theorem elementaryModel_scalarGap_tendsto {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) :
    Tendsto (fun n => (scalarGap (modelData h ε) (ρ n) : ℝ)) atTop
      (𝓝 (scalarGap (modelData h ε) ρL : ℝ)) := by
  have hw := elementaryModel_moments_of_uniform_roots ρ ρL hη hae R hub
  have hmC := hw (BoundedContinuousFunction.mkOfCompact
    ⟨featureC h, (isSmooth_featureC h).continuous_torus⟩)
  have hmS := hw (BoundedContinuousFunction.mkOfCompact
    ⟨featureS h, (isSmooth_featureS h).continuous_torus⟩)
  have hmB := hw (BoundedContinuousFunction.mkOfCompact
    ⟨featureB h, (isSmooth_featureB h).continuous_torus⟩)
  change Tendsto (fun n => momC h (densityMeasure (ρ n))) atTop
    (𝓝 (momC h (densityMeasure ρL))) at hmC
  change Tendsto (fun n => momS h (densityMeasure (ρ n))) atTop
    (𝓝 (momS h (densityMeasure ρL))) at hmS
  change Tendsto (fun n => momB h (densityMeasure (ρ n))) atTop
    (𝓝 (momB h (densityMeasure ρL))) at hmB
  have hQ : Tendsto (fun n => elementaryQ h (densityMeasure (ρ n))) atTop
      (𝓝 (elementaryQ h (densityMeasure ρL))) := by
    simp_rw [elementaryQ_moments]
    exact ((hmC.pow 2).add (hmS.pow 2)).const_mul kAlpha |>.sub ((hmB.pow 2).const_mul kBeta)
  have hH := (ENNReal.tendsto_toReal (str025_entropy_ne_top h ρL)).comp
    (tendsto_ordinaryEntropy h hub (root_pointwise_limit ρ ρL hη hae))
  have hgap (τ : AbsoluteDensity 1) : (scalarGap (modelData h ε) τ : ℝ) =
      (ordinaryEntropy h τ).toReal + ε / 2 * elementaryQ h (densityMeasure τ) := by
    have hg := elementaryModel_speciesGap_expansion hh hε hεmax (SpeciesFamily.single τ)
    simpa only [speciesGap_single, densityMeasure_barycenter_single, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] using hg
  simp_rw [hgap]
  exact hH.add (hQ.const_mul (ε / 2))

/-- Extended-real gap convergence for the actual canonical scalar quotient. -/
theorem elementaryModel_scalarGap_ennreal_tendsto {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) :
    Tendsto (fun n => (scalarGap (modelData h ε) (ρ n) : ℝ≥0∞)) atTop
      (𝓝 (scalarGap (modelData h ε) ρL : ℝ≥0∞)) := by
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.tendsto_ofReal
    (elementaryModel_scalarGap_tendsto hh hε hεmax ρ ρL hη hae R hub)

/-- True scalar dissipation lower semicontinuity for the changing mean field.
The finite correction continuity and ordinary Fisher lower semicontinuity are
derived from the same original a.e.-uniform root convergence. -/
theorem elementaryModel_scalarDissipation_le_liminf (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) :
    scalarDissipation (modelData h ε) b ρL ≤
      liminf (fun n => scalarDissipation (modelData h ε) b (ρ n)) atTop := by
  let c := fun τ : AbsoluteDensity 1 => ε * elementaryC h 0 τ + ε ^ 2 * elementaryJ h τ
  have hc : Tendsto (fun n => c (ρ n)) atTop (𝓝 (c ρL)) := by
    have ht := elementary_deficit_correction_tendsto h ε ρ ρL
      (elementaryModel_moments_of_uniform_roots ρ ρL hη hae R hub)
    have he (τ : AbsoluteDensity 1) : c τ =
        2 * ε * (∫ x, τ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
          ε ^ 2 * elementaryJ h τ := by dsimp only [c, elementaryC]; ring
    simpa only [he] using ht
  have hD (τ : AbsoluteDensity 1) : scalarDissipation (modelData h ε) b τ =
      ENNReal.ofReal ((ordinaryFisher h τ).toReal + c τ) := by
    obtain ⟨hfin, hval⟩ := elementaryModel_scalarDissipation_real h ε b τ
    have hv : (scalarDissipation (modelData h ε) b τ).toReal =
        (ordinaryFisher h τ).toReal + c τ := by
      rw [hval]
      dsimp only [c]
      ring
    rw [← hv, ENNReal.ofReal_toReal hfin]
  have hlim := correction_liminf (fun n => str025_fisher_ne_top h (ρ n))
    (str025_fisher_ne_top h ρL) (ordinaryFisher_le_liminf h ρ ρL hη hae) hc
  simpa only [← hD] using hlim

end DGPS.Examples.ThreeSpeciesCircle
