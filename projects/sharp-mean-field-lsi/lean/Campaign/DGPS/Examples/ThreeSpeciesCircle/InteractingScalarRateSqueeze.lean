import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarTrialLinear

/-! The actual scalar rate approaches the ordinary rate at fixed field, with
linear coupling control. The lower bound covers all original H1 competitors;
the upper bound uses the actual ordinary-root trial. No attainment premise. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A uniform lower bound for the actual scalar rate, derived from the full-H1
ordinary inequality and the true signed correction entropy bound. -/
theorem elementaryModel_scalarRate_coupling_lower {h : ℝ} (hh : 0 < h) :
    ∃ ε0 K : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < K ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ENNReal.ofReal ((ordinaryLSRate (ordinaryReference h)).toReal - K * ε) ≤
          scalarRate (modelData h ε) b := by
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  obtain ⟨K, hK, hCorrection⟩ := elementaryC_family_entropy_bound hh a
  obtain ⟨ε0, hε0, hεmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  refine ⟨ε0, K, hε0, hεmax, hK, fun ε hε hεsmall b => ?_⟩
  unfold scalarRate
  apply le_iInf
  intro τ
  let ρ := τ.1
  let H := (ordinaryEntropy h ρ).toReal
  let I := (ordinaryFisher h ρ).toReal
  let GP : ℝ := scalarGap (modelData h ε) ρ
  let DD := (scalarDissipation (modelData h ε) b ρ).toReal
  have hGP : 0 < GP := τ.2
  have hGlo : H ≤ 2 * GP := by
    have hg := (hgap ε hε hεsmall (SpeciesFamily.single ρ)).1
    have ht : (1 / 2 : ℝ) * H ≤ GP := by
      simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
        SpeciesFamily.single_density, one_mul] using hg
    linarith
  have hCorr : |elementaryC h a ρ| ≤ K * H := by
    have hc := hCorrection (SpeciesFamily.single ρ)
    have he : elementaryC h a (barycenter (SpeciesFamily.single ρ)) = elementaryC h a ρ := by
      unfold elementaryC
      simp_rw [densityMeasure_barycenter_single, barycenter_single_density]
    rw [he] at hc
    simpa only [sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul] using hc
  have hDef := elementaryModel_scalar_deficit_real hh hε (hεsmall.trans_le hεmax) b ρ a
  change DD - 2 * a * GP = I - 2 * a * H + ε * elementaryC h a ρ + ε ^ 2 * elementaryJ h ρ at hDef
  have hOrdinary := elementary_ordinary_deficit_nonneg h ρ
  change 0 ≤ I - 2 * a * H at hOrdinary
  have hClo := mul_le_mul_of_nonneg_left (abs_le.mp hCorr).1 hε.le
  have hJ := mul_nonneg (sq_nonneg ε) (elementaryJ_nonneg h ρ)
  have hHmul := mul_le_mul_of_nonneg_left hGlo (mul_nonneg hε.le hK.le)
  have hDlower : 2 * (a - K * ε) * GP ≤ DD := by nlinarith
  have hreal : a - K * ε ≤ DD / (2 * GP) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * GP)).2
    nlinarith
  have hDfin := (elementaryModel_scalarDissipation_real h ε b ρ).1
  have hq : scalarQuotient (modelData h ε) b ρ = ENNReal.ofReal (DD / (2 * GP)) := by
    unfold scalarQuotient
    rw [ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * GP),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal hDfin]
    simp only [DD, GP, ENNReal.ofReal_ofNat]
  change ENNReal.ofReal (a - K * ε) ≤ scalarQuotient (modelData h ε) b ρ
  rw [hq]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Concrete two-sided linear control at fixed field. Both constants precede
the coupling and every drift provider; no actual optimizer or rate limit is an
input. This supplies the rate convergence needed for subsequent Euler capture. -/
theorem elementaryModel_scalarRate_coupling_squeeze (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 K : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < K ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ENNReal.ofReal ((ordinaryLSRate (ordinaryReference h)).toReal - K * ε) ≤
            scalarRate (modelData h ε) b ∧
          scalarRate (modelData h ε) b ≤
            ENNReal.ofReal ((ordinaryLSRate (ordinaryReference h)).toReal + K * ε) := by
  refine ⟨D.radius, D.radius_pos, le_rfl, fun h hh hhd => ?_⟩
  obtain ⟨εL, KL, hεL, hεLmax, hKL, hlower⟩ := elementaryModel_scalarRate_coupling_lower hh
  obtain ⟨σ, _, hpos, hquot, _⟩ := D.roots h hh hhd
  obtain ⟨εT, KT, hεT, _, hKT, htrial⟩ :=
    ordinaryRoot_interacting_scalar_trial_linear hh (σ 0) (hpos 0) (hquot 0)
  refine ⟨min εL εT, KL + KT, lt_min hεL hεT, (min_le_left _ _).trans hεLmax,
    add_pos hKL hKT, fun ε hε hεsmall b => ⟨?_, ?_⟩⟩
  · exact (ENNReal.ofReal_le_ofReal (by nlinarith)).trans
      (hlower ε hε (hεsmall.trans_le (min_le_left _ _)) b)
  · obtain ⟨hG, hQ⟩ := htrial ε hε (hεsmall.trans_le (min_le_right _ _)) b
    exact ((scalarRate_le_quotient (modelData h ε) b (σ 0) hG).trans hQ).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith))

end DGPS.Examples.ThreeSpeciesCircle
