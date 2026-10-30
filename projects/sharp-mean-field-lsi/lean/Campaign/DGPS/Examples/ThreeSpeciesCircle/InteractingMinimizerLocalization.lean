import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerInformation
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarTrialLinear
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitGlobal

/-! Uniform-in-coupling ordinary deficit and original-H1 localization for EVERY
actual scalar minimizer. No localization, information or regularity conclusion is a premise. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every actual scalar minimizer has ordinary deficit O(epsilon), with a single
constant fixed after h and before epsilon, drift and the minimizer. -/
theorem elementaryModel_minimizer_ordinaryDeficit_bound (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 K : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < K ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            (ordinaryFisher h ρ).toReal - 2 * (ordinaryLSRate (ordinaryReference h)).toReal *
              (ordinaryEntropy h ρ).toReal ≤ K * ε := by
  obtain ⟨δ, hδ, hδr, hinfo⟩ := elementaryModel_minimizer_uniform_information D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨εI, C, hεI, hεImax, hC, hInformation⟩ := hinfo h hh hhd
  obtain ⟨σ, _, hpos, hquot, _⟩ := D.roots h hh (hhd.trans_le hδr)
  obtain ⟨εT, KT, hεT, hεTmax, hKT, htrial⟩ :=
    ordinaryRoot_interacting_scalar_trial_linear hh (σ 0) (hpos 0) (hquot 0)
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  obtain ⟨KC, hKC, hCorrection⟩ := elementaryC_family_entropy_bound hh a
  obtain ⟨εG, hεG, _, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let K := (3 * KT + KC) * C + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min εI (min εT εG), K, lt_min hεI (lt_min hεT hεG),
    (min_le_left _ _).trans hεImax, hK, fun ε hε hεsmall b ρ hGP hmin => ?_⟩
  have heI : ε < εI := hεsmall.trans_le (min_le_left _ _)
  have heT : ε < εT := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heG : ε < εG := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let H := (ordinaryEntropy h ρ).toReal
  let I := (ordinaryFisher h ρ).toReal
  let G : ℝ := scalarGap (modelData h ε) ρ
  let DD := (scalarDissipation (modelData h ε) b ρ).toReal
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  have hG : 0 < G := hGP
  have hIH : I + H ≤ C := hInformation ε hε heI b ρ hGP hmin
  have hHC : H ≤ C := by linarith
  obtain ⟨hσG, hσQ⟩ := htrial ε hε heT b
  have hQ : scalarQuotient (modelData h ε) b ρ ≤ ENNReal.ofReal (a + KT * ε) := by
    rw [hmin]
    exact (scalarRate_le_quotient (modelData h ε) b (σ 0) hσG).trans hσQ
  have hDD : DD ≤ 2 * (a + KT * ε) * G := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hQ
    unfold scalarQuotient at hr
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity : 0 ≤ a + KT * ε)] at hr
    have hm := (div_le_iff₀ (by positivity : 0 < 2 * G)).mp hr
    change DD ≤ _ at hm
    nlinarith
  have hGap : G ≤ (3 / 2 : ℝ) * H := by
    have hg := (hgap ε hε heG (SpeciesFamily.single ρ)).2
    simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul] using hg
  have hCorr : |elementaryC h a ρ| ≤ KC * H := by
    have hc := hCorrection (SpeciesFamily.single ρ)
    have he : elementaryC h a (barycenter (SpeciesFamily.single ρ)) = elementaryC h a ρ := by
      unfold elementaryC
      simp_rw [densityMeasure_barycenter_single, barycenter_single_density]
    rw [he] at hc
    simpa only [sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul] using hc
  have hDef := elementaryModel_scalar_deficit_real hh hε (heI.trans_le hεImax) b ρ a
  change DD - 2 * a * G = I - 2 * a * H + ε * elementaryC h a ρ + ε ^ 2 * elementaryJ h ρ at hDef
  have hClo := mul_le_mul_of_nonneg_left (abs_le.mp hCorr).1 hε.le
  have hJ := mul_nonneg (sq_nonneg ε) (elementaryJ_nonneg h ρ)
  have hGapC := mul_le_mul_of_nonneg_left hGap (mul_nonneg hKT.le hε.le)
  have hHC' := mul_le_mul_of_nonneg_left hHC
    (mul_nonneg hε.le (show 0 ≤ 3 * KT + KC by positivity))
  change I - 2 * a * H ≤ K * ε
  dsimp only [K]
  nlinarith

/-- The actual global ordinary estimate converts the uniform ordinary deficit bound
into O(sqrt(epsilon)) localization in the ORIGINAL four-root Haar H1 metric. The same
triple is chosen before epsilon and every minimizer. Reference exclusion/positivity
and Euler regularity are separate subsequent steps. -/
theorem elementaryModel_minimizer_fourRoot_localization (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ (σ : Fin 3 → AbsoluteDensity 1) (ε0 K : ℝ),
        (∀ j θ, (σ j).density (DGPS.Circle.AngularNormalization.angEquiv.symm θ) =
          DGPS.Frontier.STR029.rhoT_STR02901 h
            (DGPS.Frontier.STR029.chartU_STR02924 D.ψ h (D.Z j h))
            (DGPS.Circle.AngularNormalization.angSec θ)) ∧
        0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < K ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ordinaryFourRootH1Distance h σ ρ ^ 2 ≤ K * ε := by
  obtain ⟨δE, hδE, hδEr, hEnergy⟩ := elementaryModel_minimizer_ordinaryDeficit_bound D
  obtain ⟨δG, hδG, hδGr, hGlobal⟩ := ordinaryDeficit_global_same_graph D
  refine ⟨min δE δG, lt_min hδE hδG, (min_le_left _ _).trans hδEr, fun h hh hhd => ?_⟩
  obtain ⟨ε0, K, hε0, hεmax, hK, hDef⟩ := hEnergy h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨σ, hσ, c, hc, hOrdinary⟩ := hGlobal h hh (hhd.trans_le (min_le_right _ _))
  refine ⟨σ, ε0, K / c, hσ, hε0, hεmax, div_pos hK hc, fun ε hε hεsmall b ρ hG hmin => ?_⟩
  have hO := hOrdinary ρ
  have hD := hDef ε hε hεsmall b ρ hG hmin
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).2
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
