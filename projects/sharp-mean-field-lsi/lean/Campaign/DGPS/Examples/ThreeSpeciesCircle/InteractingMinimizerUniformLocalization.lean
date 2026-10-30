import DGPS.Examples.ThreeSpeciesCircle.InteractingRootUniformControl
import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerPositivity

/-! Quantitative uniform localization at the SAME ordinary roots. This retains
the actual nearest-root index and continuous representative for subsequent
score/capture arguments. The reference sector is excluded by the actual barrier. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem deviation_rep (σ ρ : AbsoluteDensity 1) {u : Torus 1 → ℝ}
    (hae : σ.sqrt =ᵐ[haar 1] u) :
    ordinaryRootH1Deviation σ ρ σ.sqrt = ordinaryRootH1Deviation σ ρ u := by
  unfold ordinaryRootH1Deviation
  congr 1
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards [hae] with x hx
  change ρ.sqrt x - σ.sqrt x = ρ.sqrt x - u x
  rw [hx]

/-- At fixed small h the SAME three ordinary roots and all constants are chosen
before the coupling, drift and EVERY actual original-H1 scalar minimizer. Each
minimizer has a genuine positive continuous representative and a retained root
index, with the quantitative uniform squared distance bounded by K*epsilon. -/
theorem elementaryModel_minimizer_uniform_threeRoot_localization (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ (σ : Fin 3 → AbsoluteDensity 1) (u : Fin 3 → Torus 1 → ℝ)
        (ε0 m K : ℝ),
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) ∧
        (∀ j, Continuous (u j) ∧ (∀ x, 0 < u j x) ∧ (σ j).sqrt =ᵐ[haar 1] u j) ∧
        0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧ 0 < K ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ∃ v : Torus 1 → ℝ, Continuous v ∧ ρ.sqrt =ᵐ[haar 1] v ∧
              (∀ x, m ≤ v x) ∧ ∃ j : Fin 3,
                ordinaryRootH1Deviation (σ j) ρ (u j) ^ 2 ≤ K * ε ∧
                  ∀ x, |v x - u j x| ^ 2 ≤ K * ε := by
  classical
  obtain ⟨δL, hδL, hδLr, hlocal⟩ := elementaryModel_minimizer_fourRoot_localization D
  obtain ⟨δB, hδB, _, hbarrier⟩ := elementaryModel_scalar_trial_below_reference_barrier D
  obtain ⟨δP, hδP, _, hpositive⟩ := elementaryModel_minimizer_positive_representative D
  refine ⟨min δL (min δB δP), lt_min hδL (lt_min hδB hδP),
    (min_le_left _ _).trans hδLr, fun h hh hsmall => ?_⟩
  obtain ⟨σ, εL, K, hσ, hεL, hεLmax, hK, hloc⟩ :=
    hlocal h hh (hsmall.trans_le (min_le_left _ _))
  obtain ⟨τ, r, εB, η, _, hεB, _, hη, hb⟩ :=
    hbarrier h hh (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨εP, m, hεP, _, hm, hp⟩ :=
    hpositive h hh (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  choose u hu hup hrep using fun j => ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (σ j) (hσ j)
  refine ⟨σ, u, min εL (min εB (min εP (η ^ 2 / K))), m, K, hσ,
    (fun j => ⟨hu j, hup j, hrep j⟩),
    lt_min hεL (lt_min hεB (lt_min hεP (div_pos (sq_pos_of_pos hη) hK))),
    (min_le_left _ _).trans hεLmax, hm, hK,
    fun ε hε he b ρ hG hmin => ?_⟩
  have heL : ε < εL := he.trans_le (min_le_left _ _)
  have heB : ε < εB := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heP : ε < εP := he.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have heK : K * ε < η ^ 2 := by
    have he' := he.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have ht := (lt_div_iff₀ hK).mp he'
    nlinarith
  obtain ⟨v, hv, hvae, hvmin⟩ := hp ε hε heP b ρ hG hmin
  have hd := hloc ε hε heL b ρ hG hmin
  have hnear : ordinaryFourRootH1Distance h σ ρ ≤ η := by
    nlinarith [hd.trans_lt heK, sq_nonneg (ordinaryFourRootH1Distance h σ ρ + η)]
  obtain ⟨i, hi⟩ := ordinaryFourRootH1Distance_attained h σ ρ
  have hzero : i ≠ 0 := by
    intro hz
    have hn : ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η := by
      have ht := hi.le.trans hnear
      simp only [hz,Fin.cases_zero] at ht
      change ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ
        (ordinaryReferenceAbsolute h).sqrt≤η at ht
      have href : (ordinaryReferenceAbsolute h).sqrt=str025_w h := rfl
      simpa only [href] using ht
    obtain ⟨htrial, hbar⟩ := hb ε hε heB b
    have hlo := hbar ρ hG hn
    have hhi : scalarQuotient (modelData h ε) b ρ < ENNReal.ofReal r := by
      rw [hmin]
      exact (scalarRate_le_quotient (modelData h ε) b τ htrial.1).trans_lt htrial.2
    exact (not_lt_of_ge hlo) hhi
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hzero
  have hdev : ordinaryRootH1Deviation (σ j) ρ (u j) = ordinaryFourRootH1Distance h σ ρ := by
    have ht := hi
    rw [← hj] at ht
    change ordinaryRootH1Deviation (σ j) ρ (σ j).sqrt = _ at ht
    rw [deviation_rep (σ j) ρ (hrep j)] at ht
    exact ht
  have hdj : ordinaryRootH1Deviation (σ j) ρ (u j) ^ 2 ≤ K * ε := by rw [hdev]; exact hd
  refine ⟨v, hv, hvae, hvmin, j, hdj, fun x => ?_⟩
  have hbnd := ordinaryRoot_continuous_deviation_bound (σ j) ρ (hu j) hv (hrep j) hvae x
  exact ((sq_le_sq₀ (abs_nonneg (v x - u j x))
    ((abs_nonneg (v x - u j x)).trans hbnd)).2 hbnd).trans hdj

end DGPS.Examples.ThreeSpeciesCircle
