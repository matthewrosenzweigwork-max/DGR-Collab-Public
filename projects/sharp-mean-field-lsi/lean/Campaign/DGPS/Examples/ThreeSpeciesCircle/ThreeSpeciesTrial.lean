import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentSigns
import DGPS.Examples.ThreeSpeciesCircle.InteractingEntropyComparison

/-! A genuine equal-third family of the SAME actual ordinary roots has quotient
strictly below the ordinary rate. The root triple and h are chosen before the
coupling interval, and every drift is the actual weak drift of the model. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual equal-third ternary competitor, without a coefficient-sign or
trial-rate premise. It is one fixed genuine family before epsilon and the drift. -/
theorem elementaryModel_equalThird_trial (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ F : SpeciesFamily 1, F.count = 3 ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          0 < speciesGap (modelData h ε) F ∧
          speciesQuotient (modelData h ε) b F < ordinaryLSRate (ordinaryReference h) := by
  obtain ⟨δ, hδ, hδr, hsign⟩ := ordinaryRoot_correction_coefficient_signs D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  have hhr : h < D.radius := hhd.trans_le hδr
  obtain ⟨σ, hσ, hpos, hquot, hmin, hdist, hexact, hratefin, hrate⟩ := D.roots h hh hhr
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let α := ordinaryRootCorrectionAlpha h a σ
  have hα : 0 < α := (hsign h hh hhd σ hσ).1
  let F := SpeciesFamily.uniform (3 : ℕ+) σ
  have hE : 0 < ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
    change 0 < ∑ s : Fin 3, (1 / 3 : ℝ) * (ordinaryEntropy h (σ s)).toReal
    have hH0 : 0 < (ordinaryEntropy h (σ 0)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (hpos 0)) (str025_entropy_ne_top h (σ 0))
    have hs := Finset.single_le_sum
      (f := fun s : Fin 3 => (1 / 3 : ℝ) * (ordinaryEntropy h (σ s)).toReal)
      (fun s _ => mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (Finset.mem_univ 0)
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 3) hH0).trans_le hs
  have hroot (j : Fin 3) : (ordinaryFisher h (σ j)).toReal -
      2 * a * (ordinaryEntropy h (σ j)).toReal = 0 := by
    have he := congrArg ENNReal.toReal (hquot j)
    change (ordinaryFisher h (σ j) / (2 * ordinaryEntropy h (σ j))).toReal = a at he
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at he
    have hH : 0 < (ordinaryEntropy h (σ j)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (hpos j)) (str025_entropy_ne_top h (σ j))
    have hm := (div_eq_iff (show 2 * (ordinaryEntropy h (σ j)).toReal ≠ 0 by positivity)).mp he
    nlinarith only [hm]
  have hD0 : (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
      2 * a * (ordinaryEntropy h (F.density s)).toReal)) = 0 := by
    change (∑ s : Fin 3, (1 / 3 : ℝ) * ((ordinaryFisher h (σ s)).toReal -
      2 * a * (ordinaryEntropy h (σ s)).toReal)) = 0
    simp only [hroot, mul_zero, Finset.sum_const_zero]
  have hC : elementaryC h a (barycenter F) = -α := by
    have he := elementaryC_assigned_ordinary_roots D hh ⟨by linarith, hhr⟩ σ hσ a F
      (fun j : Fin 3 => j.succ)
    change elementaryC h a (barycenter F) = threefoldQuadratic
      (ordinaryRootCorrectionAlpha h a σ) (ordinaryRootCorrectionBeta h a σ)
        (assignedOrbitWeights F (fun j : Fin 3 => j.succ)) at he
    have hp : assignedOrbitWeights F (fun j : Fin 3 => j.succ) = fun _ => (1 / 3 : ℝ) := by
      funext j
      change (∑ x : Fin 3, if x.succ = j.succ then (1 / 3 : ℝ) else 0) = 1 / 3
      fin_cases j <;> norm_num [Fin.sum_univ_three]
    rw [hp, threefoldQuadratic_equal_thirds] at he
    exact he
  let J := elementaryJ h (barycenter F)
  have hJ : 0 ≤ J := elementaryJ_nonneg h (barycenter F)
  obtain ⟨εg, hεg, hεgmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let ε0 := min εg (α / (J + 1))
  refine ⟨F, rfl, ε0, lt_min hεg (div_pos hα (by positivity)),
    (min_le_left _ _).trans hεgmax, fun ε hε hε0' b => ?_⟩
  have hepsg : ε < εg := hε0'.trans_le (min_le_left _ _)
  have hepsmax : ε < epsMax h := hepsg.trans_le hεgmax
  have hG : 0 < speciesGap (modelData h ε) F := by
    have hg := (hgap ε hε hepsg F).1
    change 0 < (speciesGap (modelData h ε) F : ℝ)
    linarith
  have hεJ : ε * J < α := by
    have he := (lt_div_iff₀ (by positivity : 0 < J + 1)).mp
      (hε0'.trans_le (min_le_right _ _))
    nlinarith only [he, hε]
  obtain ⟨-, -, hDfin, -, hdef⟩ := elementaryModel_exactDeficitExpansion hh hε hepsmax b F
  have hnegative : (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) < 0 := by
    change (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) = _ at hdef
    rw [hD0, hC] at hdef
    have hn := mul_neg_of_pos_of_neg hε (show -α + ε * J < 0 by linarith)
    nlinarith only [hdef, hn]
  have hGr : 0 < (speciesGap (modelData h ε) F : ℝ) := hG
  have hQ : speciesQuotient (modelData h ε) b F = ENNReal.ofReal
      ((speciesDissipation (modelData h ε) b F).toReal / (2 * (speciesGap (modelData h ε) F : ℝ))) := by
    unfold speciesQuotient
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hDfin]
    simp
  have hQr : (speciesDissipation (modelData h ε) b F).toReal /
      (2 * (speciesGap (modelData h ε) F : ℝ)) < a :=
    (div_lt_iff₀ (by positivity)).mpr (by nlinarith only [hnegative])
  have ha : 0 < a := (div_nonneg ENNReal.toReal_nonneg (by positivity)).trans_lt hQr
  refine ⟨hG, ?_⟩
  rw [hQ, ← ENNReal.ofReal_toReal hratefin]
  exact (ENNReal.ofReal_lt_ofReal_iff ha).2 hQr

end DGPS.Examples.ThreeSpeciesCircle
