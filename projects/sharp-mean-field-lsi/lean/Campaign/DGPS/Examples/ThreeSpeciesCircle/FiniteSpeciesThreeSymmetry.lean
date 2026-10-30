import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesThreeUniqueness
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesCyclicDistance
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesThirdTurn
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesGroupingObjective

/-! Exact equal weights and actual law rotation for matched minimizing triples.
The rotated FULL finite family remains a minimizer, is genuinely reindexed by
positive original group masses, and enters the SAME retained chart by exact
Haar H1 transport. No invariant IFT neighborhood or scalar restriction is used. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every actual minimizing triple in the SAME root tubes has exactly equal
weights and literal positive-third-turn covariance of its probability laws. -/
theorem elementaryModel_three_minimizer_equal_weights_rotation (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (σ j).density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
      ∀ A : ℝ, 0 < A → ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∀ p : Fin 3 → ℝ, ∀ hp : ∀ j, 0 < p j, ∀ hps : ∑ j, p j = 1,
        ∀ ρ : Fin 3 → AbsoluteDensity 1,
        let F := SpeciesFamily.ofData 3 p hp hps ρ
        0 < speciesGap (modelData h ε) F →
        speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
        (∀ j, ordinaryRootH1Deviation (σ j) (ρ j) (σ j).sqrt ≤ A * ε) →
        (∀ j, p j = 1 / 3) ∧ ∀ j : Fin 3,
          densityMeasure (ρ (j + 1)) = densityMeasure (interactingDensityTranslate (pt (1 / 3)) (ρ j)) := by
  obtain ⟨δ, hδ, hδr, hUnique⟩ := elementaryModel_three_minimizers_unique D
  refine ⟨δ, hδ, hδr, fun h hh hhd σ hσ A hA => ?_⟩
  obtain ⟨ε0, hε0, hε0max, hCompare⟩ := hUnique h hh hhd σ hσ A hA
  refine ⟨ε0, hε0, hε0max, fun ε hε hεsmall b p hp hps ρ hF hFm hρ => ?_⟩
  let F := SpeciesFamily.ofData 3 p hp hps ρ
  let H := finiteSpeciesThirdTurn 1 F
  let label : Fin H.count → Fin 3 := by
    change Fin 3 → Fin 3
    exact fun j => j + 1
  have hWeight (j : Fin 3) : finiteSpeciesGroupWeight H label (j + 1) = p j := by
    change (∑ s : Fin 3, if s + 1 = j + 1 then p s else 0) = p j
    simp only [add_left_inj, add_right_inj, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hpG (j : Fin 3) : 0 < finiteSpeciesGroupWeight H label j := by
    have hpre : ∃ k : Fin 3, k + 1 = j := by
      fin_cases j
      · exact ⟨2, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨1, by decide⟩
    obtain ⟨k, hk⟩ := hpre
    rw [← hk, hWeight]
    exact hp k
  have hSame (s t : Fin H.count) (he : label s = label t) :
      densityMeasure (H.density s) = densityMeasure (H.density t) := by
    change s + 1 = t + 1 at he
    have hst : s = t := add_right_cancel he
    rw [hst]
  let G := finiteSpeciesGroup3 H label hpG
  have heMax : ε < epsMax h := hεsmall.trans_le hε0max
  have hH : 0 < speciesGap (modelData h ε) H := by
    rw [speciesGap_finiteSpeciesThirdTurn hh hε heMax]
    exact hF
  have hHm : speciesQuotient (modelData h ε) b H = speciesRate (modelData h ε) b := by
    rw [speciesQuotient_finiteSpeciesThirdTurn hh hε heMax]
    exact hFm
  have hG : 0 < speciesGap (modelData h ε) G := by
    rw [speciesGap_finiteSpeciesGroup3 H label hpG hSame hh hε heMax]
    exact hH
  have hGm : speciesQuotient (modelData h ε) b G = speciesRate (modelData h ε) b := by
    rw [speciesQuotient_finiteSpeciesGroup3 H label hpG hSame hh hε heMax]
    exact hHm
  have hhr : h ∈ Set.Ioo (-D.radius) D.radius :=
    ⟨by linarith [D.radius_pos], hhd.trans_le hδr⟩
  have hDen (j : Fin 3) : G.density j =
      interactingDensityTranslate (pt (1 / 3))
        (ρ (finiteSpeciesGroupRepresentative H label hpG j)) := by
    change interactingDensityTranslate (pt (((1 : Fin 3) : ℕ) / 3)) _ = _
    norm_num [F, SpeciesFamily.ofData]
    rfl
  have hNearG (j : Fin 3) : ordinaryRootH1Deviation (σ j) (G.density j) (σ j).sqrt ≤ A * ε := by
    let k : Fin 3 := finiteSpeciesGroupRepresentative H label hpG j
    have hk : k + 1 = j := finiteSpeciesGroupRepresentative_label H label hpG j
    rw [hDen]
    change ordinaryRootH1Deviation (σ j)
      (interactingDensityTranslate (pt (1 / 3)) (ρ k)) (σ j).sqrt ≤ A * ε
    rw [← hk, ordinaryRootH1Deviation_thirdTurn D h hhr σ hσ k (ρ k)]
    exact hρ k
  have hu := hCompare ε hε hεsmall b p G.weight hp G.weight_pos hps G.weight_sum
    ρ G.density hF hFm hG hGm hρ hNearG
  have hCycle (j : Fin 3) : p (j + 1) = p j := by
    have he := congrFun hu.1 (j + 1)
    change p (j + 1) = finiteSpeciesGroupWeight H label (j + 1) at he
    exact he.trans (hWeight j)
  have hThirds (j : Fin 3) : p j = 1 / 3 := by
    have h0 := hCycle 0
    have h1 := hCycle 1
    have hs := hps
    change p 1 = p 0 at h0
    change p 2 = p 1 at h1
    rw [Fin.sum_univ_three] at hs
    fin_cases j
    · change p 0 = 1 / 3
      linarith only [h0, h1, hs]
    · change p 1 = 1 / 3
      linarith only [h0, h1, hs]
    · change p 2 = 1 / 3
      linarith only [h0, h1, hs]
  refine ⟨hThirds, fun j => ?_⟩
  let k : Fin 3 := finiteSpeciesGroupRepresentative H label hpG (j + 1)
  have hk' : k + 1 = j + 1 := finiteSpeciesGroupRepresentative_label H label hpG (j + 1)
  have hk : k = j := add_right_cancel hk'
  have he := hu.2 (j + 1)
  rw [hDen] at he
  change densityMeasure (ρ (j + 1)) =
    densityMeasure (interactingDensityTranslate (pt (1 / 3)) (ρ k)) at he
  rw [hk] at he
  exact he

end DGPS.Examples.ThreeSpeciesCircle
