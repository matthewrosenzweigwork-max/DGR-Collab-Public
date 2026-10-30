import DGPS.Examples.ThreeSpeciesCircle.CompensatingDilutionLimit
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceLocalStability

/-! Actual bounded relative H1 tests at the retained ordinary roots, for the
compensating sequence. No smooth relative-density carrier is substituted. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open DGPS.Lipschitz DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

theorem ordinary_positiveRoot_relative_data (h : ℝ) (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) :
    ∃ (g : Torus 1 → ℝ) (hg : g ∈ WeightedH1 (ordinaryReference h))
      (hg0 : ∀ x, 0 ≤ g x)
      (hmass : ∫ x, g x ^ 2 ∂(ordinaryReference h).measure = 1) (M : ℝ),
        Continuous g ∧ 0 < M ∧ (∀ x, |g x| ≤ M) ∧
        densityMeasure (t01RelativeAbsoluteDensity (ordinaryReference h) (ordinaryReference_lip h)
          g hg hg0 hmass) = densityMeasure σ := by
  let g := fun x : Torus 1 => u x / str025_w h x
  have hgpos : ∀ x, 0 < g x := fun x => div_pos (hup x) (str025_w_pos h x)
  have hgc : Continuous g := hu.div (str025_continuous_w h) (fun x => (str025_w_pos h x).ne')
  have hh := ordinaryEquality_relativeRoot_memH1 (ordinaryReferenceAbsolute h) σ
    (str025_w h) (str025_continuous_w h) (str025_w_pos h) (EventuallyEq.refl _ _)
  have hgeq : (fun x => σ.sqrt x / str025_w h x) =ᵐ[haar 1] g :=
    hurep.mono fun x hx => by
      change σ.sqrt x / str025_w h x = u x / str025_w h x
      rw [hx]
  have hgm : MemH1 g := mem_H1Haar_congr_ae hh hgeq
  have hg : g ∈ WeightedH1 (ordinaryReference h) := (mem_weightedH1_iff _).2 hgm
  have hdens : (fun x => (ordinaryReference h).density x * g x ^ 2) =ᵐ[haar 1] σ.density := by
    filter_upwards [hurep] with x hx
    change referenceDensity h x * (u x / str025_w h x) ^ 2 = σ.sqrt x ^ 2
    rw [hx, ← str025_w_sq h x]
    field_simp [(str025_w_pos h x).ne']
  have hmass : ∫ x, g x ^ 2 ∂(ordinaryReference h).measure = 1 := by
    rw [t01_integral_reference (ordinaryReference h) (ordinaryReference_lip h)]
    exact (integral_congr_ae hdens).trans σ.integral_density
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hgc.continuousOn
  let M := max B 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hgM (x : Torus 1) : |g x| ≤ M :=
    (show |g x| ≤ B by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x)).trans
      (le_max_left _ _)
  have hμ : densityMeasure (t01RelativeAbsoluteDensity (ordinaryReference h) (ordinaryReference_lip h)
      g hg (fun x => (hgpos x).le) hmass) = densityMeasure σ := by
    apply Subtype.ext
    apply withDensity_congr_ae
    filter_upwards [hdens] with x hx
    change ENNReal.ofReal ((t01RelativeAbsoluteDensity (ordinaryReference h) (ordinaryReference_lip h)
      g hg (fun x => (hgpos x).le) hmass).density x) = ENNReal.ofReal (σ.density x)
    rw [t01RelativeAbsoluteDensity_density, hx]
  refine ⟨g, hg, fun x => (hgpos x).le, hmass, M, hgc, hM, hgM, ?_⟩
  exact hμ

/-- The SAME actual ordinary root triple supplies the bounded relative tests
internally. Entropy positivity and optimal quotient are actual root facts. -/
theorem ordinaryRoots_compensating_data (D : OrdinaryRootGraphData)
    {h : ℝ} (hh : 0 < h) (hhd : h < D.radius) :
    ∃ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j, 0 < ordinaryEntropy h (σ j)) ∧
      (∀ j, str025_quot h (σ j) = ordinaryLSRate (ordinaryReference h)) ∧
      ∀ j : Fin 3,
        ∃ (g : Torus 1 → ℝ) (hg : g ∈ WeightedH1 (ordinaryReference h))
          (hg0 : ∀ x, 0 ≤ g x)
          (hmass : ∫ x, g x ^ 2 ∂(ordinaryReference h).measure = 1) (M : ℝ),
          Continuous g ∧ 0 < M ∧ (∀ x, |g x| ≤ M) ∧
          densityMeasure (t01RelativeAbsoluteDensity (ordinaryReference h) (ordinaryReference_lip h)
            g hg hg0 hmass) = densityMeasure (σ j) := by
  obtain ⟨σ, hσ, hpos, hquot, _⟩ := D.roots h hh hhd
  refine ⟨σ, hpos, hquot, fun j => ?_⟩
  obtain ⟨u, hu, hup, hurep⟩ := ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (σ j) (hσ j)
  obtain ⟨g, hg, hg0, hmass, M, hgc, hM, hgM, hμ⟩ :=
    ordinary_positiveRoot_relative_data h (σ j) u hu hup hurep
  exact ⟨g, hg, hg0, hmass, M, hgc, hM, hgM, hμ⟩

end DGPS.Examples.ThreeSpeciesCircle
