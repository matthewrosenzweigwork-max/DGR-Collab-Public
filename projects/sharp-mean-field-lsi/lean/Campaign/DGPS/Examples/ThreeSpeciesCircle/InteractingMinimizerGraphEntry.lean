import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerHolderCapture
import DGPS.Examples.ThreeSpeciesCircle.InteractingChartCoordinates

/-! Actual EVERY-minimizer entry into arbitrary fixed neighborhoods of the
SAME ordinary seeds. The neighborhoods can be those of ONE retained interacting
graph packet selected beforehand; this theorem never reselects its graph.
All norm/rate/coordinate smallness is supplied by actual model producers. -/

noncomputable section
open MeasureTheory Filter Topology Set Metric
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- For every fixed family of actual seed neighborhoods, one positive coupling
threshold precedes EVERY drift and EVERY original-H1 scalar minimizer. The
actual normalized chart enters the complement domain, parameter domain and
scaled-coordinate ball together. Openness and seed membership describe the
target neighborhoods; no optimizer-nearness or desired entry is a premise. -/
theorem elementaryModel_scalarMinimizer_retained_graph_entry (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0<δ ∧ δ≤D.radius ∧ ∀ h : ℝ, 0<h → h<δ →
      ∀ (U : Fin 3 → Set (ℝ×ℝ×ℝ×ℝ)) (V : Fin 3 → Set E_STR02969) (r : Fin 3 → ℝ),
        (∀ j, IsOpen (U j)) →
        (∀ j, (0,h*D.Z j h 0,h*D.Z j h 1,h^2*D.Z j h 2)∈U j) →
        (∀ j, IsOpen (V j)) → (∀ j, D.ψ (ptPar_STR02923 h (D.Z j h))∈V j) →
        (∀ j, 0<r j) → ∃ ε0 : ℝ, 0<ε0 ∧ ε0≤epsMax h ∧
          ∀ ε : ℝ, 0<ε → ε<ε0 → ∀ b : AbsoluteDrift (modelData h ε),
            ∀ ρ : AbsoluteDensity 1, 0<scalarGap (modelData h ε) ρ →
              scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b →
              ∃ (j : Fin 3) (u : PeriodicC2_STR02969) (hm : meanT_STR02901 u.val=0),
                (∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ)=rhoT_STR02901 h u.val (angSec θ)) ∧
                (let γ := (scalarRate (modelData h ε) b).toReal/a0-1;
                 let z : Fin 3 → ℝ := ![interactingChartCos u/h,interactingChartSin u/h,γ/h^2];
                 (ε,h*z 0,h*z 1,h^2*z 2)∈U j ∧ interactingChartComplement u hm∈V j ∧
                   (ε,z)∈ball ((0:ℝ),D.Z j h) (r j)) := by
  classical
  obtain ⟨δ,hδ,hδr,hcapture⟩ := elementaryModel_scalarMinimizer_fullHolder_capture D
  refine ⟨δ,hδ,hδr,fun h hh hsmall U V r hU hp0 hV hw0 hr => ?_⟩
  have hEntry (j : Fin 3) : ∃ d : ℝ, 0<d ∧
      ∀ (ε γ : ℝ) (u : PeriodicC2_STR02969) (hm : meanT_STR02901 u.val=0),
        |ε|<d → ‖u-ordinaryHolderCaptureSeed D h j‖<d → |γ-h^2*D.Z j h 2|<d →
        (let z : Fin 3 → ℝ := ![interactingChartCos u/h,interactingChartSin u/h,γ/h^2];
         (ε,h*z 0,h*z 1,h^2*z 2)∈U j ∧ interactingChartComplement u hm∈V j ∧
           (ε,z)∈ball ((0:ℝ),D.Z j h) (r j)) := by
    have he := interactingChart_coordinate_neighborhood_entry h hh.ne' (D.Z j h)
      (D.ψ (ptPar_STR02923 h (D.Z j h))) (U j) (hU j) (hp0 j)
      (V j) (hV j) (hw0 j) (r j) (hr j)
    simpa only [ordinaryHolderCaptureSeed,Lamp_STR02956,iota_STR02956,ptPar_STR02923] using he
  choose d hd henter using hEntry
  let η := min (d 0) (min (d 1) (d 2))
  have hη : 0<η := lt_min (hd 0) (lt_min (hd 1) (hd 2))
  have hηd (j : Fin 3) : η≤d j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨εC,hεC,hεCmax,hcap⟩ := hcapture h hh hsmall η hη
  refine ⟨min εC η,lt_min hεC hη,(min_le_left _ _).trans hεCmax,
    fun ε hε he b ρ hG hmin => ?_⟩
  obtain ⟨j,u,hm,hae,hnorm,_,hgamma⟩ := hcap ε hε
    (he.trans_le (min_le_left _ _)) b ρ hG hmin
  refine ⟨j,u,hm,hae,?_⟩
  apply henter j ε ((scalarRate (modelData h ε) b).toReal/a0-1) u hm
  · rw [abs_of_pos hε]
    exact (he.trans_le (min_le_right _ _)).trans_le (hηd j)
  · exact hnorm.trans_le (hηd j)
  · exact hgamma.trans_le (hηd j)

end DGPS.Examples.ThreeSpeciesCircle
