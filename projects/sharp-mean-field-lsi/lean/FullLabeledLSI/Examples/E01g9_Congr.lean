import FullLabeledLSI.Examples.E01g8_MinSeq
import FullLabeledLSI.Examples.Paper.Sec9Regularity

/-!
# Lane D, Task C (E01g9): a.e.-invariance of `H, ⟨ρ,C*ρ⟩, G, D`, and continuous representatives
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem densMeasure_congr_ae {ρ ρ' : Torus 1 → ℝ} (h : ρ =ᵐ[haar 1] ρ') :
    densMeasure ρ = densMeasure ρ' := by
  unfold densMeasure
  exact withDensity_congr_ae (h.mono fun x hx => by simp only [hx])

theorem entR_congr_ae {ρ ρ' : Torus 1 → ℝ} (h : ρ =ᵐ[haar 1] ρ') : entR ρ = entR ρ' := by
  unfold entR; rw [densMeasure_congr_ae h]

theorem convT_congr_ae {g ρ ρ' : Torus 1 → ℝ} (h : ρ =ᵐ[haar 1] ρ') :
    convT g ρ = convT g ρ' := by
  funext x
  unfold convT
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

theorem cqR_congr_ae {C ρ ρ' : Torus 1 → ℝ} (h : ρ =ᵐ[haar 1] ρ') : cqR C ρ = cqR C ρ' := by
  unfold cqR
  rw [convT_congr_ae (g := C) h]
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

theorem GR_congr_ae {C ρ ρ' : Torus 1 → ℝ} (h : ρ =ᵐ[haar 1] ρ') : GR C ρ = GR C ρ' := by
  unfold GR; rw [entR_congr_ae h, cqR_congr_ae h]

theorem DR_congr_ae {C ρ ρ' : Torus 1 → ℝ} (h : ρ =ᵐ[haar 1] ρ')
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) : DR C ρ = DR C ρ' := by
  have hs : (fun x => Real.sqrt (ρ x)) =ᵐ[haar 1] fun x => Real.sqrt (ρ' x) :=
    h.mono fun x hx => by simp only [hx]
  have hg := appA_weakGrad_congr_ae hs hH.1
  unfold DR
  rw [convT_congr_ae (g := dT C) h]
  refine integral_congr_ae ?_
  filter_upwards [h, hg] with x hx hgx
  rw [hx, congrFun hgx 0]

/-- A continuous representative of an `H¹` function. -/
theorem exists_cont_rep {u : Torus 1 → ℝ} (hu : MemH1 (haar 1) u) :
    ∃ v : Torus 1 → ℝ, Continuous v ∧ v =ᵐ[haar 1] u := by
  obtain ⟨F, hFc, hFp, -, hae, -⟩ := Reg.exists_continuous_rep_memH1 hu
  refine ⟨fun y => F (secT y 0), ?_, hae.mono fun y hy => hy.symm⟩
  refine continuous_of_liftT' ?_
  rw [Reg.comp_secT_lift hFp]
  exact hFc.comp (continuous_apply 0)

end SharpLSI.FL.Ex.LaneD
