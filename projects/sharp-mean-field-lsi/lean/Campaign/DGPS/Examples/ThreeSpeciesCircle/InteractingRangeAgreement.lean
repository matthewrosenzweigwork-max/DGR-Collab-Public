import DGPS.Examples.ThreeSpeciesCircle.InteractingRangeGraph

/-! The new fixed-h range graph agrees as a germ with the SAME retained ordinary
graph at zero coupling. Consequently its reduced deficit has the exact ordinary
zero slice. No interacting optimizer or capture statement is used. -/

noncomputable section
open Filter Topology Set
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Local range graphs with exact zero-coupling identification of the retained
ordinary reduced deficit. All graph inputs are produced internally. -/
theorem interactingChartRange_graphs_zero_agreement (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ j : Fin 3,
      let p0 : ℝ × ℝ × ℝ × ℝ := (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2)
      let w0 := D.ψ (ptPar_STR02923 h (D.Z j h))
      ∃ (U : Set (ℝ × ℝ × ℝ × ℝ)) (V : Set E_STR02969)
          (ψ : (ℝ × ℝ × ℝ × ℝ) → E_STR02969),
        IsOpen U ∧ p0 ∈ U ∧ IsOpen V ∧ w0 ∈ V ∧ ContDiffOn ℝ ∞ ψ U ∧
          ψ p0 = w0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
          (∀ p ∈ U, ∀ w ∈ V, interactingChartRange h (p, w) = 0 ↔ ψ p = w) ∧
          ((fun z : Fin 3 → ℝ => ψ (0, h * z 0, h * z 1, h ^ 2 * z 2)) =ᶠ[𝓝 (D.Z j h)]
            fun z => D.ψ (ptPar_STR02923 h z)) ∧
          ((fun z : Fin 3 → ℝ => interactingChartDeficit h
              (0, h ^ 2 * z 2, (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 +
                (ψ (0, h * z 0, h * z 1, h ^ 2 * z 2) : PeriodicC2_STR02969)) / h ^ 4) =ᶠ[𝓝 (D.Z j h)]
            fun z => D.reduced (h, z)) := by
  obtain ⟨δ, hδ, hδr, hgraphs⟩ := interactingChartRange_local_graphs D
  refine ⟨δ, hδ, hδr, fun h hh hhd j => ?_⟩
  have habs : |h| < δ := by simpa only [abs_of_pos hh] using hhd
  obtain ⟨U, V, ψ, hUo, hUp0, hVo, hVw0, hψ, hψ0, hψV, hkey⟩ := hgraphs h habs j
  let z0 := D.Z j h
  let p : (Fin 3 → ℝ) → ℝ × ℝ × ℝ × ℝ := fun z => (0, h * z 0, h * z 1, h ^ 2 * z 2)
  let q : (Fin 3 → ℝ) → Par_STR02916 := fun z => ptPar_STR02923 h z
  have hhr : h ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos, hhd.trans_le hδr]
  have hqU : q z0 ∈ D.U := D.branch_memU j h hhr
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hq : Continuous q := by dsimp [q, ptPar_STR02923]; fun_prop
  have hψq : ContinuousAt (fun z => D.ψ (q z)) z0 :=
    (D.smoothψ.continuousOn.continuousAt (D.openU.mem_nhds hqU)).comp
      (f := q) hq.continuousAt
  have heU : ∀ᶠ z in 𝓝 z0, p z ∈ U := hp.continuousAt.eventually_mem (hUo.mem_nhds hUp0)
  have heV : ∀ᶠ z in 𝓝 z0, D.ψ (q z) ∈ V :=
    hψq.eventually_mem (hVo.mem_nhds hVw0)
  have heqU : ∀ᶠ z in 𝓝 z0, q z ∈ D.U :=
    hq.continuousAt.eventually_mem (D.openU.mem_nhds hqU)
  have heO : ∀ᶠ z in 𝓝 z0, (h, z) ∈ D.O :=
    (show Continuous (fun z : Fin 3 → ℝ => (h, z)) from
      continuous_const.prodMk continuous_id).continuousAt.eventually_mem
        (D.openO.mem_nhds (D.branch_memO j h hhr))
  have heq : (fun z => ψ (p z)) =ᶠ[𝓝 z0] fun z => D.ψ (q z) := by
    filter_upwards [heU, heV, heqU] with z hzU hzV hzqU
    apply (hkey (p z) hzU (D.ψ (q z)) hzV).mp
    dsimp only [p]
    rw [interactingChartRange_zero]
    exact (D.range_eq (q z) hzqU _ (D.memψ _ hzqU)).mpr rfl
  refine ⟨U, V, ψ, hUo, hUp0, hVo, hVw0, hψ, hψ0, hψV, hkey, heq, ?_⟩
  filter_upwards [heq, heO] with z hz hzO
  change ψ (p z) = D.ψ (q z) at hz
  change interactingChartDeficit h
    (0, h ^ 2 * z 2, (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 +
      (ψ (p z) : PeriodicC2_STR02969)) / h ^ 4 = D.reduced (h, z)
  rw [hz, interactingChartDeficit_zero]
  change JC2_STR02956 h (h ^ 2 * z 2)
    (Lamp_STR02956 D.ψ (h, h ^ 2 * z 2) (h * z 0, h * z 1)) / h ^ 4 = D.reduced (h, z)
  have hFred : Fred_STR02956 D.ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) =
      JC2_STR02956 h (h ^ 2 * z 2)
        (Lamp_STR02956 D.ψ (h, h ^ 2 * z 2) (h * z 0, h * z 1)) :=
    Fred_eq_STR02956 D.ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2)
  exact (congrArg (fun v : ℝ => v / h ^ 4) hFred.symm).trans
    (D.reduced_value h z hzO hh.ne').symm

end DGPS.Examples.ThreeSpeciesCircle
