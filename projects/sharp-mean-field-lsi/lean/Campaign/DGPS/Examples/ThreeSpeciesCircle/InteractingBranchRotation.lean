import DGPS.Examples.ThreeSpeciesCircle.InteractingChartTurnCoordinates
import DGPS.Examples.ThreeSpeciesCircle.InteractingSelfChartRotation

/-! C3 identification of the SAME locally unique interacting branches. Actual
continuity and exact transported seeds give entry into each target U,V and
reduced ball after shrinking epsilon. No neighborhood invariance is assumed. -/

noncomputable section
open Filter Topology Set Metric
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem retained_branches_rotate (D : OrdinaryRootGraphData) (h : ℝ) (hh : 0 < h)
    (hhr : h ∈ Ioo (-D.radius) D.radius)
    (U : Fin 3 → Set (ℝ × ℝ × ℝ × ℝ)) (V : Fin 3 → Set E_STR02969)
    (ψ : Fin 3 → (ℝ × ℝ × ℝ × ℝ) → E_STR02969)
    (Z : Fin 3 → ℝ → (Fin 3 → ℝ)) (η r : Fin 3 → ℝ)
    (hU : ∀ j, IsOpen (U j)) (hV : ∀ j, IsOpen (V j))
    (hw0 : ∀ j, D.ψ (ptPar_STR02923 h (D.Z j h)) ∈ V j)
    (hη : ∀ j, 0 < η j) (hr : ∀ j, 0 < r j)
    (hZ0 : ∀ j, Z j 0 = D.Z j h)
    (hψ : ∀ j, ContDiffOn ℝ ∞ (ψ j) (U j))
    (hZ : ∀ j, ContDiffOn ℝ ∞ (Z j) (Ioo (-(η j)) (η j)))
    (hψ0 : ∀ j, ψ j (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2) =
      D.ψ (ptPar_STR02923 h (D.Z j h)))
    (hbranch : ∀ j ε, |ε| < η j →
      (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2) ∈ U j ∧
      let u := (h * Z j ε 0) • cosC2_STR02915 + (h * Z j ε 1) • sinC2_STR02915 +
        (ψ j (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2) : PeriodicC2_STR02969)
      interactingChartGradient h (ε, h ^ 2 * Z j ε 2, u) = 0 ∧
        interactingChartDeficit h (ε, h ^ 2 * Z j ε 2, u) = 0)
    (huniq : ∀ j (ε : ℝ) (z : Fin 3 → ℝ) (w : E_STR02969),
      (ε, h * z 0, h * z 1, h ^ 2 * z 2) ∈ U j → w ∈ V j →
      (ε, z) ∈ ball ((0 : ℝ), D.Z j h) (r j) →
      interactingChartGradient h (ε, h ^ 2 * z 2,
        (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 + (w : PeriodicC2_STR02969)) = 0 →
      interactingChartDeficit h (ε, h ^ 2 * z 2,
        (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 + (w : PeriodicC2_STR02969)) = 0 →
      z = Z j ε ∧ w = ψ j (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ j ε, |ε| < ρ → |ε| < η j ∧
      h ^ 2 * Z j ε 2 = h ^ 2 * Z 0 ε 2 ∧
      ((h * Z j ε 0) • cosC2_STR02915 + (h * Z j ε 1) • sinC2_STR02915 +
        (ψ j (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2) : PeriodicC2_STR02969)) =
      interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3))
        ((h * Z 0 ε 0) • cosC2_STR02915 + (h * Z 0 ε 1) • sinC2_STR02915 +
          (ψ 0 (ε, h * Z 0 ε 0, h * Z 0 ε 1, h ^ 2 * Z 0 ε 2) : PeriodicC2_STR02969)) := by
  let p : Fin 3 → ℝ → ℝ × ℝ × ℝ × ℝ :=
    fun j ε => (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2)
  let w : Fin 3 → ℝ → E_STR02969 := fun j ε => ψ j (p j ε)
  have hZc (j : Fin 3) : ContinuousAt (Z j) 0 :=
    (hZ j).continuousOn.continuousAt (Ioo_mem_nhds (show -(η j) < (0 : ℝ) by linarith [hη j]) (hη j))
  have hpc (j : Fin 3) : ContinuousAt (p j) 0 := by
    have hc (i : Fin 3) : ContinuousAt (fun ε => Z j ε i) 0 :=
      (continuous_apply i).continuousAt.comp (hZc j)
    dsimp only [p]
    fun_prop
  have hp0 (j : Fin 3) : p j 0 ∈ U j := (hbranch j 0 (by simpa using hη j)).1
  have hwc (j : Fin 3) : ContinuousAt (w j) 0 :=
    ((hψ j).continuousOn.continuousAt ((hU j).mem_nhds (hp0 j))).comp (f := p j) (hpc j)
  have hwseed (j : Fin 3) : w j 0 = D.ψ (ptPar_STR02923 h (D.Z j h)) := by
    dsimp only [w, p]
    rw [hZ0 j, hψ0 j]
  let q : Fin 3 → ℝ → ℝ × ℝ × ℝ × ℝ := fun j ε =>
    (ε, h * interactingThirdCoordinates j (Z 0 ε) 0,
      h * interactingThirdCoordinates j (Z 0 ε) 1, h ^ 2 * interactingThirdCoordinates j (Z 0 ε) 2)
  let v : Fin 3 → ℝ → E_STR02969 := fun j ε =>
    pullE_STR02916 1 (Or.inl rfl) (-(2 * Real.pi * ((j : ℕ) / 3))) (w 0 ε)
  have htc (j : Fin 3) : ContinuousAt (fun ε => interactingThirdCoordinates j (Z 0 ε)) 0 :=
    (interactingThirdCoordinates_continuous j).continuousAt.comp (hZc 0)
  have hqc (j : Fin 3) : ContinuousAt (q j) 0 := by
    have hc (i : Fin 3) : ContinuousAt (fun ε => interactingThirdCoordinates j (Z 0 ε) i) 0 :=
      (continuous_apply i).continuousAt.comp (htc j)
    dsimp only [q]
    fun_prop
  have hq0 (j : Fin 3) : q j 0 = p j 0 := by
    dsimp only [q, p]
    rw [hZ0 0, hZ0 j, (ordinaryRoot_thirdTurn_components D h hh.ne' hhr j).1]
  have hvc (j : Fin 3) : ContinuousAt (v j) 0 :=
    (interactingComplementTranslate_isometry j).continuous.continuousAt.comp (hwc 0)
  have hv0 (j : Fin 3) : v j 0 = D.ψ (ptPar_STR02923 h (D.Z j h)) := by
    dsimp only [v]
    rw [hwseed 0]
    exact (ordinaryRoot_thirdTurn_components D h hh.ne' hhr j).2
  have hev (j : Fin 3) : ∀ᶠ ε in 𝓝 (0 : ℝ),
      q j ε ∈ U j ∧ v j ε ∈ V j ∧
      (ε, interactingThirdCoordinates j (Z 0 ε)) ∈ ball ((0 : ℝ), D.Z j h) (r j) ∧
      |ε| < η 0 ∧ |ε| < η j := by
    have hpEv := (hqc j).eventually_mem (by rw [hq0 j]; exact (hU j).mem_nhds (hp0 j))
    have hwEv := (hvc j).eventually_mem (by rw [hv0 j]; exact (hV j).mem_nhds (hw0 j))
    have hzEv := (continuousAt_id.prodMk (htc j)).eventually_mem (by
      rw [hZ0 0, (ordinaryRoot_thirdTurn_components D h hh.ne' hhr j).1]
      exact ball_mem_nhds ((0 : ℝ), D.Z j h) (hr j))
    have he0 : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < η 0 := by
      filter_upwards [Ioo_mem_nhds (show -(η 0) < (0 : ℝ) by linarith [hη 0]) (hη 0)] with ε hε
      exact abs_lt.mpr hε
    have hej : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < η j := by
      filter_upwards [Ioo_mem_nhds (show -(η j) < (0 : ℝ) by linarith [hη j]) (hη j)] with ε hε
      exact abs_lt.mpr hε
    exact hpEv.and (hwEv.and (hzEv.and (he0.and hej)))
  obtain ⟨ρ, hρ, hρall⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.2 hev)
  refine ⟨ρ, hρ, fun j ε hε => ?_⟩
  obtain ⟨hpU, hvV, hzB, he0, hej⟩ := hρall (by simpa only [Real.dist_eq, sub_zero] using hε) j
  let u0 := (h * Z 0 ε 0) • cosC2_STR02915 + (h * Z 0 ε 1) • sinC2_STR02915 +
    (w 0 ε : PeriodicC2_STR02969)
  have hG0 : interactingChartGradient h (ε, h ^ 2 * Z 0 ε 2, u0) = 0 := (hbranch 0 ε he0).2.1
  have hF0 : interactingChartDeficit h (ε, h ^ 2 * Z 0 ε 2, u0) = 0 := (hbranch 0 ε he0).2.2
  have hGrot : interactingChartGradient h (ε, h ^ 2 * interactingThirdCoordinates j (Z 0 ε) 2,
      (h * interactingThirdCoordinates j (Z 0 ε) 0) • cosC2_STR02915 +
      (h * interactingThirdCoordinates j (Z 0 ε) 1) • sinC2_STR02915 +
      (v j ε : PeriodicC2_STR02969)) = 0 := by
    rw [← interactingChart_thirdTurn_decomposition]
    change interactingChartGradient h (ε, h ^ 2 * Z 0 ε 2,
      interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u0) = 0
    rw [interactingChartGradient_interactingThirdTurn hh, hG0]
    apply ext_STR02954
    funext t
    rfl
  have hFrot : interactingChartDeficit h (ε, h ^ 2 * interactingThirdCoordinates j (Z 0 ε) 2,
      (h * interactingThirdCoordinates j (Z 0 ε) 0) • cosC2_STR02915 +
      (h * interactingThirdCoordinates j (Z 0 ε) 1) • sinC2_STR02915 +
      (v j ε : PeriodicC2_STR02969)) = 0 := by
    rw [← interactingChart_thirdTurn_decomposition]
    change interactingChartDeficit h (ε, h ^ 2 * Z 0 ε 2,
      interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u0) = 0
    rw [interactingChartDeficit_interactingThirdTurn hh, hF0]
  obtain ⟨hzEq, hwEq⟩ := huniq j ε (interactingThirdCoordinates j (Z 0 ε)) (v j ε)
    hpU hvV hzB hGrot hFrot
  have hγ := congrArg (fun z : Fin 3 → ℝ => h ^ 2 * z 2) hzEq
  have hu := interactingChart_thirdTurn_decomposition h j (Z 0 ε) (w 0 ε)
  change interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u0 = _ at hu
  change v j ε = ψ j (p j ε) at hwEq
  dsimp only [v] at hwEq
  rw [hzEq, hwEq] at hu
  exact ⟨hej, hγ.symm, hu.symm⟩

/-- The same retained graph/branch witnesses have full local uniqueness AND
C3-related charts with one common physical rate on a genuinely shrunk interval. -/
theorem interactingChart_same_witness_C3_branches (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ (U : Fin 3 → Set (ℝ × ℝ × ℝ × ℝ)) (V : Fin 3 → Set E_STR02969)
          (ψ : Fin 3 → (ℝ × ℝ × ℝ × ℝ) → E_STR02969)
          (Z : Fin 3 → ℝ → (Fin 3 → ℝ)) (η r : Fin 3 → ℝ),
        (∀ j, IsOpen (U j) ∧ IsOpen (V j) ∧ D.ψ (ptPar_STR02923 h (D.Z j h)) ∈ V j ∧
          0 < η j ∧ 0 < r j ∧ Z j 0 = D.Z j h ∧
          ContDiffOn ℝ ∞ (ψ j) (U j) ∧ ContDiffOn ℝ ∞ (Z j) (Ioo (-(η j)) (η j)) ∧
          ψ j (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2) =
            D.ψ (ptPar_STR02923 h (D.Z j h)) ∧
          (∀ p ∈ U j, ψ j p ∈ V j) ∧
          (∀ p ∈ U j, ∀ w ∈ V j, interactingChartRange h (p, w) = 0 ↔ ψ j p = w) ∧
          (∀ ε, |ε| < η j →
            (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2) ∈ U j ∧
            let u := (h * Z j ε 0) • cosC2_STR02915 + (h * Z j ε 1) • sinC2_STR02915 +
              (ψ j (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2) : PeriodicC2_STR02969)
            interactingChartGradient h (ε, h ^ 2 * Z j ε 2, u) = 0 ∧
              interactingChartDeficit h (ε, h ^ 2 * Z j ε 2, u) = 0) ∧
          ∀ (ε : ℝ) (z : Fin 3 → ℝ) (w : E_STR02969),
            (ε, h * z 0, h * z 1, h ^ 2 * z 2) ∈ U j → w ∈ V j →
            (ε, z) ∈ ball ((0 : ℝ), D.Z j h) (r j) →
            interactingChartGradient h (ε, h ^ 2 * z 2,
              (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 + (w : PeriodicC2_STR02969)) = 0 →
            interactingChartDeficit h (ε, h ^ 2 * z 2,
              (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 + (w : PeriodicC2_STR02969)) = 0 →
            z = Z j ε ∧ w = ψ j (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2)) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ j ε, |ε| < ρ → |ε| < η j ∧
          h ^ 2 * Z j ε 2 = h ^ 2 * Z 0 ε 2 ∧
          ((h * Z j ε 0) • cosC2_STR02915 + (h * Z j ε 1) • sinC2_STR02915 +
            (ψ j (ε, h * Z j ε 0, h * Z j ε 1, h ^ 2 * Z j ε 2) : PeriodicC2_STR02969)) =
          interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3))
            ((h * Z 0 ε 0) • cosC2_STR02915 + (h * Z 0 ε 1) • sinC2_STR02915 +
              (ψ 0 (ε, h * Z 0 ε 0, h * Z 0 ε 1, h ^ 2 * Z 0 ε 2) : PeriodicC2_STR02969)) := by
  classical
  obtain ⟨δ, hδ, hδr, hbranches⟩ := interactingChart_local_unique_branches D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  choose U V ψ Z η r hU hV hw0 hη hr hZ0 hψ hZ hψ0 hψV hgraph hbranch huniq using
    (fun j : Fin 3 => hbranches h hh hhd j)
  refine ⟨U, V, ψ, Z, η, r, ?_, ?_⟩
  · intro j
    exact ⟨hU j, hV j, hw0 j, hη j, hr j, hZ0 j, hψ j, hZ j, hψ0 j,
      hψV j, hgraph j, hbranch j, huniq j⟩
  · have hhr : h ∈ Ioo (-D.radius) D.radius := by
      constructor <;> linarith [hhd.trans_le hδr, D.radius_pos]
    exact retained_branches_rotate D h hh hhr U V ψ Z η r hU hV hw0 hη hr hZ0 hψ hZ
      hψ0 hbranch huniq

end DGPS.Examples.ThreeSpeciesCircle
