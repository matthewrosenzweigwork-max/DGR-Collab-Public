import DGPS.Examples.ThreeSpeciesCircle.InteractingChartTurn
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData

/-! Exact SAME-D chart-seed rotation, including the additive log gauge. Density
rotation alone determines a chart only up to a constant; zero Haar means remove
that constant. This supplies a factual seed identity for later neighborhood
entry and does not assume invariant IFT domains. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The retained ordinary full C2-Holder chart seeds rotate exactly, with the
same mean-zero gauge. Neither an invariant complement neighborhood nor an
interacting classification premise is required. -/
theorem ordinaryRoot_chart_seed_thirdTurn (D : OrdinaryRootGraphData) (h : ℝ)
    (hh : h ∈ Set.Ioo (-D.radius) D.radius) (j : Fin 3) :
    Lamp_STR02956 D.ψ (h, h ^ 2 * D.Z j h 2) (h * D.Z j h 0, h * D.Z j h 1) =
      interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3))
        (Lamp_STR02956 D.ψ (h, h ^ 2 * D.Z 0 h 2) (h * D.Z 0 h 0, h * D.Z 0 h 1)) := by
  let u : Fin 3 → PeriodicC2_STR02969 := fun i =>
    Lamp_STR02956 D.ψ (h, h ^ 2 * D.Z i h 2) (h * D.Z i h 0, h * D.Z i h 1)
  let δ := 2 * Real.pi * ((j : ℕ) / 3)
  let v := interactingC2Translate δ (u 0)
  have hu (i : Fin 3) : (u i).val = chartU_STR02924 D.ψ h (D.Z i h) := rfl
  have hm (i : Fin 3) : meanT_STR02901 (u i).val = 0 := by
    have hw : InE_STR02901
        (D.ψ (ptPar_STR02923 h (D.Z i h)) : PeriodicC2_STR02969).val :=
      (c2Data_STR02969.mem_sub_iff _).mp (D.ψ (ptPar_STR02923 h (D.Z i h))).property
    exact (meanT_uT_STR02924 (h * D.Z i h 0) (h * D.Z i h 1)
      (D.ψ (ptPar_STR02923 h (D.Z i h)) : PeriodicC2_STR02969).isC2.2.1.continuous hw).1
  have hmv : meanT_STR02901 v.val = 0 :=
    (meanT_pb_STR02916 (Or.inl rfl) (-δ) (u 0).isC2.1).trans (hm 0)
  have hrot (t : ℝ) : rhoT_STR02901 h (u j).val t = rhoT_STR02901 h (u 0).val (t - δ) := by
    rw [hu j, hu 0]
    fin_cases j
    · dsimp only [δ]
      norm_num
    · convert (D.density_rotations h hh t).1 using 1 <;> dsimp only [δ] <;> congr 2 <;> ring
    · convert (D.density_rotations h hh t).2 using 1 <;> dsimp only [δ] <;> congr 2 <;> ring
  have hvρ (t : ℝ) : rhoT_STR02901 h v.val t = rhoT_STR02901 h (u 0).val (t - δ) := by
    have he := congrArg (fun F : PeriodicHolder_STR02968 => F.val t)
      (interactingC2Translate_rho h j (u 0))
    change (rho_STR02954 (h, e0_STR02955 v)).val t = (rho_STR02954 (h, e0_STR02955 (u 0))).val (t - δ) at he
    simpa only [rho_val_STR02954, e0_val_STR02955] using he
  obtain ⟨c, hc⟩ := rho_eq_const_STR02924 h (u j).isC2.2.1.continuous v.isC2.2.1.continuous
    (funext fun t => (hrot t).trans (hvρ t).symm)
  have he : (u j).val = v.val + (fun _ => c) := funext hc
  have hemean := congrArg meanT_STR02901 he
  rw [hm j, meanT_add_STR02953 v.isC2.2.1.continuous continuous_const,
    hmv, meanT_const_STR02955] at hemean
  have hc0 : c = 0 := by linarith
  change u j = v
  apply Subtype.ext
  funext t
  change (u j).val t = v.val t
  simpa only [hc0, add_zero] using hc t

end DGPS.Examples.ThreeSpeciesCircle
