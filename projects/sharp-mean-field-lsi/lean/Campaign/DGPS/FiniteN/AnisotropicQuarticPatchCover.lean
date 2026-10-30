import DGPS.FiniteN.AnisotropicQuarticCriticalPatches

/-! Fixed finite actual critical patches with one common FIN070 local rate. -/

open MeasureTheory Set Metric
open DGPS.Models DGPS.Circle.BesselMoments
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.FiniteN

/-- Actual finite precompact critical cover. Its minimum ball, Hessian and normalized
tails share one physical field; all other patches have a common positive sqrt-N rate. -/
theorem quartic_finite_critical_patch_cover :
    ∃ t : ℝ, 1 < t ∧ t = 1 + quarticKappa * besselRatio t ∧
      ∃ r c1 : ℝ, 0 < r ∧ 0 < c1 ∧
        (∀ x ∈ ball (!₂[t, 0] : EuclideanSpace ℝ (Fin 2)) r,
          ∀ v : EuclideanSpace ℝ (Fin 2),
            c1 * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ quarticPsi_FIN066) x v v) ∧
        (∀ R : ℝ, 0 < R → ∃ b > 0, ∃ C > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧
          ∀ N : ℝ, N0 ≤ N →
            ((imsEta N quarticPsi_FIN066)
              {w | R ≤ dist w (!₂[t, 0] : EuclideanSpace ℝ (Fin 2))}).toReal ≤
                C * Real.exp (-(b * N))) ∧
        ∃ (m : ℕ) (U : Fin m → Set (EuclideanSpace ℝ (Fin 2))) (j0 : Fin m),
          U j0 = ball !₂[t, 0] r ∧ (∀ j, IsOpen (U j)) ∧
          (∀ j, IsCompact (closure (U j))) ∧
          {w | fderiv ℝ quarticPsi_FIN066 w = 0} ⊆ ⋃ j, U j ∧
          ∃ a : ℝ, 0 < a ∧ ∀ j, j ≠ j0 → ∀ N : ℝ, 1 ≤ N →
            ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ,
              ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ U j →
                a * Real.sqrt N * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
                  ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
  classical
  obtain ⟨t, ht, hroot, hg, hu, hcrit, r, c1, hr, hc1, hess, htail⟩ := quartic_minimum_data
  let w0 : EuclideanSpace ℝ (Fin 2) := !₂[t, 0]
  let P := {w : EuclideanSpace ℝ (Fin 2) // fderiv ℝ quarticPsi_FIN066 w = 0 ∧ w ≠ w0}
  have hEach : ∀ p : P, ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ IsCompact (closure V) ∧ p.1 ∈ V ∧ ∃ a : ℝ, 0 < a ∧
      ∀ N : ℝ, 1 ≤ N → ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ V →
          a * Real.sqrt N * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
            ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
    intro p
    obtain ⟨V, hV, hp, a, ha, hlocal⟩ :=
      quartic_nonminimum_critical_patch ht hroot p.1 p.2.1 p.2.2
    refine ⟨V ∩ ball p.1 1, hV.inter isOpen_ball, ?_, ⟨hp, mem_ball_self zero_lt_one⟩,
      a, ha, fun N hN F hF hFc hFU => hlocal N hN F hF hFc (hFU.trans inter_subset_left)⟩
    exact (isCompact_closedBall p.1 1).of_isClosed_subset isClosed_closure
      ((closure_mono inter_subset_right).trans closure_ball_subset_closedBall)
  choose V hVo hVc hVp a ha hRate using hEach
  let W : Option P → Set (EuclideanSpace ℝ (Fin 2))
    | none => ball w0 r
    | some p => V p
  have hWo : ∀ i, IsOpen (W i) := by intro i; cases i with
    | none => exact isOpen_ball
    | some p => exact hVo p
  have hWc : ∀ i, IsCompact (closure (W i)) := by
    intro i
    cases i with
    | none =>
        exact (isCompact_closedBall w0 r).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall
    | some p => exact hVc p
  have hcover : {w | fderiv ℝ quarticPsi_FIN066 w = 0} ⊆ ⋃ i, W i := by
    intro w hw
    by_cases heq : w = w0
    · refine mem_iUnion.mpr ⟨none, ?_⟩
      simpa only [W, heq] using (mem_ball_self hr : w0 ∈ ball w0 r)
    · exact mem_iUnion.mpr ⟨some (⟨w, hw, heq⟩ : P), hVp ⟨w, hw, heq⟩⟩
  obtain ⟨s0, hs0⟩ := quartic_critical_set_compact.elim_finite_subcover W hWo hcover
  let s : Finset (Option P) := insert none s0
  have hnone : none ∈ s := Finset.mem_insert_self _ _
  let e : s ≃ Fin s.card := s.equivFin
  let U : Fin s.card → Set (EuclideanSpace ℝ (Fin 2)) := fun j => W (e.symm j).1
  let j0 := e ⟨none, hnone⟩
  let A : Fin s.card → ℝ := fun j => match (e.symm j).1 with
    | none => 1
    | some p => a p
  have hA : ∀ j, 0 < A j := by
    intro j
    dsimp [A]
    cases (e.symm j).1 with
    | none => exact zero_lt_one
    | some p => exact ha p
  let D := 1 + ∑ j : Fin s.card, 1 / A j
  have hD : 0 < D := by
    change 0 < 1 + ∑ j : Fin s.card, 1 / A j
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hA j)).le)
  let b := 1 / D
  have hb : 0 < b := one_div_pos.mpr hD
  have hbA : ∀ j, b ≤ A j := by
    intro j
    have hsingle : 1 / A j ≤ ∑ k : Fin s.card, 1 / A k :=
      Finset.single_le_sum (fun k _ => (one_div_pos.mpr (hA k)).le) (Finset.mem_univ j)
    have hle : 1 / A j ≤ D := by dsimp [D]; linarith
    change 1 / D ≤ A j
    apply (div_le_iff₀ hD).mpr
    have hmul := (div_le_iff₀ (hA j)).mp hle
    calc
      1 ≤ D * A j := hmul
      _ = A j * D := mul_comm D (A j)
  refine ⟨t, ht, hroot, r, c1, hr, hc1, hess, htail,
    s.card, U, j0, ?_, (fun j => hWo _), (fun j => hWc _), ?_, b, hb, ?_⟩
  · have he0 : e.symm j0 = ⟨none, hnone⟩ := e.symm_apply_apply _
    change W (e.symm j0).1 = ball !₂[t, 0] r
    rw [he0]
  · intro w hw
    obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp (hs0 hw)
    have his : i ∈ s := Finset.mem_insert_of_mem hi
    refine mem_iUnion.mpr ⟨e ⟨i, his⟩, ?_⟩
    simpa only [U, Equiv.symm_apply_apply] using hwi
  · intro j hj N hN F hF hFc hFU
    cases hcase : (e.symm j).1 with
    | none =>
        have hx : e.symm j = ⟨none, hnone⟩ := Subtype.ext hcase
        have he : j = j0 := by
          calc
            j = e (e.symm j) := (e.apply_symm_apply j).symm
            _ = e ⟨none, hnone⟩ := congrArg e hx
            _ = j0 := rfl
        exact False.elim (hj he)
    | some p =>
        have hFp : tsupport F ⊆ V p := by simpa only [U, hcase, W] using hFU
        have hbp : b ≤ a p := by simpa only [A, hcase] using hbA j
        have h := hRate p N hN F hF hFc hFp
        have hm : 0 ≤ ∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066 := integral_nonneg fun w => sq_nonneg _
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbp (Real.sqrt_nonneg N)) hm).trans h

end DGPS.FiniteN
