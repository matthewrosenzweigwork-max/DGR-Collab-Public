import LeanResearch.PeriodicAttractiveLogGas.GreenRepresentative
import LeanResearch.PeriodicAttractiveLogGas.TorusDistance

/-! Compact estimates away from the pole in the centered Euclidean square.
All bounds below concern the actual regular Green lift and its ordinary
Fréchet derivatives. The constants arise from compactness of a fixed set. -/

noncomputable section
open Set Metric
open scoped ContDiff

namespace PeriodicAttractiveLogGas

def centeredClosedSquare : Set PlanarSpace :=
  {x | ∀ j : Fin 2, |x j| ≤ (1 / 2 : ℝ)}

theorem isClosed_centeredClosedSquare : IsClosed centeredClosedSquare := by
  have he : centeredClosedSquare = ⋂ j : Fin 2, {x : PlanarSpace | |x j| ≤ (1 / 2 : ℝ)} := by
    ext x
    simp only [centeredClosedSquare, mem_ofPred_eq, mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro j
  exact isClosed_le ((EuclideanSpace.proj j).continuous.abs) continuous_const

theorem norm_le_one_of_mem_centeredClosedSquare {x : PlanarSpace}
    (hx : x ∈ centeredClosedSquare) : ‖x‖ ≤ 1 := by
  have hsq := EuclideanSpace.real_norm_sq_eq x
  rw [Fin.sum_univ_two] at hsq
  have h0 := sq_le_sq₀ (abs_nonneg (x 0)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h1 := sq_le_sq₀ (abs_nonneg (x 1)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h0' : (x 0) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by simpa using h0.mpr (hx 0)
  have h1' : (x 1) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by simpa using h1.mpr (hx 1)
  nlinarith [norm_nonneg x]

theorem isCompact_centeredClosedSquare : IsCompact centeredClosedSquare :=
  isCompact_iff_isClosed_bounded.mpr ⟨isClosed_centeredClosedSquare,
    isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx ↦ norm_le_one_of_mem_centeredClosedSquare hx⟩⟩

theorem centeredLift_mem_closedSquare (z : Torus) : centeredLift z ∈ centeredClosedSquare :=
  centeredLift_abs_le_half z

theorem mem_offIntegerLattice_of_mem_closedSquare {x : PlanarSpace}
    (hx : x ∈ centeredClosedSquare) (hne : x ≠ 0) : x ∈ offIntegerLattice := by
  intro hzero
  apply hne
  ext j
  have hc : (x j : UnitAddCircle) = 0 := congrFun hzero j
  have hn : ‖(x j : UnitAddCircle)‖ = |x j| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hx j)
  rw [hc, norm_zero] at hn
  simpa only [PiLp.zero_apply] using (abs_eq_zero.mp hn.symm)

def centeredFarSet : Set PlanarSpace :=
  centeredClosedSquare ∩ {x | (1 / 4 : ℝ) ≤ ‖x‖}

theorem isCompact_centeredFarSet : IsCompact centeredFarSet :=
  isCompact_centeredClosedSquare.inter_right (isClosed_le continuous_const continuous_norm)

theorem centeredFarSet_subset_offIntegerLattice : centeredFarSet ⊆ offIntegerLattice := by
  intro x hx
  apply mem_offIntegerLattice_of_mem_closedSquare hx.1
  intro he
  have hl : (1 / 4 : ℝ) ≤ ‖x‖ := hx.2
  rw [he, norm_zero] at hl
  norm_num at hl

theorem contDiffOn_fderiv_smoothGreenLift :
    ContDiffOn ℝ ∞ (fderiv ℝ smoothGreenLift) offIntegerLattice :=
  contDiffOn_smoothGreenLift.fderiv_of_isOpen isOpen_offIntegerLattice (by simp)

theorem contDiffOn_hessian_smoothGreenLift :
    ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ smoothGreenLift)) offIntegerLattice :=
  contDiffOn_fderiv_smoothGreenLift.fderiv_of_isOpen isOpen_offIntegerLattice (by simp)

theorem exists_greenFar_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ centeredFarSet,
      |smoothGreenLift x| ≤ C ∧ ‖fderiv ℝ smoothGreenLift x‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ smoothGreenLift) x‖ ≤ C := by
  obtain ⟨C0, h0⟩ := isCompact_centeredFarSet.exists_bound_of_continuousOn (f := smoothGreenLift)
    (contDiffOn_smoothGreenLift.continuousOn.mono centeredFarSet_subset_offIntegerLattice)
  obtain ⟨C1, h1⟩ := isCompact_centeredFarSet.exists_bound_of_continuousOn
    (f := fderiv ℝ smoothGreenLift)
    (contDiffOn_fderiv_smoothGreenLift.continuousOn.mono centeredFarSet_subset_offIntegerLattice)
  obtain ⟨C2, h2⟩ := isCompact_centeredFarSet.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ smoothGreenLift))
    (contDiffOn_hessian_smoothGreenLift.continuousOn.mono centeredFarSet_subset_offIntegerLattice)
  refine ⟨|C0| + |C1| + |C2|, by positivity, ?_⟩
  intro x hx
  have h0x : |smoothGreenLift x| ≤ C0 := by simpa only [Real.norm_eq_abs] using h0 x hx
  exact ⟨by linarith [le_abs_self C0, abs_nonneg C1, abs_nonneg C2],
    by linarith [h1 x hx, le_abs_self C1, abs_nonneg C0, abs_nonneg C2],
    by linarith [h2 x hx, le_abs_self C2, abs_nonneg C0, abs_nonneg C1]⟩

end PeriodicAttractiveLogGas
