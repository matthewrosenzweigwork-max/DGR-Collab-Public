import LeanResearch.PeriodicAttractiveLogGas.ClusterScaling
import LeanResearch.PeriodicAttractiveLogGas.CollisionComparison

/-! The outer shell boundary is null under the actual product Lebesgue measure.
This supplies the null-set justification needed when the source enlarges
the shell with maximum radius at most one to a product of open unit balls. -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace PeriodicAttractiveLogGas

theorem ae_cluster_coordinate_norm_ne (n : ℕ) (ρ : ℝ) (i : Fin n) :
    ∀ᵐ w : Fin n → PlanarSpace ∂volume, ‖w i‖ ≠ ρ := by
  have hm : (volume : Measure (Fin n → PlanarSpace))
      ((Function.eval i) ⁻¹' sphere (0 : PlanarSpace) ρ) = 0 :=
    Measure.pi_eval_preimage_null (fun _ : Fin n => (volume : Measure PlanarSpace))
      (Measure.addHaar_sphere volume (0 : PlanarSpace) ρ)
  have h : ∀ᵐ w : Fin n → PlanarSpace ∂volume,
      w ∉ (Function.eval i) ⁻¹' sphere (0 : PlanarSpace) ρ := compl_mem_ae_iff.mpr hm
  filter_upwards [h] with w hw
  intro he
  exact hw (by simpa only [mem_preimage, mem_sphere, dist_zero_right, Function.eval] using he)

theorem ae_cluster_all_norm_ne (n : ℕ) (ρ : ℝ) :
    ∀ᵐ w : Fin n → PlanarSpace ∂volume, ∀ i : Fin n, ‖w i‖ ≠ ρ :=
  ae_all_iff.mpr (ae_cluster_coordinate_norm_ne n ρ)

theorem clusterShell_ae_subset_clusterBox (n : ℕ) (ρ : ℝ) :
    clusterShell n ρ ≤ᵐ[volume] clusterBox n ρ := by
  filter_upwards [ae_cluster_all_norm_ne n ρ] with w hw
  intro hs i _
  apply mem_ball_zero_iff.mpr
  exact lt_of_le_of_ne ((norm_le_pi_norm w i).trans hs.2) (hw i)

theorem closedClusterBox_ae_eq_clusterBox (n : ℕ) (ρ : ℝ) :
    Set.pi Set.univ (fun _ : Fin n => closedBall (0 : PlanarSpace) ρ) =ᵐ[volume]
      clusterBox n ρ := by
  filter_upwards [ae_cluster_all_norm_ne n ρ] with w hw
  apply propext
  constructor
  · intro h i _
    exact mem_ball_zero_iff.mpr
      (lt_of_le_of_ne (mem_closedBall_zero_iff.mp (h i (mem_univ i))) (hw i))
  · intro h i _
    exact ball_subset_closedBall (h i (mem_univ i))

end PeriodicAttractiveLogGas
