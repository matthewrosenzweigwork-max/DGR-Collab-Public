import LeanResearch.PeriodicAttractiveLogGas.WeylLocal
import LeanResearch.PeriodicAttractiveLogGas.HarmonicGluing

/-! Weyl regularity on an arbitrary open subset of actual Euclidean two-space.

The hypotheses are local integrability and the zero ordinary-Laplacian pairing
against every smooth compactly supported test in the open set. Small closed
balls provide the margin required by the local convolution theorem, and the
proved gluing theorem combines the resulting representatives. No global
integrability or regularity outside the open set is assumed.
-/

noncomputable section

open MeasureTheory InnerProductSpace Metric Set
open scoped ContDiff Topology

namespace PeriodicAttractiveLogGas

/-- A single open chart of weak harmonicity supplies a smooth local
representative near any point of that chart. The representative is globally
smooth, while harmonicity and almost-everywhere equality hold on the neighborhood. -/
theorem exists_smooth_harmonic_representative_nhds
    {V : Set PlanarSpace} {u : PlanarSpace → ℝ}
    (hu : PlanarWeaklyHarmonicOn V u) (hV : IsOpen V)
    {x : PlanarSpace} (hx : x ∈ V) :
    ∃ W : Set PlanarSpace, ∃ h : PlanarSpace → ℝ,
      IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ ContDiff ℝ ∞ h ∧
        HarmonicOnNhd h W ∧ u =ᵐ[volume.restrict W] h := by
  obtain ⟨ρ, hρ, hρV⟩ : ∃ ρ, 0 < ρ ∧ closedBall x ρ ⊆ V :=
    nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hx)
  let R : ℝ := ρ / 4
  have hR : 0 < R := div_pos hρ (by norm_num)
  have h4R : 4 * R = ρ := by dsimp only [R]; ring
  have hball : closedBall x (4 * R) ⊆ V := by rwa [h4R]
  obtain ⟨h, hsmooth, hharm, hae⟩ :=
    exists_smooth_harmonic_representative_ball hu hR hball
  refine ⟨ball x R, h, isOpen_ball, mem_ball_self hR, ?_, hsmooth, hharm, hae⟩
  intro y hy
  apply hball
  exact closedBall_subset_closedBall (by linarith : R ≤ 4 * R)
    (ball_subset_closedBall hy)

/-- Every locally integrable weakly harmonic planar function on an open set
has one smooth harmonic representative on that set, for Euclidean volume. -/
theorem exists_smooth_harmonic_representative_open
    {U : Set PlanarSpace} {u : PlanarSpace → ℝ}
    (hu : PlanarWeaklyHarmonicOn U u) (hU : IsOpen U) :
    ∃ h : PlanarSpace → ℝ, ContDiffOn ℝ ∞ h U ∧ HarmonicOnNhd h U ∧
      u =ᵐ[volume.restrict U] h := by
  apply exists_smooth_harmonic_representative_of_local hU
  intro x hx
  exact exists_smooth_harmonic_representative_nhds hu hU hx

end PeriodicAttractiveLogGas
