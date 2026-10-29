import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierFarUpper

/-! Pointwise convergence of the actual radial regularization off the
collision pole. Full local convergence of all derivatives is a separate
remaining assertion of source Lemma 2.2. -/

noncomputable section
open MeasureTheory Metric Set Filter
open scoped Topology Convolution

namespace PeriodicAttractiveLogGas

theorem tendsto_regularizedGreen {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) {z : Torus} (hz : z ≠ 0) :
    Tendsto (fun i ↦ regularizedGreen (ε i) (hε i) z) l (𝓝 (regularGreenRepresentative z)) := by
  let x := centeredLift z
  have hx : x ∈ offIntegerLattice := by
    change torusQuotient (centeredLift z) ≠ 0
    simpa only [torusQuotient_centeredLift] using hz
  have hc : ContinuousAt regularGreenLift x :=
    (contDiffOn_regularGreenLift.contDiffAt (isOpen_offIntegerLattice.mem_nhds hx)).continuousAt
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc (η / 2) (by positivity)
  have he : ∀ᶠ i in l, ε i < δ := ht.eventually (gt_mem_nhds hδ)
  filter_upwards [he] with i hi
  have hs : Function.support (scaledRadialMollifier (ε i)) ⊆ ball (0 : PlanarSpace) δ :=
    (support_scaledRadialMollifier_subset (ε i) (hε i)).trans (ball_subset_ball (by linarith [hε i]))
  have hb := dist_convolution_le (μ := (volume : Measure PlanarSpace))
    (f := scaledRadialMollifier (ε i)) (g := regularGreenLift) (x₀ := x)
    (R := δ) (z₀ := regularGreenLift x) (by positivity : 0 ≤ η / 2) hs
    (scaledRadialMollifier_nonneg (ε i)) (integral_scaledRadialMollifier (ε i) (hε i))
    locallyIntegrable_regularGreenLift.aestronglyMeasurable
    (fun y hy ↦ (hcont hy).le)
  have heq : regularizedGreen (ε i) (hε i) z =
      (scaledRadialMollifier (ε i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] regularGreenLift) x := by
    rw [← torusQuotient_centeredLift z, regularizedGreen_lift_eq_convolution (ε i) (hε i) (hsmall i)]
    rw [convolution_mul_swap]
    change (∫ y, regularGreenLift (x - y) * scaledRadialMollifier (ε i) y) =
      ∫ y, scaledRadialMollifier (ε i) y * regularGreenLift (x - y)
    exact integral_congr_ae (Eventually.of_forall (fun _ ↦ mul_comm _ _))
  rw [heq]
  have hvalue : regularGreenRepresentative z = regularGreenLift x := by
    simpa only [x, torusQuotient_centeredLift] using regularGreenRepresentative_lift (centeredLift z)
  rw [hvalue]
  exact hb.trans_lt (by linarith)

end PeriodicAttractiveLogGas
