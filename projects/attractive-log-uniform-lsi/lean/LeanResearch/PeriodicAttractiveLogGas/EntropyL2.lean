import LeanResearch.PeriodicAttractiveLogGas.Entropy
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Sequences

/-! Entropy limits in the actual L2 topology. Source: lem:cutoffs and the last
paragraph of the proof of thm:main. The later concrete smooth-gradient graph
must still be constructed and proved closable; this file does not assume it. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_sq_eq_L2_norm_sq (f : Lp ℝ 2 μ) :
    (∫ x, (f x) ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  simpa only [L2.inner_def, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
    (real_inner_self_eq_norm_sq f)

/-- L2 convergence suffices to pass converging finite entropy bounds.
No integrability of the entropy of the limit is assumed. -/
theorem entropy_sq_le_of_tendsto {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    {b : ℕ → ℝ} {B : ℝ} (hf : Tendsto f atTop (𝓝 g)) (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ n, entropy μ (fun x ↦ (f n x) ^ 2) ≤ (b n : EReal)) :
    entropy μ (fun x ↦ (g x) ^ 2) ≤ (B : EReal) := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  refine entropy_le_of_ae_tendsto
    (F := fun n x ↦ (f (ns n) x) ^ 2) (b := fun n ↦ b (ns n))
    (fun n ↦ (Lp.aestronglyMeasurable (f (ns n))).aemeasurable.pow_const 2)
    (hae.mono fun _ hx ↦ hx.pow 2) ?_ (hb.comp hns.tendsto_atTop) (fun n ↦ hbound (ns n))
  simp only [integral_sq_eq_L2_norm_sq]
  exact (hf.comp hns.tendsto_atTop).norm.pow 2

/-- Entropy control extends to the closure of a graph in scalar/vector L2.
Application to the manuscript still requires its concrete smooth gradient
graph, its closability, and the smooth-core inequality with uniform constant. -/
theorem entropy_sq_le_on_graph_closure {E : Type*} [NormedAddCommGroup E]
    {core : Set (Lp ℝ 2 μ × Lp E 2 μ)} {C : ℝ}
    (hcore : ∀ z ∈ core, entropy μ (fun x ↦ (z.1 x) ^ 2) ≤ ((2 * C * ‖z.2‖ ^ 2 : ℝ) : EReal))
    {z : Lp ℝ 2 μ × Lp E 2 μ} (hz : z ∈ closure core) :
    entropy μ (fun x ↦ (z.1 x) ^ 2) ≤ ((2 * C * ‖z.2‖ ^ 2 : ℝ) : EReal) := by
  obtain ⟨w, hw, ht⟩ := mem_closure_iff_seq_limit.mp hz
  exact entropy_sq_le_of_tendsto ((continuous_fst.tendsto z).comp ht)
    (tendsto_const_nhds.mul (((continuous_snd.tendsto z).comp ht).norm.pow 2))
    (fun n ↦ hcore (w n) (hw n))

end PeriodicAttractiveLogGas
