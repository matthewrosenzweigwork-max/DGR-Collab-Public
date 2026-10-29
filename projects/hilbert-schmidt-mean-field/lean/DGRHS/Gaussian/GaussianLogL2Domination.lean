import DGRHS.Kernel.PositiveLimit
import DGRHS.Kernel.Separated
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Supporting development. Proper fixed-majorant L2 convergence. Physical use must
construct the majorant, AE convergence and positivity of every approximation. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace DGRHS.Gaussian

lemma toLp_two_tendsto_of_sq_domination {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (a : ℕ → X → ℝ) (h : X → ℝ)
    (ha : ∀ j, MemLp (a j) 2 μ) (hh : MemLp h 2 μ)
    (B : X → ℝ) (hB : Integrable B μ)
    (hab : ∀ j, ∀ᵐ x ∂μ, (a j x)^2 ≤ B x)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun j => a j x) atTop (𝓝 (h x))) :
    Tendsto (fun j => (ha j).toLp (a j)) atTop (𝓝 (hh.toLp h)) := by
  have hb : ∀ᵐ x ∂μ, (h x)^2 ≤ B x := by
    filter_upwards [hc, ae_all_iff.2 hab] with x hx hxB
    exact le_of_tendsto (hx.pow 2) (Filter.Eventually.of_forall hxB)
  have ht : Tendsto (fun j => ∫ x, (a j x-h x)^2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
    have ht' : Tendsto (fun j => ∫ x, (a j x-h x)^2 ∂μ) atTop
        (𝓝 (∫ _ : X, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x => 4*B x)
      · intro j
        exact ((ha j).aestronglyMeasurable.sub hh.aestronglyMeasurable).pow 2
      · exact hB.const_mul 4
      · intro j
        filter_upwards [hab j,hb] with x hax hx
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (a j x+h x)]
      · filter_upwards [hc] with x hx
        simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using (hx.sub (tendsto_const_nhds (x := h x))).pow 2
    simpa only [integral_zero] using ht'
  have he (j : ℕ) : Real.sqrt (∫ x, (a j x-h x)^2 ∂μ) =
      ‖(ha j).toLp (a j)-hh.toLp h‖ := by
    change Real.sqrt (∫ x, ((a j-h) x)^2 ∂μ) = ‖(ha j).toLp (a j)-hh.toLp h‖
    rw [← DGRHS.Kernel.norm_toLp_sq ((ha j).sub hh),MemLp.toLp_sub,
      Real.sqrt_sq (norm_nonneg _)]
  have hn : Tendsto (fun j => ‖(ha j).toLp (a j)-hh.toLp h‖) atTop (𝓝 (0 : ℝ)) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp ht
    simpa only [Function.comp_def,he,Real.sqrt_zero] using hs
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hn.eventually (gt_mem_nhds hε)] with j hj
  simpa only [dist_eq_norm] using hj

end DGRHS.Gaussian
#check @DGRHS.Gaussian.toLp_two_tendsto_of_sq_domination
#print axioms DGRHS.Gaussian.toLp_two_tendsto_of_sq_domination
