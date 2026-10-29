/- Prepared outside the active proof snapshot while root compilation waits.
Not Lean checked; not an accepted paper result. Direct assembly of pinned
Mathlib scalar CLT and finite-dimensional Levy convergence. -/
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace BigOperators
namespace DGRHS.CLT
variable {E Ω Ω' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Finite-dimensional Levy gives the projection criterion, with actual
vector measurability stated separately. -/
theorem tendstoInDistribution_of_inner_projections
    (X : ℕ → Ω → E) (Y : Ω' → E)
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P')
    (hproj : ∀ t : E, TendstoInDistribution
      (fun n ω ↦ inner ℝ (X n ω) t) atTop
      (fun ω ↦ inner ℝ (Y ω) t) (fun _ ↦ P) P') :
    TendstoInDistribution X atTop Y (fun _ ↦ P) P' where
  forall_aemeasurable := hX
  aemeasurable_limit := hY
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    have hp := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (hproj t).tendsto (1 : ℝ)
    change Tendsto (fun n => charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (P'.map Y) t))
    change Tendsto (fun n => charFun (P.map (fun ω => inner ℝ (X n ω) t)) (1 : ℝ))
      atTop (𝓝 (charFun (P'.map (fun ω => inner ℝ (Y ω) t)) (1 : ℝ))) at hp
    simpa only [charFun_map_eq_charFun_map_inner_one (hX _) t,
      charFun_map_eq_charFun_map_inner_one hY t] using hp

set_option diagnostics true in
set_option maxHeartbeats 1000000 in
/-- The iid centered finite-dimensional CLT, with the target identified by
all actual scalar projection Gaussian laws rather than an assumed limit. -/
theorem finite_dimensional_centered_clt
    (X : ℕ → Ω → E) (Y : Ω' → E)
    (hX : MemLp (X 0) 2 P) (hmean : (∫ ω, X 0 ω ∂P) = 0)
    (hindep : iIndepFun X P) (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hY : AEMeasurable Y P')
    (hprojLaw : ∀ t : E, HasLaw (fun ω ↦ inner ℝ (Y ω) t)
      (gaussianReal 0 (Real.toNNReal (variance (fun ω ↦ inner ℝ (X 0 ω) t) P))) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop Y (fun _ ↦ P) P' := by
  have hx : ∀ n, AEMeasurable (X n) P := fun n ↦ (hident n).aemeasurable_fst
  have hsum (n : ℕ) : AEMeasurable
      (fun ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, X i ω) P := by
    fun_prop
  apply tendstoInDistribution_of_inner_projections
    (fun n ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, X i ω) Y hsum hY
  intro t
  have hm : (∫ ω, inner ℝ (X 0 ω) t ∂P) = 0 := by
    simp_rw [real_inner_comm t]
    rw [integral_inner (hX.integrable (by norm_num)), hmean, inner_zero_right]
  have hpm : Measurable (fun x : E ↦ inner ℝ x t) := by fun_prop
  have hi : iIndepFun (fun n ω ↦ inner ℝ (X n ω) t) P :=
    hindep.comp (fun _ (x : E) ↦ inner ℝ x t) (fun _ ↦ hpm)
  have hd : ∀ n, IdentDistrib (fun ω ↦ inner ℝ (X n ω) t)
      (fun ω ↦ inner ℝ (X 0 ω) t) P P :=
    fun n ↦ (hident n).comp (u := fun x ↦ inner ℝ x t) hpm
  have hc := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun n ω ↦ inner ℝ (X n ω) t)
    (Y := fun ω ↦ inner ℝ (Y ω) t) (P := P) (P' := P') (hprojLaw t)
    (hX.inner_const t) hi hd
  simpa only [hm, mul_zero, sub_zero, real_inner_smul_left, sum_inner] using hc
end DGRHS.CLT
#print axioms DGRHS.CLT.tendstoInDistribution_of_inner_projections
#print axioms DGRHS.CLT.finite_dimensional_centered_clt
#check DGRHS.CLT.finite_dimensional_centered_clt
