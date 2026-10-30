import DGPS.Lipschitz.T01SmoothingWitness
import FullLabeledLSI.Paper.Prop23ReplaceA

/-! Uniform particle-number value moments on the same finite-rank smoothing witness. -/

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology KernelApproximation CenteredKernelMoments
open scoped ENNReal

/-- The chosen legacy fluctuation polynomial is exactly the actual smoothed particle energy. -/
theorem t01_URN_eq_smoothK {d : ℕ} (S : Spec d) (aux : Aux S) (D : KData d)
    (hsym : ∀ x y, D.K x y = D.K y x) (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0)
    (J : InteractionData d) (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v)
    (R : ℕ) (t : ℝ) (m : ℕ) (hs : F.s R = Finset.range m)
    (ha : ∀ i j, F.a R i j = positiveKernelCoefficient S D t m i j)
    (N : ℕ) (X : SharpLSI.Config N d) :
    SharpLSI.FL.URN F R N X = ((2 : ℝ) * N)⁻¹ * ∑ i, ∑ j, smoothK S D t m (X i) (X j) := by
  rw [SharpLSI.FL.URN_eq_Ukernel]
  have hker : (fun x y => ∑ i ∈ F.s R, ∑ j ∈ F.s R,
      F.a R i j * S.v (i + 1) x * S.v (j + 1) y) = smoothK S D t m := by
    funext x y
    rw [hs]
    simp only [ha]
    exact (smoothK_eq_positive_block S aux D hc hsym t m x y).symm
  rw [hker]
  simp only [SharpLSI.Ukernel, one_div]

/-- Every finite value moment of the actual particle-energy residual vanishes uniformly in N. -/
theorem t01_residual_Ucentered_eLpNorm_tendsto {d : ℕ} (S : Spec d) (aux : Aux S)
    (J : InteractionData d) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (t : ℕ → ℝ) (m : ℕ → ℕ)
    (hU : TendstoUniformly (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
      (fun p => D.K p.1 p.2) atTop)
    (F : SharpLSI.FL.FiniteRankApprox J.W S.mu S.v)
    (hs : ∀ R, F.s R = Finset.range (m R))
    (ha : ∀ R i j, F.a R i j = positiveKernelCoefficient S D (t R) (m R) i j)
    {q : ℝ≥0∞} (hq : q ≠ ⊤) :
    Tendsto (fun R => ⨆ N : ℕ,
      eLpNorm (fun X => SharpLSI.Ucentered J.W S.mu N X - SharpLSI.FL.URN F R N X) q
        (Measure.pi fun _ : Fin N => S.mu)) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hsym : ∀ x y, D.K x y = D.K y x := by
    rw [hD]
    exact centeredKernel_symm J S.mu
  have hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0 := by
    intro y
    simp only [hD, centeredKernel_symm J S.mu _ y]
    exact integral_centeredKernel_right J S.mu y
  have hKc : ∀ y, Continuous fun x => D.K x y := fun y =>
    D.Kc.comp (continuous_id.prodMk continuous_const)
  have key := uStat_family_tendsto (μ := S.mu)
    (F := fun R x y => D.K x y - smoothK S D (t R) (m R) x y)
    (fun R => (D.Kc.sub (smoothK_continuous S D (t R) (m R))).measurable)
    (fun R x y => by rw [hsym x y, smoothK_symm S D hsym])
    (fun R y => by
      rw [integral_sub (S.int_cont (hKc y)), hc y, smoothK_centered S D aux.v0 hc]
      · simp
      · exact S.int_cont ((smoothK_continuous S D (t R) (m R)).comp
          (continuous_id.prodMk continuous_const)))
    (fun δ hδ => by
      filter_upwards [Metric.tendstoUniformly_iff.mp hU δ hδ] with R hR x y
      simpa only [Real.dist_eq, abs_sub_comm] using (hR (x, y)).le)
    hq
  apply key.congr
  intro R
  congr 1
  funext N
  congr 1
  funext X
  rw [t01_URN_eq_smoothK S aux D hsym hc J F R (t R) (m R) (hs R) (ha R)]
  unfold SharpLSI.Ucentered
  rw [legacy_centeredKernel_eq]
  simp only [← hD, one_div]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]

end DGPS.Lipschitz
