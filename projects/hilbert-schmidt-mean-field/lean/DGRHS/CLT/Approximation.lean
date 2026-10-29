/- UNCHECKED outside the frozen coordinator snapshot. Quantitative approximation
for bounded Lipschitz tests. The full-kernel theorem must instantiate all three
limits from actual spectral remainders, the finite CLT, and the constructed
square-summable Gaussian chaos. -/
import DGRHS.Gaussian.FeatureCentering
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace DGRHS.CLT

lemma tendsto_of_uniform_approximation
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (r : ℕ → ℝ) (z : ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 z))
    (hv : ∀ m, Tendsto (v m) atTop (𝓝 (a m)))
    (huv : ∀ m n, dist (u n) (v m n) ≤ r m) :
    Tendsto u atTop (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  obtain ⟨m, hm, ham⟩ :=
    ((hr.eventually_lt_const he).and ((Metric.tendsto_nhds.mp ha) (ε / 3) he)).exists
  filter_upwards [(Metric.tendsto_nhds.mp (hv m)) (ε / 3) he] with n hn
  have htri := (dist_triangle (u n) (v m n) z).trans
    (add_le_add_right (dist_triangle (v m n) (a m) z) _)
  have hbound := huv m n
  linarith

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma integrable_bounded_lipschitz_comp (F : ℝ → ℝ) (L : ℝ≥0)
    (hF : LipschitzWith L F) (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
    {X : S → ℝ} (hX : AEMeasurable X μ) : Integrable (fun x => F (X x)) μ := by
  obtain ⟨C,hC⟩ := hb
  apply Integrable.of_bound (hF.continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable
    (‖F 0‖ + C)
  exact ae_of_all _ fun x => by
    have h := hC (X x) 0
    change ‖F (X x)‖ ≤ ‖F 0‖ + C
    have ht := norm_sub_norm_le (F (X x)) (F 0)
    rw [dist_eq_norm] at h
    linarith

lemma integral_bounded_lipschitz_difference_le
    (F : ℝ → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
    {X Y : S → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hR : Integrable (fun x => X x - Y x) μ) :
    dist (∫ x, F (X x) ∂μ) (∫ x, F (Y x) ∂μ) ≤
      L * (∫ x, ‖X x - Y x‖ ∂μ) := by
  have hiX := integrable_bounded_lipschitz_comp F L hF hb hX
  have hiY := integrable_bounded_lipschitz_comp F L hF hb hY
  rw [dist_eq_norm, ← integral_sub hiX hiY]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ x, ‖F (X x) - F (Y x)‖ ∂μ) ≤ ∫ x, (L : ℝ) * ‖X x - Y x‖ ∂μ := by
      apply integral_mono (hiX.sub hiY).norm (hR.norm.const_mul (L : ℝ))
      intro x
      change ‖F (X x) - F (Y x)‖ ≤ (L : ℝ) * ‖X x - Y x‖
      simpa only [dist_eq_norm] using hF.dist_le_mul (X x) (Y x)
    _ = _ := integral_const_mul _ _

lemma integral_bounded_lipschitz_Lp_difference_le
    (F : ℝ → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
    (X Y : Lp ℝ 2 μ) :
    dist (∫ x, F (X x) ∂μ) (∫ x, F (Y x) ∂μ) ≤ L * ‖X - Y‖ := by
  have hR : (X - Y : Lp ℝ 2 μ) =ᵐ[μ] (fun x => X x - Y x) := Lp.coeFn_sub X Y
  have hiR : Integrable (fun x => X x - Y x) μ :=
    ((Lp.memLp (X-Y)).integrable (by norm_num)).congr hR
  apply (integral_bounded_lipschitz_difference_le F L hF hb
    (Lp.memLp X).aemeasurable (Lp.memLp Y).aemeasurable hiR).trans
  gcongr
  calc
    (∫ x, ‖X x - Y x‖ ∂μ) = ∫ x, ‖(X-Y : Lp ℝ 2 μ) x‖ ∂μ :=
      integral_congr_ae (hR.symm.fun_comp norm)
    _ ≤ ‖X-Y‖ := DGRHS.Gaussian.integral_norm_Lp_two_le_norm (X-Y)

end DGRHS.CLT
#print axioms DGRHS.CLT.tendsto_of_uniform_approximation
#print axioms DGRHS.CLT.integral_bounded_lipschitz_difference_le
#print axioms DGRHS.CLT.integral_bounded_lipschitz_Lp_difference_le
