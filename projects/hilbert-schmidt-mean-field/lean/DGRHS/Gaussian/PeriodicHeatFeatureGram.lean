import DGRHS.Gaussian.PeriodicHeatHilbertFeature

/-! The full heat covariance is the exact real Hilbert Gram kernel.
The diagonal is its genuine finite trace, not a renormalized replacement. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ComplexConjugate lp InnerProductSpace ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicHeatFeatureCoefficient_inner (τ : ℝ) (x y : PeriodicTorus ι) (k : PeriodicFrequency ι) :
    inner ℝ (periodicHeatFeatureCoefficient τ y k) (periodicHeatFeatureCoefficient τ x k) =
      ((periodicHeatCoefficient τ k:ℂ)*UnitAddTorus.mFourier k (x-y)).re := by
  rw [Complex.inner]
  unfold periodicHeatFeatureCoefficient
  rw [map_mul,Complex.conj_ofReal,periodic_mFourier_argument_sub]
  have hs : (Real.sqrt (periodicHeatCoefficient τ k):ℂ)*(Real.sqrt (periodicHeatCoefficient τ k):ℂ)=
      (periodicHeatCoefficient τ k:ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    exact Real.mul_self_sqrt (periodicHeatCoefficient_nonneg τ k)
  congr 1
  calc
    _ = ((Real.sqrt (periodicHeatCoefficient τ k):ℂ)*(Real.sqrt (periodicHeatCoefficient τ k):ℂ))*
        (UnitAddTorus.mFourier k x*conj (UnitAddTorus.mFourier k y)) := by ring
    _ = _ := by rw [hs]

/-- Exact full covariance, at every pair of spatial points. -/
theorem periodicHeatFeature_gram (τ : ℝ) (hτ : 0<τ) (x y : PeriodicTorus ι) :
    inner ℝ (periodicHeatFeature τ hτ x) (periodicHeatFeature τ hτ y)=periodicHeatFourierKernel τ (x-y) := by
  rw [real_inner_comm,lp.inner_eq_tsum]
  simp only [periodicHeatFeature_apply,periodicHeatFeatureCoefficient_inner]
  exact (Complex.re_tsum (periodicHeatFourierSeries_summable τ hτ (x-y))).symm

lemma periodicHeatFeature_norm_sq (τ : ℝ) (hτ : 0<τ) (x : PeriodicTorus ι) :
    ‖periodicHeatFeature τ hτ x‖^2=periodicHeatFourierKernel (ι := ι) τ 0 := by
  simpa only [real_inner_self_eq_norm_sq,sub_self] using periodicHeatFeature_gram τ hτ x x

lemma periodicHeatFeature_sum_norm_sq (τ : ℝ) (hτ : 0<τ) (N : ℕ) (x : Fin N → PeriodicTorus ι) :
    ‖∑ i : Fin N,periodicHeatFeature τ hτ (x i)‖^2=
      ∑ i : Fin N,∑ j : Fin N,periodicHeatFourierKernel τ (x i-x j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,periodicHeatFeature_gram]
  exact Finset.sum_comm

lemma periodicHeatFourierKernel_zero_nonneg (τ : ℝ) (hτ : 0<τ) :
    0≤periodicHeatFourierKernel (ι := ι) τ 0 := by
  rw [periodicHeatFourierKernel_zero τ hτ]
  exact tsum_nonneg (periodicHeatCoefficient_nonneg τ)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatFeature_gram
#print axioms DGRHS.Periodic.periodicHeatFeature_norm_sq
#print axioms DGRHS.Periodic.periodicHeatFeature_sum_norm_sq
#check @DGRHS.Periodic.periodicHeatFeature_gram
