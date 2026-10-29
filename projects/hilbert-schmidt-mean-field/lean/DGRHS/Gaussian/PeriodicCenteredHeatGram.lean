import DGRHS.Gaussian.PeriodicPositiveFourierGram
import DGRHS.Gaussian.PeriodicHeatTimeTail

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Actual nonzero heat modes, including a finite
trace and a centered particle cap. The zero mode is removed BEFORE integrating
over an infinite Mellin tail; retaining the zero mode would yield a divergent
large-time diagonal envelope. This is not a pointwise heat-order assertion. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ComplexConjugate lp InnerProductSpace ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicCenteredHeatCoefficient (t : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  if k = 0 then 0 else Real.exp (-t * ‖periodicFrequencyVector k‖ ^ 2)

lemma periodicCenteredHeatCoefficient_nonneg (t : ℝ) (k : PeriodicFrequency ι) :
    0 ≤ periodicCenteredHeatCoefficient t k := by
  unfold periodicCenteredHeatCoefficient
  split_ifs <;> positivity

lemma periodicCenteredHeatCoefficient_le (t : ℝ) (k : PeriodicFrequency ι) :
    periodicCenteredHeatCoefficient t k ≤ Real.exp (-t * ‖periodicFrequencyVector k‖ ^ 2) := by
  unfold periodicCenteredHeatCoefficient
  split_ifs with hk
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma periodicCenteredHeatCoefficient_summable (t : ℝ) (ht : 0 < t) :
    Summable (periodicCenteredHeatCoefficient (ι := ι) t) :=
  (summable_periodicGaussian t ht).of_nonneg_of_le
    (periodicCenteredHeatCoefficient_nonneg t) (periodicCenteredHeatCoefficient_le t)

lemma periodicCenteredHeatCoefficient_sqrt_bound (t : ℝ) (k : PeriodicFrequency ι) :
    Real.sqrt (periodicCenteredHeatCoefficient t k) ≤
      Real.exp (-(t / 2) * ‖periodicFrequencyVector k‖ ^ 2) := by
  have he : (Real.exp (-(t / 2) * ‖periodicFrequencyVector k‖ ^ 2)) ^ 2 =
      Real.exp (-t * ‖periodicFrequencyVector k‖ ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
  rw [Real.sq_sqrt (periodicCenteredHeatCoefficient_nonneg t k), he]
  exact periodicCenteredHeatCoefficient_le t k

lemma periodicCenteredHeatCoefficient_sqrt_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun k : PeriodicFrequency ι => Real.sqrt (periodicCenteredHeatCoefficient t k)) :=
  (summable_periodicGaussian (t / 2) (by positivity)).of_nonneg_of_le
    (fun _ => Real.sqrt_nonneg _) (periodicCenteredHeatCoefficient_sqrt_bound t)

lemma periodicCenteredHeatCoefficient_kernel (t : ℝ) (ht : 0 < t)
    (x : PeriodicTorus ι) :
    periodicPositiveFourierKernel (periodicCenteredHeatCoefficient t) x =
      (periodicGaussianHeat t x).re - 1 := by
  have he (k : PeriodicFrequency ι) :
      (periodicCenteredHeatCoefficient t k : ℂ) * UnitAddTorus.mFourier k x =
        periodicCenteredHeatTerm t x k := by
    by_cases hk : k = 0 <;> simp [periodicCenteredHeatCoefficient, periodicCenteredHeatTerm, hk]
  unfold periodicPositiveFourierKernel
  simp only [he]
  rw [← periodicGaussianHeat_centered_series t ht x]
  simp only [Complex.sub_re, Complex.one_re]

lemma periodicCenteredHeatCoefficient_trace (t : ℝ) (ht : 0 < t) :
    (∑' k : PeriodicFrequency ι, periodicCenteredHeatCoefficient t k) =
      (periodicGaussianHeat t (0 : PeriodicTorus ι)).re - 1 := by
  rw [← periodicPositiveFourierKernel_zero _ (periodicCenteredHeatCoefficient_nonneg t)
    (periodicCenteredHeatCoefficient_summable t ht), periodicCenteredHeatCoefficient_kernel t ht]

lemma periodicCenteredHeatCoefficient_gram (t : ℝ) (ht : 0 < t)
    (x y : PeriodicTorus ι) :
    inner ℝ
      (periodicPositiveFourierFeature _ (periodicCenteredHeatCoefficient_nonneg t)
        (periodicCenteredHeatCoefficient_summable t ht) x)
      (periodicPositiveFourierFeature _ (periodicCenteredHeatCoefficient_nonneg t)
        (periodicCenteredHeatCoefficient_summable t ht) y) =
      (periodicGaussianHeat t (x - y)).re - 1 := by
  rw [periodicPositiveFourierFeature_gram, periodicCenteredHeatCoefficient_kernel t ht]

lemma periodicCenteredHeat_centered_bound (t : ℝ) (ht : 0 < t)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    ‖hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      (periodicGaussianHeat t (q.1 - q.2)).re - 1) p‖ ≤
      4 * ((periodicGaussianHeat t (0 : PeriodicTorus ι)).re - 1) := by
  have h := periodicPositiveFourier_centered_bound _
    (periodicCenteredHeatCoefficient_nonneg t) (periodicCenteredHeatCoefficient_summable t ht)
    (periodicCenteredHeatCoefficient_sqrt_summable t ht) μ p
  simpa only [periodicCenteredHeatCoefficient_kernel t ht,
    periodicCenteredHeatCoefficient_trace t ht] using h

lemma periodicCenteredHeat_centered_particle_cap (t : ℝ) (ht : 0 < t)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    -(∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
      hoeffdingCentered μ (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        (periodicGaussianHeat t (p.1 - p.2)).re - 1) (x i,x j)) / (2 * (N : ℝ)) ≤
      2 * ((periodicGaussianHeat t (0 : PeriodicTorus ι)).re - 1) := by
  have h := periodicPositiveFourier_centered_particle_cap _
    (periodicCenteredHeatCoefficient_nonneg t) (periodicCenteredHeatCoefficient_summable t ht)
    (periodicCenteredHeatCoefficient_sqrt_summable t ht) μ N hN x
  simpa only [periodicCenteredHeatCoefficient_kernel t ht,
    periodicCenteredHeatCoefficient_trace t ht] using h

end DGRHS.Periodic
