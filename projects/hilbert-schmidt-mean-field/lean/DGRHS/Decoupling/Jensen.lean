import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Set

namespace DGRHS.Decoupling

/-- The scalar even-power Jensen step used on selector and product averages. -/
theorem even_moment_jensen {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (k : ℕ)
    (hf : Integrable f μ) (hp : Integrable (fun x ↦ |f x| ^ (2 * k)) μ) :
    |∫ x, f x ∂μ| ^ (2 * k) ≤ ∫ x, |f x| ^ (2 * k) ∂μ := by
  have hp' : Integrable (fun x ↦ f x ^ (2 * k)) μ := by
    simpa only [pow_abs_two_mul] using hp
  simpa only [pow_abs_two_mul] using
    ((even_two_mul k).convexOn_pow (𝕜 := ℝ)).map_integral_le
      (continuous_pow (2 * k)).continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ ↦ mem_univ _)) hf hp'

/-- The high moment assumption supplies both integrability obligations for Jensen. -/
theorem even_moment_jensen_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hf : MemLp f (2 * k : ℕ) μ) :
    |∫ x, f x ∂μ| ^ (2 * k) ≤ ∫ x, |f x| ^ (2 * k) ∂μ := by
  apply even_moment_jensen μ f k
  · apply hf.integrable
    have h : 1 ≤ 2 * k := by omega
    exact_mod_cast h
  · simpa only [Real.norm_eq_abs] using hf.integrable_norm_pow'

/-- Averaging over an independent coordinate is contractive for every scalar even moment.
All required integrability is explicit; no conditional-expectation premise is assumed. -/
theorem product_average_even_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × Ξ → ℝ) (k : ℕ)
    (hf : Integrable f (μ.prod ν))
    (hp : Integrable (fun z ↦ |f z| ^ (2 * k)) (μ.prod ν)) :
    (∫ x, |∫ y, f (x, y) ∂ν| ^ (2 * k) ∂μ) ≤
      ∫ z, |f z| ^ (2 * k) ∂μ.prod ν := by
  have hj : ∀ᵐ x ∂μ, |∫ y, f (x, y) ∂ν| ^ (2 * k) ≤
      ∫ y, |f (x, y)| ^ (2 * k) ∂ν := by
    filter_upwards [hf.prod_right_ae, hp.prod_right_ae] with x hfx hpx
    exact even_moment_jensen ν (fun y ↦ f (x, y)) k hfx hpx
  have hm : AEStronglyMeasurable (fun x ↦ |∫ y, f (x, y) ∂ν| ^ (2 * k)) μ :=
    hf.aestronglyMeasurable.integral_prod_right'.norm.pow (2 * k)
  have hI : Integrable (fun x ↦ |∫ y, f (x, y) ∂ν| ^ (2 * k)) μ := by
    apply hp.integral_prod_left.mono' hm
    filter_upwards [hj] with x hx
    have hn : 0 ≤ |∫ y, f (x, y) ∂ν| ^ (2 * k) := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hx
  rw [integral_prod _ hp]
  exact integral_mono_ae hI hp.integral_prod_left hj

#print axioms DGRHS.Decoupling.product_average_even_moment

#print axioms DGRHS.Decoupling.even_moment_jensen
#print axioms DGRHS.Decoupling.even_moment_jensen_memLp

end DGRHS.Decoupling
