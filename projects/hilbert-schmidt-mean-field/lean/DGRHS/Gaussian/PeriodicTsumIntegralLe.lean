import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Packet P9h: a series of integrals of nonnegative functions whose pointwise sum is dominated by an
integrable function is summable, with sum bounded by the integral of the dominating function.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic

theorem summable_integral_tsum_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {κ : Type*} [Countable κ] {F : κ → α → ℝ} {g : α → ℝ}
    (hF : ∀ i, Integrable (F i) μ) (hnn : ∀ i, 0 ≤ᵐ[μ] F i)
    (hpt : ∀ᵐ x ∂μ, Summable fun i => F i x) (hg : Integrable g μ)
    (hle : ∀ᵐ x ∂μ, ∑' i, F i x ≤ g x) :
    Summable (fun i => ∫ x, F i x ∂μ) ∧ ∑' i, ∫ x, F i x ∂μ ≤ ∫ x, g x ∂μ := by
  have hint0 : ∀ i, 0 ≤ ∫ x, F i x ∂μ := fun i => integral_nonneg_of_ae (hnn i)
  have h1 : ∀ i, ∫⁻ x, ENNReal.ofReal (F i x) ∂μ = ENNReal.ofReal (∫ x, F i x ∂μ) :=
    fun i => (ofReal_integral_eq_lintegral_ofReal (hF i) (hnn i)).symm
  have h2 : ∫⁻ x, ∑' i, ENNReal.ofReal (F i x) ∂μ ≤ ENNReal.ofReal (∫ x, g x ∂μ) := by
    have hpt' : ∀ᵐ x ∂μ, ∑' i, ENNReal.ofReal (F i x) ≤ ENNReal.ofReal (g x) := by
      filter_upwards [hpt, hle, ae_all_iff.2 hnn] with x hx hx2 hx3
      rw [← ENNReal.ofReal_tsum_of_nonneg hx3 hx]
      exact ENNReal.ofReal_le_ofReal hx2
    calc _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := lintegral_mono_ae hpt'
      _ = ENNReal.ofReal (∫ x, g x ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hg]
        filter_upwards [hpt, hle, ae_all_iff.2 hnn] with x hx hx2 hx3
        exact (tsum_nonneg hx3).trans hx2
  have h3 : ∑' i, ENNReal.ofReal (∫ x, F i x ∂μ) ≤ ENNReal.ofReal (∫ x, g x ∂μ) := by
    simp_rw [← h1]
    rw [← lintegral_tsum (fun i => (hF i).1.aemeasurable.ennreal_ofReal)]
    exact h2
  have hfin : ∑' i, ENNReal.ofReal (∫ x, F i x ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h3
  have hsum : Summable (fun i => ∫ x, F i x ∂μ) := by
    have := ENNReal.summable_toReal hfin
    exact this.congr (fun i => ENNReal.toReal_ofReal (hint0 i))
  refine ⟨hsum, ?_⟩
  have hg0 : 0 ≤ ∫ x, g x ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hpt, hle, ae_all_iff.2 hnn] with x hx hx2 hx3
    exact (tsum_nonneg hx3).trans hx2
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
  rw [ENNReal.toReal_ofReal hg0, ← ENNReal.ofReal_tsum_of_nonneg hint0 hsum,
    ENNReal.toReal_ofReal (tsum_nonneg hint0)] at this
  exact this

end DGRHS.Periodic
#print axioms DGRHS.Periodic.summable_integral_tsum_le
