/- Outside proof pending exact A8 review/integration.
Reciprocal source thresholds use an explicitly positive admissible witness.
The product-smallness theorem separately retains C=0 honestly. -/
import DGRHS.Attractive.CanonicalExponential
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
variable {S : Type*} [MeasurableSpace S]

lemma RowFactorialMoments.mono {μ : Measure S} {h : S × S → ℝ} {C D : ℝ}
    (hc : RowFactorialMoments μ h C) (hCD : C≤D) : RowFactorialMoments μ h D := by
  refine ⟨hc.nonneg.trans hCD,hc.proper,?_⟩
  intro p hp y
  exact (hc.bound p hp y).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hc.nonneg hCD p) (Nat.cast_nonneg _))

lemma RowFactorialMoments.positive_witness {μ : Measure S} {h : S × S → ℝ} {C : ℝ}
    (hc : RowFactorialMoments μ h C) :
    0<C+1 ∧ RowFactorialMoments μ h (C+1) := by
  exact ⟨by linarith [hc.nonneg],hc.mono (by linarith)⟩

def attractiveBetaThreshold (C : ℝ) : ℝ := (attractiveMomentConstant*C)⁻¹

lemma attractiveBetaThreshold_pos {C : ℝ} (hC : 0<C) : 0<attractiveBetaThreshold C :=
  inv_pos.mpr (mul_pos attractiveMomentConstant_pos hC)

lemma attractiveBetaThreshold_lt_iff {C β : ℝ} (hC : 0<C) :
    β<attractiveBetaThreshold C ↔ β*(attractiveMomentConstant*C)<1 := by
  unfold attractiveBetaThreshold
  rw [←one_div,lt_div_iff₀ (mul_pos attractiveMomentConstant_pos hC)]

end DGRHS.Attractive
#print axioms DGRHS.Attractive.RowFactorialMoments.positive_witness
#print axioms DGRHS.Attractive.attractiveBetaThreshold_lt_iff
