import DGRHS.Gaussian.D11Imported.ElevenLabelTails
import DGRHS.Gaussian.D11Imported.GeometricEntropy
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! The first absolute moment of the actual coordinate label and the resulting
one-coordinate Shannon entropy estimate from Section 4. -/
noncomputable section
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma coordinateLabel_positive_moment :
    Summable (fun n : ℕ => (n+1:ℝ)*coordinateLabelProbability ((n+1:ℕ):ℤ)) ∧
      (∑' n : ℕ, (n+1:ℝ)*coordinateLabelProbability ((n+1:ℕ):ℤ)) =
        ∑' k : ℕ, ∑' m : ℕ, coordinateLabelProbability ((m+k+1:ℕ):ℤ) := by
  let f : ℕ × ℕ → ℝ := fun v => coordinateLabelProbability ((v.2+v.1+1:ℕ):ℤ)
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => coordinateLabelProbability_nonneg _)).mpr
    ⟨coordinateLabel_positive_tail_summable, coordinateLabel_tail_series_summable⟩
  have hs : Summable (f ∘ e) := e.summable_iff.mpr hf
  have hrow (n : ℕ) : (∑' ij : ↥(Finset.antidiagonal n), (f ∘ e) ⟨n, ij⟩) =
      (n+1:ℝ)*coordinateLabelProbability ((n+1:ℕ):ℤ) := by
    have he (ij : ↥(Finset.antidiagonal n)) : (f ∘ e) ⟨n, ij⟩ =
        coordinateLabelProbability ((n+1:ℕ):ℤ) := by
      have h := Finset.HasAntidiagonal.mem_antidiagonal.mp ij.property
      change coordinateLabelProbability ((ij.val.2+ij.val.1+1:ℕ):ℤ) = _
      congr 1
      omega
    simp_rw [he]
    simp [Finset.Nat.card_antidiagonal]
  constructor
  · simpa only [hrow] using hs.sigma
  · calc
      _ = ∑' v, (f ∘ e) v := by rw [hs.tsum_sigma]; simp_rw [hrow]
      _ = ∑' v, f v := e.tsum_eq f
      _ = _ := hf.tsum_prod

set_option maxHeartbeats 800000 in
lemma coordinateLabel_abs_moment :
    Summable (fun n : ℤ => coordinateLabelProbability n*(n.natAbs:ℝ)) ∧
      coordinateLabelMoment =
        2*(∑' k : ℕ, ∑' m : ℕ, coordinateLabelProbability ((m+k+1:ℕ):ℤ)) := by
  have hpos : Summable (fun n : ℕ =>
      coordinateLabelProbability (n+1) * (((n+1:ℤ).natAbs):ℝ)) := by
    convert coordinateLabel_positive_moment.1 using 1
    funext n
    simp only [← Int.natCast_one, ← Int.natCast_add, Int.natAbs_natCast]
    push_cast
    ring
  have hneg : Summable (fun n : ℕ =>
      coordinateLabelProbability (-(n+1)) * (((-(n+1):ℤ).natAbs):ℝ)) := by
    simpa only [coordinateLabelProbability_even, Int.natAbs_neg] using hpos
  have hs := Summable.of_add_one_of_neg_add_one
    (f := fun n : ℤ => coordinateLabelProbability n*(n.natAbs:ℝ)) hpos hneg
  refine ⟨hs, ?_⟩
  unfold coordinateLabelMoment
  rw [tsum_of_add_one_of_neg_add_one
    (f := fun n : ℤ => coordinateLabelProbability n*(n.natAbs:ℝ)) hpos hneg]
  simp only [coordinateLabelProbability_even, Int.natAbs_neg, Int.natAbs_zero, Nat.cast_zero,
    mul_zero, add_zero]
  have he : (∑' n : ℕ, coordinateLabelProbability (n+1)*(((n+1:ℤ).natAbs):ℝ)) =
      ∑' n : ℕ, (n+1:ℝ)*coordinateLabelProbability ((n+1:ℕ):ℤ) := by
    apply tsum_congr
    intro n
    simp only [← Int.natCast_one, ← Int.natCast_add, Int.natAbs_natCast]
    push_cast
    ring
  rw [he, coordinateLabel_positive_moment.2]
  ring

lemma coordinateLabelMoment_lt : coordinateLabelMoment < (83927/8121093750:ℝ) := by
  rw [coordinateLabel_abs_moment.2]
  have ht := coordinateLabel_tail_series_bound
  have hp : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hc : (1280/(693*Real.pi*25^6)) * (2047*1025/1024) < (83927/16242187500:ℝ) := by
    calc
      _ < ((1280:ℝ)/(693*3*25^6)) * (2047*1025/1024) := by gcongr
      _ = _ := by norm_num
  linarith

lemma coordinateLabel_entropy_lt :
    Summable (fun n : ℤ => coordinateLabelProbability n*Real.log (coordinateLabelProbability n)) ∧
      11 * (-(∑' n : ℤ, coordinateLabelProbability n*Real.log (coordinateLabelProbability n))) < (1/600:ℝ) :=
  CountableShannon.eleven_label_entropy_of_moment coordinateLabelProbability
    coordinateLabelProbability_nonneg coordinateLabelProbability_hasSum coordinateLabel_abs_moment.1
    coordinateLabelMoment_lt

#print axioms coordinateLabelMoment_lt
#print axioms coordinateLabel_entropy_lt
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
