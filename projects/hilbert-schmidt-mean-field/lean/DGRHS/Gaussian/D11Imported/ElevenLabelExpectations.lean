import DGRHS.Gaussian.D11Imported.ElevenLabelMarginals
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Coordinate expectations of the genuine joint label law, including
absolute summability needed for logarithmic cross entropies. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma labelProbability_coordinate_summable (i : Fin 11) (n : ℤ) :
    Summable (fun m : Frequency 10 => labelProbability (i.insertNth n m)) := by
  apply labelProbability_hasSum.summable.comp_injective
  intro a b h
  funext j
  have hh := congrFun h (i.succAbove j)
  simpa only [Fin.insertNth_apply_succAbove] using hh

lemma labelProbability_coordinate_tsum (i : Fin 11) (n : ℤ) :
    (∑' m : Frequency 10, labelProbability (i.insertNth n m)) = coordinateLabelProbability n := by
  have h := labelProbability_coordinate_lsum i n
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => labelProbability_nonneg _)
    (labelProbability_coordinate_summable i n)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg (fun _ => labelProbability_nonneg _))
    (coordinateLabelProbability_nonneg n)).mp h

theorem label_coordinate_expectation (i : Fin 11) (g : ℤ → ℝ)
    (hg : Summable (fun n => coordinateLabelProbability n * ‖g n‖)) :
    Summable (fun n : Frequency 11 => labelProbability n * g (n i)) ∧
      (∑' n : Frequency 11, labelProbability n * g (n i)) =
        ∑' n : ℤ, coordinateLabelProbability n * g n := by
  let e := Fin.insertNthEquiv (fun _ : Fin 11 => ℤ) i
  have hpa : Summable (fun v : ℤ × Frequency 10 => labelProbability (i.insertNth v.1 v.2) * ‖g v.1‖) := by
    apply (summable_prod_of_nonneg
      (f := fun v : ℤ × Frequency 10 => labelProbability (i.insertNth v.1 v.2) * ‖g v.1‖)
      (fun v => mul_nonneg (labelProbability_nonneg _) (norm_nonneg _))).mpr
    constructor
    · intro n
      change Summable (fun m : Frequency 10 => labelProbability (i.insertNth n m) * ‖g n‖)
      exact (labelProbability_coordinate_summable i n).mul_right ‖g n‖
    · change Summable (fun n : ℤ => ∑' m : Frequency 10, labelProbability (i.insertNth n m) * ‖g n‖)
      simpa only [tsum_mul_right, labelProbability_coordinate_tsum] using hg
  have hp : Summable (fun v : ℤ × Frequency 10 => labelProbability (i.insertNth v.1 v.2) * g v.1) := by
    apply hpa.of_norm_bounded
    intro v
    rw [norm_mul, Real.norm_of_nonneg (labelProbability_nonneg _)]
  have hs : Summable (fun n : Frequency 11 => labelProbability n * g (n i)) := by
    apply e.summable_iff.mp
    simpa only [e, Fin.insertNthEquiv, Equiv.coe_fn_mk, Function.comp_def, Fin.insertNth_apply_same] using hp
  refine ⟨hs, ?_⟩
  calc
    _ = ∑' v : ℤ × Frequency 10, labelProbability (i.insertNth v.1 v.2) * g v.1 := by
      have he := e.tsum_eq (fun n : Frequency 11 => labelProbability n * g (n i))
      simpa only [e, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same] using he.symm
    _ = ∑' n : ℤ, ∑' m : Frequency 10, labelProbability (i.insertNth n m) * g n := hp.tsum_prod
    _ = _ := by simp_rw [tsum_mul_right, labelProbability_coordinate_tsum]

#print axioms label_coordinate_expectation
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
