import LeanResearch.PeriodicAttractiveLogGas.ClusterFactorization
import LeanResearch.PeriodicAttractiveLogGas.CollisionComparison
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure

/-! Integration of one freely moving cluster anchor.

Source: `lem:collision-integral`, lines 209–218 of the immutable corrected
manuscript. The head/tail decomposition preserves the actual product volume.
For each fixed head, translation of the tail preserves its product volume;
the translated open product ball is contained in the product ball of twice
the radius. Tonelli applies to the nonnegative extended integrals before any
finiteness conclusion. The unit-radius coefficient is the actual planar
volume `pi`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace PeriodicAttractiveLogGas

/-- The complete pair product with every coordinate integrated, including
the coordinate that will subsequently become the anchor. -/
def unanchoredClusterIntegral (k : ℕ) (ρ a : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in clusterBox k ρ, ENNReal.ofReal (planarPairWeight k a w)

/-- Subtracting a point of the radius-`ρ` ball sends every tail coordinate
from that ball into the radius-`2ρ` ball. -/
theorem clusterBox_subset_preimage_sub_anchor (n : ℕ) {ρ : ℝ} {x : PlanarSpace}
    (hx : x ∈ ball (0 : PlanarSpace) ρ) :
    clusterBox n ρ ⊆
      (fun w : Fin n → PlanarSpace ↦ w - fun _ ↦ x) ⁻¹' clusterBox n (2 * ρ) := by
  intro w hw
  change (fun i ↦ w i - x) ∈ clusterBox n (2 * ρ)
  intro i _
  have hwi : ‖w i‖ < ρ := by
    simpa only [mem_ball, dist_zero_right] using hw i (mem_univ i)
  have hxi : ‖x‖ < ρ := by simpa only [mem_ball, dist_zero_right] using hx
  have hsum : ‖w i‖ + ‖x‖ < 2 * ρ := by linarith
  simpa only [mem_ball, dist_zero_right] using (norm_sub_le (w i) x).trans_lt hsum

/-- The fixed-anchor bound uses an actual measure-preserving translation.
It is an inequality of extended integrals, with no finiteness assumption. -/
theorem clusterIntegral_sub_anchor_le (n : ℕ) (a : ℝ) {ρ : ℝ} {x : PlanarSpace}
    (hx : x ∈ ball (0 : PlanarSpace) ρ) :
    (∫⁻ w in clusterBox n ρ,
      ENNReal.ofReal (clusterWeight n a (fun i ↦ w i - x))) ≤
        clusterIntegral n (2 * ρ) a := by
  have htrans : MeasurePreserving
      (fun w : Fin n → PlanarSpace ↦ w - fun _ ↦ x) volume volume :=
    measurePreserving_sub_right (volume : Measure (Fin n → PlanarSpace)) (fun _ ↦ x)
  calc
    (∫⁻ w in clusterBox n ρ,
        ENNReal.ofReal (clusterWeight n a (fun i ↦ w i - x))) ≤
      ∫⁻ w in (fun w : Fin n → PlanarSpace ↦ w - fun _ ↦ x) ⁻¹' clusterBox n (2 * ρ),
        ENNReal.ofReal (clusterWeight n a (fun i ↦ w i - x)) :=
      lintegral_mono_set (clusterBox_subset_preimage_sub_anchor n hx)
    _ = clusterIntegral n (2 * ρ) a :=
      htrans.setLIntegral_comp_preimage (measurableSet_clusterBox n (2 * ρ))
        (measurable_clusterWeight n a).ennreal_ofReal

/-- Exact head/tail decomposition followed by reanchoring of the complete
pair product. Both coordinate splitting and Tonelli use the actual volumes. -/
theorem unanchoredClusterIntegral_eq_iterated (n : ℕ) (ρ a : ℝ) :
    unanchoredClusterIntegral (n + 1) ρ a =
      ∫⁻ x in ball (0 : PlanarSpace) ρ, ∫⁻ w in clusterBox n ρ,
        ENNReal.ofReal (clusterWeight n a (fun i ↦ w i - x)) := by
  let e : (PlanarSpace × (Fin n → PlanarSpace)) ≃ᵐ (Fin (n + 1) → PlanarSpace) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ PlanarSpace) 0).symm
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ PlanarSpace) 0).symm _
  have he_apply (p : PlanarSpace × (Fin n → PlanarSpace)) :
      e p = Fin.cons (α := fun _ => PlanarSpace) p.1 p.2 := by
    change Fin.insertNth (0 : Fin (n + 1)) p.1 p.2 =
      Fin.cons (α := fun _ => PlanarSpace) p.1 p.2
    exact Fin.insertNth_zero' _ _
  have hpre : e ⁻¹' clusterBox (n + 1) ρ =
      ball (0 : PlanarSpace) ρ ×ˢ clusterBox n ρ := by
    ext p
    change e p ∈ clusterBox (n + 1) ρ ↔
      p.1 ∈ ball (0 : PlanarSpace) ρ ∧ p.2 ∈ clusterBox n ρ
    rw [he_apply]
    constructor
    · intro hp
      constructor
      · simpa only [Fin.cons_zero] using hp 0 (mem_univ 0)
      · intro i _
        simpa only [Fin.cons_succ] using hp i.succ (mem_univ i.succ)
    · rintro ⟨hx, hw⟩ i _
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.cons_zero] using hx
      · simpa only [Fin.cons_succ] using hw j (mem_univ j)
  have hf : Measurable (fun w : Fin (n + 1) → PlanarSpace ↦
      ENNReal.ofReal (planarPairWeight (n + 1) a w)) :=
    (measurable_planarPairWeight (n + 1) a).ennreal_ofReal
  have hfe : Measurable (fun p : PlanarSpace × (Fin n → PlanarSpace) ↦
      ENNReal.ofReal (planarPairWeight (n + 1) a (e p))) := hf.comp e.measurable
  calc
    unanchoredClusterIntegral (n + 1) ρ a =
      ∫⁻ p in ball (0 : PlanarSpace) ρ ×ˢ clusterBox n ρ,
        ENNReal.ofReal (planarPairWeight (n + 1) a (e p)) := by
      simpa only [unanchoredClusterIntegral, hpre] using
        (he.setLIntegral_comp_preimage (measurableSet_clusterBox (n + 1) ρ) hf).symm
    _ = ∫⁻ x in ball (0 : PlanarSpace) ρ, ∫⁻ w in clusterBox n ρ,
        ENNReal.ofReal (planarPairWeight (n + 1) a (e (x, w))) := by
      rw [Measure.volume_eq_prod]
      exact setLIntegral_prod _ hfe.aemeasurable
    _ = ∫⁻ x in ball (0 : PlanarSpace) ρ, ∫⁻ w in clusterBox n ρ,
        ENNReal.ofReal (clusterWeight n a (fun i ↦ w i - x)) := by
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro w
      rw [he_apply, planarPairWeight_reanchor]
      simp only [Fin.cons_succ, Fin.cons_zero]

/-- The freely moving anchor contributes exactly its ball volume to the
upper bound. No finiteness is needed for the bound itself. -/
theorem unanchoredClusterIntegral_le (n : ℕ) (a : ℝ) {ρ : ℝ} (_hρ : 0 < ρ) :
    unanchoredClusterIntegral (n + 1) ρ a ≤
      volume (ball (0 : PlanarSpace) ρ) * clusterIntegral n (2 * ρ) a := by
  rw [unanchoredClusterIntegral_eq_iterated]
  calc
    (∫⁻ x in ball (0 : PlanarSpace) ρ, ∫⁻ w in clusterBox n ρ,
        ENNReal.ofReal (clusterWeight n a (fun i ↦ w i - x))) ≤
      ∫⁻ _x in ball (0 : PlanarSpace) ρ, clusterIntegral n (2 * ρ) a :=
      setLIntegral_mono measurable_const (fun _ hx ↦ clusterIntegral_sub_anchor_le n a hx)
    _ = volume (ball (0 : PlanarSpace) ρ) * clusterIntegral n (2 * ρ) a := by
      rw [setLIntegral_const, mul_comm]

/-- The exact coefficient used for the unanchored group on the unit ball. -/
theorem unanchoredClusterIntegral_unit_le (n : ℕ) (a : ℝ) :
    unanchoredClusterIntegral (n + 1) 1 a ≤
      ENNReal.ofReal Real.pi * clusterIntegral n 2 a := by
  simpa only [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_one, one_pow, one_mul,
    mul_one] using unanchoredClusterIntegral_le n a (by norm_num : (0 : ℝ) < 1)

/-- Finiteness follows only after the anchored integral has been shown finite. -/
theorem unanchoredClusterIntegral_lt_top_of_clusterIntegral (n : ℕ) (a : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hfinite : clusterIntegral n (2 * ρ) a < ∞) :
    unanchoredClusterIntegral (n + 1) ρ a < ∞ :=
  (unanchoredClusterIntegral_le n a hρ).trans_lt
    (ENNReal.mul_lt_top measure_ball_lt_top hfinite)

end PeriodicAttractiveLogGas
