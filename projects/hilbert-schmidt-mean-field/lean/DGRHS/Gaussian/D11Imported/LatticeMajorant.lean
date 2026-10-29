/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.Definitions
import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Square summability of the actual critical Green multiplier

The frequency radius is the Euclidean radius from EndpointNormalization,
not the function-space supremum norm. Lattice summability is proved by a
finite product comparison; it is not an additional hypothesis.
-/

open Filter
open MeasureTheory
open scoped BigOperators ENNReal

namespace DGRHS.Gaussian.D11Imported.LatticeMajorant
open HighDim

set_option maxHeartbeats 800000

noncomputable def radiusSq {d : ℕ} (k : Frequency d) : ℝ :=
  ∑ j : Fin d, (k j : ℝ) ^ 2

lemma radiusSq_nonneg {d : ℕ} (k : Frequency d) : 0 ≤ radiusSq k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma summable_int_one_add_sq_inv :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply hbase.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  have hp : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)), ← one_div]
  exact one_div_le_one_div_of_le hp (by linarith)

noncomputable def productMajorant {d : ℕ} (k : Frequency d) : ℝ :=
  ∏ j : Fin d, (1 + (k j : ℝ) ^ 2)⁻¹

lemma productMajorant_nonneg {d : ℕ} (k : Frequency d) :
    0 ≤ productMajorant k := by
  apply Finset.prod_nonneg
  intro j _
  positivity

lemma summable_productMajorant (d : ℕ) :
    Summable (productMajorant : Frequency d → ℝ) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    have hp := summable_int_one_add_sq_inv.mul_of_nonneg ih
      (fun n => by positivity) (fun k => productMajorant_nonneg k)
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff.mp
    simpa [Function.comp_def, productMajorant, Fin.prod_univ_succ, Fin.consEquiv, mul_comm] using hp

lemma shifted_radial_inv_le_product {d : ℕ} (k : Frequency d) :
    (1 + radiusSq k)⁻¹ ^ d ≤ productMajorant k := by
  have hprod : (∏ j : Fin d, (1 + (k j : ℝ) ^ 2)) ≤ (1 + radiusSq k) ^ d := by
    calc
      _ ≤ ∏ _ : Fin d, (1 + radiusSq k) := by
        apply Finset.prod_le_prod₀
        · intro j _
          positivity
        · intro j _
          simpa [radiusSq, add_comm] using add_le_add_left
            (Finset.single_le_sum (fun i _ => sq_nonneg (k i : ℝ)) (Finset.mem_univ j)) 1
      _ = _ := by simp
  have hpos : 0 < ∏ j : Fin d, (1 + (k j : ℝ) ^ 2) := by
    apply Finset.prod_pos
    intro j _
    positivity
  simpa only [productMajorant, ← Finset.prod_inv_distrib, ← inv_pow] using
    inv_anti₀ hpos hprod

end DGRHS.Gaussian.D11Imported.LatticeMajorant
#print axioms DGRHS.Gaussian.D11Imported.LatticeMajorant.summable_productMajorant
#print axioms DGRHS.Gaussian.D11Imported.LatticeMajorant.shifted_radial_inv_le_product
