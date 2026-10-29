import DGRHS.Gaussian.D11Imported.CountableShannon
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.CountableShannon

lemma product_probability_hasSum (q : ℤ → ℝ) (hq : ∀ n, 0 ≤ q n) (hs : HasSum q 1) (d : ℕ) :
    HasSum (fun n : Fin d → ℤ => ∏ i : Fin d, q (n i)) 1 := by
  induction d with
  | zero =>
    convert hasSum_fintype (fun n : Fin 0 → ℤ => ∏ i : Fin 0, q (n i)) using 1 <;> simp
  | succ d ih =>
    have hp := hs.summable.mul_of_nonneg ih.summable hq
      (fun n => Finset.prod_nonneg (fun _ _ => hq _))
    have hp' : HasSum (fun v : ℤ × (Fin d → ℤ) => q v.1 * ∏ i : Fin d, q (v.2 i)) 1 := by
      have he := hs.mul_eq ih hp.hasSum
      norm_num only [one_mul] at he
      exact he.symm ▸ hp.hasSum
    apply (Fin.consEquiv (fun _ : Fin (d+1) => ℤ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.consEquiv, Fin.prod_univ_succ] using hp'

#print axioms product_probability_hasSum
end DGRHS.Gaussian.D11Imported.CountableShannon
