/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ElevenShellPolynomial

/-! Truncated convolution computes the exact coefficients up to squared
radius 100; no terms that can reach those coefficients are discarded. -/
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell
open scoped BigOperators

def initialArray : Array ℕ := (List.range 101).toArray.map (fun q => if q=0 then 1 else 0)
def convolution (a : Array ℕ) : Array ℕ := (List.range 101).toArray.map fun q =>
  ∑ j : Fin 21, if coordinateRadius j ≤ q then a[q-coordinateRadius j]! else 0
def shellArray : ℕ → Array ℕ
  | 0 => initialArray
  | n+1 => convolution (shellArray n)

lemma convolution_size (a : Array ℕ) : (convolution a).size = 101 := by simp [convolution]
lemma initialArray_size : initialArray.size = 101 := by simp [initialArray]

lemma convolution_get (a : Array ℕ) {q : ℕ} (hq : q < 101) :
    (convolution a)[q]! = ∑ j : Fin 21, if coordinateRadius j ≤ q then a[q-coordinateRadius j]! else 0 := by
  rw [getElem!_pos _ q (by simpa [convolution_size] using hq)]
  simp only [convolution, Array.getElem_map, List.getElem_toArray, List.getElem_range]

lemma initialArray_get {q : ℕ} (hq : q < 101) :
    initialArray[q]! = if q=0 then 1 else 0 := by
  rw [getElem!_pos _ q (by simpa [initialArray_size] using hq)]
  simp [initialArray]

lemma thetaPolynomial_mul_coeff (p : Polynomial ℕ) (q : ℕ) :
    (thetaPolynomial*p).coeff q =
      ∑ j : Fin 21, if coordinateRadius j ≤ q then p.coeff (q-coordinateRadius j) else 0 := by
  simp only [thetaPolynomial, Finset.sum_mul, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul']

lemma shellArray_coeff (d : ℕ) {q : ℕ} (hq : q < 101) :
    (shellArray d)[q]! = (thetaPolynomial^d).coeff q := by
  induction d generalizing q with
  | zero => simp only [shellArray, initialArray_get hq, pow_zero, Polynomial.coeff_one]
  | succ d ih =>
    rw [shellArray, convolution_get _ hq, pow_succ', thetaPolynomial_mul_coeff]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · rw [ih (by omega)]
    · rfl

#print axioms shellArray_coeff
end DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell
