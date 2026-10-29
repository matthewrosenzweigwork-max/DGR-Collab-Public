/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.Definitions
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact shell multiplicities in the integer box [-10,10]^d. The polynomial
identity counts genuine lattice vectors, before any numerical certificate is
used. Every shell of squared radius at most 100 lies in this box. -/
noncomputable section
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell

def coordinate (j : Fin 21) : ℤ := (j.val:ℤ)-10
def coordinateRadius (j : Fin 21) : ℕ := (coordinate j).natAbs^2
def vector (d : ℕ) (x : Fin d → Fin 21) : Frequency d := fun i => coordinate (x i)
def radius (d : ℕ) (x : Fin d → Fin 21) : ℕ := ∑ i, coordinateRadius (x i)

def thetaPolynomial : Polynomial ℕ := ∑ j : Fin 21, Polynomial.X^(coordinateRadius j)

lemma vector_injective (d : ℕ) : Function.Injective (vector d) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change ((x i).val:ℤ)-10 = ((y i).val:ℤ)-10 at hi
  omega

lemma polynomial_power (d : ℕ) :
    thetaPolynomial^d = ∑ x : Fin d → Fin 21, Polynomial.X^(radius d x) := by
  rw [thetaPolynomial, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.prod_pow_eq_pow_sum _ _ _

lemma coefficient_count (d m : ℕ) :
    (thetaPolynomial^d).coeff m =
      (Finset.univ.filter (fun x : Fin d → Fin 21 => radius d x = m)).card := by
  rw [polynomial_power, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow, Finset.sum_boole, eq_comm, Nat.cast_id]

lemma coordinateRadius_le (j : Fin 21) : coordinateRadius j ≤ 100 := by
  fin_cases j <;> norm_num [coordinateRadius, coordinate]

lemma radius_le (d : ℕ) (x : Fin d → Fin 21) : radius d x ≤ 100*d := by
  calc
    _ ≤ ∑ _i : Fin d, 100 := Finset.sum_le_sum (fun i _ => coordinateRadius_le (x i))
    _ = _ := by simp [mul_comm]

lemma radius_eq_length_sq (d : ℕ) (x : Fin d → Fin 21) :
    (radius d x:ℝ) = ∑ i : Fin d, (vector d x i:ℝ)^2 := by
  simp only [radius, coordinateRadius, Nat.cast_sum, Nat.cast_pow, vector]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun z : ℤ => (z:ℝ)) (Int.natAbs_sq (coordinate (x i)))
  simpa using h

lemma length_eq_sqrt_radius (d : ℕ) (x : Fin d → Fin 21) :
    frequencyLength (vector d x) = Real.sqrt (radius d x) := by
  rw [frequencyLength, radius_eq_length_sq]

lemma radius_zero_iff (d : ℕ) (x : Fin d → Fin 21) : radius d x = 0 ↔ vector d x = 0 := by
  rw [radius, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_univ, forall_true_left, coordinateRadius, pow_eq_zero_iff (by decide : 2≠0),
    Int.natAbs_eq_zero]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

#print axioms coefficient_count
end DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell
