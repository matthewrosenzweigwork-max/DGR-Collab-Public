/- UNCHECKED outside frozen proof. The original weak spectral threshold
and squared summability construct a common exponent strictly above one.
The stronger doubled threshold is not assumed. -/
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic
noncomputable section
open Filter
open scoped Topology
namespace DGRHS.Gaussian
variable {ι : Type*}

lemma finite_small_spectral_increment (x : ι → ℝ) (hm : ∀ i, 0 < 1+x i)
    (s : Finset ι) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧ ∀ i ∈ s, ε*|x i| < (1+x i)/2 := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1/2, by norm_num, le_rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ε,hε,hhalf,hs⟩ := ih
    obtain ⟨c,hc,hca⟩ := exists_pos_mul_lt (show 0 < (1+x a)/2 by
      exact div_pos (hm a) (by norm_num)) |x a|
    refine ⟨min ε c, lt_min hε hc, (min_le_left _ _).trans hhalf, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (mul_le_mul_of_nonneg_right (min_le_right ε c) (abs_nonneg _)).trans_lt
        (by simpa only [mul_comm] using hca)
    · exact (mul_le_mul_of_nonneg_right (min_le_left ε c) (abs_nonneg _)).trans_lt (hs i hi)

/-- Finite exceptional coefficients are handled individually; cofinite small
coefficients share the elementary uniform tail bound. -/
theorem exists_spectral_power_above_one (β : ℝ) (a : ι → ℝ)
    (ha : Summable (fun i => (a i)^2)) (hm : ∀ i, 0 < 1+β*a i) :
    ∃ p : ℝ, 1 < p ∧ p ≤ 3/2 ∧ ∀ i, 0 < 1+p*β*a i := by
  classical
  let x := fun i => β*a i
  have hx : Summable (fun i => (x i)^2) := by
    simpa only [x, mul_pow] using Summable.mul_left (β^2) ha
  have ht : ∀ᶠ i in cofinite, (x i)^2 < (1/16 : ℝ) :=
    hx.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  let s := (Filter.eventually_cofinite.mp ht).toFinset
  obtain ⟨ε,hε,hhalf,hs⟩ := finite_small_spectral_increment x hm s
  refine ⟨1+ε, by linarith, by linarith, ?_⟩
  intro i
  rw [mul_assoc]
  change 0 < 1+(1+ε)*x i
  by_cases hi : i ∈ s
  · have h := hs i hi
    have hn := neg_abs_le (x i)
    have hp := hm i
    change 0 < 1+x i at hp
    nlinarith
  · have hsmall : (x i)^2 < (1/16 : ℝ) := by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hi
    have hlow : -(1/4 : ℝ) < x i := by nlinarith [sq_nonneg (x i + 1/4)]
    have hprod : 0 ≤ (1+ε)*(x i+1/4) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.finite_small_spectral_increment
#print axioms DGRHS.Gaussian.exists_spectral_power_above_one
