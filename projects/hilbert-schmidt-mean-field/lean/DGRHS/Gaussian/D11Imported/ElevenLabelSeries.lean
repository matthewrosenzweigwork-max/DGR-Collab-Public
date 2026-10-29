import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! The zeta(11) integral comparison and odd-integer tail used in the
first absolute moment of the lattice label. All sums here are infinite sums. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma inverse_eleven_rpow (x : ℝ) : x^(-(11:ℝ)) = (x^(11:ℕ))⁻¹ := by
  rw [show -(11:ℝ) = ((-11:ℤ):ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_ofNat]

lemma eleven_inverse_summable : Summable (fun n : ℕ => ((n:ℝ)^11)⁻¹) :=
  Real.summable_nat_pow_inv.mpr (by norm_num)

lemma eleven_zeta_bound : (∑' n : ℕ, ((n:ℝ)^11)⁻¹) < (1025/1024:ℝ) := by
  have ha : AntitoneOn (fun x : ℝ => (x^11)⁻¹) (Ici (2:ℝ)) := by
    intro x hx y hy hxy
    change 2 ≤ x at hx
    change 2 ≤ y at hy
    have hx0 : 0 < x := by linarith
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by linarith [hx]) hxy 11
  have hi : IntegrableOn (fun x : ℝ => (x^11)⁻¹) (Ioi (2:ℝ)) := by
    simpa only [inverse_eleven_rpow] using
      integrableOn_Ioi_rpow_of_lt (by norm_num : -(11:ℝ)< -1) (by norm_num : (0:ℝ)<2)
  have htail := ha.tsum_comp_add_le_integral 2 hi (fun t ht => by
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    positivity)
  have hint : (∫ t : ℝ in Ioi (2:ℝ), (t^11)⁻¹) = (1/10240:ℝ) := by
    simp_rw [← inverse_eleven_rpow]
    rw [integral_Ioi_rpow_of_lt (by norm_num : -(11:ℝ)< -1) (by norm_num : (0:ℝ)<2)]
    norm_num [Real.rpow_neg, Real.rpow_ofNat]
  norm_num only [Nat.cast_ofNat] at htail
  rw [hint] at htail
  have hsplit := eleven_inverse_summable.sum_add_tsum_nat_add 3
  norm_num [Finset.sum_range_succ] at hsplit
  have ht : (∑' n : ℕ, (((n+3:ℕ):ℝ)^11)⁻¹) ≤ (1/10240:ℝ) := by
    simpa only [Nat.add_assoc] using htail
  push_cast at ht
  linarith

lemma eleven_odd_series :
    (∑' n : ℕ, (((2*n+1:ℕ):ℝ)^11)⁻¹) =
      (1-(2:ℝ)^(-11:ℤ)) * (∑' n : ℕ, ((n:ℝ)^11)⁻¹) := by
  have he := eleven_inverse_summable.comp_injective (show Function.Injective (fun n : ℕ => 2*n) by intro a b h; dsimp only at h; omega)
  have ho := eleven_inverse_summable.comp_injective (show Function.Injective (fun n : ℕ => 2*n+1) by intro a b h; dsimp only at h; omega)
  have hs := tsum_even_add_odd (f := fun n : ℕ => ((n:ℝ)^11)⁻¹) he ho
  have hev : (∑' n : ℕ, (((2*n:ℕ):ℝ)^11)⁻¹) =
      (2:ℝ)^(-11:ℤ) * (∑' n : ℕ, ((n:ℝ)^11)⁻¹) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, mul_inv, zpow_neg, zpow_ofNat]
    rw [tsum_mul_left]
  rw [hev] at hs
  linarith

lemma eleven_shifted_series :
    (∑' n : ℕ, (((n:ℝ)+1/2)^11)⁻¹) =
      (2047:ℝ) * (∑' n : ℕ, ((n:ℝ)^11)⁻¹) := by
  have he (n : ℕ) : (((n:ℝ)+1/2)^11)⁻¹ =
      (2048:ℝ) * (((2*n+1:ℕ):ℝ)^11)⁻¹ := by
    have heq : (n:ℝ)+1/2 = (((2*n+1:ℕ):ℝ))/2 := by push_cast; ring
    rw [heq, div_pow, inv_div]
    norm_num
    ring
  simp_rw [he]
  rw [tsum_mul_left, eleven_odd_series]
  norm_num
  ring

lemma eleven_shifted_series_bound :
    (∑' n : ℕ, (((n:ℝ)+1/2)^11)⁻¹) < (2047*1025/1024:ℝ) := by
  rw [eleven_shifted_series]
  linarith [eleven_zeta_bound]

#print axioms eleven_shifted_series_bound
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
