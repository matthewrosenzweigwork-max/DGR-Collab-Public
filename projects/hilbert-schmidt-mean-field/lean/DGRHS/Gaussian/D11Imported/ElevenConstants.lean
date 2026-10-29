/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ElevenDefinitions
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Exact constants and elementary numerical consequences from Section 4.
These do not assume or claim the still separate analytic competitor proof. -/
noncomputable section
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

theorem spectralThreshold_eleven :
    spectralThreshold 11 = 64 * Real.pi^5 / 945 := by
  have hg : Real.Gamma ((11 : ℝ) / 2) = 945 * Real.sqrt Real.pi / 32 := by
    convert Real.Gamma_nat_add_half 5 using 1 <;> norm_num
  have hp : Real.pi^((11 : ℝ)/2) = Real.pi^(5 : ℕ) * Real.sqrt Real.pi := by
    rw [show (11 : ℝ)/2 = (5 : ℕ)+(1/2 : ℝ) by norm_num,
      Real.rpow_add Real.pi_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold spectralThreshold
  norm_num only [Nat.cast_ofNat]
  rw [hg, hp]
  field_simp
  <;> ring

theorem pi_fine_bounds : (103993 : ℝ)/33102 < Real.pi ∧ Real.pi < 104348/33215 := by
  constructor
  · linarith [Real.pi_gt_d20]
  · linarith [Real.pi_lt_d20]

theorem spectralThreshold_bounds :
    (2063 : ℝ)/100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 := by
  rw [spectralThreshold_eleven]
  have hl : ((31415 : ℝ)/10000)^5 < Real.pi^5 := by
    gcongr
    linarith [Real.pi_gt_d4]
  have hu : Real.pi^5 < ((31416 : ℝ)/10000)^5 := by
    gcongr
    linarith [Real.pi_lt_d4]
  norm_num at hl hu
  constructor <;> nlinarith

theorem label_entropy_rational :
    (11 : ℝ) * ((63/5) * (83927/8121093750) + 2^19/(2^36-1)) < 1/600 := by
  norm_num

theorem competitor_gap_rational :
    (14475384292906 : ℝ)/10^12 - 8653/600 > 1/30 := by
  norm_num

theorem transition_quotient_rational :
    ((64 : ℝ)/945) * (104348/33215)^5 *
      (7305164/10^6 + 17897/2520 + 1/600) / (14475384292906/10^12) < 2063/100 := by
  norm_num

theorem fourierPolynomial_pos {z : ℝ} (hz : 0 ≤ z) : 0 < fourierPolynomial z := by
  unfold fourierPolynomial
  positivity

theorem fourierProfile_pos {z : ℝ} (hz : 0 ≤ z) : 0 < fourierProfile z := by
  unfold fourierProfile
  exact div_pos (mul_pos (Real.exp_pos _) (fourierPolynomial_pos hz)) (by norm_num)

theorem entropy_exp_polynomial :
    (1494 : ℝ) < ∑ j ∈ Finset.range 15, ((92207 : ℝ)/12600)^j / j.factorial := by
  norm_num [Finset.sum_range_succ]

theorem entropy_log_argument :
    (3 : ℝ)*5^12/(2^9*Real.pi^6) < 1493 := by
  have hp : ((157 : ℝ)/50)^6 < Real.pi^6 := by
    gcongr
    linarith [Real.pi_gt_d2]
  apply (div_lt_iff₀ (by positivity)).mpr
  norm_num at hp
  nlinarith

/-- This certifies the exact expression in the Euclidean entropy identity.
Identifying that expression with an actual integral is a separate theorem. -/
theorem euclidean_entropy_expression_lt :
    Real.log ((3 : ℝ)*5^12/(2^9*Real.pi^6)) + 17897/2520 < 721/50 := by
  have he : (1494 : ℝ) < Real.exp ((92207 : ℝ)/12600) :=
    entropy_exp_polynomial.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 15)
  have hl : Real.log ((3 : ℝ)*5^12/(2^9*Real.pi^6)) < 92207/12600 := by
    apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
    linarith [entropy_log_argument]
  linarith

theorem euclidean_entropy_expression_fine :
    Real.log ((3 : ℝ)*5^12/(2^9*Real.pi^6)) < 7305164/10^6 := by
  have hp : ((103993 : ℝ)/33102)^6 < Real.pi^6 := by
    gcongr
    exact pi_fine_bounds.1
  have ha : (3 : ℝ)*5^12/(2^9*Real.pi^6) <
      (3 : ℝ)*5^12/2^9*(33102/103993)^6 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    norm_num at hp ⊢
    nlinarith
  have he : (3 : ℝ)*5^12/2^9*(33102/103993)^6 <
      ∑ j ∈ Finset.range 25, ((7305164 : ℝ)/10^6)^j / j.factorial := by
    norm_num [Finset.sum_range_succ]
  apply (Real.log_lt_iff_lt_exp (by positivity)).mpr
  exact ha.trans (he.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 25))

#print axioms spectralThreshold_bounds
#print axioms label_entropy_rational
#print axioms transition_quotient_rational
#print axioms euclidean_entropy_expression_fine
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
