import LeanResearch.PeriodicAttractiveLogGas.ResolutionCutoffs
import LeanResearch.PeriodicAttractiveLogGas.CrudeEntropyIntegrated
import Mathlib.Analysis.SpecificLimits.Normed

/-! The coefficients and single particle threshold of manuscript Theorem 7.5.
The infinite series starts at refinement level one, exactly as in the source. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.ResolutionCoefficients
open ResolutionCutoffs CrudeEntropyIntegrated CrudeResidualIntegrated
  ConditionalLawEstimates HeavyCoercivityConstants OccupationMassCutoff MovingPoleCalculus

def kappa (J : ℕ) (β₀ t C₂ : ℝ) (m : ℕ) : ℝ :=
  2 * entropyBound β₀ / ((J : ℝ) ^ 2) ^ (m + 1) +
    (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) *
      coercivityConstant β₀ (t / 4) * (1 + ((m : ℝ) + 1) * Real.log J) /
        ((J : ℝ) ^ 2) ^ m

def entropyConstant (J : ℕ) (β₀ t C₂ : ℝ) : ℝ :=
  ∑' m : ℕ, (2 : ℝ) ^ (m + 1) * kappa J β₀ t C₂ (m + 1)

def threshold (J : ℕ) (β₀ t : ℝ) : ℕ :=
  max (halfMassThreshold β₀ (t / 4) (t / 2))
    (max (particleThreshold β₀ (t / 4))
      ⌈(J : ℝ) * Real.sqrt (angleConstant t * coercivityConstant β₀ (t / 4))⌉₊)

theorem crude_coefficient_nonneg {β₀ t C₂ : ℝ}
    (hβ₀ : 0 ≤ β₀) (ht : 0 ≤ t) (hC : 0 ≤ C₂) :
    0 ≤ 2 * conditionalConstant β₀ t C₂ + labelConstant β₀ := by
  have hnear := nearConstant_nonneg (radius β₀)
  have hself := selfScale_nonneg
  have hkernel := kernelConstant_pos.le
  have hgreen := greenLowerConstant_pos.le
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ 5 * Real.exp 1 by linarith)
  have hl10 := Real.log_nonneg (show (1 : ℝ) ≤ 10 by norm_num)
  unfold conditionalConstant labelConstant integratedConstant
  positivity

theorem kappa_nonneg {J : ℕ} (hJ : 0 < J) {β₀ t C₂ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t) (hC : 0 ≤ C₂) (m : ℕ) :
    0 ≤ kappa J β₀ t C₂ m := by
  have hL := ConditionalEntropyTightening.entropyBound_nonneg hβ₀
  have hD := crude_coefficient_nonneg hβ₀ ht.le hC
  have hDP := (coercivityConstant_pos hsub (by linarith : 0 < t / 4)).le
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ J by exact_mod_cast hJ)
  unfold kappa
  positivity

theorem mesh_square (J m : ℕ) : (mesh J m : ℝ) ^ 2 = ((J : ℝ) ^ 2) ^ (m + 1) := by
  simp only [mesh, Nat.cast_pow, ← pow_mul, Nat.mul_comm]

theorem log_mesh (J m : ℕ) : Real.log (mesh J m : ℝ) = ((m : ℝ) + 1) * Real.log J := by
  simp only [mesh, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]

/-- This is the source coefficient after the factor N in the defect cancels
against the preceding-resolution heavy estimate. -/
theorem kappa_succ_mesh (J : ℕ) (β₀ t C₂ : ℝ) (m : ℕ) :
    kappa J β₀ t C₂ (m + 1) =
      2 * entropyBound β₀ / (mesh J (m + 1) : ℝ) ^ 2 +
        (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) *
          coercivityConstant β₀ (t / 4) * (1 + Real.log (mesh J (m + 1) : ℝ)) /
            (mesh J m : ℝ) ^ 2 := by
  simp only [kappa, mesh_square, log_mesh, Nat.cast_add, Nat.cast_one]

theorem weighted_kappa_identity {J : ℕ} (hJ : 0 < J) (β₀ t C₂ : ℝ) (m : ℕ) :
    (2 : ℝ) ^ m * kappa J β₀ t C₂ m =
      (2 * entropyBound β₀ / (J : ℝ) ^ 2 +
        (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) *
          coercivityConstant β₀ (t / 4) * (1 + Real.log J)) *
            (2 / (J : ℝ) ^ 2) ^ m +
      ((2 * conditionalConstant β₀ t C₂ + labelConstant β₀) *
        coercivityConstant β₀ (t / 4) * Real.log J) *
          ((m : ℝ) * (2 / (J : ℝ) ^ 2) ^ m) := by
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  simp only [kappa, pow_succ, div_pow]
  field_simp [hj]
  ring

theorem weighted_kappa_summable {J : ℕ} (hJ : 3 ≤ J) (β₀ t C₂ : ℝ) :
    Summable (fun m : ℕ => (2 : ℝ) ^ (m + 1) * kappa J β₀ t C₂ (m + 1)) := by
  have hj : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have hr : ‖2 / (J : ℝ) ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (J : ℝ) ^ 2)]
    apply (div_lt_one (by positivity : (0 : ℝ) < (J : ℝ) ^ 2)).mpr
    nlinarith only [hj]
  have hg := summable_geometric_of_norm_lt_one hr
  have hn : Summable (fun m : ℕ => (m : ℝ) * (2 / (J : ℝ) ^ 2) ^ m) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs := (hg.mul_left (2 * entropyBound β₀ / (J : ℝ) ^ 2 +
    (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) *
      coercivityConstant β₀ (t / 4) * (1 + Real.log J))).add
    (hn.mul_left ((2 * conditionalConstant β₀ t C₂ + labelConstant β₀) *
      coercivityConstant β₀ (t / 4) * Real.log J))
  have hall : Summable (fun m : ℕ => (2 : ℝ) ^ m * kappa J β₀ t C₂ m) :=
    hs.congr fun m => (weighted_kappa_identity (by omega) β₀ t C₂ m).symm
  exact (summable_nat_add_iff 1).mpr hall

theorem entropyConstant_nonneg {J : ℕ} (hJ : 0 < J) {β₀ t C₂ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t) (hC : 0 ≤ C₂) :
    0 ≤ entropyConstant J β₀ t C₂ := by
  apply tsum_nonneg
  intro m
  exact mul_nonneg (by positivity) (kappa_nonneg hJ hβ₀ hsub ht hC (m + 1))

end PeriodicAttractiveLogGas.ResolutionCoefficients
