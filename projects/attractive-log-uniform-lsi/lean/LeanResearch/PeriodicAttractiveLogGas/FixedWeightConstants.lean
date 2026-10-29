import LeanResearch.PeriodicAttractiveLogGas.CollisionIntegral
import LeanResearch.PeriodicAttractiveLogGas.TorusCollisionIntegrability

/-! The exact fixed-particle constants of Appendix A. The cluster bound is
constructed from the proved collision integral at the largest exponent;
the maximum is finite and controls every smaller exponent and subcluster. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.FixedWeightConstants

def radius (N : ℕ) : ℝ := 4 * N

def exponent (N : ℕ) (β₀ : ℝ) : ℝ := β₀ / N

def clusterBound (N : ℕ) (β₀ : ℝ) (k : ℕ) : ℝ≥0 :=
  ⟨((ENNReal.ofReal ((max 1 (2 * radius N)) ^
      (exponent N β₀ * ((k - 1 : ℕ) : ℝ) * (((k - 1 : ℕ) : ℝ) + 1) / 2))) *
      clusterIntegral (k - 1) (radius N) (exponent N β₀)).toReal, ENNReal.toReal_nonneg⟩

def maximumClusterBound (N : ℕ) (β₀ : ℝ) : ℝ≥0 :=
  max 1 ((Finset.Icc 2 N).sup (clusterBound N β₀))

def partitionBound (N : ℕ) (β₀ : ℝ) : ℝ :=
  (2 * radius N ^ 2 * (16 * N + 1)) ^ (exponent N β₀ * N ^ 2 / 2) *
    (maximumClusterBound N β₀ : ℝ) ^ N

def aOneConstant (N : ℕ) (β₀ : ℝ) : ℝ :=
  (1 + 32 * (N : ℝ)) ^ (2 * N) *
    (12 * radius N ^ 2 * (16 * N + 1)) ^ (exponent N β₀ * N ^ 2 / 2) *
      (maximumClusterBound N β₀ : ℝ) ^ N

theorem subcluster_subcritical {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : k ≤ N)
    {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) :
    exponent N β₀ * (((k - 1 : ℕ) : ℝ) + 1) < 4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkn : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hk' : (((k - 1 : ℕ) : ℝ) + 1) = k := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hk']
  unfold exponent
  have hh := mul_le_mul_of_nonneg_left hkn (div_nonneg hβ₀ hn.le)
  rw [div_mul_cancel₀ β₀ hn.ne'] at hh
  exact hh.trans_lt hsub

theorem clusterBound_controls {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : k ≤ N)
    {β₀ a : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a) (haa : a ≤ exponent N β₀) :
    clusterIntegral (k - 1) (radius N) a ≤ ENNReal.ofReal (clusterBound N β₀ k : ℝ) := by
  have hr : 0 < radius N := by unfold radius; positivity
  have hexp : 0 ≤ exponent N β₀ := div_nonneg hβ₀ (Nat.cast_nonneg N)
  have hf : (ENNReal.ofReal ((max 1 (2 * radius N)) ^
      (exponent N β₀ * ((k - 1 : ℕ) : ℝ) * (((k - 1 : ℕ) : ℝ) + 1) / 2))) *
      clusterIntegral (k - 1) (radius N) (exponent N β₀) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (clusterIntegral_lt_top (k - 1) hexp (subcluster_subcritical hN hk hkN hβ₀ hsub) hr)
  change clusterIntegral (k - 1) (radius N) a ≤ ENNReal.ofReal
    ((ENNReal.ofReal ((max 1 (2 * radius N)) ^
      (exponent N β₀ * ((k - 1 : ℕ) : ℝ) * (((k - 1 : ℕ) : ℝ) + 1) / 2))) *
      clusterIntegral (k - 1) (radius N) (exponent N β₀)).toReal
  rw [ENNReal.ofReal_toReal hf.ne]
  exact clusterIntegral_exponent_comparison (k - 1) ha haa hr

theorem one_le_maximum (N : ℕ) (β₀ : ℝ) : 1 ≤ (maximumClusterBound N β₀ : ℝ) := by
  exact_mod_cast (le_max_left (1 : ℝ≥0) ((Finset.Icc 2 N).sup (clusterBound N β₀)))

theorem cluster_le_maximum {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) (β₀ : ℝ) :
    (clusterBound N β₀ k : ℝ) ≤ maximumClusterBound N β₀ := by
  exact_mod_cast ((Finset.le_sup (f := clusterBound N β₀) (Finset.mem_Icc.mpr ⟨hk, hkN⟩)).trans
    (le_max_right (1 : ℝ≥0) ((Finset.Icc 2 N).sup (clusterBound N β₀))))

/-- One source maximum controls all genuine subclusters, uniformly over
the closed exponent interval; no cluster integral is an additional input. -/
theorem clusterIntegral_le_maximum {N k : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hkN : k ≤ N)
    {β₀ a : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a) (haa : a ≤ exponent N β₀) :
    clusterIntegral (k - 1) (radius N) a ≤ ENNReal.ofReal (maximumClusterBound N β₀ : ℝ) :=
  (clusterBound_controls hN hk hkN hβ₀ hsub ha haa).trans
    (ENNReal.ofReal_le_ofReal (cluster_le_maximum hk hkN β₀))

theorem one_le_partitionBound {N : ℕ} (hN : 2 ≤ N) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    1 ≤ partitionBound N β₀ := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 1 ≤ 2 * radius N ^ 2 * (16 * N + 1) := by
    unfold radius
    nlinarith
  have he : 0 ≤ exponent N β₀ * N ^ 2 / 2 := by unfold exponent; positivity
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hr he)
    (one_le_pow₀ (one_le_maximum N β₀))

theorem one_le_aOneConstant {N : ℕ} (hN : 2 ≤ N) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    1 ≤ aOneConstant N β₀ := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 1 ≤ 12 * radius N ^ 2 * (16 * N + 1) := by
    unfold radius
    nlinarith
  have he : 0 ≤ exponent N β₀ * N ^ 2 / 2 := by unfold exponent; positivity
  have hb : (1 : ℝ) ≤ 1 + 32 * (N : ℝ) := by nlinarith only [hn]
  have hp : (1 : ℝ) ≤ (1 + 32 * (N : ℝ)) ^ (2 * N) := one_le_pow₀ hb
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hp (Real.one_le_rpow hr he))
    (one_le_pow₀ (one_le_maximum N β₀))

end PeriodicAttractiveLogGas.FixedWeightConstants
