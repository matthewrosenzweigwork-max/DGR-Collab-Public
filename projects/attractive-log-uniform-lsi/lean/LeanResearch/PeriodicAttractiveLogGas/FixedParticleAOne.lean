import LeanResearch.PeriodicAttractiveLogGas.SmallCubeWeight
import LeanResearch.PeriodicAttractiveLogGas.PeriodicWeightRegularity

/-! The full fixed-particle A1 cube estimate. Small cubes use the proved
cluster argument; larger cubes use the exact periodic cube law. The finite
constant below is deliberately larger than the displayed source constant.
It depends only on N and the enclosing subcritical beta0, not on the cube
or on the individual exponent in the closed interval. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.FixedParticleAOne
open PhysicalCubes CubeProbability PeriodicCubeVolume PeriodicWeightRegularity

/-- A finite real majorant of the true normalizing integral. Its use below
is accompanied by the independently proved integrability of the weight. -/
def normalizationBound (N : ℕ) (β₀ : ℝ) : ℝ :=
  max 1 (∫ X, torusPairWeight N (FixedWeightConstants.exponent N β₀) X ∂referenceMeasure N)

def constant (N : ℕ) (β₀ : ℝ) : ℝ :=
  max (SmallCubeWeight.coefficient N β₀ ^ (N ^ 2))
    ((1 + 16 * (N : ℝ)) ^ (2 * N) * normalizationBound N β₀)

theorem normalizationBound_ge_one (N : ℕ) (β₀ : ℝ) : 1 ≤ normalizationBound N β₀ := le_max_left _ _

theorem constant_ge_one (N : ℕ) (β₀ : ℝ) : 1 ≤ constant N β₀ :=
  (one_le_pow₀ (SmallCubeWeight.coefficient_ge_one N β₀)).trans (le_max_left _ _)

theorem exponent_subcritical {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ} (hsub : β₀ < 4)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) : a * (N : ℝ) < 4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact ((le_div_iff₀ hn).mp haa).trans_lt hsub

theorem weight_integrable {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ} (hsub : β₀ < 4)
    (ha : 0 ≤ a) (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    Integrable (torusPairWeight N a) (referenceMeasure N) :=
  integrable_torusPairWeight N hN ha (exponent_subcritical hN hsub haa)

theorem normalization_bounds {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    1 ≤ (∫ X, torusPairWeight N a X ∂referenceMeasure N) ∧
      (∫ X, torusPairWeight N a X ∂referenceMeasure N) ≤ normalizationBound N β₀ := by
  have hi := weight_integrable hN hsub ha haa
  have ha₀ : 0 ≤ FixedWeightConstants.exponent N β₀ := div_nonneg hβ₀ (Nat.cast_nonneg N)
  have hi₀ := weight_integrable hN hsub ha₀ (le_refl _)
  constructor
  · simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using
      integral_mono_ae (integrable_const (1 : ℝ)) hi (ae_one_le_reference_weight N ha)
  · exact (integral_mono_ae hi hi₀ ((ae_reference_pair_positive N).mono
      (fun X hX => weight_exponent_mono haa X hX))).trans (le_max_right _ _)

theorem particleCube_mono {N : ℕ} (c : Fin N → PlanarSpace) {ℓ r : ℝ} (hℓr : ℓ ≤ r) :
    particleCube N c ℓ ⊆ particleCube N c r := by
  intro X hX i _
  apply (mem_cube (c i) (X i) r).mpr
  intro j
  have hh := (mem_cube (c i) (X i) ℓ).mp (hX i (mem_univ i)) j
  linarith

/-- Periodicity controls every cube above the fixed small-cube threshold.
The integral comparison is between genuinely integrable functions. -/
theorem large_cube_integral_bound {N : ℕ} (hN : 2 ≤ N) {β₀ a ℓ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (hℓ : 0 < ℓ)
    (hlarge : 1 / (16 * (N : ℝ)) ≤ ℓ) (c : Fin N → PlanarSpace) :
    (∫ X in particleCube N c ℓ, torusPairWeight N a (planarConfigurationQuotient N X)) ≤
      (1 + 16 * (N : ℝ)) ^ (2 * N) * normalizationBound N β₀ * ℓ ^ (2 * N) := by
  let n := ⌈ℓ⌉₊
  have hn : 0 < n := Nat.one_le_ceil_iff.mpr hℓ
  have hnl : ℓ ≤ (n : ℝ) := Nat.le_ceil ℓ
  have hnlt : (n : ℝ) < ℓ + 1 := Nat.ceil_lt_add_one hℓ.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbase : 1 ≤ 16 * (N : ℝ) * ℓ := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * N)).mp hlarge
    nlinarith only [hh]
  have hnupper : (n : ℝ) ≤ (1 + 16 * (N : ℝ)) * ℓ := by nlinarith
  have hip := (locallyIntegrable_torusPairWeight_lift N (by omega) ha
    (exponent_subcritical hN hsub haa)).integrableOn_isCompact
      (isCompact_particleCube N c (n : ℝ))
  have hmono := setIntegral_mono_set hip
    (Eventually.of_forall fun X => torusPairWeight_nonneg N a (planarConfigurationQuotient N X))
    (Eventually.of_forall fun X hX => particleCube_mono c hnl hX)
  rw [integral_cube_integer N hn c _ (measurable_torusPairWeight N a)] at hmono
  have hb := (normalization_bounds hN hβ₀ hsub ha haa).2
  have hp : (n : ℝ) ^ (2 * N) ≤ (1 + 16 * (N : ℝ)) ^ (2 * N) * ℓ ^ (2 * N) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) hnupper _
  calc
    _ ≤ (n : ℝ) ^ (2 * N) * ∫ X, torusPairWeight N a X ∂referenceMeasure N := hmono
    _ ≤ (n : ℝ) ^ (2 * N) * normalizationBound N β₀ :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ ((1 + 16 * (N : ℝ)) ^ (2 * N) * ℓ ^ (2 * N)) * normalizationBound N β₀ :=
      mul_le_mul_of_nonneg_right hp (zero_le_one.trans (normalizationBound_ge_one N β₀))
    _ = _ := by ring

/-- The full A1 inequality on every axis-parallel product cube, at every
point off the one fixed closed null collision set. -/
theorem cube_integral_le {N : ℕ} (hN : 2 ≤ N) {β₀ a ℓ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (hℓ : 0 < ℓ)
    (c Y : Fin N → PlanarSpace) (hY : Y ∈ particleCube N c ℓ)
    (hYcol : Y ∉ liftedCollisionSet N) :
    (∫ X in particleCube N c ℓ, torusPairWeight N a (planarConfigurationQuotient N X)) ≤
      constant N β₀ * ℓ ^ (2 * N) * torusPairWeight N a (planarConfigurationQuotient N Y) := by
  have hYpos := pair_positive_of_no_collision (X := planarConfigurationQuotient N Y) hYcol
  by_cases hsmall : ℓ ≤ 1 / (16 * (N : ℝ))
  · exact (SmallCubeWeight.original_small_cube_bound hN hβ₀ hsub ha haa hℓ hsmall c Y hY hYpos).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hℓ.le _))
        (torusPairWeight_nonneg _ _ _))
  · have hh := large_cube_integral_bound hN hβ₀ hsub ha haa hℓ (le_of_not_ge hsmall) c
    have hy := one_le_weight ha (planarConfigurationQuotient N Y) hYpos
    calc
      _ ≤ (1 + 16 * (N : ℝ)) ^ (2 * N) * normalizationBound N β₀ * ℓ ^ (2 * N) := hh
      _ ≤ constant N β₀ * ℓ ^ (2 * N) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hℓ.le _)
      _ ≤ _ := by
        have hC : 0 ≤ constant N β₀ * ℓ ^ (2 * N) :=
          mul_nonneg (zero_le_one.trans (constant_ge_one N β₀)) (pow_nonneg hℓ.le _)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hy hC

/-- The usual almost-everywhere cube formulation is a consequence of
actual global collision nullity, not an extra assumption. -/
theorem ae_cube_integral_le {N : ℕ} (hN : 2 ≤ N) {β₀ a ℓ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (hℓ : 0 < ℓ)
    (c : Fin N → PlanarSpace) :
    ∀ᵐ Y ∂volume.restrict (particleCube N c ℓ),
      (∫ X in particleCube N c ℓ, torusPairWeight N a (planarConfigurationQuotient N X)) ≤
        constant N β₀ * ℓ ^ (2 * N) * torusPairWeight N a (planarConfigurationQuotient N Y) := by
  filter_upwards [ae_restrict_of_ae (ae_no_lifted_collision N),
    ae_restrict_mem (particleCube_measurable N c ℓ)] with Y hYcol hY
  exact cube_integral_le hN hβ₀ hsub ha haa hℓ c Y hY hYcol

end PeriodicAttractiveLogGas.FixedParticleAOne
