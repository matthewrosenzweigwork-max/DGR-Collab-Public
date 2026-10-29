import LeanResearch.PeriodicAttractiveLogGas.CollisionWeights
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecificLimits.Basic

/-! Conditional dyadic-shell reduction for the actual collision integral.

Source: `lem:collision-integral`, "Scaling of the whole cluster", lines 187–200
of the immutable corrected manuscript. There are `n` free planar coordinates,
so the volume dimension is `2*n`, while the radial size is their Pi supremum
norm. Inverse dilation gives an identity of extended integrals without assuming
finiteness. A genuine dyadic cover, the null singleton at the origin, and the
geometric series then reduce ball finiteness to unit-shell finiteness.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

/-- A half-open shell for the maximum of the free-coordinate Euclidean norms. -/
def clusterShell (n : ℕ) (r : ℝ) : Set (Fin n → PlanarSpace) :=
  {w | r / 2 < ‖w‖ ∧ ‖w‖ ≤ r}

def clusterUnitShellIntegral (n : ℕ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in clusterShell n 1, ENNReal.ofReal (clusterWeight n a w)

theorem measurableSet_clusterShell (n : ℕ) (r : ℝ) : MeasurableSet (clusterShell n r) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

theorem finrank_clusterSpace (n : ℕ) :
    Module.finrank ℝ (Fin n → PlanarSpace) = 2 * n := by
  simp [Module.finrank_pi_fintype, PlanarSpace, Nat.mul_comm]

theorem clusterShell_preimage_inv_smul (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (fun w : Fin n → PlanarSpace ↦ r⁻¹ • w) ⁻¹' clusterShell n 1 = clusterShell n r := by
  ext w
  change (1 / 2 < ‖r⁻¹ • w‖ ∧ ‖r⁻¹ • w‖ ≤ 1) ↔
    (r / 2 < ‖w‖ ∧ ‖w‖ ≤ r)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
    mul_comm r⁻¹, ← div_eq_mul_inv, lt_div_iff₀ hr, div_le_iff₀ hr]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> nlinarith

/-- Exact extended-integral scaling on a shell. No shell or ball finiteness is
used, and no cancellation of potentially infinite integrals occurs. -/
theorem clusterShell_lintegral (n : ℕ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in clusterShell n r, ENNReal.ofReal (clusterWeight n a w)) =
      ENNReal.ofReal (r ^ clusterScalingExponent n a) * clusterUnitShellIntegral n a := by
  have hm : Measure.map (fun w : Fin n → PlanarSpace ↦ r⁻¹ • w) volume =
      ENNReal.ofReal (r ^ (2 * n)) • (volume : Measure (Fin n → PlanarSpace)) := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), finrank_clusterSpace,
      inv_pow, inv_inv, abs_of_pos (pow_pos hr _)]
  have hf : Measurable (fun w : Fin n → PlanarSpace ↦
      ENNReal.ofReal (clusterWeight n a (r • w))) :=
    ((measurable_clusterWeight n a).comp (measurable_const_smul r)).ennreal_ofReal
  have hchange := setLIntegral_map (μ := (volume : Measure (Fin n → PlanarSpace)))
    (measurableSet_clusterShell n 1) hf (measurable_const_smul r⁻¹)
  have hexp : ((2 * n : ℕ) : ℝ) + (-a * (n : ℝ) * ((n : ℝ) + 1) / 2) =
      clusterScalingExponent n a := by
    rw [clusterScalingExponent_eq_dimension_sub_degree]
    push_cast
    ring
  calc
    (∫⁻ w in clusterShell n r, ENNReal.ofReal (clusterWeight n a w)) =
        ∫⁻ w in clusterShell n 1, ENNReal.ofReal (clusterWeight n a (r • w))
          ∂Measure.map (fun w : Fin n → PlanarSpace ↦ r⁻¹ • w) volume := by
      simpa only [clusterShell_preimage_inv_smul n hr, smul_inv_smul₀ hr.ne']
        using hchange.symm
    _ = ENNReal.ofReal (r ^ (2 * n)) *
        ∫⁻ w in clusterShell n 1, ENNReal.ofReal (clusterWeight n a (r • w)) := by
      simp only [hm, setLIntegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal (r ^ (2 * n)) *
        (ENNReal.ofReal (r ^ (-a * (n : ℝ) * ((n : ℝ) + 1) / 2)) *
          clusterUnitShellIntegral n a) := by
      congr 1
      simp_rw [clusterWeight_smul n a hr,
        ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      exact lintegral_const_mul _ (measurable_clusterWeight n a).ennreal_ofReal
    _ = ENNReal.ofReal (r ^ clusterScalingExponent n a) * clusterUnitShellIntegral n a := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _),
        ← Real.rpow_natCast, ← Real.rpow_add hr, hexp]

/-- Every nonzero point of the product ball belongs to one of the actual
dyadic shells, including points on a shell's outer boundary. -/
theorem clusterBox_subset_zero_union_dyadicShells (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    clusterBox n ρ ⊆ ({0} : Set (Fin n → PlanarSpace)) ∪
      ⋃ m : ℕ, clusterShell n (ρ * (1 / 2 : ℝ) ^ m) := by
  intro w hw
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  · have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hnormρ : ‖w‖ ≤ ρ := by
      apply (pi_norm_le_iff_of_nonneg hρ.le).2
      intro i
      have hwi := hw i (mem_univ i)
      exact (by simpa only [mem_ball, dist_zero_right] using hwi : ‖w i‖ < ρ).le
    have hratio : ‖w‖ / ρ ≤ 1 := by
      exact (div_le_iff₀ hρ).2 (by simpa only [one_mul] using hnormρ)
    obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near_of_lt_one
      (div_pos hnorm hρ) hratio (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine Or.inr (mem_iUnion.mpr ⟨m, ?_⟩)
    change (ρ * (1 / 2 : ℝ) ^ m) / 2 < ‖w‖ ∧ ‖w‖ ≤ ρ * (1 / 2 : ℝ) ^ m
    have hlo := (lt_div_iff₀ hρ).mp hmlo
    rw [pow_succ] at hlo
    have hhi := (div_le_iff₀ hρ).mp hmhi
    constructor
    · nlinarith
    · simpa only [mul_comm] using hhi

/-- Exact summation of the extended nonnegative dyadic coefficients. -/
theorem ennreal_dyadic_scaling_sum {ρ γ : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (I : ℝ≥0∞) :
    (∑' m : ℕ, ENNReal.ofReal ((ρ * (1 / 2 : ℝ) ^ m) ^ γ) * I) =
      ENNReal.ofReal (ρ ^ γ / (1 - (1 / 2 : ℝ) ^ γ)) * I := by
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ γ := Real.rpow_nonneg (by norm_num) _
  have hq1 : (1 / 2 : ℝ) ^ γ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hpow (m : ℕ) : ((1 / 2 : ℝ) ^ m) ^ γ = ((1 / 2 : ℝ) ^ γ) ^ m := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_comm (m : ℝ) γ, Real.rpow_mul_natCast (by norm_num)]
  have hcoeff (m : ℕ) : ENNReal.ofReal ((ρ * (1 / 2 : ℝ) ^ m) ^ γ) =
      ENNReal.ofReal (ρ ^ γ) * ENNReal.ofReal ((1 / 2 : ℝ) ^ γ) ^ m := by
    rw [Real.mul_rpow hρ.le (pow_nonneg (by norm_num) _), hpow,
      ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _), ENNReal.ofReal_pow hq0]
  calc
    (∑' m : ℕ, ENNReal.ofReal ((ρ * (1 / 2 : ℝ) ^ m) ^ γ) * I) =
        ENNReal.ofReal (ρ ^ γ) * (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ γ))⁻¹ * I := by
      simp_rw [hcoeff]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (ρ ^ γ / (1 - (1 / 2 : ℝ) ^ γ)) * I := by
      rw [div_eq_mul_inv (ρ ^ γ) (1 - (1 / 2 : ℝ) ^ γ),
        ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _),
        ENNReal.ofReal_inv_of_pos (sub_pos.mpr hq1), ENNReal.ofReal_sub 1 hq0,
        ENNReal.ofReal_one]

/-- The complete quantitative shell reduction for the actual anchored product.
The right side is an extended integral; it is not assumed finite here. -/
theorem clusterIntegral_le_unitShell_bound {n : ℕ} (hn : 0 < n) {a ρ : ℝ}
    (ha : a * ((n : ℝ) + 1) < 4) (hρ : 0 < ρ) :
    clusterIntegral n ρ a ≤
      ENNReal.ofReal (ρ ^ clusterScalingExponent n a /
        (1 - (1 / 2 : ℝ) ^ clusterScalingExponent n a)) * clusterUnitShellIntegral n a := by
  let : NullSingletonClass (volume : Measure (Fin n → PlanarSpace)) :=
    Measure.pi_nullSingletonClass (μ := fun _ : Fin n => (volume : Measure PlanarSpace)) ⟨0, hn⟩
  have hγ : 0 < clusterScalingExponent n a := clusterScalingExponent_pos hn ha
  have hz : (∫⁻ w in ({0} : Set (Fin n → PlanarSpace)),
      ENNReal.ofReal (clusterWeight n a w)) = 0 := by
    have hz0 : (volume : Measure (Fin n → PlanarSpace)) {0} = 0 := measure_singleton 0
    rw [lintegral_singleton, hz0, mul_zero]
  calc
    clusterIntegral n ρ a ≤ ∫⁻ w in ({0} : Set (Fin n → PlanarSpace)) ∪
        ⋃ m : ℕ, clusterShell n (ρ * (1 / 2 : ℝ) ^ m),
        ENNReal.ofReal (clusterWeight n a w) :=
      lintegral_mono_set (clusterBox_subset_zero_union_dyadicShells n hρ)
    _ ≤ (∫⁻ w in ({0} : Set (Fin n → PlanarSpace)),
          ENNReal.ofReal (clusterWeight n a w)) +
        ∫⁻ w in ⋃ m : ℕ, clusterShell n (ρ * (1 / 2 : ℝ) ^ m),
          ENNReal.ofReal (clusterWeight n a w) := lintegral_union_le _ _ _
    _ = ∫⁻ w in ⋃ m : ℕ, clusterShell n (ρ * (1 / 2 : ℝ) ^ m),
        ENNReal.ofReal (clusterWeight n a w) := by rw [hz, zero_add]
    _ ≤ ∑' m : ℕ, ∫⁻ w in clusterShell n (ρ * (1 / 2 : ℝ) ^ m),
        ENNReal.ofReal (clusterWeight n a w) := lintegral_iUnion_le _ _
    _ = ∑' m : ℕ, ENNReal.ofReal ((ρ * (1 / 2 : ℝ) ^ m) ^
        clusterScalingExponent n a) * clusterUnitShellIntegral n a := by
      apply tsum_congr
      intro m
      exact clusterShell_lintegral n a (mul_pos hρ (pow_pos (by norm_num) m))
    _ = ENNReal.ofReal (ρ ^ clusterScalingExponent n a /
        (1 - (1 / 2 : ℝ) ^ clusterScalingExponent n a)) * clusterUnitShellIntegral n a :=
      ennreal_dyadic_scaling_sum hρ hγ _

/-- Unit-shell finiteness implies finiteness on every product ball at every
subcritical exponent. The separate subcluster argument must supply `hunit`. -/
theorem clusterIntegral_lt_top_of_unitShell {n : ℕ} (hn : 0 < n) {a : ℝ}
    (ha : a * ((n : ℝ) + 1) < 4) (hunit : clusterUnitShellIntegral n a < ∞)
    {ρ : ℝ} (hρ : 0 < ρ) : clusterIntegral n ρ a < ∞ :=
  (clusterIntegral_le_unitShell_bound hn ha hρ).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hunit)

end PeriodicAttractiveLogGas
