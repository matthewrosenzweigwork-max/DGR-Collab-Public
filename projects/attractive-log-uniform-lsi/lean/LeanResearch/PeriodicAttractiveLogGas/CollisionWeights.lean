import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! The actual planar collision product and its exact homogeneity.
`clusterIntegral n` denotes the source's H_(n+1): n free planar coordinates
and one fixed anchor at zero. The integral is extended; no finiteness is
assumed or asserted by these algebraic and measurable preliminaries. -/

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

def planarOrderedPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun ij ↦ ij.1 < ij.2)

@[simp] theorem mem_planarOrderedPairs {k : ℕ} (ij : Fin k × Fin k) :
    ij ∈ planarOrderedPairs k ↔ ij.1 < ij.2 := by
  simp [planarOrderedPairs]

theorem card_planarOrderedPairs (k : ℕ) :
    (planarOrderedPairs k).card = k.choose 2 := by
  simpa only [planarOrderedPairs, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin k))))

def planarPairWeight (k : ℕ) (a : ℝ) (w : Fin k → PlanarSpace) : ℝ :=
  ∏ ij ∈ planarOrderedPairs k, ‖w ij.1 - w ij.2‖ ^ (-a)

theorem planarPairWeight_nonneg (k : ℕ) (a : ℝ) (w : Fin k → PlanarSpace) :
    0 ≤ planarPairWeight k a w :=
  Finset.prod_nonneg (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)

theorem measurable_planarPairWeight (k : ℕ) (a : ℝ) :
    Measurable (planarPairWeight k a) := by
  unfold planarPairWeight
  fun_prop

theorem planarPairWeight_zero (k : ℕ) (w : Fin k → PlanarSpace) :
    planarPairWeight k 0 w = 1 := by simp [planarPairWeight]

theorem planarPairWeight_smul (k : ℕ) (a : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Fin k → PlanarSpace) :
    planarPairWeight k a (r • w) =
      r ^ (-a * (k : ℝ) * ((k : ℝ) - 1) / 2) * planarPairWeight k a w := by
  have hpair (ij : Fin k × Fin k) :
      ‖(r • w) ij.1 - (r • w) ij.2‖ ^ (-a) =
        r ^ (-a) * ‖w ij.1 - w ij.2‖ ^ (-a) := by
    simp only [Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact Real.mul_rpow hr.le (norm_nonneg _)
  unfold planarPairWeight
  simp_rw [hpair]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_planarOrderedPairs,
    ← Real.rpow_mul_natCast hr.le, Nat.cast_choose_two]
  congr 2
  ring

theorem rpow_neg_exponent_comparison {a a₀ t M : ℝ}
    (ha : 0 ≤ a) (haa : a ≤ a₀) (ht : 0 < t) (htM : t ≤ M) (hM : 1 ≤ M) :
    t ^ (-a) ≤ M ^ a₀ * t ^ (-a₀) := by
  have he : 0 ≤ a₀ - a := sub_nonneg.mpr haa
  have hc : t ^ (a₀ - a) ≤ M ^ a₀ :=
    (Real.rpow_le_rpow ht.le htM he).trans
      (Real.rpow_le_rpow_of_exponent_le hM (by linarith))
  calc
    t ^ (-a) = t ^ (a₀ - a) * t ^ (-a₀) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    _ ≤ M ^ a₀ * t ^ (-a₀) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ht.le _)

/-- Exact exponent comparison away from all pair collisions. The excluded
diagonals must be proved null before this is used under an integral. -/
theorem planarPairWeight_exponent_comparison (k : ℕ) {a a₀ M : ℝ}
    (ha : 0 ≤ a) (haa : a ≤ a₀) (hM : 1 ≤ M) (w : Fin k → PlanarSpace)
    (hpos : ∀ ij ∈ planarOrderedPairs k, 0 < ‖w ij.1 - w ij.2‖)
    (hbound : ∀ ij ∈ planarOrderedPairs k, ‖w ij.1 - w ij.2‖ ≤ M) :
    planarPairWeight k a w ≤
      M ^ (a₀ * (k : ℝ) * ((k : ℝ) - 1) / 2) * planarPairWeight k a₀ w := by
  calc
    planarPairWeight k a w ≤ ∏ ij ∈ planarOrderedPairs k,
        M ^ a₀ * ‖w ij.1 - w ij.2‖ ^ (-a₀) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
        (fun ij hij ↦ rpow_neg_exponent_comparison ha haa (hpos ij hij) (hbound ij hij) hM)
    _ = M ^ (a₀ * (k : ℝ) * ((k : ℝ) - 1) / 2) * planarPairWeight k a₀ w := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, card_planarOrderedPairs,
        ← Real.rpow_mul_natCast (by linarith : 0 ≤ M), Nat.cast_choose_two]
      congr 2
      ring

def anchoredCluster (n : ℕ) (w : Fin n → PlanarSpace) : Fin (n + 1) → PlanarSpace :=
  Fin.cases 0 w

@[simp] theorem anchoredCluster_zero (n : ℕ) (w : Fin n → PlanarSpace) :
    anchoredCluster n w 0 = 0 := rfl

@[simp] theorem anchoredCluster_succ (n : ℕ) (w : Fin n → PlanarSpace) (i : Fin n) :
    anchoredCluster n w i.succ = w i := rfl

theorem measurable_anchoredCluster (n : ℕ) : Measurable (anchoredCluster n) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact measurable_const
  · exact measurable_pi_apply j

theorem anchoredCluster_smul (n : ℕ) (r : ℝ) (w : Fin n → PlanarSpace) :
    anchoredCluster n (r • w) = r • anchoredCluster n w := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [anchoredCluster_zero, Pi.smul_apply, smul_zero]
  · rfl

def clusterWeight (n : ℕ) (a : ℝ) (w : Fin n → PlanarSpace) : ℝ :=
  planarPairWeight (n + 1) a (anchoredCluster n w)

theorem measurable_clusterWeight (n : ℕ) (a : ℝ) : Measurable (clusterWeight n a) :=
  (measurable_planarPairWeight (n + 1) a).comp (measurable_anchoredCluster n)

theorem clusterWeight_smul (n : ℕ) (a : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Fin n → PlanarSpace) :
    clusterWeight n a (r • w) =
      r ^ (-a * (n : ℝ) * ((n : ℝ) + 1) / 2) * clusterWeight n a w := by
  unfold clusterWeight
  rw [anchoredCluster_smul, planarPairWeight_smul _ _ hr]
  congr 2
  push_cast
  ring

def clusterBox (n : ℕ) (ρ : ℝ) : Set (Fin n → PlanarSpace) :=
  Set.pi Set.univ (fun _ ↦ ball (0 : PlanarSpace) ρ)

def clusterIntegral (n : ℕ) (ρ a : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in clusterBox n ρ, ENNReal.ofReal (clusterWeight n a w)

def clusterScalingExponent (n : ℕ) (a : ℝ) : ℝ :=
  (n : ℝ) * (2 - a * ((n : ℝ) + 1) / 2)

@[simp] theorem clusterWeight_no_free_particles (a : ℝ) (w : Fin 0 → PlanarSpace) :
    clusterWeight 0 a w = 1 := by
  have hp : planarOrderedPairs 1 = ∅ := by decide
  simp [clusterWeight, planarPairWeight, hp]

@[simp] theorem clusterWeight_one_free_particle (a : ℝ) (w : Fin 1 → PlanarSpace) :
    clusterWeight 1 a w = ‖w 0‖ ^ (-a) := by
  have hp : planarOrderedPairs 2 = {((0 : Fin 2), (1 : Fin 2))} := by decide
  simp [clusterWeight, planarPairWeight, hp, anchoredCluster]
  rfl

@[simp] theorem clusterIntegral_no_free_particles (ρ a : ℝ) : clusterIntegral 0 ρ a = 1 := by
  have hbox : clusterBox 0 ρ = Set.univ := by
    ext w
    simp [clusterBox, Set.mem_pi]
  simp only [clusterIntegral, hbox, Measure.restrict_univ, clusterWeight_no_free_particles,
    ENNReal.ofReal_one, lintegral_one]
  change (Measure.pi (fun _ : Fin 0 ↦ (volume : Measure PlanarSpace))) Set.univ = 1
  simp

theorem clusterScalingExponent_pos {n : ℕ} (hn : 0 < n) {a : ℝ}
    (ha : a * ((n : ℝ) + 1) < 4) : 0 < clusterScalingExponent n a := by
  unfold clusterScalingExponent
  apply mul_pos (Nat.cast_pos.mpr hn)
  linarith

theorem clusterScalingExponent_eq_dimension_sub_degree (n : ℕ) (a : ℝ) :
    clusterScalingExponent n a = 2 * (n : ℝ) - a * (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  unfold clusterScalingExponent
  ring

end PeriodicAttractiveLogGas
