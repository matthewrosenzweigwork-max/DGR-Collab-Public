import LeanResearch.PeriodicAttractiveLogGas.ClusterPartitionIntegral
import LeanResearch.PeriodicAttractiveLogGas.ClusterBoundary

/-! The complete strong-induction proof of the source collision integral.
The finite sum covers every proper partition containing the fixed anchor.
Its actual product integrals were identified in `ClusterPartitionIntegral`;
the shell enlargement uses the proved null outer boundary. -/

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

def properClusterPartitions (n : ℕ) : Finset (Finset (Fin (n + 1))) :=
  Finset.univ.filter (fun S ↦ 0 ∈ S ∧ S ⊂ Finset.univ)

@[simp] theorem mem_properClusterPartitions {n : ℕ} (S : Finset (Fin (n + 1))) :
    S ∈ properClusterPartitions n ↔ 0 ∈ S ∧ S ⊂ Finset.univ := by
  simp [properClusterPartitions]

def clusterPartitionCoefficient (n : ℕ) (a : ℝ) (S : Finset (Fin (n + 1))) : ℝ :=
  ((1 : ℝ) / (2 * (n : ℝ))) ^ (-a * (S.card : ℝ) * (Sᶜ.card : ℝ))

theorem clusterPartitionCoefficient_nonneg (n : ℕ) (a : ℝ)
    (S : Finset (Fin (n + 1))) : 0 ≤ clusterPartitionCoefficient n a S := by
  exact Real.rpow_nonneg (by positivity) _

def clusterPartitionMajorant (n : ℕ) (a : ℝ) (S : Finset (Fin (n + 1)))
    (w : Fin n → PlanarSpace) : ℝ≥0∞ :=
  ENNReal.ofReal (clusterPartitionCoefficient n a S) *
    ENNReal.ofReal (planarRestrictedPairWeight (n + 1) a S (anchoredCluster n w) *
      planarRestrictedPairWeight (n + 1) a Sᶜ (anchoredCluster n w))

theorem measurable_clusterPartitionMajorant (n : ℕ) (a : ℝ)
    (S : Finset (Fin (n + 1))) : Measurable (clusterPartitionMajorant n a S) := by
  unfold clusterPartitionMajorant
  exact measurable_const.mul
    ((((measurable_planarRestrictedPairWeight (n + 1) a S).comp
      (measurable_anchoredCluster n)).mul
      ((measurable_planarRestrictedPairWeight (n + 1) a Sᶜ).comp
        (measurable_anchoredCluster n))).ennreal_ofReal)

theorem clusterWeight_le_partition_sum {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a)
    (w : Fin n → PlanarSpace) (hw : w ∈ clusterShell n 1) :
    ENNReal.ofReal (clusterWeight n a w) ≤
      ∑ S ∈ properClusterPartitions n, clusterPartitionMajorant n a S w := by
  classical
  have hfar : ∃ j : Fin (n + 1), (1 / 2 : ℝ) ≤ ‖anchoredCluster n w j‖ := by
    by_contra! h
    have hbound : ‖w‖ ≤ (1 / 2 : ℝ) :=
      (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
        (fun i ↦ (by simpa only [anchoredCluster_succ] using (h i.succ).le))
    exact (not_le_of_gt hw.1) hbound
  obtain ⟨S, h0, _, hproper, _, _, hbound⟩ :=
    exists_unitShell_clusterFactorization (by omega : 2 ≤ n + 1) ha
      (anchoredCluster n w) (anchoredCluster_zero n w) hfar
  have hcoeff : ((1 : ℝ) / (2 * (((n + 1 : ℕ) : ℝ) - 1))) ^
      (-a * (S.card : ℝ) * (Sᶜ.card : ℝ)) = clusterPartitionCoefficient n a S := by
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, clusterPartitionCoefficient]
  have hbound' : clusterWeight n a w ≤ clusterPartitionCoefficient n a S *
      (planarRestrictedPairWeight (n + 1) a S (anchoredCluster n w) *
        planarRestrictedPairWeight (n + 1) a Sᶜ (anchoredCluster n w)) := by
    rw [hcoeff] at hbound
    simpa only [clusterWeight, mul_assoc] using hbound
  have hle : ENNReal.ofReal (clusterWeight n a w) ≤ clusterPartitionMajorant n a S w := by
    simpa only [clusterPartitionMajorant,
      ENNReal.ofReal_mul (clusterPartitionCoefficient_nonneg n a S)] using
      ENNReal.ofReal_le_ofReal hbound'
  exact hle.trans (Finset.single_le_sum (f := fun S ↦ clusterPartitionMajorant n a S w)
    (fun _ _ ↦ zero_le)
    (mem_properClusterPartitions S |>.mpr ⟨h0, hproper⟩))

theorem clusterUnitShellIntegral_le_partition_sum {n : ℕ} (hn : 0 < n) {a : ℝ}
    (ha : 0 ≤ a) :
    clusterUnitShellIntegral n a ≤
      ∑ S ∈ properClusterPartitions n,
        ENNReal.ofReal (clusterPartitionCoefficient n a S) * clusterPartitionIntegral n 1 a S := by
  calc
    clusterUnitShellIntegral n a ≤ ∫⁻ w in clusterShell n 1,
        ∑ S ∈ properClusterPartitions n, clusterPartitionMajorant n a S w :=
      setLIntegral_mono' (measurableSet_clusterShell n 1) (clusterWeight_le_partition_sum hn ha)
    _ ≤ ∫⁻ w in clusterBox n 1,
        ∑ S ∈ properClusterPartitions n, clusterPartitionMajorant n a S w :=
      lintegral_mono_set' (clusterShell_ae_subset_clusterBox n 1)
    _ = ∑ S ∈ properClusterPartitions n,
        ENNReal.ofReal (clusterPartitionCoefficient n a S) * clusterPartitionIntegral n 1 a S := by
      rw [lintegral_finsetSum _ (fun S _ ↦ measurable_clusterPartitionMajorant n a S)]
      apply Finset.sum_congr rfl
      intro S _
      exact lintegral_const_mul _
        ((((measurable_planarRestrictedPairWeight (n + 1) a S).comp
          (measurable_anchoredCluster n)).mul
          ((measurable_planarRestrictedPairWeight (n + 1) a Sᶜ).comp
            (measurable_anchoredCluster n))).ennreal_ofReal)

theorem clusterUnitShellIntegral_lt_top_of_smaller {n : ℕ} (hn : 0 < n) {a : ℝ}
    (ha : 0 ≤ a)
    (hsmaller : ∀ m < n, ∀ ρ : ℝ, 0 < ρ → clusterIntegral m ρ a < ∞) :
    clusterUnitShellIntegral n a < ∞ := by
  apply (clusterUnitShellIntegral_le_partition_sum hn ha).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro S hS
  have hs := (mem_properClusterPartitions S).mp hS
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (clusterPartitionIntegral_lt_top_of_smaller n a S hs.1 hs.2 hsmaller)

/-- Source Lemma 2.3, with `n` free coordinates and `n+1` total particles.
The induction runs over all positive radii and all subcritical exponents. -/
theorem clusterIntegral_lt_top (n : ℕ) {a ρ : ℝ} (ha : 0 ≤ a)
    (hsubcritical : a * ((n : ℝ) + 1) < 4) (hρ : 0 < ρ) :
    clusterIntegral n ρ a < ∞ := by
  induction n using Nat.strong_induction_on generalizing a ρ with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [clusterIntegral_no_free_particles, ENNReal.one_lt_top]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      apply clusterIntegral_lt_top_of_unitShell hnpos hsubcritical ?_ hρ
      apply clusterUnitShellIntegral_lt_top_of_smaller hnpos ha
      intro m hm r hr
      have hmn : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        exact_mod_cast (show m + 1 ≤ n + 1 by omega)
      have ham : a * ((m : ℝ) + 1) < 4 :=
        (mul_le_mul_of_nonneg_left hmn ha).trans_lt hsubcritical
      exact ih m hm ha ham hr

theorem integrableOn_clusterWeight (n : ℕ) {a ρ : ℝ} (ha : 0 ≤ a)
    (hsubcritical : a * ((n : ℝ) + 1) < 4) (hρ : 0 < ρ) :
    IntegrableOn (clusterWeight n a) (clusterBox n ρ) volume := by
  refine ⟨(measurable_clusterWeight n a).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun w ↦ planarPairWeight_nonneg (n + 1) a (anchoredCluster n w)))).mpr
  exact clusterIntegral_lt_top n ha hsubcritical hρ

theorem clusterIntegral_eq_ofReal_integral (n : ℕ) {a ρ : ℝ} (ha : 0 ≤ a)
    (hsubcritical : a * ((n : ℝ) + 1) < 4) (hρ : 0 < ρ) :
    clusterIntegral n ρ a = ENNReal.ofReal (∫ w in clusterBox n ρ, clusterWeight n a w) := by
  have hn : 0 ≤ᵐ[volume.restrict (clusterBox n ρ)] clusterWeight n a :=
    Filter.Eventually.of_forall
      (fun w ↦ planarPairWeight_nonneg (n + 1) a (anchoredCluster n w))
  rw [integral_eq_lintegral_of_nonneg_ae hn
    (measurable_clusterWeight n a).aestronglyMeasurable]
  exact (ENNReal.ofReal_toReal (clusterIntegral_lt_top n ha hsubcritical hρ).ne).symm

/-- The finite comparison constant is chosen before every exponent in the
closed interval, including zero. No positivity of the exponent is required. -/
theorem clusterIntegral_uniform_bound (n : ℕ) {a₀ ρ : ℝ} (ha₀ : 0 ≤ a₀)
    (hsubcritical : a₀ * ((n : ℝ) + 1) < 4) (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, 0 ≤ a → a ≤ a₀ →
      clusterIntegral n ρ a ≤ ENNReal.ofReal K := by
  let B : ℝ≥0∞ := ENNReal.ofReal ((max 1 (2 * ρ)) ^
    (a₀ * (n : ℝ) * ((n : ℝ) + 1) / 2)) * clusterIntegral n ρ a₀
  have hB : B < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (clusterIntegral_lt_top n ha₀ hsubcritical hρ)
  refine ⟨B.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a ha haa
  rw [ENNReal.ofReal_toReal hB.ne]
  exact clusterIntegral_exponent_comparison n ha haa hρ

/-- All assertions of source Lemma 2.3, in the exact free-coordinate convention. -/
theorem collisionIntegralLemma (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ a : ℝ, 0 ≤ a → a * ((n : ℝ) + 1) < 4 → clusterIntegral n ρ a < ∞) ∧
    (∀ a a₀ : ℝ, 0 ≤ a → a ≤ a₀ → a₀ * ((n : ℝ) + 1) < 4 →
      clusterIntegral n ρ a ≤ ENNReal.ofReal ((max 1 (2 * ρ)) ^
        (a₀ * (n : ℝ) * ((n : ℝ) + 1) / 2)) * clusterIntegral n ρ a₀) ∧
    (∀ a₀ : ℝ, 0 ≤ a₀ → a₀ * ((n : ℝ) + 1) < 4 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, 0 ≤ a → a ≤ a₀ →
        clusterIntegral n ρ a ≤ ENNReal.ofReal K) := by
  exact ⟨fun _ ha hsub ↦ clusterIntegral_lt_top n ha hsub hρ,
    fun _ _ ha haa _ ↦ clusterIntegral_exponent_comparison n ha haa hρ,
    fun _ ha hsub ↦ clusterIntegral_uniform_bound n ha hsub hρ⟩

end PeriodicAttractiveLogGas
