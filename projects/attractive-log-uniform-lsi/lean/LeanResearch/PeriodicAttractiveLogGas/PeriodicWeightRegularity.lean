import LeanResearch.PeriodicAttractiveLogGas.PeriodicCubeVolume
import LeanResearch.PeriodicAttractiveLogGas.Collisions

/-! The genuine periodic collision set is closed and Lebesgue null in
the full lifted configuration space. The nullity proof uses the exact
integer-cube quotient laws and a countable exhaustion, not merely the
nonperiodic diagonals. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.PeriodicWeightRegularity
open PhysicalCubes CubeProbability PeriodicCubeVolume

theorem collisionSet_closed (N : ℕ) : IsClosed (collisionSet N) := by
  have he : collisionSet N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j), {X | X i = X j} := by
    ext X
    simp [collisionSet]
  rw [he]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

def liftedCollisionSet (N : ℕ) : Set (Fin N → PlanarSpace) :=
  planarConfigurationQuotient N ⁻¹' collisionSet N

theorem liftedCollisionSet_closed (N : ℕ) : IsClosed (liftedCollisionSet N) :=
  (collisionSet_closed N).preimage (continuous_planarConfigurationQuotient N)

theorem liftedCollisionSet_null_integer_cube (N : ℕ) {n : ℕ} (hn : 0 < n)
    (c : Fin N → PlanarSpace) :
    (volume.restrict (particleCube N c (n : ℝ))) (liftedCollisionSet N) = 0 := by
  have hz := (quotient_productLaw_integer N hn c).measure_preimage
    (collisionSet_closed N).measurableSet.nullMeasurableSet
  rw [collisionSet_null] at hz
  change productLaw N c (n : ℝ) (liftedCollisionSet N) = 0 at hz
  rw [productLaw_eq N c (by exact_mod_cast hn), Measure.smul_apply, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)

theorem integer_cubes_cover (N : ℕ) :
    (⋃ n : ℕ, particleCube N 0 ((n + 1 : ℕ) : ℝ)) = univ := by
  apply eq_univ_of_forall
  intro X
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖X‖)
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  intro i _
  apply (mem_cube (0 : PlanarSpace) (X i) ((n + 1 : ℕ) : ℝ)).mpr
  intro j
  have hi : ‖X i‖ ≤ ‖X‖ := norm_le_pi_norm X i
  have hj : |X i j| ≤ ‖X i‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (X i) j
  simp only [PiLp.zero_apply, sub_zero, Nat.cast_add, Nat.cast_one]
  linarith

/-- Periodic collision nullity on the whole Euclidean lift, including
all lattice translates of every pair diagonal. -/
theorem liftedCollisionSet_null (N : ℕ) : volume (liftedCollisionSet N) = 0 := by
  have hnull (n : ℕ) : volume (liftedCollisionSet N ∩ particleCube N 0 ((n + 1 : ℕ) : ℝ)) = 0 := by
    simpa only [Measure.restrict_apply (liftedCollisionSet_closed N).measurableSet] using
      liftedCollisionSet_null_integer_cube N (Nat.succ_pos n) 0
  rw [← inter_univ (liftedCollisionSet N), ← integer_cubes_cover N, inter_iUnion]
  exact measure_iUnion_null hnull

theorem ae_no_lifted_collision (N : ℕ) :
    ∀ᵐ X : Fin N → PlanarSpace ∂volume, X ∉ liftedCollisionSet N := by
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using liftedCollisionSet_null N

theorem pair_positive_of_no_collision {N : ℕ} {X : Configuration N} (hX : X ∉ collisionSet N) :
    ∀ ij ∈ planarOrderedPairs N, 0 < torusEuclideanDist (X ij.1) (X ij.2) := by
  intro ij hij
  apply torusEuclideanDist_pos_of_ne
  intro he
  exact hX ⟨ij.1, ij.2, (ne_of_lt ((mem_planarOrderedPairs ij).mp hij)), he⟩

theorem ae_reference_pair_positive (N : ℕ) :
    ∀ᵐ X ∂referenceMeasure N, ∀ ij ∈ planarOrderedPairs N,
      0 < torusEuclideanDist (X ij.1) (X ij.2) := by
  have he : ∀ᵐ X ∂referenceMeasure N, X ∉ collisionSet N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
  exact he.mono fun _ hX => pair_positive_of_no_collision hX

theorem ae_lifted_pair_positive (N : ℕ) :
    ∀ᵐ X : Fin N → PlanarSpace ∂volume, ∀ ij ∈ planarOrderedPairs N,
      0 < torusEuclideanDist (torusQuotient (X ij.1)) (torusQuotient (X ij.2)) := by
  filter_upwards [ae_no_lifted_collision N] with X hX
  exact pair_positive_of_no_collision (X := planarConfigurationQuotient N X) hX

/-- The original distance product is at least one off the collision set.
No assertion is made at its arbitrary totalized collision values. -/
theorem one_le_weight {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (X : Configuration N)
    (hX : ∀ ij ∈ planarOrderedPairs N, 0 < torusEuclideanDist (X ij.1) (X ij.2)) :
    1 ≤ torusPairWeight N a X := by
  have hh : (∏ _ij ∈ planarOrderedPairs N, (1 : ℝ)) ≤ torusPairWeight N a X := by
    unfold torusPairWeight
    apply Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
    intro ij hij
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hX ij hij)
      (torusEuclideanNorm_le_one _) (neg_nonpos.mpr ha)
  simpa using hh

theorem weight_exponent_mono {N : ℕ} {a b : ℝ} (hab : a ≤ b) (X : Configuration N)
    (hX : ∀ ij ∈ planarOrderedPairs N, 0 < torusEuclideanDist (X ij.1) (X ij.2)) :
    torusPairWeight N a X ≤ torusPairWeight N b X := by
  apply Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (torusEuclideanDist_nonneg _ _) _)
  intro ij hij
  exact Real.rpow_le_rpow_of_exponent_ge (hX ij hij) (torusEuclideanNorm_le_one _)
    (neg_le_neg hab)


/-- Away from the closed periodic collision set the actual real weight
is continuous, including the zero exponent. -/
theorem continuousAt_lifted_weight (N : ℕ) (a : ℝ) {X : Fin N → PlanarSpace}
    (hX : X ∉ liftedCollisionSet N) :
    ContinuousAt (fun Y => torusPairWeight N a (planarConfigurationQuotient N Y)) X := by
  unfold torusPairWeight
  apply tendsto_finsetProd
  intro ij hij
  have hqi : Continuous (fun Y : Fin N → PlanarSpace => torusQuotient (Y ij.1)) :=
    isOpenQuotientMap_torusQuotient.continuous.comp (continuous_apply ij.1)
  have hqj : Continuous (fun Y : Fin N → PlanarSpace => torusQuotient (Y ij.2)) :=
    isOpenQuotientMap_torusQuotient.continuous.comp (continuous_apply ij.2)
  have hd := continuous_torusEuclideanNorm.comp (hqi.sub hqj)
  have hpos := pair_positive_of_no_collision (X := planarConfigurationQuotient N X) hX ij hij
  exact hd.continuousAt.rpow_const (Or.inl hpos.ne')

theorem ae_one_le_lifted_weight (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ X : Fin N → PlanarSpace ∂volume,
      1 ≤ torusPairWeight N a (planarConfigurationQuotient N X) :=
  (ae_lifted_pair_positive N).mono fun X hX => one_le_weight ha _ hX

theorem ae_one_le_reference_weight (N : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ X ∂referenceMeasure N, 1 ≤ torusPairWeight N a X :=
  (ae_reference_pair_positive N).mono fun X hX => one_le_weight ha _ hX

end PeriodicAttractiveLogGas.PeriodicWeightRegularity
