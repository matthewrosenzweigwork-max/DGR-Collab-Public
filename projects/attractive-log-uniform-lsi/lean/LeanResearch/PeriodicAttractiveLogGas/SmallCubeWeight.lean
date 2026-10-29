import LeanResearch.PeriodicAttractiveLogGas.ConnectedCubeWeight
import LeanResearch.PeriodicAttractiveLogGas.TorusWeightPartition

/-! The small-cube A1 estimate. The finite grouping argument is implemented
by successively separating connected components. The deliberately enlarged
coefficient depends only on the fixed particle bound and enclosing exponent;
it is not asserted to be the manuscript's displayed numerical coefficient. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.SmallCubeWeight
open PhysicalCubes CubeProbability SmallCubeGeometry ConnectedCubeWeight TorusWeightPartition

/-- A finite coefficient large enough for each complete cluster and each
cross-pair comparison. The final power absorbs the finite grouping. -/
def coefficient (N : ℕ) (β₀ : ℝ) : ℝ :=
  max 1 (max (FixedWeightConstants.maximumClusterBound N β₀ : ℝ)
    (max (FixedWeightConstants.radius N ^ FixedWeightConstants.exponent N β₀)
      ((3 : ℝ) ^ FixedWeightConstants.exponent N β₀)))

theorem coefficient_ge_one (N : ℕ) (β₀ : ℝ) : 1 ≤ coefficient N β₀ := le_max_left _ _

theorem cluster_le_coefficient (N : ℕ) (β₀ : ℝ) :
    (FixedWeightConstants.maximumClusterBound N β₀ : ℝ) ≤ coefficient N β₀ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem radius_power_le_coefficient {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (haa : a ≤ FixedWeightConstants.exponent N β₀) :
    FixedWeightConstants.radius N ^ a ≤ coefficient N β₀ := by
  have hR : 1 ≤ FixedWeightConstants.radius N := by
    unfold FixedWeightConstants.radius
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  exact (Real.rpow_le_rpow_of_exponent_le hR haa).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem three_power_le_coefficient {N : ℕ} {β₀ a : ℝ}
    (haa : a ≤ FixedWeightConstants.exponent N β₀) : (3 : ℝ) ^ a ≤ coefficient N β₀ :=
  (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) haa).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Smaller clusters still satisfy the same chosen small-cube condition. -/
theorem smallness_of_le {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k) (hkN : k ≤ N)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hsmall : ℓ ≤ 1 / (16 * (N : ℝ))) :
    ℓ ≤ 1 / (16 * (k : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hle : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * N)).mp hsmall
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * k)).mpr
  nlinarith only [hh, mul_le_mul_of_nonneg_left hle hℓ.le]

theorem reindexed_cube_mem {k : ℕ} (S : Finset (Fin k)) (c Y : Fin k → PlanarSpace)
    {ℓ : ℝ} (hY : Y ∈ particleCube k c ℓ) :
    (fun i => Y (S.orderEmbOfFin rfl i)) ∈
      particleCube S.card (fun i => c (S.orderEmbOfFin rfl i)) ℓ :=
  fun i _ => hY (S.orderEmbOfFin rfl i) (mem_univ _)

theorem reindexed_pair_positive {k : ℕ} (S : Finset (Fin k)) (Y : Fin k → PlanarSpace)
    (hY : ∀ ij ∈ planarOrderedPairs k,
      0 < torusEuclideanDist (torusQuotient (Y ij.1)) (torusQuotient (Y ij.2))) :
    ∀ ij ∈ planarOrderedPairs S.card,
      0 < torusEuclideanDist (torusQuotient (Y (S.orderEmbOfFin rfl ij.1)))
        (torusQuotient (Y (S.orderEmbOfFin rfl ij.2))) := by
  intro ij hij
  let e : Fin S.card ↪o Fin k := S.orderEmbOfFin rfl
  have hijlt : ij.1 < ij.2 := (mem_planarOrderedPairs ij).mp hij
  have he : e ij.1 < e ij.2 := e.strictMono hijlt
  exact hY (e ij.1, e ij.2) ((mem_planarOrderedPairs (e ij.1, e ij.2)).mpr he)

/-- One genuine separation step: integrate the independent internal
products, then multiply the already proved bounds for the two subclusters. -/
theorem split_cube_mean_bound {k : ℕ} {a D ℓ : ℝ} (ha : 0 ≤ a)
    (hsub : a * (k : ℝ) < 4) (hD : 1 ≤ D) (h3D : (3 : ℝ) ^ a ≤ D)
    (hℓ : 0 < ℓ) (S : Finset (Fin k)) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (c Y : Fin k → PlanarSpace) (hY : Y ∈ particleCube k c ℓ)
    (hcross : ∀ ij ∈ planarCrossPairs k S, ¬ (centreGraph c ℓ).Reachable ij.1 ij.2)
    (hA : (∫ X, torusPairWeight S.card a (planarConfigurationQuotient S.card X)
      ∂productLaw S.card (fun i => c (S.orderEmbOfFin rfl i)) ℓ) ≤
        D ^ (S.card ^ 2) * torusPairWeight S.card a
          (planarConfigurationQuotient S.card (fun i => Y (S.orderEmbOfFin rfl i))))
    (hB : (∫ X, torusPairWeight Sᶜ.card a (planarConfigurationQuotient Sᶜ.card X)
      ∂productLaw Sᶜ.card (fun i => c (Sᶜ.orderEmbOfFin rfl i)) ℓ) ≤
        D ^ (Sᶜ.card ^ 2) * torusPairWeight Sᶜ.card a
          (planarConfigurationQuotient Sᶜ.card (fun i => Y (Sᶜ.orderEmbOfFin rfl i)))) :
    (∫ X, torusPairWeight k a (planarConfigurationQuotient k X) ∂productLaw k c ℓ) ≤
      D ^ (k ^ 2) * torusPairWeight k a (planarConfigurationQuotient k Y) := by
  let C := D ^ (S.card * Sᶜ.card) * crossWeight k a S (planarConfigurationQuotient k Y)
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) (crossWeight_nonneg _ _ _ _)
  have hk : 0 < k := hS.card_pos.trans_le (by simpa only [Fintype.card_fin] using S.card_le_univ)
  have hi := integrable_torusWeight_productLaw k hk c ha hsub hℓ
  have hG := integrable_restricted_product ha hsub S hS hSc c hℓ
  have hpoint : ∀ X ∈ particleCube k c ℓ,
      torusPairWeight k a (planarConfigurationQuotient k X) ≤
        C * (restrictedWeight k a S (planarConfigurationQuotient k X) *
          restrictedWeight k a Sᶜ (planarConfigurationQuotient k X)) := by
    intro X hX
    have hpos (Z : Fin k → PlanarSpace) (hZ : Z ∈ particleCube k c ℓ)
        (ij : Fin k × Fin k) (hij : ij ∈ planarCrossPairs k S) :
        0 < torusEuclideanDist (torusQuotient (Z ij.1)) (torusQuotient (Z ij.2)) :=
      (by positivity : (0 : ℝ) < 2 * ℓ).trans_le (cross_pair_bounds c Z hℓ hZ (hcross ij hij)).1
    have hb := crossWeight_comparison ha S (planarConfigurationQuotient k X)
      (planarConfigurationQuotient k Y) h3D (hpos X hX) (hpos Y hY)
      (fun ij hij => cross_pair_oscillation c Y X hℓ hY hX (hcross ij hij))
    rw [weight_partition]
    exact (mul_le_mul_of_nonneg_left hb
      (mul_nonneg (restrictedWeight_nonneg _ _ _ _) (restrictedWeight_nonneg _ _ _ _))).trans_eq (by ring)
  have hint := integral_mono_ae hi (hG.const_mul C)
    ((ae_mem_productCube k c hℓ).mono fun X hX => hpoint X hX)
  rw [integral_const_mul, integral_restricted_product a S c hℓ] at hint
  have hp := mul_le_mul hA hB
    (integral_nonneg (fun _ => torusPairWeight_nonneg _ _ _))
    (mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) (torusPairWeight_nonneg _ _ _))
  have hcount : S.card + Sᶜ.card = k := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl S
  have hdegree : S.card * Sᶜ.card + S.card ^ 2 + Sᶜ.card ^ 2 ≤ k ^ 2 := by
    nlinarith
  calc
    _ ≤ C * ((D ^ (S.card ^ 2) * torusPairWeight S.card a
        (planarConfigurationQuotient S.card (fun i => Y (S.orderEmbOfFin rfl i)))) *
      (D ^ (Sᶜ.card ^ 2) * torusPairWeight Sᶜ.card a
        (planarConfigurationQuotient Sᶜ.card (fun i => Y (Sᶜ.orderEmbOfFin rfl i))))) :=
      hint.trans (mul_le_mul_of_nonneg_left hp hC)
    _ = D ^ (S.card * Sᶜ.card + S.card ^ 2 + Sᶜ.card ^ 2) *
        torusPairWeight k a (planarConfigurationQuotient k Y) := by
      rw [weight_partition k a S (planarConfigurationQuotient k Y),
        restricted_reindex a S rfl, restricted_reindex a Sᶜ rfl]
      simp only [pow_add]
      dsimp only [C]
      simp only [planarConfigurationQuotient]
      ring
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD hdegree) (torusPairWeight_nonneg _ _ _)


/-- A disconnected finite centre graph supplies two nonempty groups and
literal separation of every cross pair. -/
theorem exists_separated_partition {k : ℕ} (c : Fin k → PlanarSpace) (ℓ : ℝ)
    (anchor : Fin k) (hconn : ¬ ∀ i, (centreGraph c ℓ).Reachable i anchor) :
    ∃ S : Finset (Fin k), S.Nonempty ∧ Sᶜ.Nonempty ∧ S.card < k ∧ Sᶜ.card < k ∧
      ∀ ij ∈ planarCrossPairs k S, ¬ (centreGraph c ℓ).Reachable ij.1 ij.2 := by
  classical
  let S := Finset.univ.filter (fun i => (centreGraph c ℓ).Reachable i anchor)
  have hmem (i : Fin k) : i ∈ S ↔ (centreGraph c ℓ).Reachable i anchor := by simp [S]
  have hs : S.Nonempty := ⟨anchor, (hmem anchor).mpr (SimpleGraph.Reachable.refl anchor)⟩
  obtain ⟨j, hj⟩ := not_forall.mp hconn
  have hsc : Sᶜ.Nonempty := ⟨j, Finset.mem_compl.mpr (fun h => hj ((hmem j).mp h))⟩
  have hcount : S.card + Sᶜ.card = k := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl S
  refine ⟨S, hs, hsc, by have := hsc.card_pos; omega, by have := hs.card_pos; omega, ?_⟩
  intro ij hij hr
  rcases ((mem_planarCrossPairs S ij).mp hij).2 with ⟨hi,hj⟩ | ⟨hi,hj⟩
  · exact hj ((hmem ij.2).mpr (hr.symm.trans ((hmem ij.1).mp hi)))
  · exact hi ((hmem ij.1).mpr (hr.trans ((hmem ij.2).mp hj)))

/-- The small-cube mean is controlled at every collision-free point.
Strong induction simply integrates the finitely many independent clusters;
no higher singular exponent is introduced. -/
theorem small_cube_mean_le_weight {N : ℕ} (hN : 2 ≤ N) {β₀ a ℓ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀)
    (hℓ : 0 < ℓ) (hsmall : ℓ ≤ 1 / (16 * (N : ℝ)))
    (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (c Y : Fin k → PlanarSpace)
    (hY : Y ∈ particleCube k c ℓ)
    (hYpos : ∀ ij ∈ planarOrderedPairs k,
      0 < torusEuclideanDist (torusQuotient (Y ij.1)) (torusQuotient (Y ij.2))) :
    (∫ X, torusPairWeight k a (planarConfigurationQuotient k X) ∂productLaw k c ℓ) ≤
      coefficient N β₀ ^ (k ^ 2) * torusPairWeight k a (planarConfigurationQuotient k Y) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hasub : a * (N : ℝ) < 4 := by
    have hh : a * (N : ℝ) ≤ β₀ := (le_div_iff₀ hn).mp haa
    exact hh.trans_lt hsub
  have hR : 0 < FixedWeightConstants.radius N := by unfold FixedWeightConstants.radius; positivity
  have hH : 0 ≤ (FixedWeightConstants.maximumClusterBound N β₀ : ℝ) := NNReal.coe_nonneg _
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst k
      have hp : planarOrderedPairs 1 = ∅ := by decide
      have he (X : Configuration 1) : torusPairWeight 1 a X = 1 := by
        simp only [torusPairWeight, hp, Finset.prod_empty]
      letI := productLaw_probability 1 c hℓ
      simp only [he, integral_const, probReal_univ, smul_eq_mul, one_mul, one_pow, pow_one, mul_one]
      exact coefficient_ge_one N β₀
    · have hk2 : 2 ≤ k := by omega
      let anchor : Fin k := ⟨0, by omega⟩
      by_cases hconn : ∀ i : Fin k, (centreGraph c ℓ).Reachable i anchor
      · have hradius : FixedWeightConstants.radius k ≤ FixedWeightConstants.radius N := by
          unfold FixedWeightConstants.radius
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) (by norm_num)
        have hs := smallness_of_le hN hk hkN hℓ hsmall
        have hc := FixedWeightConstants.clusterIntegral_le_maximum hN hk2 hkN hβ₀ hsub ha haa
        cases k with
        | zero => omega
        | succ n =>
          have hanchor : anchor = (0 : Fin (n + 1)) := rfl
          rw [hanchor] at hconn
          simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
            connected_cube_mean_le_weight n (by omega) c ha hℓ hs hradius hR hH
              (coefficient_ge_one N β₀) (cluster_le_coefficient N β₀)
              (radius_power_le_coefficient hN haa) hconn hc Y hY hYpos
      · obtain ⟨S,hS,hSc,hs,hsc,hcross⟩ := exists_separated_partition c ℓ anchor hconn
        have hA := ih S.card hs (by have := hS.card_pos; omega) (hs.le.trans hkN)
          (fun i => c (S.orderEmbOfFin rfl i)) (fun i => Y (S.orderEmbOfFin rfl i))
          (reindexed_cube_mem S c Y hY) (reindexed_pair_positive S Y hYpos)
        have hB := ih Sᶜ.card hsc (by have := hSc.card_pos; omega) (hsc.le.trans hkN)
          (fun i => c (Sᶜ.orderEmbOfFin rfl i)) (fun i => Y (Sᶜ.orderEmbOfFin rfl i))
          (reindexed_cube_mem Sᶜ c Y hY) (reindexed_pair_positive Sᶜ Y hYpos)
        exact split_cube_mean_bound ha (subcritical_of_le ha hasub hkN)
          (coefficient_ge_one N β₀) (three_power_le_coefficient haa) hℓ S hS hSc c Y hY
          hcross hA hB

/-- The actual fixed-particle weight, on every sufficiently small cube.
The constant is independent of the cube, its center and the smaller exponent. -/
theorem original_small_cube_bound {N : ℕ} (hN : 2 ≤ N) {β₀ a ℓ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀)
    (hℓ : 0 < ℓ) (hsmall : ℓ ≤ 1 / (16 * (N : ℝ)))
    (c Y : Fin N → PlanarSpace) (hY : Y ∈ particleCube N c ℓ)
    (hYpos : ∀ ij ∈ planarOrderedPairs N,
      0 < torusEuclideanDist (torusQuotient (Y ij.1)) (torusQuotient (Y ij.2))) :
    (∫ X in particleCube N c ℓ, torusPairWeight N a (planarConfigurationQuotient N X)) ≤
      coefficient N β₀ ^ (N ^ 2) * ℓ ^ (2 * N) *
        torusPairWeight N a (planarConfigurationQuotient N Y) := by
  have hh := small_cube_mean_le_weight hN hβ₀ hsub ha haa hℓ hsmall N (by omega) le_rfl c Y hY hYpos
  rw [integral_productLaw N c hℓ, smul_eq_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (pow_nonneg hℓ.le (2 * N))
  have he : ℓ ^ (2 * N) * (ℓ ^ (2 * N))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hℓ.ne')
  rw [← mul_assoc, he, one_mul] at hmul
  exact hmul.trans_eq (by ring)

end PeriodicAttractiveLogGas.SmallCubeWeight
