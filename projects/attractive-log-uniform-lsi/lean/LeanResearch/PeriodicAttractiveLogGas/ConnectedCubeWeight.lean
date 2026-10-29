import LeanResearch.PeriodicAttractiveLogGas.CubeProbability
import LeanResearch.PeriodicAttractiveLogGas.SmallCubeGeometry

/-! The one-cluster case of the fixed-particle cube bound. A connected
center graph is lifted consistently. Translation preserves the actual
cube law, and the singular integral is the already proved planar one. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.ConnectedCubeWeight
open PhysicalCubes CubeProbability SmallCubeGeometry ClusterCubeIntegral

/-- Membership is preserved when each coordinate and its center undergo
the same translation. -/
theorem translated_cube_mem {k : ℕ} (c b X : Fin k → PlanarSpace) (ℓ : ℝ) :
    X + b ∈ particleCube k (c + b) ℓ ↔ X ∈ particleCube k c ℓ := by
  simp only [particleCube, Set.mem_pi, Pi.add_apply, mem_cube, PiLp.add_apply,
    add_sub_add_right_eq_sub]

/-- Every point of the consistently lifted cube has the ordinary planar
pair distances and the required uniform diameter. -/
theorem lifted_cube_geometry {k : ℕ} (hk : 2 ≤ k) (c : Fin k → PlanarSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hsmall : ℓ ≤ 1 / (16 * (k : ℝ))) (anchor : Fin k)
    (hconn : ∀ i : Fin k, (centreGraph c ℓ).Reachable i anchor)
    (X : Fin k → PlanarSpace) (hX : X ∈ particleCube k (liftedCentre c anchor) ℓ)
    (i j : Fin k) :
    torusEuclideanDist (torusQuotient (X i)) (torusQuotient (X j)) = ‖X i - X j‖ ∧
      ‖X i - X j‖ < FixedWeightConstants.radius k * ℓ := by
  let c' := liftedCentre c anchor
  let Y := X + (c - c')
  have hY : Y ∈ particleCube k c ℓ := by
    have hh := (translated_cube_mem c' (c - c') X ℓ).mpr hX
    have hc : c' + (c - c') = c := by abel
    simpa only [hc] using hh
  have hpoint (l : Fin k) : liftedPoint c Y anchor l = X l := by
    dsimp only [liftedPoint, Y, c', Pi.add_apply, Pi.sub_apply]
    abel
  have hq (l : Fin k) : torusQuotient (Y l) = torusQuotient (X l) := by
    dsimp only [Y, c', Pi.add_apply, Pi.sub_apply]
    rw [torusQuotient_add, torusQuotient_sub, quotient_liftedCentre, sub_self, add_zero]
  have hh := small_cube_pair_lift hk c Y hℓ hsmall hY anchor (hconn i) (hconn j)
  simpa only [hpoint, hq] using hh

theorem lifted_cube_weight {k : ℕ} (hk : 2 ≤ k) (c : Fin k → PlanarSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hsmall : ℓ ≤ 1 / (16 * (k : ℝ))) (anchor : Fin k)
    (hconn : ∀ i : Fin k, (centreGraph c ℓ).Reachable i anchor)
    (a : ℝ) (X : Fin k → PlanarSpace) (hX : X ∈ particleCube k (liftedCentre c anchor) ℓ) :
    torusPairWeight k a (planarConfigurationQuotient k X) = planarPairWeight k a X := by
  unfold torusPairWeight planarPairWeight
  apply Finset.prod_congr rfl
  intro ij _
  rw [show torusEuclideanDist (planarConfigurationQuotient k X ij.1)
      (planarConfigurationQuotient k X ij.2) = ‖X ij.1 - X ij.2‖ from
    (lifted_cube_geometry hk c hℓ hsmall anchor hconn X hX ij.1 ij.2).1]

/-- Exact degree of the complete pair product after one coordinate is
chosen as its free anchor. -/
theorem degree_eq_choose (n : ℕ) (a : ℝ) :
    -a * (n : ℝ) * ((n : ℝ) + 1) / 2 = -a * (((n + 1).choose 2 : ℕ) : ℝ) := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- Uniform normalized cube integral in the connected case. The only
remaining input here is the explicitly identified anchored integral. -/
theorem connected_cube_mean_bound (n : ℕ) (hn : 1 ≤ n) (c : Fin (n + 1) → PlanarSpace)
    {a ℓ R H : ℝ} (hℓ : 0 < ℓ) (hsmall : ℓ ≤ 1 / (16 * ((n + 1 : ℕ) : ℝ)))
    (hR : FixedWeightConstants.radius (n + 1) ≤ R) (hH : 0 ≤ H)
    (hconn : ∀ i : Fin (n + 1), (centreGraph c ℓ).Reachable i 0)
    (hcluster : clusterIntegral n R a ≤ ENNReal.ofReal H) :
    (∫ X, torusPairWeight (n + 1) a (planarConfigurationQuotient (n + 1) X)
      ∂productLaw (n + 1) c ℓ) ≤
      ℓ ^ (-a * (((n + 1).choose 2 : ℕ) : ℝ)) * H := by
  let c' := liftedCentre c 0
  have hk : 2 ≤ n + 1 := by omega
  have hgeom := lifted_cube_geometry hk c hℓ hsmall 0 hconn
  have hdiam : ∀ X ∈ particleCube (n + 1) c' ℓ,
      ∀ i : Fin n, ‖X i.succ - X 0‖ < ℓ * R := by
    intro X hX i
    exact (hgeom X hX i.succ 0).2.trans_le (by nlinarith only [hR, hℓ])
  have hi := integrable_pairWeight_cube_bound n a c' hℓ hH hdiam hcluster
  have hperiod (i : Fin (n + 1)) : torusQuotient ((c' - c) i) = 0 := by
    dsimp only [c', Pi.sub_apply]
    rw [torusQuotient_sub, quotient_liftedCentre, sub_self]
  have htrans := integral_periodic_translate (n + 1) c (c' - c) hℓ
    (torusPairWeight (n + 1) a) hperiod
  have hc : c + (c' - c) = c' := by abel
  rw [hc] at htrans
  calc
    _ = ∫ X, torusPairWeight (n + 1) a (planarConfigurationQuotient (n + 1) X)
        ∂productLaw (n + 1) c' ℓ := htrans.symm
    _ = ∫ X, planarPairWeight (n + 1) a X ∂productLaw (n + 1) c' ℓ := by
      apply integral_congr_ae
      filter_upwards [ae_mem_productCube (n + 1) c' hℓ] with X hX
      exact lifted_cube_weight hk c hℓ hsmall 0 hconn a X hX
    _ = (ℓ ^ (2 * (n + 1)))⁻¹ *
        ∫ X in particleCube (n + 1) c' ℓ, planarPairWeight (n + 1) a X :=
      integral_productLaw (n + 1) c' hℓ _
    _ ≤ (ℓ ^ (2 * (n + 1)))⁻¹ *
        (ℓ ^ (2 * (n + 1)) * ℓ ^ (-a * (n : ℝ) * ((n : ℝ) + 1) / 2) * H) :=
      mul_le_mul_of_nonneg_left hi.2 (inv_nonneg.mpr (pow_nonneg hℓ.le _))
    _ = _ := by
      rw [degree_eq_choose]
      field_simp [hℓ.ne']


/-- Lower bound for a complete pair product on a cube of controlled
pair diameter. Collision-free evaluation is required only at this point. -/
theorem weight_lower_of_pair_bound (k : ℕ) {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (Y : Configuration k)
    (hY : ∀ ij ∈ planarOrderedPairs k, 0 < torusEuclideanDist (Y ij.1) (Y ij.2))
    (hb : ∀ ij ∈ planarOrderedPairs k, torusEuclideanDist (Y ij.1) (Y ij.2) ≤ L) :
    L ^ (-a * ((k.choose 2 : ℕ) : ℝ)) ≤ torusPairWeight k a Y := by
  have hh : (∏ _ij ∈ planarOrderedPairs k, L ^ (-a)) ≤ torusPairWeight k a Y := by
    apply Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg hL.le _)
    intro ij hij
    exact Real.rpow_le_rpow_of_nonpos (hY ij hij) (hb ij hij) (neg_nonpos.mpr ha)
  simpa only [Finset.prod_const, card_planarOrderedPairs,
    ← Real.rpow_mul_natCast hL.le] using hh

theorem homogeneity_cancel (p : ℕ) (a : ℝ) {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) :
    (R ^ a) ^ p * (ℓ * R) ^ (-a * (p : ℝ)) = ℓ ^ (-a * (p : ℝ)) := by
  calc
    _ = ℓ ^ (-a * (p : ℝ)) * (R ^ (a * (p : ℝ)) * R ^ (-(a * (p : ℝ)))) := by
      rw [← Real.rpow_mul_natCast hR.le, Real.mul_rpow hℓ.le hR.le]
      simp only [neg_mul]
      ring
    _ = _ := by rw [← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, mul_one]

theorem pair_count_add_one_le_square {k : ℕ} (hk : 1 ≤ k) : k.choose 2 + 1 ≤ k ^ 2 := by
  have hh : k.choose 2 ≤ k * (k - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_le_self _ _
  have hs := Nat.sub_add_cancel hk
  nlinarith

/-- The one-cluster A1 bound, with a deliberately coarse coefficient
suitable for multiplication along a finite cluster partition. -/
theorem connected_cube_mean_le_weight (n : ℕ) (hn : 1 ≤ n) (c : Fin (n + 1) → PlanarSpace)
    {a ℓ R H D : ℝ} (ha : 0 ≤ a) (hℓ : 0 < ℓ)
    (hsmall : ℓ ≤ 1 / (16 * ((n + 1 : ℕ) : ℝ)))
    (hR : FixedWeightConstants.radius (n + 1) ≤ R) (hRpos : 0 < R)
    (hH : 0 ≤ H) (hD : 1 ≤ D) (hHD : H ≤ D) (hRD : R ^ a ≤ D)
    (hconn : ∀ i : Fin (n + 1), (centreGraph c ℓ).Reachable i 0)
    (hcluster : clusterIntegral n R a ≤ ENNReal.ofReal H)
    (Y : Fin (n + 1) → PlanarSpace) (hY : Y ∈ particleCube (n + 1) c ℓ)
    (hYpos : ∀ ij ∈ planarOrderedPairs (n + 1),
      0 < torusEuclideanDist (torusQuotient (Y ij.1)) (torusQuotient (Y ij.2))) :
    (∫ X, torusPairWeight (n + 1) a (planarConfigurationQuotient (n + 1) X)
      ∂productLaw (n + 1) c ℓ) ≤
      D ^ ((n + 1) ^ 2) * torusPairWeight (n + 1) a (planarConfigurationQuotient (n + 1) Y) := by
  have hk : 2 ≤ n + 1 := by omega
  have hb : ∀ ij ∈ planarOrderedPairs (n + 1),
      torusEuclideanDist (torusQuotient (Y ij.1)) (torusQuotient (Y ij.2)) ≤ ℓ * R := by
    intro ij _
    have hh := small_cube_pair_lift hk c Y hℓ hsmall hY 0 (hconn ij.1) (hconn ij.2)
    rw [hh.1]
    exact hh.2.le.trans (by nlinarith only [hR, hℓ])
  have hlower := weight_lower_of_pair_bound (n + 1) ha (mul_pos hℓ hRpos)
    (planarConfigurationQuotient (n + 1) Y) hYpos hb
  have hcoef : (R ^ a) ^ ((n + 1).choose 2) * H ≤ D ^ ((n + 1) ^ 2) := by
    calc
      _ ≤ D ^ ((n + 1).choose 2) * D := by gcongr
      _ = D ^ ((n + 1).choose 2 + 1) := (pow_succ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hD (pair_count_add_one_le_square (by omega))
  calc
    _ ≤ ℓ ^ (-a * (((n + 1).choose 2 : ℕ) : ℝ)) * H :=
      connected_cube_mean_bound n hn c hℓ hsmall hR hH hconn hcluster
    _ = ((R ^ a) ^ ((n + 1).choose 2) * H) *
        (ℓ * R) ^ (-a * (((n + 1).choose 2 : ℕ) : ℝ)) := by
      rw [mul_right_comm, homogeneity_cancel _ a hℓ hRpos]
    _ ≤ ((R ^ a) ^ ((n + 1).choose 2) * H) *
        torusPairWeight (n + 1) a (planarConfigurationQuotient (n + 1) Y) :=
      mul_le_mul_of_nonneg_left hlower
        (mul_nonneg (pow_nonneg (Real.rpow_nonneg hRpos.le _) _) hH)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (torusPairWeight_nonneg _ _ _)

end PeriodicAttractiveLogGas.ConnectedCubeWeight
