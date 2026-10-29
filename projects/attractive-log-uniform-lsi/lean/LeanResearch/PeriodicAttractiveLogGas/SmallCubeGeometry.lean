import LeanResearch.PeriodicAttractiveLogGas.PhysicalCubes
import LeanResearch.PeriodicAttractiveLogGas.ClusterSeparation

/-! Quantitative small-cube geometry for Appendix A. Connected components
are those of the actual torus centre graph. Their consistent lifts are
constructed, and all periodic distance identities are proved below the
injectivity radius. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace PeriodicAttractiveLogGas.SmallCubeGeometry
open PhysicalCubes

def physicalCenter {N : ℕ} (c : Fin N → PlanarSpace) (i : Fin N) :
    PiLp 2 (fun _ : Fin 2 ↦ UnitAddCircle) := WithLp.toLp 2 (torusQuotient (c i))

def centreGraph {N : ℕ} (c : Fin N → PlanarSpace) (ℓ : ℝ) : SimpleGraph (Fin N) :=
  clusterThresholdGraph (physicalCenter c) (4 * ℓ)

theorem physicalCenter_dist {N : ℕ} (c : Fin N → PlanarSpace) (i j : Fin N) :
    dist (physicalCenter c i) (physicalCenter c j) =
      torusEuclideanDist (torusQuotient (c i)) (torusQuotient (c j)) :=
  (torusEuclideanDist_eq_piLp_dist _ _).symm

theorem reachable_centre_dist_lt {N : ℕ} (hN : 2 ≤ N) (c : Fin N → PlanarSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hr : (centreGraph c ℓ).Reachable i j) :
    torusEuclideanDist (torusQuotient (c i)) (torusQuotient (c j)) <
      4 * ((N - 1 : ℕ) : ℝ) * ℓ := by
  have hn : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
  have hR : 0 < 4 * ((N - 1 : ℕ) : ℝ) * ℓ := by positivity
  have he : (4 * ((N - 1 : ℕ) : ℝ) * ℓ) / ((Fintype.card (Fin N) - 1 : ℕ) : ℝ) = 4 * ℓ := by
    simp only [Fintype.card_fin]
    field_simp [hn.ne']
  have hh := clusterThresholdGraph_reachable_dist_lt (physicalCenter c)
    (by simpa only [Fintype.card_fin] using hN) hR (by simpa only [he, centreGraph] using hr)
  simpa only [physicalCenter_dist] using hh

def liftedCentre {N : ℕ} (c : Fin N → PlanarSpace) (anchor i : Fin N) : PlanarSpace :=
  c anchor + centeredLift (torusQuotient (c i) - torusQuotient (c anchor))

def liftedPoint {N : ℕ} (c X : Fin N → PlanarSpace) (anchor i : Fin N) : PlanarSpace :=
  liftedCentre c anchor i + (X i - c i)

theorem quotient_liftedCentre {N : ℕ} (c : Fin N → PlanarSpace) (anchor i : Fin N) :
    torusQuotient (liftedCentre c anchor i) = torusQuotient (c i) := by
  rw [liftedCentre, torusQuotient_add, torusQuotient_centeredLift]
  abel

theorem quotient_liftedPoint {N : ℕ} (c X : Fin N → PlanarSpace) (anchor i : Fin N) :
    torusQuotient (liftedPoint c X anchor i) = torusQuotient (X i) := by
  rw [liftedPoint, torusQuotient_add, quotient_liftedCentre, torusQuotient_sub]
  abel

theorem liftedCentre_dist_lt {N : ℕ} (hN : 2 ≤ N) (c : Fin N → PlanarSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (anchor : Fin N) {i : Fin N}
    (hi : (centreGraph c ℓ).Reachable i anchor) :
    ‖liftedCentre c anchor i - c anchor‖ < 4 * ((N - 1 : ℕ) : ℝ) * ℓ := by
  have he : liftedCentre c anchor i - c anchor =
      centeredLift (torusQuotient (c i) - torusQuotient (c anchor)) := by
    unfold liftedCentre
    abel
  rw [he, norm_centeredLift]
  exact reachable_centre_dist_lt hN c hℓ hi

theorem small_cube_pair_lift {N : ℕ} (hN : 2 ≤ N) (c X : Fin N → PlanarSpace)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hsmall : ℓ ≤ 1 / (16 * (N : ℝ)))
    (hX : X ∈ particleCube N c ℓ) (anchor : Fin N) {i j : Fin N}
    (hi : (centreGraph c ℓ).Reachable i anchor) (hj : (centreGraph c ℓ).Reachable j anchor) :
    torusEuclideanDist (torusQuotient (X i)) (torusQuotient (X j)) =
        ‖liftedPoint c X anchor i - liftedPoint c X anchor j‖ ∧
      ‖liftedPoint c X anchor i - liftedPoint c X anchor j‖ < FixedWeightConstants.radius N * ℓ := by
  have hni := liftedCentre_dist_lt hN c hℓ anchor hi
  have hnj := liftedCentre_dist_lt hN c hℓ anchor hj
  have hxi := particle_cube_norm_sub hℓ.le hX i
  have hxj := particle_cube_norm_sub hℓ.le hX j
  have he : liftedPoint c X anchor i - liftedPoint c X anchor j =
      (liftedCentre c anchor i - c anchor) - (liftedCentre c anchor j - c anchor) +
        ((X i - c i) - (X j - c j)) := by
    unfold liftedPoint
    abel
  have hn : ‖liftedPoint c X anchor i - liftedPoint c X anchor j‖ <
      8 * ((N - 1 : ℕ) : ℝ) * ℓ + 2 * ℓ := by
    rw [he]
    have h1 := norm_add_le ((liftedCentre c anchor i - c anchor) - (liftedCentre c anchor j - c anchor))
      ((X i - c i) - (X j - c j))
    have h2 := norm_sub_le (liftedCentre c anchor i - c anchor) (liftedCentre c anchor j - c anchor)
    have h3 := norm_sub_le (X i - c i) (X j - c j)
    linarith only [h1, h2, h3, hni, hnj, hxi, hxj]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hl := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hNr)).mp hsmall
  have hhalf : ‖liftedPoint c X anchor i - liftedPoint c X anchor j‖ < (1 / 2 : ℝ) := by
    rw [hc] at hn
    nlinarith only [hn, hl, hℓ]
  have hdist := torusEuclideanDist_quotient_eq_of_dist_lt_half
    (show dist (liftedPoint c X anchor i) (liftedPoint c X anchor j) < (1 / 2 : ℝ) by
      simpa only [dist_eq_norm] using hhalf)
  rw [quotient_liftedPoint, quotient_liftedPoint, dist_eq_norm] at hdist
  refine ⟨hdist, ?_⟩
  rw [← hdist]
  have hcent := reachable_centre_dist_lt hN c hℓ (hi.trans hj.symm)
  have htri := (torusEuclideanDist_triangle (torusQuotient (X i)) (torusQuotient (c i))
    (torusQuotient (X j))).trans (add_le_add le_rfl
      (torusEuclideanDist_triangle (torusQuotient (c i)) (torusQuotient (c j)) (torusQuotient (X j))))
  have hpi := (torusEuclideanDist_quotient_le (X i) (c i)).trans (by simpa only [dist_eq_norm] using hxi)
  have hpj := (torusEuclideanDist_quotient_le (c j) (X j)).trans (by
    simpa only [dist_eq_norm, norm_sub_rev] using hxj)
  unfold FixedWeightConstants.radius
  rw [hc] at hcent
  nlinarith only [htri, hcent, hpi, hpj, hℓ]

theorem disconnected_centre_separation {N : ℕ} (c : Fin N → PlanarSpace) {ℓ : ℝ}
    {i j : Fin N} (hij : ¬ (centreGraph c ℓ).Reachable i j) :
    4 * ℓ ≤ torusEuclideanDist (torusQuotient (c i)) (torusQuotient (c j)) := by
  by_contra h
  have hne : i ≠ j := by
    intro he
    subst j
    exact hij (SimpleGraph.Reachable.refl i)
  have ha : (centreGraph c ℓ).Adj i j := ⟨hne, by
    rw [physicalCenter_dist]
    exact lt_of_not_ge h⟩
  exact hij ha.reachable

theorem cross_pair_bounds {N : ℕ} (c X : Fin N → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hX : X ∈ particleCube N c ℓ) {i j : Fin N}
    (hij : ¬ (centreGraph c ℓ).Reachable i j) :
    2 * ℓ ≤ torusEuclideanDist (torusQuotient (X i)) (torusQuotient (X j)) ∧
      torusEuclideanDist (torusQuotient (X i)) (torusQuotient (X j)) ≤
        torusEuclideanDist (torusQuotient (c i)) (torusQuotient (c j)) + 2 * ℓ ∧
      torusEuclideanDist (torusQuotient (c i)) (torusQuotient (c j)) ≤
        torusEuclideanDist (torusQuotient (X i)) (torusQuotient (X j)) + 2 * ℓ := by
  have hi := (torusEuclideanDist_quotient_le (X i) (c i)).trans
    (by simpa only [dist_eq_norm] using particle_cube_norm_sub hℓ.le hX i)
  have hj := (torusEuclideanDist_quotient_le (X j) (c j)).trans
    (by simpa only [dist_eq_norm] using particle_cube_norm_sub hℓ.le hX j)
  have hupper := (torusEuclideanDist_triangle (torusQuotient (X i)) (torusQuotient (c i))
    (torusQuotient (X j))).trans (add_le_add le_rfl
      (torusEuclideanDist_triangle (torusQuotient (c i)) (torusQuotient (c j)) (torusQuotient (X j))))
  have hlower := (torusEuclideanDist_triangle (torusQuotient (c i)) (torusQuotient (X i))
    (torusQuotient (c j))).trans (add_le_add le_rfl
      (torusEuclideanDist_triangle (torusQuotient (X i)) (torusQuotient (X j)) (torusQuotient (c j))))
  rw [torusEuclideanDist_comm (torusQuotient (c j)) (torusQuotient (X j))] at hupper
  rw [torusEuclideanDist_comm (torusQuotient (c i)) (torusQuotient (X i))] at hlower
  have hsep := disconnected_centre_separation c hij
  constructor
  · linarith only [hlower, hi, hj, hsep]
  · constructor <;> linarith only [hupper, hlower, hi, hj]

theorem cross_pair_oscillation {N : ℕ} (c X Y : Fin N → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hX : X ∈ particleCube N c ℓ) (hY : Y ∈ particleCube N c ℓ) {i j : Fin N}
    (hij : ¬ (centreGraph c ℓ).Reachable i j) :
    torusEuclideanDist (torusQuotient (X i)) (torusQuotient (X j)) ≤
      3 * torusEuclideanDist (torusQuotient (Y i)) (torusQuotient (Y j)) := by
  have hx := cross_pair_bounds c X hℓ hX hij
  have hy := cross_pair_bounds c Y hℓ hY hij
  linarith only [hx.2.1, hy.1, hy.2.2]

end PeriodicAttractiveLogGas.SmallCubeGeometry
