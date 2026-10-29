import LeanResearch.PeriodicAttractiveLogGas.CollisionIntegral
import LeanResearch.PeriodicAttractiveLogGas.TorusIntegrability
import LeanResearch.PeriodicAttractiveLogGas.Ensemble

/-! Integrability of the complete torus collision product in the first
paragraph of source Proposition 2.4's proof.

This is an adaptation of the source's local grouping argument. Near a fixed
lifted configuration, pairs with coincident torus centers have exactly the
Euclidean distance of their perturbations; all other pair factors are
bounded. On a sufficiently small product neighborhood, every nonzero
perturbation distance is less than one. Adding the remaining planar pair
factors therefore only increases the local majorant. The full planar
`H_N`, already proved subcritical, controls this enlarged product. We do not
assert a new independent product identity for the original collision groups.

Perturbation diagonals are removed only after proving their actual volume
nullity. Compactness and the product of the normalized quotient-box maps
then give integrability for the specified reference measure. No local
integrability, collision-finiteness, or independence premise is assumed.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped BigOperators ENNReal Topology

namespace PeriodicAttractiveLogGas

/-- The source product, with each unordered pair counted once. Powers at
zero use Mathlib's totalized real-power convention. -/
def torusPairWeight (N : ℕ) (a : ℝ) (x : Configuration N) : ℝ :=
  ∏ ij ∈ planarOrderedPairs N, torusEuclideanDist (x ij.1) (x ij.2) ^ (-a)

theorem torusPairWeight_nonneg (N : ℕ) (a : ℝ) (x : Configuration N) :
    0 ≤ torusPairWeight N a x :=
  Finset.prod_nonneg (fun ij _ ↦
    Real.rpow_nonneg (torusEuclideanDist_nonneg (x ij.1) (x ij.2)) _)

theorem measurable_torusPairWeight (N : ℕ) (a : ℝ) :
    Measurable (torusPairWeight N a) := by
  unfold torusPairWeight
  apply Finset.measurable_prod
  intro ij _
  have hi : Measurable (fun x : Configuration N ↦ x ij.1) := measurable_pi_apply ij.1
  have hj : Measurable (fun x : Configuration N ↦ x ij.2) := measurable_pi_apply ij.2
  have hp : Measurable (fun x : Configuration N ↦ x ij.1 - x ij.2) := hi.sub hj
  have hd : Measurable (fun x : Configuration N ↦ torusEuclideanDist (x ij.1) (x ij.2)) :=
    measurable_torusEuclideanNorm.comp hp
  exact hd.pow_const (-a)

theorem torusPairWeight_zero (N : ℕ) (x : Configuration N) :
    torusPairWeight N 0 x = 1 := by
  simp [torusPairWeight]

/-- Coordinatewise quotient for the product of planar spaces. The domain
has the ordinary finite-product topology and actual product Lebesgue volume. -/
def planarConfigurationQuotient (N : ℕ) (w : Fin N → PlanarSpace) : Configuration N :=
  fun i ↦ torusQuotient (w i)

theorem continuous_planarConfigurationQuotient (N : ℕ) :
    Continuous (planarConfigurationQuotient N) :=
  continuous_pi (fun i ↦
    isOpenQuotientMap_torusQuotient.continuous.comp (continuous_apply i))

theorem torusEuclideanDist_pos_of_ne {z w : Torus} (hzw : z ≠ w) :
    0 < torusEuclideanDist z w := by
  apply lt_of_le_of_ne (torusEuclideanDist_nonneg z w)
  intro h
  exact hzw ((torusEuclideanDist_eq_zero_iff z w).mp h.symm)

/-- At coincident torus centers, the distance in the local chart is the
Euclidean distance between perturbations, even when the original lifts
differ by a nonzero integer vector. -/
theorem torusEuclideanDist_lift_eq_perturbation_norm {N : ℕ}
    (b w : Fin N → PlanarSpace) (i j : Fin N)
    (hbij : torusQuotient (b i) = torusQuotient (b j))
    (hsmall : ‖(w - b) i - (w - b) j‖ < (1 / 2 : ℝ)) :
    torusEuclideanDist (torusQuotient (w i)) (torusQuotient (w j)) =
      ‖(w - b) i - (w - b) j‖ := by
  have hdiff : torusQuotient (w i) - torusQuotient (w j) =
      torusQuotient ((w - b) i - (w - b) j) := by
    simp only [Pi.sub_apply, torusQuotient_sub, hbij]
    abel
  rw [torusEuclideanDist, hdiff]
  exact torusEuclideanNorm_quotient_eq_of_norm_lt_half hsmall

/-- All perturbation diagonals have zero actual product Lebesgue measure. -/
theorem ae_planar_pairwise_ne (N : ℕ) :
    ∀ᵐ w : Fin N → PlanarSpace ∂volume,
      ∀ i j : Fin N, i ≠ j → w i ≠ w j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Eventually.of_forall (fun _ h ↦ (h hij).elim)
  · exact (ae_planar_pair_ne N hij).mono (fun _ h _ ↦ h)

/-- The checked anchored collision integral, combined with integration of
the freely moving anchor, gives the actual unanchored planar L1 bound. -/
theorem integrableOn_planarPairWeight (N : ℕ) (hN : 0 < N) {a ρ : ℝ}
    (ha : 0 ≤ a) (hsubcritical : a * (N : ℝ) < 4) (hρ : 0 < ρ) :
    IntegrableOn (planarPairWeight N a) (clusterBox N ρ) volume := by
  cases N with
  | zero => omega
  | succ n =>
    have hsub : a * ((n : ℝ) + 1) < 4 := by
      simpa only [Nat.cast_succ] using hsubcritical
    have hfinite : unanchoredClusterIntegral (n + 1) ρ a < ∞ :=
      unanchoredClusterIntegral_lt_top_of_clusterIntegral n a hρ
        (clusterIntegral_lt_top n ha hsub (by linarith : 0 < 2 * ρ))
    refine ⟨(measurable_planarPairWeight (n + 1) a).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (fun w ↦ planarPairWeight_nonneg (n + 1) a w))).mpr
    exact hfinite

/-- A concrete local majorant by a translated full planar collision product.
The comparison is almost everywhere, because extra planar factors vanish at
their totalized collision values when the exponent is strictly positive. -/
theorem exists_torusPairWeight_lift_local_majorant (N : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (b : Fin N → PlanarSpace) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ (1 / 8 : ℝ) ∧ 0 ≤ C ∧
      ∀ᵐ w ∂(volume.restrict (ball b r)),
        torusPairWeight N a (planarConfigurationQuotient N w) ≤
          C * planarPairWeight N a (w - b) := by
  classical
  have hsep : ∀ᶠ w in 𝓝 b, ∀ i j : Fin N,
      torusQuotient (b i) ≠ torusQuotient (b j) →
      torusEuclideanDist (torusQuotient (b i)) (torusQuotient (b j)) / 2 <
        torusEuclideanDist (torusQuotient (w i)) (torusQuotient (w j)) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hbij : torusQuotient (b i) = torusQuotient (b j)
    · exact Eventually.of_forall (fun _ h ↦ (h hbij).elim)
    · have hpos := torusEuclideanDist_pos_of_ne hbij
      have hi : Continuous (fun w : Fin N → PlanarSpace ↦ w i) := continuous_apply i
      have hj : Continuous (fun w : Fin N → PlanarSpace ↦ w j) := continuous_apply j
      have hqi : Continuous (fun w : Fin N → PlanarSpace ↦ torusQuotient (w i)) :=
        isOpenQuotientMap_torusQuotient.continuous.comp hi
      have hqj : Continuous (fun w : Fin N → PlanarSpace ↦ torusQuotient (w j)) :=
        isOpenQuotientMap_torusQuotient.continuous.comp hj
      have hp : Continuous (fun w : Fin N → PlanarSpace ↦
          torusQuotient (w i) - torusQuotient (w j)) := hqi.sub hqj
      have hcont : Continuous (fun w : Fin N → PlanarSpace ↦
          torusEuclideanDist (torusQuotient (w i)) (torusQuotient (w j))) :=
        continuous_torusEuclideanNorm.comp hp
      have hmem : {w : Fin N → PlanarSpace |
          torusEuclideanDist (torusQuotient (b i)) (torusQuotient (b j)) / 2 <
            torusEuclideanDist (torusQuotient (w i)) (torusQuotient (w j))} ∈ 𝓝 b :=
        (isOpen_lt continuous_const hcont).mem_nhds (by
          change torusEuclideanDist (torusQuotient (b i)) (torusQuotient (b j)) / 2 <
            torusEuclideanDist (torusQuotient (b i)) (torusQuotient (b j))
          linarith)
      exact Filter.Eventually.mono hmem (fun _ h _ ↦ h)
  obtain ⟨s, hs, hsepBall⟩ := Metric.mem_nhds_iff.mp hsep
  let r : ℝ := min s (1 / 8)
  have hr : 0 < r := lt_min hs (by norm_num)
  have hrs : r ≤ s := min_le_left _ _
  have hrsmall : r ≤ (1 / 8 : ℝ) := min_le_right _ _
  let A : Fin N × Fin N → ℝ := fun ij ↦
    if torusQuotient (b ij.1) = torusQuotient (b ij.2) then 1
    else (torusEuclideanDist (torusQuotient (b ij.1)) (torusQuotient (b ij.2)) / 2) ^ (-a)
  have hA : ∀ ij, 0 ≤ A ij := by
    intro ij
    dsimp only [A]
    split_ifs
    · norm_num
    · exact Real.rpow_nonneg
        (div_nonneg (torusEuclideanDist_nonneg _ _) (by norm_num)) _
  let C : ℝ := ∏ ij ∈ planarOrderedPairs N, A ij
  have hC : 0 ≤ C := Finset.prod_nonneg (fun ij _ ↦ hA ij)
  refine ⟨r, C, hr, hrsmall, hC, ?_⟩
  have hne : ∀ᵐ w : Fin N → PlanarSpace ∂volume,
      ∀ i j : Fin N, i ≠ j → (w - b) i ≠ (w - b) j :=
    (measurePreserving_sub_right (volume : Measure (Fin N → PlanarSpace)) b).quasiMeasurePreserving.ae
      (ae_planar_pairwise_ne N)
  filter_upwards [ae_restrict_of_ae hne,
    ae_restrict_mem (measurableSet_ball : MeasurableSet (ball b r))] with w hwne hw
  have hwsep := hsepBall (ball_subset_ball hrs hw)
  have hwb : ‖w - b‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have hcoord (i : Fin N) : ‖(w - b) i‖ < (1 / 8 : ℝ) :=
    (norm_le_pi_norm (w - b) i).trans_lt (hwb.trans_le hrsmall)
  have hdist (i j : Fin N) : ‖(w - b) i - (w - b) j‖ < (1 / 2 : ℝ) := by
    have hnorm := norm_sub_le ((w - b) i) ((w - b) j)
    have hi := hcoord i
    have hj := hcoord j
    linarith
  have hpair : ∀ ij ∈ planarOrderedPairs N,
      torusEuclideanDist (torusQuotient (w ij.1)) (torusQuotient (w ij.2)) ^ (-a) ≤
        A ij * ‖(w - b) ij.1 - (w - b) ij.2‖ ^ (-a) := by
    intro ij hij
    have hpos : 0 < ‖(w - b) ij.1 - (w - b) ij.2‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr
        (hwne _ _ (ne_of_lt ((mem_planarOrderedPairs ij).mp hij))))
    have hgeone : 1 ≤ ‖(w - b) ij.1 - (w - b) ij.2‖ ^ (-a) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos
        (by linarith [hdist ij.1 ij.2]) (neg_nonpos.mpr ha)
    by_cases hbij : torusQuotient (b ij.1) = torusQuotient (b ij.2)
    · rw [show A ij = 1 by simp only [A, ite_eq_left hbij], one_mul,
        torusEuclideanDist_lift_eq_perturbation_norm b w ij.1 ij.2 hbij (hdist _ _)]
    · have hcenter := torusEuclideanDist_pos_of_ne hbij
      have hupper :
          torusEuclideanDist (torusQuotient (w ij.1)) (torusQuotient (w ij.2)) ^ (-a) ≤
          A ij := by
        dsimp only [A]
        rw [ite_eq_right hbij]
        exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 <
          torusEuclideanDist (torusQuotient (b ij.1)) (torusQuotient (b ij.2)) / 2)
          (hwsep ij.1 ij.2 hbij).le (neg_nonpos.mpr ha)
      exact hupper.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hgeone (hA ij))
  calc
    torusPairWeight N a (planarConfigurationQuotient N w) ≤
        ∏ ij ∈ planarOrderedPairs N, A ij * ‖(w - b) ij.1 - (w - b) ij.2‖ ^ (-a) :=
      Finset.prod_le_prod₀ (fun ij _ ↦ Real.rpow_nonneg
        (torusEuclideanDist_nonneg (torusQuotient (w ij.1)) (torusQuotient (w ij.2))) _)
        hpair
    _ = C * planarPairWeight N a (w - b) := by
      rw [Finset.prod_mul_distrib]
      rfl

/-- The entire lifted torus product is locally integrable, including every
simultaneous and nested collision configuration. -/
theorem locallyIntegrable_torusPairWeight_lift (N : ℕ) (hN : 0 < N) {a : ℝ}
    (ha : 0 ≤ a) (hsubcritical : a * (N : ℝ) < 4) :
    LocallyIntegrable (fun w : Fin N → PlanarSpace ↦
      torusPairWeight N a (planarConfigurationQuotient N w)) volume := by
  intro b
  obtain ⟨r, C, hr, hrsmall, _hC, hbound⟩ :=
    exists_torusPairWeight_lift_local_majorant N ha b
  refine ⟨ball b r, ball_mem_nhds b hr, ?_⟩
  have htrans : MeasurePreserving (fun w : Fin N → PlanarSpace ↦ w - b) volume volume :=
    measurePreserving_sub_right (volume : Measure (Fin N → PlanarSpace)) b
  have hint : IntegrableOn (fun w : Fin N → PlanarSpace ↦ planarPairWeight N a (w - b))
      ((fun w : Fin N → PlanarSpace ↦ w - b) ⁻¹' clusterBox N 1) volume :=
    (htrans.restrict_preimage (measurableSet_clusterBox N 1)).integrable_comp_of_integrable
      (integrableOn_planarPairWeight N hN ha hsubcritical (by norm_num : (0 : ℝ) < 1))
  have hsubset : ball b r ⊆
      (fun w : Fin N → PlanarSpace ↦ w - b) ⁻¹' clusterBox N 1 := by
    intro w hw i _
    apply mem_ball_zero_iff.mpr
    have hwb : ‖w - b‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    exact (norm_le_pi_norm (w - b) i).trans_lt (hwb.trans_le (by linarith : r ≤ 1))
  have hmajorant : IntegrableOn (fun w : Fin N → PlanarSpace ↦
      C * planarPairWeight N a (w - b)) (ball b r) volume :=
    (hint.mono_set hsubset).const_mul C
  exact hmajorant.mono_nonneg
    ((measurable_torusPairWeight N a).comp
      (continuous_planarConfigurationQuotient N).measurable).aestronglyMeasurable
    (Eventually.of_forall (fun w ↦ torusPairWeight_nonneg N a
      (planarConfigurationQuotient N w))) hbound

/-- The centered fundamental box for each planar coordinate. -/
def planarConfigurationFundamentalBox (N : ℕ) : Set (Fin N → PlanarSpace) :=
  Set.pi Set.univ (fun _ ↦ euclideanFundamentalBox (centeredBoxAnchor 0))

theorem measurableSet_planarConfigurationFundamentalBox (N : ℕ) :
    MeasurableSet (planarConfigurationFundamentalBox N) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_euclideanFundamentalBox _)

/-- The compact enlargement uses the product supremum norm only to express
a compact set; the collision factors retain the Euclidean quotient metric. -/
theorem planarConfigurationFundamentalBox_subset_closedBall (N : ℕ) :
    planarConfigurationFundamentalBox N ⊆ closedBall (0 : Fin N → PlanarSpace) 1 := by
  intro w hw
  apply mem_closedBall_zero_iff.mpr
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  rw [← torusEuclideanNorm_quotient_eq_of_mem_centeredBox (hw i (mem_univ i))]
  exact torusEuclideanNorm_le_one _

/-- The product of the actual normalized quotient maps transports product
Lebesgue volume on the boxes to the specified labelled reference measure. -/
theorem measurePreserving_planarConfigurationQuotient_box (N : ℕ) :
    MeasurePreserving (planarConfigurationQuotient N)
      (volume.restrict (planarConfigurationFundamentalBox N)) (referenceMeasure N) := by
  change MeasurePreserving (fun w : Fin N → PlanarSpace ↦ fun i ↦ torusQuotient (w i))
    ((Measure.pi (fun _ : Fin N ↦ (volume : Measure PlanarSpace))).restrict
      (Set.pi Set.univ (fun _ ↦ euclideanFundamentalBox (centeredBoxAnchor 0))))
    (Measure.pi (fun _ : Fin N ↦ torusMeasure))
  rw [Measure.restrict_pi_pi]
  exact measurePreserving_pi
    (fun _ : Fin N ↦ volume.restrict (euclideanFundamentalBox (centeredBoxAnchor 0)))
    (fun _ : Fin N ↦ torusMeasure)
    (fun _ ↦ measurePreserving_torusQuotient_box (centeredBoxAnchor 0))

/-- The collision product in source Proposition 2.4 is integrable on the
entire product torus for the exact subcritical exponent range. -/
theorem integrable_torusPairWeight (N : ℕ) (hN : 2 ≤ N) {a : ℝ}
    (ha : 0 ≤ a) (hsubcritical : a * (N : ℝ) < 4) :
    Integrable (torusPairWeight N a) (referenceMeasure N) := by
  have hcompact : IntegrableOn (fun w : Fin N → PlanarSpace ↦
      torusPairWeight N a (planarConfigurationQuotient N w))
      (closedBall (0 : Fin N → PlanarSpace) 1) volume :=
    (locallyIntegrable_torusPairWeight_lift N (by omega) ha hsubcritical).integrableOn_isCompact
      (isCompact_closedBall (0 : Fin N → PlanarSpace) 1)
  have hbox := hcompact.mono_set (planarConfigurationFundamentalBox_subset_closedBall N)
  exact ((measurePreserving_planarConfigurationQuotient_box N).integrable_comp
    (measurable_torusPairWeight N a).aestronglyMeasurable).mp hbox

/-- The corresponding nonnegative extended integral is genuinely finite. -/
theorem lintegral_torusPairWeight_lt_top (N : ℕ) (hN : 2 ≤ N) {a : ℝ}
    (ha : 0 ≤ a) (hsubcritical : a * (N : ℝ) < 4) :
    (∫⁻ x, ENNReal.ofReal (torusPairWeight N a x) ∂referenceMeasure N) < ∞ :=
  (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (torusPairWeight_nonneg N a))).mp
    (integrable_torusPairWeight N hN ha hsubcritical).hasFiniteIntegral

end PeriodicAttractiveLogGas
