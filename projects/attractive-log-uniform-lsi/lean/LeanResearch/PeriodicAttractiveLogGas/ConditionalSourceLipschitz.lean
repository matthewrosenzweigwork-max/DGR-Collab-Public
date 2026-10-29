import LeanResearch.PeriodicAttractiveLogGas.ConditionalSourceCharts
import LeanResearch.PeriodicAttractiveLogGas.CrossingLogistic

/-! Physical Lipschitz transfer for the actual conditional observables.

Small physical source rectangles are isometric to their closed torus
products for the unscaled Euclidean configuration distance. Surjectivity
and the distance identity are proved, rather than supplied as inverse
Lipschitz hypotheses. Source-chart logarithms, actual conditional means,
and the actual adjacent-cell normalizer ratio can therefore be used in
the physical configuration Poincare theorem.

SOURCE_ONLY. No Lean execution, transitive axiom check, independent
source-alignment review, or protected acceptance is claimed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators NNReal ENNReal Topology ContDiff

namespace PeriodicAttractiveLogGas.ConditionalSourceLipschitz

open MovingPoleNumerators hiding patchDomain
open GreenPointWeights MovingPoleCalculus
open MovingPoleCharts MovingPoleNormalized
open MovingPoleDerivativeIdentification ConditionalSourceCharts
open MeshCells MeshAdjacentCells MeshNearbyGeometry LabelOccupations ConditionalParameters
open OneCoordinateConditionals DeletedConditionalPoincare LabelRatioTransport

variable {n J : ℕ}

/-- The actual closed product of outside patches, ordered by `Fin.succAbove`. -/
def closedOutsideProduct (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch) : Set (Configuration n) :=
  closedPatchProduct hJ (fun j ↦ A (i.succAbove j)) (fun j ↦ B (i.succAbove j))

theorem physicalBlock_dist_lt_half (hJ8 : 8 ≤ J) (a : MeshIndex J) (b : Patch)
    {x y : PlanarSpace} (hx : x ∈ physicalBlock J a b) (hy : y ∈ physicalBlock J a b) :
    dist x y < (1 / 2 : ℝ) := by
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hj8 : (8 : ℝ) ≤ J := by exact_mod_cast hJ8
  have hcoord (k : Fin 2) : |(x - y) k| ≤ 2 / (J : ℝ) := by
    have h₁ := hx k (mem_univ k)
    have h₂ := hy k (mem_univ k)
    change (a k : ℝ) / J ≤ x k ∧ x k ≤ ((a k : ℝ) + patchWidth b k) / J at h₁
    change (a k : ℝ) / J ≤ y k ∧ y k ≤ ((a k : ℝ) + patchWidth b k) / J at h₂
    have hw := div_le_div_of_nonneg_right (patchWidth_le_two b k) hj.le
    rw [add_div] at h₁ h₂
    change |x k - y k| ≤ _
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hn := euclidean_norm_le_sqrt_two_mul (show (0 : ℝ) ≤ 2 / J by positivity) hcoord
  have hs : Real.sqrt (2 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hh : Real.sqrt (2 : ℝ) * (2 / J) < 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hj).mpr
    nlinarith
  simpa only [dist_eq_norm] using hn.trans_lt hh

theorem physicalBlock_distance (hJ8 : 8 ≤ J) (a : MeshIndex J) (b : Patch)
    {x y : PlanarSpace} (hx : x ∈ physicalBlock J a b) (hy : y ∈ physicalBlock J a b) :
    torusEuclideanDist (torusQuotient x) (torusQuotient y) = dist x y :=
  torusEuclideanDist_quotient_eq_of_dist_lt_half (physicalBlock_dist_lt_half hJ8 a b hx hy)

theorem configurationEuclideanDist_sq_blocks {N : ℕ} (Y Z : Configuration N) :
    configurationEuclideanDist Y Z ^ 2 = ∑ j, torusEuclideanDist (Y j) (Z j) ^ 2 := by
  rw [configurationEuclideanDist, configurationEuclideanNorm_sq]
  apply Finset.sum_congr rfl
  intro j hj
  rw [torusEuclideanDist, torusEuclideanNorm,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  rfl

theorem source_dist_sq_blocks {ι : Type*} [Fintype ι] (X Y : SourceSpace ι) :
    dist X Y ^ 2 = ∑ k, dist (sourceProjection k X) (sourceProjection k Y) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Exact physical distance on the closed outside chart. The constant is
one, independently of the original particle number and the mesh size. -/
theorem outsideCoordinates_distance (hJ8 : 8 ≤ J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    {X Y : SourceSpace (otherParticles i)}
    (hX : X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))
    (hY : Y ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) :
    configurationEuclideanDist (outsideCoordinates i X) (outsideCoordinates i Y) = dist X Y := by
  have hb (Z : SourceSpace (otherParticles i))
      (hZ : Z ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))
      (k : otherParticles i) : sourceProjection k Z ∈ physicalBlock J (A k) (B k) := by
    intro q hq
    exact (mem_closedChart_iff J _ _ Z).mp hZ (k, q)
  apply (sq_eq_sq₀ (configurationEuclideanDist_nonneg _ _) dist_nonneg).mp
  rw [configurationEuclideanDist_sq_blocks, source_dist_sq_blocks]
  apply Fintype.sum_equiv (otherIndexEquiv i)
  intro j
  change torusEuclideanDist
    (torusQuotient (sourceProjection (otherIndexEquiv i j) X))
    (torusQuotient (sourceProjection (otherIndexEquiv i j) Y)) ^ 2 = _
  rw [physicalBlock_distance hJ8 _ _ (hb X hX _) (hb Y hY _)]

theorem sources_surjOn_closedChart {ι : Type*} [Fintype ι] (hJ : 0 < J)
    (A : ι → MeshIndex J) (B : ι → Patch) :
    SurjOn (sources : SourceSpace ι → ι → Torus) (closedChart J A B)
      (Set.pi univ (fun k ↦ closure (patchDomain J hJ (A k) (B k)))) := by
  classical
  intro y hy
  have hl (k : ι) : ∃ Z ∈ patchClosed (B k), meshChart J (A k) Z = y k := by
    have hk := hy k (mem_univ k)
    change y k ∈ closure (patchDomain J hJ (A k) (B k)) at hk
    rw [← source_patchDomain, closure_patchDomain hJ] at hk
    exact hk
  choose Z hZ hq using hl
  let X : SourceSpace ι := WithLp.toLp 2 (fun ik ↦ meshAffine J (A ik.1) (Z ik.1) ik.2)
  have hp (k : ι) : sourceProjection k X = meshAffine J (A k) (Z k) := by
    ext q
    rfl
  refine ⟨X, ?_, ?_⟩
  · apply (mem_closedChart_iff J A B X).mpr
    intro ik
    have hb : sourceProjection ik.1 X ∈ physicalBlock J (A ik.1) (B ik.1) := by
      rw [hp, physicalBlock_eq_image hJ]
      exact ⟨Z ik.1, hZ ik.1, rfl⟩
    exact hb ik.2 (mem_univ ik.2)
  · funext k
    rw [sources, hp]
    exact hq k

theorem outsideCoordinates_mem_closedProduct (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    {X : SourceSpace (otherParticles i)}
    (hX : X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) :
    outsideCoordinates i X ∈ closedOutsideProduct hJ i A B := by
  intro j hj
  simpa only [outsideCoordinates, source_patchDomain, otherIndexEquiv_val] using
    source_mem_closure_patch hJ _ _ hX (otherIndexEquiv i j)

/-- Every point of the actual closed outside product has a lift in the
literal physical chart, including all boundary and wrap points. -/
theorem outsideCoordinates_surjOn_closedChart (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch) :
    SurjOn (outsideCoordinates i)
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))
      (closedOutsideProduct hJ i A B) := by
  classical
  intro Y hY
  let e := otherIndexEquiv i
  let y : otherParticles i → Torus := fun k ↦ Y (e.symm k)
  have hy : y ∈ Set.pi univ (fun k : otherParticles i ↦ closure (patchDomain J hJ (A k) (B k))) := by
    intro k hk
    have h := hY (e.symm k) (mem_univ _)
    change Y (e.symm k) ∈ closure (patchDomain J hJ (A k) (B k))
    have he : i.succAbove (e.symm k) = (k : Fin (n + 1)) := by
      simpa only [e, otherIndexEquiv_val] using congrArg Subtype.val (e.apply_symm_apply k)
    simpa only [he] using h
  obtain ⟨X, hX, hXY⟩ := sources_surjOn_closedChart hJ
    (fun k : otherParticles i ↦ A k) (fun k ↦ B k) hy
  refine ⟨X, hX, ?_⟩
  funext j
  change sources X (e j) = Y j
  rw [hXY]
  exact congrArg Y (e.symm_apply_apply j)

/-- Descent from the proved isometric source chart. No inverse regularity
or physical Lipschitz hypothesis is assumed. -/
theorem physicalLipschitz_of_chart (hJ : 0 < J) (hJ8 : 8 ≤ J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    {L : ℝ≥0} {g : Configuration n → ℝ}
    (hg : LipschitzOnWith L (fun X ↦ g (outsideCoordinates i X))
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))) :
    ConfigurationPhysicalLipschitzOn L g (closedOutsideProduct hJ i A B) := by
  intro Y hY Z hZ
  obtain ⟨X, hX, rfl⟩ := outsideCoordinates_surjOn_closedChart hJ i A B hY
  obtain ⟨W, hW, rfl⟩ := outsideCoordinates_surjOn_closedChart hJ i A B hZ
  rw [outsideCoordinates_distance hJ8 i A B hX hW]
  simpa only [Real.dist_eq] using hg.dist_le_mul X hX W hW

theorem configurationEuclideanDist_removeSite_le (i : Fin (n + 1))
    (X Y : Configuration (n + 1)) :
    configurationEuclideanDist (removeSite i X) (removeSite i Y) ≤ configurationEuclideanDist X Y := by
  apply (sq_le_sq₀ (configurationEuclideanDist_nonneg _ _) (configurationEuclideanDist_nonneg _ _)).mp
  rw [configurationEuclideanDist_sq_blocks, configurationEuclideanDist_sq_blocks,
    Fin.sum_univ_succAbove (fun k ↦ torusEuclideanDist (X k) (Y k) ^ 2) i]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem removeSite_mem_closedOutsideProduct (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    {X : Configuration (n + 1)} (hX : X ∈ closedPatchProduct hJ A B) :
    removeSite i X ∈ closedOutsideProduct hJ i A B := fun j _ ↦ hX (i.succAbove j) (mem_univ _)

/-- Lifting an outside observable to the joint configuration preserves
the identical physical Lipschitz constant. -/
theorem physicalLipschitz_removeSite (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    {L : ℝ≥0} {g : Configuration n → ℝ}
    (hg : ConfigurationPhysicalLipschitzOn L g (closedOutsideProduct hJ i A B)) :
    ConfigurationPhysicalLipschitzOn L (fun X ↦ g (removeSite i X)) (closedPatchProduct hJ A B) := by
  intro X hX Y hY
  exact (hg _ (removeSite_mem_closedOutsideProduct hJ i A B hX)
    _ (removeSite_mem_closedOutsideProduct hJ i A B hY)).trans
      (mul_le_mul_of_nonneg_left (configurationEuclideanDist_removeSite_le i X Y) L.coe_nonneg)

theorem removeSite_update_self (i : Fin (n + 1)) (X : Configuration (n + 1)) (z : Torus) :
    removeSite i (Function.update X i z) = removeSite i X := by
  funext j
  exact Function.update_of_ne (Fin.succAbove_ne i j) z X

/-- The integrated physical coordinate derivative vanishes at every
configuration, without differentiability or measure hypotheses. -/
theorem coordinateOrdinaryGradient_removeSite_self (i : Fin (n + 1))
    (g : Configuration n → ℝ) (X : Configuration (n + 1)) :
    coordinateOrdinaryGradient (fun Y ↦ g (removeSite i Y)) i X = 0 := by
  simp only [coordinateOrdinaryGradient, removeSite_update_self,
    torusOrdinaryGradient, rectangleOrdinaryGradient]
  simp

theorem physicalLipschitz_sub {N : ℕ} {D : Set (Configuration N)}
    {L M : ℝ≥0} {f g : Configuration N → ℝ}
    (hf : ConfigurationPhysicalLipschitzOn L f D) (hg : ConfigurationPhysicalLipschitzOn M g D) :
    ConfigurationPhysicalLipschitzOn (L + M) (fun X ↦ f X - g X) D := by
  intro X hX Y hY
  calc
    |(f X - g X) - (f Y - g Y)| = |(f X - f Y) - (g X - g Y)| := by congr 1; ring
    _ ≤ |f X - f Y| + |g X - g Y| := abs_sub _ _
    _ ≤ (L : ℝ) * configurationEuclideanDist X Y + (M : ℝ) * configurationEuclideanDist X Y :=
      add_le_add (hf X hX Y hY) (hg X hX Y hY)
    _ = _ := by rw [NNReal.coe_add, add_mul]

theorem physicalLipschitz_comp {N : ℕ} {D : Set (Configuration N)}
    {L M : ℝ≥0} {f : Configuration N → ℝ} {g : ℝ → ℝ}
    (hf : ConfigurationPhysicalLipschitzOn L f D) (hg : LipschitzWith M g) :
    ConfigurationPhysicalLipschitzOn (M * L) (fun X ↦ g (f X)) D := by
  intro X hX Y hY
  have h := hg.dist_le_mul (f X) (f Y)
  rw [Real.dist_eq, Real.dist_eq] at h
  exact h.trans (by
    simpa only [NNReal.coe_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (hf X hX Y hY) M.coe_nonneg)

/-- Both actual observables inherit source-chart Lipschitz continuity
with exactly the same constant. The analytic chart bounds are already
fields of the constructed source calculus. -/
theorem actual_outside_lipschitz_of_sourceCalculus (hJ : 0 < J) (hJ8 : 8 ≤ J)
    (i : Fin (n + 1)) (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (β : ℝ) (a : MeshIndex J) (b : Patch) (f : Configuration (n + 1) → ℝ)
    (hc : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) (configurationFactor i f)) :
    ∃ Llog Lmean : ℝ≥0,
      ConfigurationPhysicalLipschitzOn Llog (outsideLog hJ i β a b) (closedOutsideProduct hJ i A B) ∧
      ConfigurationPhysicalLipschitzOn Lmean (outsideMean hJ i β a b f) (closedOutsideProduct hJ i A B) := by
  obtain ⟨Llog, Lraw, hl, _⟩ := hc.normalization.lipschitz
  obtain ⟨Lmean, hm⟩ := hc.mean_lipschitz
  refine ⟨Llog, Lmean, physicalLipschitz_of_chart hJ hJ8 i A B ?_,
    physicalLipschitz_of_chart hJ hJ8 i A B ?_⟩
  · simpa only [outsideLog_comp] using hl
  · apply LipschitzOnWith.of_dist_le_mul
    intro X hX Y hY
    rw [ConditionalSourceCharts.SourceCalculus.outsideMean_comp hc (by omega) X hX,
      ConditionalSourceCharts.SourceCalculus.outsideMean_comp hc (by omega) Y hY]
    exact hm.dist_le_mul X hX Y hY

/-- The optional-deletion observables obey the same exact metric transfer. -/
theorem deleted_outside_lipschitz_of_sourceCalculus (hJ : 0 < J) (hJ8 : 8 ≤ J)
    (i : Fin (n + 1)) (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (f : Configuration (n + 1) → ℝ)
    (hc : MovingPoleDerivativeIdentification.SourceCalculus
      (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) J hJ a b
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) (configurationFactor i f)) :
    ∃ Llog Lmean : ℝ≥0,
      ConfigurationPhysicalLipschitzOn Llog (deletedOutsideLog hJ i d β a b)
        (closedOutsideProduct hJ i A B) ∧
      ConfigurationPhysicalLipschitzOn Lmean (deletedOutsideMean hJ i d β a b f)
        (closedOutsideProduct hJ i A B) := by
  obtain ⟨Llog, Lraw, hl, _⟩ := hc.normalization.lipschitz
  obtain ⟨Lmean, hm⟩ := hc.mean_lipschitz
  have he (X : SourceSpace (otherParticles i))
      (hX : X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) :
      deletedOutsideMean hJ i d β a b f (outsideCoordinates i X) =
        conditionalMean (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k)
          J hJ a b (configurationFactor i f) X := by
    rw [deletedOutsideMean, deletedOutsideKernel_eq_source hJ (by omega) i d β a b X
      (hc.normalization.normalizer_pos X hX)]
    simp only [conditionalMean, source_patchDomain, configurationFactor, insertedConfiguration]
  refine ⟨Llog, Lmean, physicalLipschitz_of_chart hJ hJ8 i A B ?_,
    physicalLipschitz_of_chart hJ hJ8 i A B ?_⟩
  · simpa only [deletedOutsideLog_comp] using hl
  · apply LipschitzOnWith.of_dist_le_mul
    intro X hX Y hY
    rw [he X hX, he Y hY]
    exact hm.dist_le_mul X hX Y hY

/-- Lifting the preceding bounds to the full physical product loses no
constant, because the conditional observables are independent of coordinate i. -/
theorem deleted_joint_lipschitz_of_sourceCalculus (hJ : 0 < J) (hJ8 : 8 ≤ J)
    (i : Fin (n + 1)) (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (f : Configuration (n + 1) → ℝ)
    (hc : MovingPoleDerivativeIdentification.SourceCalculus
      (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) J hJ a b
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) (configurationFactor i f)) :
    ∃ Llog Lmean : ℝ≥0,
      ConfigurationPhysicalLipschitzOn Llog
        (fun X ↦ deletedOutsideLog hJ i d β a b (removeSite i X)) (closedPatchProduct hJ A B) ∧
      ConfigurationPhysicalLipschitzOn Lmean
        (fun X ↦ deletedOutsideMean hJ i d β a b f (removeSite i X)) (closedPatchProduct hJ A B) := by
  obtain ⟨Llog, Lmean, hl, hm⟩ :=
    deleted_outside_lipschitz_of_sourceCalculus hJ hJ8 i A B d β a b f hc
  exact ⟨Llog, Lmean, physicalLipschitz_removeSite hJ i A B hl,
    physicalLipschitz_removeSite hJ i A B hm⟩

/-- The normalized cell masses have the same common area factor. It
cancels in their actual ratio, leaving the sigmoid of the raw log difference. -/
theorem normalizerRatio_eq_sigmoid_outsideLog (hJ : 0 < J) (i : Fin (n + 1))
    (β : ℝ) (a : MeshIndex J) (r : Fin 2) (Y : Configuration n)
    (ha : 0 < outsideNormalizer hJ i β a .cell Y)
    (hb : 0 < outsideNormalizer hJ i β (nextCell J hJ a r) .cell Y) :
    CrossingLogistic.normalizerRatio hJ β a r Y =
      Real.sigmoid (outsideLog hJ i β a .cell Y -
        outsideLog hJ i β (nextCell J hJ a r) .cell Y) := by
  have he (c : MeshIndex J) : cellNormalizer hJ c β Y =
      (J : ℝ) ^ 2 * outsideNormalizer hJ i β c .cell Y :=
    cellNormalizer_eq_haar hJ c β Y
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  rw [CrossingLogistic.normalizerRatio, he a, he (nextCell J hJ a r), outsideLog, outsideLog,
    CrossingLogistic.sigmoid_log_sub ha hb, ← mul_add]
  field_simp [pow_ne_zero 2 hj, (add_pos ha hb).ne']

theorem normalizerRatio_lipschitz_of_sourceCalculus (hJ : 0 < J) (hJ8 : 8 ≤ J)
    (i : Fin (n + 1)) (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (β : ℝ) (a : MeshIndex J) (r : Fin 2)
    (ha : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a .cell
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) (fun _ _ ↦ 1))
    (hb : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ (nextCell J hJ a r) .cell
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) (fun _ _ ↦ 1)) :
    ∃ L : ℝ≥0,
      ConfigurationPhysicalLipschitzOn L (CrossingLogistic.normalizerRatio hJ β a r)
        (closedOutsideProduct hJ i A B) ∧
      ConfigurationPhysicalLipschitzOn L
        (fun X ↦ CrossingLogistic.normalizerRatio hJ β a r (removeSite i X))
        (closedPatchProduct hJ A B) := by
  obtain ⟨La, _, hLa, _⟩ := actual_outside_lipschitz_of_sourceCalculus hJ hJ8 i A B β a .cell
    (fun _ ↦ 1) ha
  obtain ⟨Lb, _, hLb, _⟩ := actual_outside_lipschitz_of_sourceCalculus hJ hJ8 i A B β
    (nextCell J hJ a r) .cell (fun _ ↦ 1) hb
  have hq := physicalLipschitz_comp (physicalLipschitz_sub hLa hLb) CrossingLogistic.sigmoid_lipschitz
  have he (Y : Configuration n) (hY : Y ∈ closedOutsideProduct hJ i A B) :
      CrossingLogistic.normalizerRatio hJ β a r Y =
        Real.sigmoid (outsideLog hJ i β a .cell Y -
          outsideLog hJ i β (nextCell J hJ a r) .cell Y) := by
    obtain ⟨X, hX, rfl⟩ := outsideCoordinates_surjOn_closedChart hJ i A B hY
    apply normalizerRatio_eq_sigmoid_outsideLog hJ i β a r
    · rw [outsideNormalizer_comp]
      exact ha.normalization.normalizer_pos X hX
    · rw [outsideNormalizer_comp]
      exact hb.normalization.normalizer_pos X hX
  have hq' : ConfigurationPhysicalLipschitzOn ((1 / 4 : ℝ≥0) * (La + Lb))
      (CrossingLogistic.normalizerRatio hJ β a r) (closedOutsideProduct hJ i A B) := by
    intro X hX Y hY
    rw [he X hX, he Y hY]
    exact hq X hX Y hY
  exact ⟨_, hq', physicalLipschitz_removeSite hJ i A B hq'⟩

section Capped

variable (K : MovingPoleIntegrability.KernelBounds) (hJ : 0 < J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)

include K hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh

/-- Every analytic and physical regularity gate is discharged from caps,
placement, the imported Green bounds, and the explicit local smooth factor. -/
theorem capped_deleted_joint_lipschitz (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (labels : SourceSpace (otherParticles i) → LabelVector J (n + 1))
    (hcap : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      OccupationCap (fixedDelta β₀ C₀ C₁) (labels X))
    (hplace : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      ∀ k ∈ otherParticles i, extendedSources (otherParticles i) X k ∈
        closure (meshCell J hJ (labels X k)))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (a : MeshIndex J) (b : Patch)
    (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))
      (patchClosed b) (torusFactor (configurationFactor i f) J a)) :
    ∃ Llog Lmean : ℝ≥0,
      ConfigurationPhysicalLipschitzOn Llog
        (fun X ↦ deletedOutsideLog hJ i d β a b (removeSite i X)) (closedPatchProduct hJ A B) ∧
      ConfigurationPhysicalLipschitzOn Lmean
        (fun X ↦ deletedOutsideMean hJ i d β a b f (removeSite i X)) (closedPatchProduct hJ A B) := by
  have hc := capped_sourceCalculus K hJ (Nat.succ_pos n) hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    (otherParticles i) _ (isCompact_closedChart J _ _) (convex_closedChart J _ _)
    labels hcap hplace (DeletedPairEnsemble.coefficients d β i)
    (fun k _ ↦ (DeletedPairEnsemble.coefficients_bounds d hβ i k).1)
    (fun k _ ↦ (DeletedPairEnsemble.coefficients_bounds d hβ i k).2) a b hf
  exact deleted_joint_lipschitz_of_sourceCalculus hJ (by omega) i A B d β a b f hc

/-- The canonical nondeleted conditional kernel and mean have the same
physical conclusion, including when the integrated patch differs from B i. -/
theorem capped_actual_joint_lipschitz (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (labels : SourceSpace (otherParticles i) → LabelVector J (n + 1))
    (hcap : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      OccupationCap (fixedDelta β₀ C₀ C₁) (labels X))
    (hplace : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      ∀ k ∈ otherParticles i, extendedSources (otherParticles i) X k ∈
        closure (meshCell J hJ (labels X k)))
    (a : MeshIndex J) (b : Patch) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))
      (patchClosed b) (torusFactor (configurationFactor i f) J a)) :
    ∃ Llog Lmean : ℝ≥0,
      ConfigurationPhysicalLipschitzOn Llog
        (fun X ↦ outsideLog hJ i β a b (removeSite i X)) (closedPatchProduct hJ A B) ∧
      ConfigurationPhysicalLipschitzOn Lmean
        (fun X ↦ outsideMean hJ i β a b f (removeSite i X)) (closedPatchProduct hJ A B) := by
  have hc := capped_sourceCalculus K hJ (Nat.succ_pos n) hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    (otherParticles i) _ (isCompact_closedChart J _ _) (convex_closedChart J _ _)
    labels hcap hplace (fun _ ↦ β / (n + 1 : ℕ))
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) a b hf
  obtain ⟨Llog, Lmean, hl, hm⟩ :=
    actual_outside_lipschitz_of_sourceCalculus hJ (by omega) i A B β a b f hc
  exact ⟨Llog, Lmean, physicalLipschitz_removeSite hJ i A B hl,
    physicalLipschitz_removeSite hJ i A B hm⟩

/-- The actual q is Lipschitz on the actual outside and full products.
The two analytic logarithm bounds and both positive masses are constructed;
no regularity or differentiability of q is an input. -/
theorem capped_normalizerRatio_lipschitz (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (labels : SourceSpace (otherParticles i) → LabelVector J (n + 1))
    (hcap : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      OccupationCap (fixedDelta β₀ C₀ C₁) (labels X))
    (hplace : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      ∀ k ∈ otherParticles i, extendedSources (otherParticles i) X k ∈
        closure (meshCell J hJ (labels X k)))
    (a : MeshIndex J) (r : Fin 2) :
    ∃ L : ℝ≥0,
      ConfigurationPhysicalLipschitzOn L (CrossingLogistic.normalizerRatio hJ β a r)
        (closedOutsideProduct hJ i A B) ∧
      ConfigurationPhysicalLipschitzOn L
        (fun X ↦ CrossingLogistic.normalizerRatio hJ β a r (removeSite i X))
        (closedPatchProduct hJ A B) := by
  have hc (c : MeshIndex J) : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ c .cell
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) (fun _ _ ↦ 1) := by
    apply capped_sourceCalculus K hJ (Nat.succ_pos n) hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
      (otherParticles i) _ (isCompact_closedChart J _ _) (convex_closedChart J _ _)
      labels hcap hplace (fun _ ↦ β / (n + 1 : ℕ))
      (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) c .cell
    exact smoothOnChart_of_contDiff contDiff_const
  exact normalizerRatio_lipschitz_of_sourceCalculus hJ (by omega) i A B β a r
    (hc a) (hc (nextCell J hJ a r))

theorem cell_deleted_joint_lipschitz (η : LabelVector J (n + 1))
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed .cell)
      (torusFactor (configurationFactor i f) J (η i))) :
    ∃ Llog Lmean : ℝ≥0,
      ConfigurationPhysicalLipschitzOn Llog
        (fun X ↦ deletedOutsideLog hJ i d β (η i) .cell (removeSite i X))
        (closedPatchProduct hJ η (fun _ ↦ .cell)) ∧
      ConfigurationPhysicalLipschitzOn Lmean
        (fun X ↦ deletedOutsideMean hJ i d β (η i) .cell f (removeSite i X))
        (closedPatchProduct hJ η (fun _ ↦ .cell)) :=
  capped_deleted_joint_lipschitz K hJ hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh i
    η (fun _ ↦ .cell) (fun _ ↦ η) (fun _ _ ↦ hη)
    (fun _ hX ↦ cellChart_placement hJ (otherParticles i) η hX) d (η i) .cell f hf

/-- Both caps are retained and both orientations and wrap are included.
The sole adjacent coordinate can be the integrated coordinate itself. -/
theorem adjacent_deleted_joint_lipschitz (η : LabelVector J (n + 1))
    (i t : Fin (n + 1)) (r : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁)
      (Function.update η t (nextCell J hJ (η t) r)))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (adjacentChart (otherParticles i) η t r)
      (patchClosed (OneCoordinateConditionals.adjacentShapes t r i))
      (torusFactor (configurationFactor i f) J (η i))) :
    ∃ Llog Lmean : ℝ≥0,
      ConfigurationPhysicalLipschitzOn Llog
        (fun X ↦ deletedOutsideLog hJ i d β (η i)
          (OneCoordinateConditionals.adjacentShapes t r i) (removeSite i X))
        (closedPatchProduct hJ η (OneCoordinateConditionals.adjacentShapes t r)) ∧
      ConfigurationPhysicalLipschitzOn Lmean
        (fun X ↦ deletedOutsideMean hJ i d β (η i)
          (OneCoordinateConditionals.adjacentShapes t r i) f (removeSite i X))
        (closedPatchProduct hJ η (OneCoordinateConditionals.adjacentShapes t r)) := by
  obtain ⟨labels, hcap, hplace⟩ := exists_capped_labels_one_adjacent hJ (otherParticles i)
    (adjacentChart (otherParticles i) η t r) η t r (fixedDelta β₀ C₀ C₁) hη₀ hη₁
    (fun _ hX ↦ adjacentChart_cell_placement hJ (otherParticles i) η t r hX)
    (fun _ hX ht ↦ adjacentChart_edge_placement hJ (otherParticles i) η t r hX ht)
  exact capped_deleted_joint_lipschitz K hJ hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh i η
    (OneCoordinateConditionals.adjacentShapes t r) labels (fun X _ ↦ hcap X)
    (by simpa only [retained_adjacentChart] using hplace) d (η i)
    (OneCoordinateConditionals.adjacentShapes t r i) f
    (by simpa only [retained_adjacentChart] using hf)

end Capped

/-- An adjacent patch at the omitted coordinate leaves precisely the
cell source chart. The full product still retains its adjacent patch. -/
theorem integrated_adjacent_closedChart (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (r : Fin 2) :
    closedChart J (fun k : otherParticles i ↦ η k)
      (fun k ↦ OneCoordinateConditionals.adjacentShapes i r k) = cellChart (otherParticles i) η := by
  have hb : (fun k : otherParticles i ↦ OneCoordinateConditionals.adjacentShapes i r k) =
      fun _ ↦ Patch.cell := by
    funext k
    exact Function.update_of_ne ((mem_otherParticles i k).mp k.property) _ _
  rw [hb]
  rfl

section CrossingEndpoints

variable (K : MovingPoleIntegrability.KernelBounds) (hJ : 0 < J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)

include K hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh

/-- Actual conditional average over a specified cell, as an observable
on the full adjacent product. In particular c may be either endpoint cell.
The local smooth factor is the only observable-regularity assumption. -/
theorem twoCell_conditional_mean_lipschitz (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (r : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (_hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁)
      (Function.update η i (nextCell J hJ (η i) r)))
    (c : MeshIndex J) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed .cell)
      (torusFactor (configurationFactor i f) J c)) :
    ∃ L : ℝ≥0, ConfigurationPhysicalLipschitzOn L
      (fun X ↦ outsideMean hJ i β c .cell f (removeSite i X))
      (closedPatchProduct hJ η (OneCoordinateConditionals.adjacentShapes i r)) := by
  have hplace : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ η k)
      (fun k ↦ OneCoordinateConditionals.adjacentShapes i r k),
      ∀ k ∈ otherParticles i, extendedSources (otherParticles i) X k ∈
        closure (meshCell J hJ (η k)) := by
    intro X hX
    rw [integrated_adjacent_closedChart] at hX
    exact cellChart_placement hJ (otherParticles i) η hX
  obtain ⟨_, L, _, hL⟩ := capped_actual_joint_lipschitz K hJ hβ hβ₀ hC₀ hC₁
    hk₀ hk₁ hmesh i η (OneCoordinateConditionals.adjacentShapes i r) (fun _ ↦ η)
    (fun _ _ ↦ hη₀) hplace c .cell f
    (by simpa only [integrated_adjacent_closedChart] using hf)
  exact ⟨L, hL⟩

/-- Actual adjacent-cell probability q, on both the outside and full
physical closed products. Both completed-label caps are exposed; positivity
and the sigmoid representation are proved from the capped source calculus. -/
theorem twoCell_normalizerRatio_lipschitz (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (r : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (_hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁)
      (Function.update η i (nextCell J hJ (η i) r))) :
    ∃ L : ℝ≥0,
      ConfigurationPhysicalLipschitzOn L (CrossingLogistic.normalizerRatio hJ β (η i) r)
        (closedOutsideProduct hJ i η (OneCoordinateConditionals.adjacentShapes i r)) ∧
      ConfigurationPhysicalLipschitzOn L
        (fun X ↦ CrossingLogistic.normalizerRatio hJ β (η i) r (removeSite i X))
        (closedPatchProduct hJ η (OneCoordinateConditionals.adjacentShapes i r)) := by
  refine capped_normalizerRatio_lipschitz K hJ hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh i
    η (OneCoordinateConditionals.adjacentShapes i r) (fun _ ↦ η) (fun _ _ ↦ hη₀) ?_ (η i) r
  intro X hX
  rw [integrated_adjacent_closedChart] at hX
  exact cellChart_placement hJ (otherParticles i) η hX

end CrossingEndpoints

end PeriodicAttractiveLogGas.ConditionalSourceLipschitz
