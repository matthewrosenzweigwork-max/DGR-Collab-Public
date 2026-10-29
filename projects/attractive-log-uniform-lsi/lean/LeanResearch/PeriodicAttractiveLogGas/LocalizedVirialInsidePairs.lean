import LeanResearch.PeriodicAttractiveLogGas.CollectiveSecondMoment
import Mathlib.Tactic.Module

/-! The actual inside-pair contribution in source `prop:localized-virial`.
The Green field and the collective field are the previously constructed
ordinary fields. The local radial inequality, the barycentric difference,
and the annulus-supported error are derived here before finite summation.
Development checks and source review have separate statuses in
`research/reviews/localized-virial-inside-pairs-development.md`. -/

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace PeriodicAttractiveLogGas.LocalizedVirialInsidePairs

open LocalizedVirialCutoffs SeparatedRadius CollectiveSecondMoment HeavyScales

/-- The literal ordered inside-pair sum, excluding only equal labels. -/
def insidePairSum {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
        torusEuclideanDist (X j) ξ < 4 * s then
      inner ℝ (greenGradient (X i - X j)) (G ξ s X (X i) - G ξ s X (X j))
    else 0

/-- Source `eq:radial-green`, obtained from the actual ordinary differential.
The positive quadratic term is retained in the identity and discarded only
in the lower bound. -/
theorem radial_green_lower_bound {u : PlanarSpace} (hu : ‖u‖ ≤ 1 / 4)
    (hne : u ≠ 0) :
    -1 - remainderGradientBound * ‖u‖ ≤ inner ℝ (greenGradient (torusQuotient u)) u := by
  have hbox := mem_centeredOpenBox_of_norm_lt_half (show ‖u‖ < 1 / 2 by linarith)
  have hoff := mem_offIntegerLattice_of_mem_centeredOpenBox hbox hne
  have hn : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
  have hr : |fderiv ℝ smoothGreenLogRemainder u u| ≤ remainderGradientBound * ‖u‖ := by
    calc
      _ ≤ ‖fderiv ℝ smoothGreenLogRemainder u‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs] using (fderiv ℝ smoothGreenLogRemainder u).le_opNorm u
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (remainder_gradient_norm_le (mem_closedBall_zero_iff.mpr hu)) (norm_nonneg u)
  rw [greenGradient_inner, greenDifferential_lift_of_mem hoff,
    fderiv_smoothGreenLift_local hbox hne]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
    real_inner_self_eq_norm_sq]
  rw [neg_mul, inv_mul_cancel₀ hn]
  have hq : 0 ≤ Real.pi * ‖u‖ ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg _)
  linarith [(abs_le.mp hr).1]

theorem quotient_chart_sub (ξ z w : Torus) :
    torusQuotient (chartPosition ξ z - chartPosition ξ w) = z - w := by
  rw [torusQuotient_sub, quotient_chartPosition, quotient_chartPosition]
  abel

theorem norm_chart_sub_lt {s : ℝ} (ξ z w : Torus)
    (hz : torusEuclideanDist z ξ < 4 * s) (hw : torusEuclideanDist w ξ < 4 * s) :
    ‖chartPosition ξ z - chartPosition ξ w‖ < 8 * s := by
  have h := norm_sub_le (chartPosition ξ z) (chartPosition ξ w)
  rw [norm_chartPosition, norm_chartPosition] at h
  linarith

theorem chart_sub_ne_zero (ξ : Torus) {z w : Torus} (hne : z ≠ w) :
    chartPosition ξ z - chartPosition ξ w ≠ 0 := by
  intro h
  have he := congrArg torusQuotient h
  rw [quotient_chart_sub, torusQuotient_zero] at he
  exact hne (sub_eq_zero.mp he)

theorem inside_radial_lower_bound {s : ℝ} (hsmall : s ≤ 1 / 64) (ξ : Torus)
    {z w : Torus} (hne : z ≠ w)
    (hz : torusEuclideanDist z ξ < 4 * s) (hw : torusEuclideanDist w ξ < 4 * s) :
    -(1 + 8 * remainderGradientBound * s) ≤
      inner ℝ (greenGradient (z - w)) (chartPosition ξ z - chartPosition ξ w) := by
  have hn := norm_chart_sub_lt ξ z w hz hw
  have h := radial_green_lower_bound (show ‖chartPosition ξ z - chartPosition ξ w‖ ≤ 1 / 4 by
    linarith) (chart_sub_ne_zero ξ hne)
  rw [quotient_chart_sub] at h
  have hb := mul_le_mul_of_nonneg_left hn.le remainderGradientBound_nonneg
  linarith

theorem phi_chart_lipschitz {s : ℝ} (hs : 0 < s) (ξ z w : Torus) :
    |phi ξ s z - phi ξ s w| ≤ (1 / s) * ‖chartPosition ξ z - chartPosition ξ w‖ := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set PlanarSpace)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ (contDiff_phiEuclidean hs).differentiable (by norm_num) y)
    (fun y _ ↦ norm_fderiv_phiEuclidean_le hs y)
    (Set.mem_univ (chartPosition ξ w)) (Set.mem_univ (chartPosition ξ z))
  simpa only [phiEuclidean_chart, Real.norm_eq_abs] using h

/-- The two genuine error fields in the source barycentric decomposition. -/
def pairRemainder {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (z w : Torus) : PlanarSpace :=
  (2 * mass ξ s X / (N : ℝ) * (phi ξ s z - phi ξ s w)) •
      ((1 / 2 : ℝ) • (chartPosition ξ z + chartPosition ξ w) - barycenter ξ s X) +
    (1 / (N : ℝ)) •
      (firstSummand ξ s X (chartPosition ξ z) - firstSummand ξ s X (chartPosition ξ w))

theorem G_sub_decomposition {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (hM : 0 < mass ξ s X) (z w : Torus) :
    G ξ s X z - G ξ s X w =
      (2 * mass ξ s X / (N : ℝ) * ((phi ξ s z + phi ξ s w) / 2)) •
        (chartPosition ξ z - chartPosition ξ w) + pairRemainder ξ s X z w := by
  rw [G_formula_barycenter ξ s X hM, G_formula_barycenter ξ s X hM]
  unfold pairRemainder firstSummand
  module

theorem norm_midpoint_sub_barycenter_le {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (hM : 0 < mass ξ s X) (z w : Torus)
    (hz : torusEuclideanDist z ξ ≤ 4 * s) (hw : torusEuclideanDist w ξ ≤ 4 * s) :
    ‖(1 / 2 : ℝ) • (chartPosition ξ z + chartPosition ξ w) - barycenter ξ s X‖ ≤ 8 * s := by
  apply norm_sub_barycenter_le hs ξ X hM
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := norm_add_le (chartPosition ξ z) (chartPosition ξ w)
  rw [norm_chartPosition, norm_chartPosition] at h
  linarith

theorem norm_pairRemainder_le {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (hM : 0 < mass ξ s X) (z w : Torus)
    (hz : torusEuclideanDist z ξ ≤ 4 * s) (hw : torusEuclideanDist w ξ ≤ 4 * s) :
    ‖pairRemainder ξ s X z w‖ ≤
      (160 * mass ξ s X / (N : ℝ)) * ‖chartPosition ξ z - chartPosition ξ w‖ := by
  have hN : 0 ≤ (1 / (N : ℝ)) := by positivity
  have hc : 0 ≤ 2 * mass ξ s X / (N : ℝ) := by positivity
  have hφ := phi_chart_lipschitz hs ξ z w
  have hm := norm_midpoint_sub_barycenter_le hs ξ X hM z w hz hw
  have hf := firstSummand_lipschitz hs ξ X (chartPosition ξ z) (chartPosition ξ w)
  unfold pairRemainder
  calc
    _ ≤ ‖(2 * mass ξ s X / (N : ℝ) * (phi ξ s z - phi ξ s w)) •
        ((1 / 2 : ℝ) • (chartPosition ξ z + chartPosition ξ w) - barycenter ξ s X)‖ +
        ‖(1 / (N : ℝ)) • (firstSummand ξ s X (chartPosition ξ z) -
          firstSummand ξ s X (chartPosition ξ w))‖ := norm_add_le _ _
    _ = (2 * mass ξ s X / (N : ℝ)) * |phi ξ s z - phi ξ s w| *
        ‖(1 / 2 : ℝ) • (chartPosition ξ z + chartPosition ξ w) - barycenter ξ s X‖ +
        (1 / (N : ℝ)) * ‖firstSummand ξ s X (chartPosition ξ z) -
          firstSummand ξ s X (chartPosition ξ w)‖ := by
      rw [norm_smul, norm_smul, norm_mul, Real.norm_of_nonneg hc,
        Real.norm_of_nonneg hN, Real.norm_eq_abs]
    _ ≤ (2 * mass ξ s X / (N : ℝ)) * ((1 / s) *
        ‖chartPosition ξ z - chartPosition ξ w‖) * (8 * s) +
        (1 / (N : ℝ)) * (144 * mass ξ s X * ‖chartPosition ξ z - chartPosition ξ w‖) :=
      add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hφ hc) hm (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hf hN)
    _ = _ := by field_simp [hs.ne']; ring

theorem pairRemainder_eq_zero_inner {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (z w : Torus)
    (hz : torusEuclideanDist z ξ ≤ 2 * s) (hw : torusEuclideanDist w ξ ≤ 2 * s) :
    pairRemainder ξ s X z w = 0 := by
  have hz' : ‖chartPosition ξ z‖ ≤ 2 * s := by simpa only [norm_chartPosition] using hz
  have hw' : ‖chartPosition ξ w‖ ≤ 2 * s := by simpa only [norm_chartPosition] using hw
  simp only [pairRemainder, firstSummand, phi_eq_one hs hz, phi_eq_one hs hw,
    sub_self, mul_zero, zero_smul, phiGradientEuclidean_eq_zero_inner hs hz',
    phiGradientEuclidean_eq_zero_inner hs hw', smul_zero, add_zero]

theorem abs_green_pairRemainder_le {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N)
    (hM : 0 < mass ξ s X) {z w : Torus} (hne : z ≠ w)
    (hz : torusEuclideanDist z ξ ≤ 4 * s) (hw : torusEuclideanDist w ξ ≤ 4 * s) :
    |inner ℝ (greenGradient (z - w)) (pairRemainder ξ s X z w)| ≤
      160 * ConditionalLawEstimates.kernelConstant * mass ξ s X / (N : ℝ) := by
  have hN' : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hd : ‖chartPosition ξ z - chartPosition ξ w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (chart_sub_ne_zero ξ hne)
  have hk := ConditionalLawEstimates.kernel_gradient_bound (z - w) (sub_ne_zero.mpr hne)
  change ‖greenGradient (z - w)‖ ≤
    ConditionalLawEstimates.kernelConstant / torusEuclideanDist z w at hk
  rw [← chart_pair_distance hsmall ξ z w hz hw] at hk
  calc
    _ ≤ ‖greenGradient (z - w)‖ * ‖pairRemainder ξ s X z w‖ := abs_real_inner_le_norm _ _
    _ ≤ (ConditionalLawEstimates.kernelConstant / ‖chartPosition ξ z - chartPosition ξ w‖) *
        ((160 * mass ξ s X / (N : ℝ)) * ‖chartPosition ξ z - chartPosition ξ w‖) :=
      mul_le_mul hk (norm_pairRemainder_le hs ξ X hM z w hz hw) (norm_nonneg _)
        (div_nonneg ConditionalLawEstimates.kernelConstant_pos.le (norm_nonneg _))
    _ = _ := by field_simp [hN', hd]

/-- Pointwise inside-pair estimate. The error is supported on the union of
the two strict annulus events, with the full plateau boundary included in
the zero-error case. -/
theorem inside_pair_lower_bound {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N)
    (hM : 0 < mass ξ s X) {z w : Torus} (hne : z ≠ w)
    (hz : torusEuclideanDist z ξ < 4 * s) (hw : torusEuclideanDist w ξ < 4 * s) :
    -(2 * mass ξ s X / (N : ℝ) * (1 + 8 * remainderGradientBound * s)) *
        ((phi ξ s z + phi ξ s w) / 2) -
      (160 * ConditionalLawEstimates.kernelConstant * mass ξ s X / (N : ℝ)) *
        (if (2 * s < torusEuclideanDist z ξ ∧ torusEuclideanDist z ξ < 4 * s) ∨
            (2 * s < torusEuclideanDist w ξ ∧ torusEuclideanDist w ξ < 4 * s)
          then 1 else 0) ≤
      inner ℝ (greenGradient (z - w)) (G ξ s X z - G ξ s X w) := by
  have hc : 0 ≤ 2 * mass ξ s X / (N : ℝ) * ((phi ξ s z + phi ξ s w) / 2) := by
    exact mul_nonneg (by positivity) (div_nonneg
      (add_nonneg (phi_mem_Icc ξ s z).1 (phi_mem_Icc ξ s w).1) (by norm_num))
  have hm := mul_le_mul_of_nonneg_left (inside_radial_lower_bound hsmall ξ hne hz hw) hc
  have he :
      -(160 * ConditionalLawEstimates.kernelConstant * mass ξ s X / (N : ℝ)) *
        (if (2 * s < torusEuclideanDist z ξ ∧ torusEuclideanDist z ξ < 4 * s) ∨
            (2 * s < torusEuclideanDist w ξ ∧ torusEuclideanDist w ξ < 4 * s)
          then 1 else 0) ≤
        inner ℝ (greenGradient (z - w)) (pairRemainder ξ s X z w) := by
    split_ifs with ha
    · simpa only [mul_one] using
        (abs_le.mp (abs_green_pairRemainder_le hN hs hsmall ξ X hM hne hz.le hw.le)).1
    · have hz' : torusEuclideanDist z ξ ≤ 2 * s := by
        by_contra h
        exact ha (Or.inl ⟨lt_of_not_ge h, hz⟩)
      have hw' : torusEuclideanDist w ξ ≤ 2 * s := by
        by_contra h
        exact ha (Or.inr ⟨lt_of_not_ge h, hw⟩)
      simp only [pairRemainder_eq_zero_inner hs ξ X z w hz' hw', inner_zero_right, mul_zero,
        le_refl]
  rw [G_sub_decomposition ξ s X hM, inner_add_right, inner_smul_right]
  nlinarith only [hm, he]

/-- The source ordered weighted count, before any particle-number bound.
The diagonal removes exactly one copy of the actual mass. -/
theorem ordered_weight_sum {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) :
    (∑ i : Fin N, ∑ j : Fin N,
      if i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
          torusEuclideanDist (X j) ξ < 4 * s then
        (phi ξ s (X i) + phi ξ s (X j)) / 2 else 0) =
      mass ξ s X * ((ballCount ξ (4 * s) X : ℝ) - 1) := by
  classical
  have hzero (i : Fin N) (hi : ¬torusEuclideanDist (X i) ξ < 4 * s) :
      phi ξ s (X i) = 0 := phi_eq_zero hs (le_of_not_gt hi)
  have hp (i j : Fin N) :
      (if i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
          torusEuclideanDist (X j) ξ < 4 * s then
        (phi ξ s (X i) + phi ξ s (X j)) / 2 else 0) =
      (phi ξ s (X i) * (if torusEuclideanDist (X j) ξ < 4 * s then 1 else 0) +
        (if torusEuclideanDist (X i) ξ < 4 * s then 1 else 0) * phi ξ s (X j)) / 2 -
        (if i = j then phi ξ s (X i) else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hi : torusEuclideanDist (X i) ξ < 4 * s
      · simp [hi]
      · simp [hi, hzero i hi]
    · by_cases hi : torusEuclideanDist (X i) ξ < 4 * s
      · by_cases hj : torusEuclideanDist (X j) ξ < 4 * s
        · simp [hij, hi, hj]
        · simp [hij, hi, hj, hzero j hj]
      · simp [hij, hi, hzero i hi]
  simp_rw [hp]
  rw [ballCount_real_eq, mass]
  simp only [div_eq_mul_inv, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The actual number of ordered inside pairs meeting the annulus is at
most twice the annulus count times the inside-ball count. Equal labels are
still excluded on the left. No replacement of the inside count by N occurs. -/
theorem ordered_annulus_pairs_le {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) :
    (∑ i : Fin N, ∑ j : Fin N,
      if i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
          torusEuclideanDist (X j) ξ < 4 * s then
        (if (2 * s < torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < 4 * s) ∨
            (2 * s < torusEuclideanDist (X j) ξ ∧ torusEuclideanDist (X j) ξ < 4 * s)
          then (1 : ℝ) else 0) else 0) ≤
      2 * (annulusCount ξ s X : ℝ) * (ballCount ξ (4 * s) X : ℝ) := by
  classical
  let a (i : Fin N) : ℝ := if 2 * s < torusEuclideanDist (X i) ξ ∧
      torusEuclideanDist (X i) ξ < 4 * s then 1 else 0
  let b (i : Fin N) : ℝ := if torusEuclideanDist (X i) ξ < 4 * s then 1 else 0
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (a i * b j + b i * a j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
          torusEuclideanDist (X j) ξ < 4 * s
      · rw [ite_eq_left hij]
        have hbi : b i = 1 := ite_eq_left hij.2.1
        have hbj : b j = 1 := ite_eq_left hij.2.2
        rw [hbi, hbj, mul_one, one_mul]
        by_cases hi : 2 * s < torusEuclideanDist (X i) ξ ∧
            torusEuclideanDist (X i) ξ < 4 * s
        · have hai : a i = 1 := ite_eq_left hi
          rw [ite_eq_left (Or.inl hi), hai]
          have haj : 0 ≤ a j := by
            dsimp [a]
            split_ifs <;> norm_num
          linarith
        · have hai : a i = 0 := ite_eq_right hi
          by_cases hj : 2 * s < torusEuclideanDist (X j) ξ ∧
              torusEuclideanDist (X j) ξ < 4 * s
          · have haj : a j = 1 := ite_eq_left hj
            rw [ite_eq_left (Or.inr hj), hai, haj]
            norm_num
          · have haj : a j = 0 := ite_eq_right hj
            rw [ite_eq_right (not_or.mpr ⟨hi, hj⟩), hai, haj]
            norm_num
      · rw [ite_eq_right hij]
        dsimp [a, b]
        positivity
    _ = _ := by
      rw [annulusCount_real_eq hs, ballCount_real_eq]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      dsimp [a, b]
      ring

/-- Exact inside-count estimate for the actual ordered sum. The error still
retains N2 here; the bound by N belongs only to the final drift theorem. -/
theorem insidePairSum_lower {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N)
    (hM : 0 < mass ξ s X) (hX : Function.Injective X) :
    -(2 * mass ξ s X / (N : ℝ) * (1 + 8 * remainderGradientBound * s)) *
        (mass ξ s X * ((ballCount ξ (4 * s) X : ℝ) - 1)) -
      (160 * ConditionalLawEstimates.kernelConstant * mass ξ s X / (N : ℝ)) *
        (2 * (annulusCount ξ s X : ℝ) * (ballCount ξ (4 * s) X : ℝ)) ≤
      insidePairSum ξ s X := by
  classical
  let c := 2 * mass ξ s X / (N : ℝ) * (1 + 8 * remainderGradientBound * s)
  let e := 160 * ConditionalLawEstimates.kernelConstant * mass ξ s X / (N : ℝ)
  let w (i j : Fin N) : ℝ :=
    if i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
        torusEuclideanDist (X j) ξ < 4 * s then
      (phi ξ s (X i) + phi ξ s (X j)) / 2 else 0
  let a (i j : Fin N) : ℝ :=
    if i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
        torusEuclideanDist (X j) ξ < 4 * s then
      (if (2 * s < torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < 4 * s) ∨
          (2 * s < torusEuclideanDist (X j) ξ ∧ torusEuclideanDist (X j) ξ < 4 * s)
        then 1 else 0) else 0
  have hsum : (∑ i : Fin N, ∑ j : Fin N, (-c * w i j - e * a i j)) ≤
      insidePairSum ξ s X := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i ≠ j ∧ torusEuclideanDist (X i) ξ < 4 * s ∧
        torusEuclideanDist (X j) ξ < 4 * s
    · have hne : X i ≠ X j := fun h ↦ hij.1 (hX h)
      simpa only [w, a, ite_eq_left hij, c, e] using
        inside_pair_lower_bound hN hs hsmall ξ X hM hne hij.2.1 hij.2.2
    · simp only [w, a, hij, ite_false, mul_zero, sub_zero, le_refl]
  have hw : (∑ i : Fin N, ∑ j : Fin N, w i j) =
      mass ξ s X * ((ballCount ξ (4 * s) X : ℝ) - 1) := ordered_weight_sum hs ξ X
  have ha : (∑ i : Fin N, ∑ j : Fin N, a i j) ≤
      2 * (annulusCount ξ s X : ℝ) * (ballCount ξ (4 * s) X : ℝ) :=
    ordered_annulus_pairs_le hs ξ X
  have he : 0 ≤ e := by
    dsimp [e]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      ConditionalLawEstimates.kernelConstant_pos.le) hM.le) (Nat.cast_nonneg N)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hw] at hsum
  have herror := mul_le_mul_of_nonneg_left ha he
  change -c * (mass ξ s X * ((ballCount ξ (4 * s) X : ℝ) - 1)) -
    e * (2 * (annulusCount ξ s X : ℝ) * (ballCount ξ (4 * s) X : ℝ)) ≤ _
  linarith only [hsum, herror]

/-- The complete source inside-pair drift estimate. It retains the original
particle number, the actual C_h and C1, and includes beta zero. Injectivity
is used only for distinct-label Green evaluations. -/
theorem insidePairSum_drift_lower {N : ℕ} (hN : 0 < N) {s β : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hβ : 0 ≤ β) (ξ : Torus) (X : Configuration N)
    (hM : 0 < mass ξ s X) (hX : Function.Injective X) :
    -(β * mass ξ s X ^ 2 / (N : ℝ) ^ 2 *
        (1 + 8 * remainderGradientBound * s) * ((ballCount ξ (4 * s) X : ℝ) - 1)) -
      160 * β * ConditionalLawEstimates.kernelConstant * (mass ξ s X / (N : ℝ)) *
        (annulusCount ξ s X : ℝ) ≤
      β / (2 * (N : ℝ)) * insidePairSum ξ s X := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hcount : (ballCount ξ (4 * s) X : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast ballCount_le_N ξ (4 * s) X
  have herr :
      (160 * ConditionalLawEstimates.kernelConstant * mass ξ s X / (N : ℝ)) *
        (2 * (annulusCount ξ s X : ℝ) * (ballCount ξ (4 * s) X : ℝ)) ≤
      (320 * ConditionalLawEstimates.kernelConstant * mass ξ s X) * (annulusCount ξ s X : ℝ) := by
    have hc : 0 ≤ 320 * ConditionalLawEstimates.kernelConstant * mass ξ s X *
        (annulusCount ξ s X : ℝ) / (N : ℝ) := by
      apply div_nonneg _ hNpos.le
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        ConditionalLawEstimates.kernelConstant_pos.le) hM.le) (Nat.cast_nonneg _)
    calc
      _ = (320 * ConditionalLawEstimates.kernelConstant * mass ξ s X *
          (annulusCount ξ s X : ℝ) / (N : ℝ)) * (ballCount ξ (4 * s) X : ℝ) := by ring
      _ ≤ (320 * ConditionalLawEstimates.kernelConstant * mass ξ s X *
          (annulusCount ξ s X : ℝ) / (N : ℝ)) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hcount hc
      _ = _ := by rw [div_mul_cancel₀ _ hNne]
  have hraw := insidePairSum_lower hN hs hsmall ξ X hM hX
  have hbound :
      -(2 * mass ξ s X / (N : ℝ) * (1 + 8 * remainderGradientBound * s)) *
          (mass ξ s X * ((ballCount ξ (4 * s) X : ℝ) - 1)) -
        (320 * ConditionalLawEstimates.kernelConstant * mass ξ s X) * (annulusCount ξ s X : ℝ) ≤
      insidePairSum ξ s X := by linarith only [hraw, herr]
  have hscaled := mul_le_mul_of_nonneg_left hbound
    (div_nonneg hβ (show 0 ≤ 2 * (N : ℝ) by positivity))
  convert hscaled using 1
  field_simp [hNne]
  ring

end PeriodicAttractiveLogGas.LocalizedVirialInsidePairs
