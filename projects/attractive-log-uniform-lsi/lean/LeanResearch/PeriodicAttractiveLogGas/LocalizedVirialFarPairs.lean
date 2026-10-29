import LeanResearch.PeriodicAttractiveLogGas.CollectiveSecondMoment
import LeanResearch.PeriodicAttractiveLogGas.GreenCovarianceBounds

/-! The actual far-pair term in the localized virial calculation, source
lines 1251--1268. The Green-gradient difference is derived from its Hessian
on a separated lifted ball. The finite-particle cancellation is the proved
sum estimate for the actual field G. Both ordered orientations and the
closed exterior boundary are retained. Development and central checks are
recorded in `research/reviews/localized-virial-far-pairs-development.md`.
-/

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators RealInnerProductSpace

namespace PeriodicAttractiveLogGas.LocalizedVirialFarPairs

open CollectiveSecondMoment SeparatedRadius CollectiveIntegrationByParts
  GreenFarOscillation GreenGradientOscillation

/-- Every point of the lifted inner ball stays separated from the actual
exterior particle, with no choice of a lift for that exterior particle. -/
theorem lifted_ball_separation {s K : ℝ} (ξ y : Torus)
    (hy : K * s ≤ torusEuclideanDist y ξ) {u : PlanarSpace}
    (hu : ‖u‖ ≤ 4 * s) :
    (K - 4) * s ≤ torusEuclideanNorm (torusQuotient u + ξ - y) := by
  have ht := torusEuclideanDist_triangle y (torusQuotient u + ξ) ξ
  rw [torusEuclideanDist_comm y (torusQuotient u + ξ)] at ht
  have hq : torusEuclideanDist (torusQuotient u + ξ) ξ ≤ ‖u‖ := by
    simpa only [torusEuclideanDist, add_sub_cancel_right] using
      torusEuclideanNorm_quotient_le u
  change torusEuclideanDist y ξ ≤
    torusEuclideanNorm (torusQuotient u + ξ - y) +
      torusEuclideanDist (torusQuotient u + ξ) ξ at ht
  nlinarith

theorem inner_far_sub_ne_zero {s K : ℝ} (hs : 0 < s) (hK : 4 < K)
    (ξ : Torus) {z y : Torus} (hz : torusEuclideanDist z ξ ≤ 4 * s)
    (hy : K * s ≤ torusEuclideanDist y ξ) : z - y ≠ 0 := by
  intro h
  have hzy := sub_eq_zero.mp h
  rw [hzy] at hz
  nlinarith

private theorem translated_gradient_derivative (ξ y : Torus) {u : PlanarSpace}
    (hu : torusQuotient u + ξ - y ≠ 0) :
    HasFDerivAt (fun v : PlanarSpace ↦ greenGradient (torusQuotient v + ξ - y))
      (greenHessianOperator (torusQuotient u + ξ - y)) u := by
  have hq (v : PlanarSpace) :
      torusQuotient (RectangleDilation.affine (centeredLift ξ) 1 v) =
        torusQuotient v + ξ := by
    simp only [RectangleDilation.affine, inv_one, one_smul, torusQuotient_add,
      torusQuotient_centeredLift, add_comm]
  have hd := hasFDerivAt_referenceGradient (centeredLift ξ) 1 y
    (by simpa only [hq] using hu)
  have hf : referenceGradient (centeredLift ξ) 1 y =
      (fun v : PlanarSpace ↦ greenGradient (torusQuotient v + ξ - y)) := by
    funext v
    simp only [referenceGradient, hq]
  rw [hf] at hd
  simpa only [hq, inv_one, one_smul] using hd

/-- The source difference estimate follows from the actual derivative and
Hessian bound along the whole Euclidean segment, including its center. -/
theorem green_gradient_oscillation {s K C₂ : ℝ} (hs : 0 < s) (hK : 4 < K)
    (hC₂ : 0 ≤ C₂) (hk : KernelHessianBound C₂) (ξ : Torus)
    {z y : Torus} (hz : torusEuclideanDist z ξ ≤ 4 * s)
    (hy : K * s ≤ torusEuclideanDist y ξ) :
    ‖greenGradient (z - y) - greenGradient (ξ - y)‖ ≤
      4 * C₂ / ((K - 4) ^ 2 * s) := by
  let F : PlanarSpace → PlanarSpace :=
    fun u ↦ greenGradient (torusQuotient u + ξ - y)
  have hR : 0 < (K - 4) * s := mul_pos (sub_pos.mpr hK) hs
  have hsep (u : PlanarSpace) (hu : u ∈ Metric.closedBall 0 (4 * s)) :
      (K - 4) * s ≤ torusEuclideanNorm (torusQuotient u + ξ - y) :=
    lifted_ball_separation ξ y hy (by simpa only [Metric.mem_closedBall, dist_zero_right] using hu)
  have hne (u : PlanarSpace) (hu : u ∈ Metric.closedBall 0 (4 * s)) :
      torusQuotient u + ξ - y ≠ 0 := by
    intro he
    have hh := hsep u hu
    rw [he, torusEuclideanNorm_zero] at hh
    linarith
  have hd (u : PlanarSpace) (hu : u ∈ Metric.closedBall 0 (4 * s)) :
      HasFDerivAt F (greenHessianOperator (torusQuotient u + ξ - y)) u :=
    translated_gradient_derivative ξ y (hne u hu)
  have hb (u : PlanarSpace) (hu : u ∈ Metric.closedBall 0 (4 * s)) :
      ‖fderiv ℝ F u‖ ≤ C₂ / ((K - 4) * s) ^ 2 := by
    rw [(hd u hu).fderiv]
    have hh := norm_scaled_hessian_le (J := 1) (R := (K - 4) * s)
      (by norm_num) hR hC₂ hk (by simpa only [div_one] using hsep u hu)
    simpa only [inv_one, one_smul, mul_one] using hh
  have h0 : (0 : PlanarSpace) ∈ Metric.closedBall 0 (4 * s) := by
    simp only [Metric.mem_closedBall, dist_self]
    positivity
  have hz' : chartPosition ξ z ∈ Metric.closedBall 0 (4 * s) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_chartPosition] using hz
  have hm := (convex_closedBall (0 : PlanarSpace) (4 * s)).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu ↦ (hd u hu).differentiableAt) hb h0 hz'
  have hF0 : F 0 = greenGradient (ξ - y) := by simp [F]
  have hFz : F (chartPosition ξ z) = greenGradient (z - y) := by
    dsimp [F]
    rw [quotient_chartPosition, sub_add_cancel]
  rw [hF0, hFz, sub_zero, norm_chartPosition] at hm
  calc
    _ ≤ (C₂ / ((K - 4) * s) ^ 2) * torusEuclideanDist z ξ := hm
    _ ≤ (C₂ / ((K - 4) * s) ^ 2) * (4 * s) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by field_simp [hs.ne', (sub_pos.mpr hK).ne']

theorem norm_greenGradient_center_le {s K C₁ : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hC₁ : 0 ≤ C₁) (hk : KernelGradientBound C₁) (ξ : Torus)
    {y : Torus} (hy : K * s ≤ torusEuclideanDist y ξ) :
    ‖greenGradient (ξ - y)‖ ≤ C₁ / (K * s) := by
  have hsep : K * s ≤ torusEuclideanNorm (ξ - y) := by
    change K * s ≤ torusEuclideanDist ξ y
    rw [torusEuclideanDist_comm]
    exact hy
  have hne : ξ - y ≠ 0 := by
    intro hz
    rw [hz, torusEuclideanNorm_zero] at hsep
    exact (not_le_of_gt (mul_pos hK hs)) hsep
  exact (hk _ hne).trans
    (div_le_div_of_nonneg_left hC₁ (mul_pos hK hs) hsep)

/-- The actual inner particle sum for one fixed exterior position. The
strict support ball counts labeled particles, including repeated positions. -/
def fixedFarSum {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (y : Torus) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s),
    inner ℝ (greenGradient (X i - y)) (G ξ s X (X i))

/-- The zero extension identifies the restricted sum with the full sum to
which the already proved source cancellation applies. -/
theorem inner_sum_G_eq_sum {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s),
      G ξ s X (X i)) = ∑ i : Fin N, G ξ s X (X i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : torusEuclideanDist (X i) ξ < 4 * s
  · simp only [hi, ite_true]
  · simp only [hi, ite_false, G_eq_zero_outer hs ξ X (le_of_not_gt hi)]

theorem fixedFarSum_centered {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) (y : Torus) :
    fixedFarSum ξ s X y =
      (∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s),
        inner ℝ (greenGradient (X i - y) - greenGradient (ξ - y))
          (G ξ s X (X i))) +
      inner ℝ (greenGradient (ξ - y)) (∑ i : Fin N, G ξ s X (X i)) := by
  rw [← inner_sum_G_eq_sum hs ξ X, inner_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sub_left]
  ring

/-- Exact fixed-exterior-particle estimate in source lines 1259--1262.
Both displayed constants come from actual earlier quantitative bounds. -/
theorem abs_fixedFarSum_le {N : ℕ} (hN : 0 < N) {s K C₁ C₂ : ℝ}
    (hs : 0 < s) (hK : 4 < K) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hk₁ : KernelGradientBound C₁) (hk₂ : KernelHessianBound C₂)
    (ξ : Torus) (X : Configuration N) {y : Torus}
    (hy : K * s ≤ torusEuclideanDist y ξ) :
    |fixedFarSum ξ s X y| ≤ (mass ξ s X / N) *
      (320 * C₂ / (K - 4) ^ 2 * (ballCount ξ (4 * s) X : ℝ) +
        64 * C₁ / K * (annulusCount ξ s X : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hKpos : 0 < K := lt_trans (by norm_num) hK
  have hM := mass_nonneg ξ s X
  have hvar :
      |∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s),
        inner ℝ (greenGradient (X i - y) - greenGradient (ξ - y))
          (G ξ s X (X i))| ≤
      320 * C₂ * mass ξ s X * (ballCount ξ (4 * s) X : ℝ) /
        ((K - 4) ^ 2 * N) := by
    calc
      _ ≤ ∑ i ∈ Finset.univ.filter
          (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s),
          |inner ℝ (greenGradient (X i - y) - greenGradient (ξ - y))
            (G ξ s X (X i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.univ.filter
          (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s),
          (4 * C₂ / ((K - 4) ^ 2 * s)) * (80 * s * mass ξ s X / N) := by
        apply Finset.sum_le_sum
        intro i hi
        have hinner := (Finset.mem_filter.mp hi).2
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (green_gradient_oscillation hs hK hC₂ hk₂ ξ hinner.le hy)
            (norm_G_le hs ξ X (X i)) (norm_nonneg _) (by positivity))
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        change (ballCount ξ (4 * s) X : ℝ) *
          ((4 * C₂ / ((K - 4) ^ 2 * s)) * (80 * s * mass ξ s X / N)) = _
        field_simp [hs.ne', hNr.ne', (sub_pos.mpr hK).ne']
        ring
  have hconst :
      |inner ℝ (greenGradient (ξ - y)) (∑ i : Fin N, G ξ s X (X i))| ≤
      64 * C₁ * mass ξ s X * (annulusCount ξ s X : ℝ) / (K * N) := by
    calc
      _ ≤ ‖greenGradient (ξ - y)‖ * ‖∑ i : Fin N, G ξ s X (X i)‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (C₁ / (K * s)) *
          (64 * s * mass ξ s X * (annulusCount ξ s X : ℝ) / N) :=
        mul_le_mul (norm_greenGradient_center_le hs hKpos hC₁ hk₁ ξ hy)
          (norm_sum_G_le hs ξ X) (norm_nonneg _) (by positivity)
      _ = _ := by field_simp [hs.ne', hKpos.ne', hNr.ne']
  rw [fixedFarSum_centered hs ξ X y]
  calc
    _ ≤ |∑ i ∈ Finset.univ.filter
          (fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s),
          inner ℝ (greenGradient (X i - y) - greenGradient (ξ - y))
            (G ξ s X (X i))| +
        |inner ℝ (greenGradient (ξ - y)) (∑ i : Fin N, G ξ s X (X i))| :=
      abs_add_le _ _
    _ ≤ 320 * C₂ * mass ξ s X * (ballCount ξ (4 * s) X : ℝ) /
          ((K - 4) ^ 2 * N) +
        64 * C₁ * mass ξ s X * (annulusCount ξ s X : ℝ) / (K * N) :=
      add_le_add hvar hconst
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The independently chosen global kernel constants discharge both generic
kernel premises, with no dependence on particles or the configuration. -/
theorem abs_fixedFarSum_le_constants {N : ℕ} (hN : 0 < N) {s K : ℝ}
    (hs : 0 < s) (hK : 4 < K) (ξ : Torus) (X : Configuration N) {y : Torus}
    (hy : K * s ≤ torusEuclideanDist y ξ) :
    |fixedFarSum ξ s X y| ≤ (mass ξ s X / N) *
      (320 * GreenCovarianceBounds.hessianConstant / (K - 4) ^ 2 *
          (ballCount ξ (4 * s) X : ℝ) +
        64 * ConditionalLawEstimates.kernelConstant / K *
          (annulusCount ξ s X : ℝ)) :=
  abs_fixedFarSum_le hN hs hK ConditionalLawEstimates.kernelConstant_pos.le
    GreenCovarianceBounds.hessianConstant_pos.le ConditionalLawEstimates.kernel_gradient_bound
    GreenCovarianceBounds.kernel_hessian_bound ξ X hy

/-- The literal two-orientation part of the manuscript's ordered drift.
The exterior predicate includes the boundary of the shell. -/
def orderedFarSum {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    if (torusEuclideanDist (X i) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X j) ξ) ∨
        (torusEuclideanDist (X j) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X i) ξ)
    then inner ℝ (greenGradient (X i - X j))
      (G ξ s X (X i) - G ξ s X (X j)) else 0

private def forwardFarTerm {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N)
    (i j : Fin N) : ℝ :=
  if torusEuclideanDist (X i) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X j) ξ
  then inner ℝ (greenGradient (X i - X j)) (G ξ s X (X i)) else 0

theorem far_predicate_irrefl {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 4 < K)
    (ξ : Torus) (X : Configuration N) (i : Fin N) :
    ¬ ((torusEuclideanDist (X i) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X i) ξ) ∨
      (torusEuclideanDist (X i) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X i) ξ)) := by
  have hKs := mul_lt_mul_of_pos_right hK hs
  rintro (⟨hi, hj⟩ | ⟨hi, hj⟩) <;> linarith

private theorem far_term_split {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 4 < K)
    (ξ : Torus) (X : Configuration N) (i j : Fin N) :
    (if (torusEuclideanDist (X i) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X j) ξ) ∨
        (torusEuclideanDist (X j) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X i) ξ)
    then inner ℝ (greenGradient (X i - X j))
      (G ξ s X (X i) - G ξ s X (X j)) else 0) =
      forwardFarTerm ξ s K X i j + forwardFarTerm ξ s K X j i := by
  have hKs := mul_lt_mul_of_pos_right hK hs
  by_cases hij : torusEuclideanDist (X i) ξ < 4 * s ∧
      K * s ≤ torusEuclideanDist (X j) ξ
  · have hji : ¬ (torusEuclideanDist (X j) ξ < 4 * s ∧
        K * s ≤ torusEuclideanDist (X i) ξ) := by
      rintro ⟨hj, _⟩
      linarith [hij.2]
    have hGj : G ξ s X (X j) = 0 :=
      G_eq_zero_outer hs ξ X (hKs.le.trans hij.2)
    simp only [forwardFarTerm, hij, hji, and_self, or_false, ite_true, ite_false,
      hGj, sub_zero, add_zero]
  · by_cases hji : torusEuclideanDist (X j) ξ < 4 * s ∧
        K * s ≤ torusEuclideanDist (X i) ξ
    · have hGi : G ξ s X (X i) = 0 :=
        G_eq_zero_outer hs ξ X (hKs.le.trans hji.2)
      have hne := inner_far_sub_ne_zero hs hK ξ hji.1.le hji.2
      have ho : greenGradient (X i - X j) = -greenGradient (X j - X i) := by
        simpa only [neg_sub] using greenGradient_odd_off_origin hne
      simp only [forwardFarTerm, hij, hji, false_or, ite_false,
        hGi, zero_sub, ho, inner_neg_left, inner_neg_right, neg_neg, zero_add]
    · simp only [forwardFarTerm, hij, hji, false_or, ite_false, add_zero]

private theorem forward_sum_eq {N : ℕ} (ξ : Torus) (s K : ℝ)
    (X : Configuration N) :
    (∑ i : Fin N, ∑ j : Fin N, forwardFarTerm ξ s K X i j) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ),
        fixedFarSum ξ s X (X j) := by
  rw [Finset.sum_comm]
  simp only [forwardFarTerm, fixedFarSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : K * s ≤ torusEuclideanDist (X j) ξ
  · simp only [hj, and_true, ite_true]
  · simp only [hj, and_false, ite_false, Finset.sum_const_zero]

/-- Both ordered orientations produce the same actual sum. Far geometry
supplies the noncollision required for oddness, without a condition on any
other pair in the configuration. -/
theorem orderedFarSum_eq_two_mul {N : ℕ} {s K : ℝ}
    (hs : 0 < s) (hK : 4 < K) (ξ : Torus) (X : Configuration N) :
    orderedFarSum ξ s K X =
      2 * ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ),
        fixedFarSum ξ s X (X j) := by
  unfold orderedFarSum
  simp_rw [far_term_split hs hK ξ X, Finset.sum_add_distrib]
  have hswap : (∑ i : Fin N, ∑ j : Fin N, forwardFarTerm ξ s K X j i) =
      ∑ i : Fin N, ∑ j : Fin N, forwardFarTerm ξ s K X i j := Finset.sum_comm
  rw [hswap]
  simp only [forward_sum_eq]
  ring

theorem exterior_card_le_N {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) :
    (Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ)).card ≤ N := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le Finset.univ (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ)

theorem abs_exterior_sum_le {N : ℕ} (hN : 0 < N) {s K C₁ C₂ : ℝ}
    (hs : 0 < s) (hK : 4 < K) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hk₁ : KernelGradientBound C₁) (hk₂ : KernelHessianBound C₂)
    (ξ : Torus) (X : Configuration N) :
    |∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ),
      fixedFarSum ξ s X (X j)| ≤ (N : ℝ) * ((mass ξ s X / N) *
        (320 * C₂ / (K - 4) ^ 2 * (ballCount ξ (4 * s) X : ℝ) +
          64 * C₁ / K * (annulusCount ξ s X : ℝ))) := by
  let B : ℝ := (mass ξ s X / N) *
    (320 * C₂ / (K - 4) ^ 2 * (ballCount ξ (4 * s) X : ℝ) +
      64 * C₁ / K * (annulusCount ξ s X : ℝ))
  have hKpos : 0 < K := lt_trans (by norm_num) hK
  have hM := mass_nonneg ξ s X
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcard :
      ((Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ)).card : ℝ) ≤ N :=
    by exact_mod_cast exterior_card_le_N ξ s K X
  change _ ≤ (N : ℝ) * B
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ),
        |fixedFarSum ξ s X (X j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ), B := by
      apply Finset.sum_le_sum
      intro j hj
      exact abs_fixedFarSum_le hN hs hK hC₁ hC₂ hk₁ hk₂ ξ X (Finset.mem_filter.mp hj).2
    _ = ((Finset.univ.filter
        (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ)).card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * B := mul_le_mul_of_nonneg_right hcard hB

/-- The exact source far-error coefficient for the literal ordered sum.
There is no assumption of global distinctness, positive local mass, or an
unproved interaction bound. The original particle number is unchanged. -/
theorem orderedFarSum_lower {N : ℕ} (hN : 0 < N) {β s K C₁ C₂ : ℝ}
    (hβ : 0 ≤ β) (hs : 0 < s) (hK : 4 < K) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hk₁ : KernelGradientBound C₁) (hk₂ : KernelHessianBound C₂)
    (ξ : Torus) (X : Configuration N) :
    -β * (mass ξ s X / N) *
      (320 * C₂ / (K - 4) ^ 2 * (ballCount ξ (4 * s) X : ℝ) +
        64 * C₁ / K * (annulusCount ξ s X : ℝ)) ≤
      (β / (2 * (N : ℝ))) * orderedFarSum ξ s K X := by
  let B : ℝ := (mass ξ s X / N) *
    (320 * C₂ / (K - 4) ^ 2 * (ballCount ξ (4 * s) X : ℝ) +
      64 * C₁ / K * (annulusCount ξ s X : ℝ))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := abs_exterior_sum_le hN hs hK hC₁ hC₂ hk₁ hk₂ ξ X
  have hn : -((N : ℝ) * B) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ),
        fixedFarSum ξ s X (X j) := (abs_le.mp hb).1
  calc
    _ = (β / (N : ℝ)) * (-((N : ℝ) * B)) := by
      rw [mul_neg, ← mul_assoc, div_mul_cancel₀ _ hNr.ne']
      dsimp [B]
      ring
    _ ≤ (β / (N : ℝ)) *
        (∑ j ∈ Finset.univ.filter (fun j : Fin N ↦ K * s ≤ torusEuclideanDist (X j) ξ),
          fixedFarSum ξ s X (X j)) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg hβ hNr.le)
    _ = _ := by
      rw [orderedFarSum_eq_two_mul hs hK ξ X]
      field_simp [hNr.ne']

/-- Source constants chosen once in the kernel modules, independent of the
particle number, coupling, localization center, radius, and configuration. -/
theorem orderedFarSum_lower_constants {N : ℕ} (hN : 0 < N) {β s K : ℝ}
    (hβ : 0 ≤ β) (hs : 0 < s) (hK : 4 < K) (ξ : Torus) (X : Configuration N) :
    -β * (mass ξ s X / N) *
      (320 * GreenCovarianceBounds.hessianConstant / (K - 4) ^ 2 *
          (ballCount ξ (4 * s) X : ℝ) +
        64 * ConditionalLawEstimates.kernelConstant / K *
          (annulusCount ξ s X : ℝ)) ≤
      (β / (2 * (N : ℝ))) * orderedFarSum ξ s K X :=
  orderedFarSum_lower hN hβ hs hK ConditionalLawEstimates.kernelConstant_pos.le
    GreenCovarianceBounds.hessianConstant_pos.le ConditionalLawEstimates.kernel_gradient_bound
    GreenCovarianceBounds.kernel_hessian_bound ξ X

/-- The same bound stated with the constructed second moment's actual
particle gradients, ready for the generator's literal ordered decomposition. -/
theorem QFunction_far_pair_lower {N : ℕ} (hN : 0 < N) {β s K : ℝ}
    (hβ : 0 ≤ β) (hs : 0 < s) (hsmall : s ≤ 1 / 64) (hK : 4 < K)
    (ξ : Torus) (X : Configuration N) :
    -β * (mass ξ s X / N) *
      (320 * GreenCovarianceBounds.hessianConstant / (K - 4) ^ 2 *
          (ballCount ξ (4 * s) X : ℝ) +
        64 * ConditionalLawEstimates.kernelConstant / K *
          (annulusCount ξ s X : ℝ)) ≤
      (β / (2 * (N : ℝ))) *
        (∑ i : Fin N, ∑ j : Fin N,
          if (torusEuclideanDist (X i) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X j) ξ) ∨
              (torusEuclideanDist (X j) ξ < 4 * s ∧ K * s ≤ torusEuclideanDist (X i) ξ)
          then inner ℝ (greenGradient (X i - X j))
            ((QFunction ξ hs hsmall).particleGradient i X -
              (QFunction ξ hs hsmall).particleGradient j X) else 0) := by
  simp only [QFunction_particleGradient hN ξ hs hsmall X]
  exact orderedFarSum_lower_constants hN hβ hs hK ξ X

end PeriodicAttractiveLogGas.LocalizedVirialFarPairs
