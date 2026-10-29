import LeanResearch.PeriodicAttractiveLogGas.CollectiveIntegrationByParts
import LeanResearch.PeriodicAttractiveLogGas.SeparatedRadius
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual localized second moment from source `lem:collective-second-moment`.
The local coordinates are the centered quotient lifts about the fixed center.
The C2 construction below proves regularity of the cutoff-weighted polynomials
through their genuine zero extensions. Quantitative gradient estimates are
separate derived statements, never fields of the constructed C2 function.
Development and exact central checks are recorded in
`research/reviews/collective-second-moment-development.md`.
-/

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff BigOperators NNReal RealInnerProductSpace

namespace PeriodicAttractiveLogGas.CollectiveSecondMoment

open LocalizedVirialCutoffs SeparatedRadius CollectiveIntegrationByParts
open MovingPoleNumerators

/-- The actual Euclidean chart coordinate about the fixed center. -/
def chartPosition (ξ z : Torus) : PlanarSpace := centeredLift (z - ξ)

@[simp] theorem norm_chartPosition (ξ z : Torus) :
    ‖chartPosition ξ z‖ = torusEuclideanDist z ξ := norm_centeredLift _

@[simp] theorem quotient_chartPosition (ξ z : Torus) :
    torusQuotient (chartPosition ξ z) = z - ξ := torusQuotient_centeredLift _

@[simp] theorem phiEuclidean_chart (ξ : Torus) (s : ℝ) (z : Torus) :
    phiEuclidean s (chartPosition ξ z) = phi ξ s z := by
  simp only [phiEuclidean, norm_chartPosition, phi]

/-- An actual chart germ for any function which vanishes outside a ball
strictly below the injectivity radius. No regularity is assumed here. -/
theorem chart_germ {E : Type*} [Zero E] {f : PlanarSpace → E} {R : ℝ}
    (hf : ∀ u, R ≤ ‖u‖ → f u = 0) (hR : R < 1 / 2)
    (ξ : Torus) (x : PlanarSpace) :
    (fun y : PlanarSpace ↦ f (chartPosition ξ (torusQuotient y))) =ᶠ[𝓝 x]
      (fun y ↦ f (y + (chartPosition ξ (torusQuotient x) - x))) := by
  let w : PlanarSpace := chartPosition ξ (torusQuotient x)
  let a : PlanarSpace := w - x
  have hxw : x + a = w := by dsimp [a]; abel
  have hw : ‖w‖ = torusEuclideanDist (torusQuotient x) ξ := norm_chartPosition _ _
  have hq (y : PlanarSpace) : torusQuotient (y + a) = torusQuotient y - ξ := by
    dsimp [a, w, chartPosition]
    rw [torusQuotient_add, torusQuotient_sub, torusQuotient_centeredLift]
    abel
  have hn : Continuous (fun y : PlanarSpace ↦ ‖y + a‖) := by fun_prop
  have ht : Continuous (fun y : PlanarSpace ↦ torusEuclideanDist (torusQuotient y) ξ) :=
    continuous_torusEuclideanNorm.comp
      (isOpenQuotientMap_torusQuotient.continuous.sub continuous_const)
  change (fun y : PlanarSpace ↦ f (chartPosition ξ (torusQuotient y))) =ᶠ[𝓝 x]
    (fun y ↦ f (y + a))
  by_cases hr : torusEuclideanDist (torusQuotient x) ξ < 1 / 2
  · have hxn : ‖x + a‖ < 1 / 2 := by rw [hxw, hw]; exact hr
    filter_upwards [hn.continuousAt (Iio_mem_nhds hxn)] with y hy
    have he : chartPosition ξ (torusQuotient y) = y + a := by
      rw [chartPosition, ← hq y]
      exact centeredLift_torusQuotient_of_norm_lt_half hy
    rw [he]
  · have hrt : R < torusEuclideanDist (torusQuotient x) ξ :=
      lt_of_lt_of_le hR (le_of_not_gt hr)
    have hrn : R < ‖x + a‖ := by rw [hxw, hw]; exact hrt
    filter_upwards [ht.continuousAt (Ioi_mem_nhds hrt),
      hn.continuousAt (Ioi_mem_nhds hrn)] with y hyt hyn
    rw [hf _ (by simpa only [norm_chartPosition] using hyt.le), hf _ hyn.le]

theorem contDiff_chart_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {f : PlanarSpace → E} {R : ℝ} (hf : ContDiff ℝ n f)
    (hzero : ∀ u, R ≤ ‖u‖ → f u = 0) (hR : R < 1 / 2) (ξ : Torus) :
    ContDiff ℝ n (fun y : PlanarSpace ↦ f (chartPosition ξ (torusQuotient y))) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (hf.comp (contDiff_id.add contDiff_const)).contDiffAt.congr_of_eventuallyEq
    (chart_germ hzero hR ξ x)

theorem chart_lift_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : PlanarSpace → E} {R : ℝ}
    (hzero : ∀ u, R ≤ ‖u‖ → f u = 0) (hR : R < 1 / 2)
    (ξ : Torus) (x : PlanarSpace) :
    fderiv ℝ (fun y : PlanarSpace ↦ f (chartPosition ξ (torusQuotient y))) x =
      fderiv ℝ f (chartPosition ξ (torusQuotient x)) := by
  rw [(chart_germ hzero hR ξ x).fderiv_eq, fderiv_comp_add_right]
  congr 1
  abel

theorem chart_lift_second_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : PlanarSpace → E} {R : ℝ}
    (hzero : ∀ u, R ≤ ‖u‖ → f u = 0) (hR : R < 1 / 2)
    (ξ : Torus) (x : PlanarSpace) :
    fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ f (chartPosition ξ (torusQuotient y)))) x =
      fderiv ℝ (fderiv ℝ f) (chartPosition ξ (torusQuotient x)) := by
  let a : PlanarSpace := chartPosition ξ (torusQuotient x) - x
  have ht : fderiv ℝ (fun y : PlanarSpace ↦ f (y + a)) =
      fun y ↦ fderiv ℝ f (y + a) := by
    funext y
    exact fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := y) a
  rw [(chart_germ hzero hR ξ x).fderiv.fderiv_eq]
  change fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ f (y + a))) x = _
  rw [ht, fderiv_comp_add_right (f := fderiv ℝ f) a]
  congr 1
  dsimp [a]
  abel

/-- A scalar polynomial multiplied by the actual radial cutoff. -/
def weightedPolynomial (ξ : Torus) (s : ℝ) (p : PlanarSpace → ℝ) (z : Torus) : ℝ :=
  phi ξ s z * p (chartPosition ξ z)

theorem weightedPolynomial_eq_chart (ξ : Torus) (s : ℝ) (p : PlanarSpace → ℝ)
    (z : Torus) : weightedPolynomial ξ s p z =
      (fun u : PlanarSpace ↦ phiEuclidean s u * p u) (chartPosition ξ z) := by
  simp only [weightedPolynomial, phiEuclidean, norm_chartPosition, phi]

theorem contDiff_weightedPolynomial_lift {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) {p : PlanarSpace → ℝ} (hp : ContDiff ℝ 2 p) :
    ContDiff ℝ 2 (fun y : PlanarSpace ↦ weightedPolynomial ξ s p (torusQuotient y)) := by
  have hzero (u : PlanarSpace) (hu : 4 * s ≤ ‖u‖) : phiEuclidean s u * p u = 0 := by
    rw [phiEuclidean, phiProfile_eq_zero hs hu, zero_mul]
  have h := contDiff_chart_lift ((contDiff_phiEuclidean hs).mul hp) hzero
    (by linarith : 4 * s < 1 / 2) ξ
  simpa only [← weightedPolynomial_eq_chart] using h

theorem continuous_weightedPolynomial {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) {p : PlanarSpace → ℝ} (hp : ContDiff ℝ 2 p) :
    Continuous (weightedPolynomial ξ s p) := by
  apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
  exact (contDiff_weightedPolynomial_lift hs hsmall ξ hp).continuous

theorem contDiff_weightedPolynomial_configuration {N : ℕ} {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus)
    {p : PlanarSpace → ℝ} (hp : ContDiff ℝ 2 p) (i : Fin N) :
    ContDiff ℝ 2 (fun y : Gradient N ↦
      weightedPolynomial ξ s p (configurationQuotient N y i)) := by
  change ContDiff ℝ 2 ((fun u : PlanarSpace ↦ weightedPolynomial ξ s p (torusQuotient u)) ∘
    sourceProjection i)
  exact (contDiff_weightedPolynomial_lift hs hsmall ξ hp).comp (sourceProjection i).contDiff

private theorem contDiff_phi_configuration {N : ℕ} {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (i : Fin N) :
    ContDiff ℝ 2 (fun y : Gradient N ↦ phi ξ s (configurationQuotient N y i)) := by
  change ContDiff ℝ 2 ((fun u : PlanarSpace ↦ phi ξ s (torusQuotient u)) ∘ sourceProjection i)
  exact (contDiff_phi_lift hs hsmall ξ).comp (sourceProjection i).contDiff

/-- Literal symmetric pair contribution in the local Euclidean chart. -/
def pairSecondMoment (ξ : Torus) (s : ℝ) (z w : Torus) : ℝ :=
  phi ξ s z * phi ξ s w * ‖chartPosition ξ z - chartPosition ξ w‖ ^ 2

@[simp] theorem pairSecondMoment_self (ξ z : Torus) (s : ℝ) :
    pairSecondMoment ξ s z z = 0 := by simp [pairSecondMoment]

theorem pairSecondMoment_symm (ξ z w : Torus) (s : ℝ) :
    pairSecondMoment ξ s z w = pairSecondMoment ξ s w z := by
  rw [pairSecondMoment, pairSecondMoment, norm_sub_rev]
  ring

theorem pairSecondMoment_nonneg (ξ z w : Torus) (s : ℝ) :
    0 ≤ pairSecondMoment ξ s z w :=
  mul_nonneg (mul_nonneg (phi_mem_Icc ξ s z).1 (phi_mem_Icc ξ s w).1) (sq_nonneg _)

theorem pairSecondMoment_eq_zero_left {s : ℝ} (hs : 0 < s) {ξ z : Torus}
    (hz : 4 * s ≤ torusEuclideanDist z ξ) (w : Torus) : pairSecondMoment ξ s z w = 0 := by
  simp only [pairSecondMoment, phi_eq_zero hs hz, zero_mul]

theorem pairSecondMoment_eq_zero_right {s : ℝ} (hs : 0 < s) {ξ w : Torus}
    (hw : 4 * s ≤ torusEuclideanDist w ξ) (z : Torus) : pairSecondMoment ξ s z w = 0 := by
  rw [pairSecondMoment_symm]
  exact pairSecondMoment_eq_zero_left hs hw z

private theorem weighted_coordinate_inner (a b : ℝ) (u v : PlanarSpace) :
    (∑ k : Fin 2, (a * u k) * (b * v k)) = a * b * inner ℝ u v := by
  have hi : inner ℝ u v = ∑ k : Fin 2, u k * v k := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The chart's discontinuity is multiplied out through actual weighted
polynomials. This identity supplies C2 regularity at every chart boundary. -/
theorem pairSecondMoment_polynomial (ξ z w : Torus) (s : ℝ) :
    pairSecondMoment ξ s z w =
      weightedPolynomial ξ s (fun u ↦ ‖u‖ ^ 2) z * phi ξ s w +
      phi ξ s z * weightedPolynomial ξ s (fun u ↦ ‖u‖ ^ 2) w -
      2 * ∑ k : Fin 2, weightedPolynomial ξ s (fun u ↦ u k) z *
        weightedPolynomial ξ s (fun u ↦ u k) w := by
  dsimp [pairSecondMoment, weightedPolynomial]
  rw [weighted_coordinate_inner, norm_sub_sq_real]
  ring

theorem contDiff_pairSecondMoment_configuration {N : ℕ} {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (i j : Fin N) :
    ContDiff ℝ 2 (fun y : Gradient N ↦
      pairSecondMoment ξ s (configurationQuotient N y i) (configurationQuotient N y j)) := by
  simp_rw [pairSecondMoment_polynomial]
  apply ContDiff.sub
  · exact ((contDiff_weightedPolynomial_configuration hs hsmall ξ (contDiff_norm_sq ℝ) i).mul
      (contDiff_phi_configuration hs hsmall ξ j)).add
        ((contDiff_phi_configuration hs hsmall ξ i).mul
          (contDiff_weightedPolynomial_configuration hs hsmall ξ (contDiff_norm_sq ℝ) j))
  · apply contDiff_const.mul
    apply ContDiff.sum
    intro k _
    exact (contDiff_weightedPolynomial_configuration hs hsmall ξ
      (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff i).mul
        (contDiff_weightedPolynomial_configuration hs hsmall ξ
          (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff j)

/-- The manuscript's actual localized second moment, with original N. -/
def Q {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : ℝ :=
  (1 / (2 * (N : ℝ))) * ∑ i : Fin N, ∑ j : Fin N, pairSecondMoment ξ s (X i) (X j)

theorem Q_nonneg {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : 0 ≤ Q ξ s X := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    pairSecondMoment_nonneg ξ (X i) (X j) s

theorem contDiff_Q_lift {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) : ContDiff ℝ 2 (fun y : Gradient N ↦ Q ξ s (configurationQuotient N y)) := by
  unfold Q
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact contDiff_pairSecondMoment_configuration hs hsmall ξ i j

theorem continuous_Q {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) : Continuous (Q (N := N) ξ s) := by
  apply (isOpenQuotientMap_configurationQuotient N).isQuotientMap.continuous_iff.mpr
  exact (contDiff_Q_lift hs hsmall ξ).continuous

/-- Genuine C2 object for use by collective integration by parts. Its only
inputs are the center, positive radius, and the manuscript's geometric size. -/
def QFunction {N : ℕ} {s : ℝ} (ξ : Torus) (hs : 0 < s) (hsmall : s ≤ 1 / 64) : C2Function N where
  value := ⟨Q ξ s, continuous_Q hs hsmall ξ⟩
  regularity := contDiff_Q_lift hs hsmall ξ

@[simp] theorem QFunction_value {N : ℕ} {s : ℝ} (ξ : Torus)
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (X : Configuration N) :
    (QFunction ξ hs hsmall).value X = Q ξ s X := rfl

theorem pairSecondMoment_eq_torusDistance {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ z w : Torus) : pairSecondMoment ξ s z w =
      phi ξ s z * phi ξ s w * torusEuclideanDist z w ^ 2 := by
  by_cases hz : phi ξ s z = 0
  · simp only [pairSecondMoment, hz, zero_mul]
  by_cases hw : phi ξ s w = 0
  · simp only [pairSecondMoment, hw, mul_zero, zero_mul]
  have hzr : torusEuclideanDist z ξ < 4 * s :=
    lt_of_not_ge fun h ↦ hz (phi_eq_zero hs h)
  have hwr : torusEuclideanDist w ξ < 4 * s :=
    lt_of_not_ge fun h ↦ hw (phi_eq_zero hs h)
  have hn : ‖chartPosition ξ z - chartPosition ξ w‖ < (1 / 2 : ℝ) := by
    have h := norm_sub_le (chartPosition ξ z) (chartPosition ξ w)
    rw [norm_chartPosition, norm_chartPosition] at h
    linarith
  have hq : torusQuotient (chartPosition ξ z - chartPosition ξ w) = z - w := by
    rw [torusQuotient_sub, quotient_chartPosition, quotient_chartPosition]
    abel
  have hd : torusEuclideanDist z w = ‖chartPosition ξ z - chartPosition ξ w‖ := by
    rw [torusEuclideanDist, ← hq]
    exact torusEuclideanNorm_quotient_eq_of_norm_lt_half hn
  rw [pairSecondMoment, hd]

/-- Ordinary planar gradient of the actual Euclidean cutoff. -/
def phiGradientEuclidean (s : ℝ) (u : PlanarSpace) : PlanarSpace :=
  rectangleOrdinaryGradient (phiEuclidean s) u

theorem phiGradientEuclidean_inner (s : ℝ) (u v : PlanarSpace) :
    inner ℝ (phiGradientEuclidean s u) v = fderiv ℝ (phiEuclidean s) u v := by
  simp only [phiGradientEuclidean, rectangleOrdinaryGradient,
    InnerProductSpace.toDual_symm_apply]

theorem hasFDerivAt_phiEuclidean {s : ℝ} (hs : 0 < s) (u : PlanarSpace) :
    HasFDerivAt (phiEuclidean s) (innerSL ℝ (phiGradientEuclidean s u)) u := by
  have he : innerSL ℝ (phiGradientEuclidean s u) = fderiv ℝ (phiEuclidean s) u := by
    ext v
    exact phiGradientEuclidean_inner s u v
  rw [he]
  exact ((contDiff_phiEuclidean hs).differentiable (by norm_num) u).hasFDerivAt

theorem contDiff_phiGradientEuclidean {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 1 (phiGradientEuclidean s) := by
  let R : (PlanarSpace →L[ℝ] ℝ) →L[ℝ] PlanarSpace :=
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
  change ContDiff ℝ 1 (R ∘ fderiv ℝ (phiEuclidean s))
  exact R.contDiff.comp ((contDiff_phiEuclidean hs).fderiv_right (m := 1) (by norm_num))

theorem norm_phiGradientEuclidean_le {s : ℝ} (hs : 0 < s) (u : PlanarSpace) :
    ‖phiGradientEuclidean s u‖ ≤ 1 / s := by
  rw [phiGradientEuclidean, norm_rectangleOrdinaryGradient]
  exact norm_fderiv_phiEuclidean_le hs u

theorem phiGradientEuclidean_eq_zero_outer {s : ℝ} (hs : 0 < s)
    {u : PlanarSpace} (hu : 4 * s ≤ ‖u‖) : phiGradientEuclidean s u = 0 := by
  have hne : u ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < 4 * s) hu)
  simp only [phiGradientEuclidean, rectangleOrdinaryGradient,
    fderiv_phiEuclidean hne, deriv_phiProfile_eq_zero_outer hs hu,
    zero_div, zero_smul, map_zero]

theorem phiGradientEuclidean_eq_zero_inner {s : ℝ} (hs : 0 < s)
    {u : PlanarSpace} (hu : ‖u‖ ≤ 2 * s) : phiGradientEuclidean s u = 0 := by
  by_cases hne : u = 0
  · subst u
    simp only [phiGradientEuclidean, rectangleOrdinaryGradient, fderiv_phiEuclidean_zero hs,
      map_zero]
  · simp only [phiGradientEuclidean, rectangleOrdinaryGradient,
      fderiv_phiEuclidean hne, deriv_phiProfile_eq_zero_inner hs hu,
      zero_div, zero_smul, map_zero]

theorem phiGradientEuclidean_eq_torusGradient {s : ℝ} (hs : 0 < s)
    (hsmall : s ≤ 1 / 64) (ξ z : Torus) :
    phiGradientEuclidean s (chartPosition ξ z) = torusOrdinaryGradient (phi ξ s) z := by
  obtain ⟨u, rfl⟩ := torusQuotient_surjective z
  rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient, fderiv_phi_lift hs hsmall]
  rfl

/-- The derivative in the first variable of the actual symmetric Euclidean
pair. The diagonal value is zero, including its cutoff derivative term. -/
def pairFirstGradient (s : ℝ) (u v : PlanarSpace) : PlanarSpace :=
  phiEuclidean s v • (‖u - v‖ ^ 2 • phiGradientEuclidean s u +
    (2 * phiEuclidean s u) • (u - v))

@[simp] theorem pairFirstGradient_self (s : ℝ) (u : PlanarSpace) :
    pairFirstGradient s u u = 0 := by simp [pairFirstGradient]

theorem pairFirstGradient_eq_zero_outer {s : ℝ} (hs : 0 < s)
    {u : PlanarSpace} (hu : 4 * s ≤ ‖u‖) (v : PlanarSpace) :
    pairFirstGradient s u v = 0 := by
  simp only [pairFirstGradient, phiGradientEuclidean_eq_zero_outer hs hu,
    phiEuclidean, phiProfile_eq_zero hs hu, smul_zero, mul_zero, zero_smul, add_zero]

theorem contDiff_pairFirstGradient {s : ℝ} (hs : 0 < s) (v : PlanarSpace) :
    ContDiff ℝ 1 (fun u ↦ pairFirstGradient s u v) := by
  change ContDiff ℝ 1 (fun u ↦ phiEuclidean s v •
    (‖u - v‖ ^ 2 • phiGradientEuclidean s u + (2 * phiEuclidean s u) • (u - v)))
  apply ContDiff.const_smul
  apply ContDiff.add
  · exact ((contDiff_id.sub contDiff_const).norm_sq ℝ).smul
      (contDiff_phiGradientEuclidean hs)
  · exact (contDiff_const.mul ((contDiff_phiEuclidean hs).of_le (by norm_num))).smul
      (contDiff_id.sub contDiff_const)

private theorem hasFDerivAt_euclideanPair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℝ} (hs : 0 < s) {u v : E → PlanarSpace} {u' v' : E →L[ℝ] PlanarSpace}
    {x : E} (hu : HasFDerivAt u u' x) (hv : HasFDerivAt v v' x) :
    HasFDerivAt (fun y ↦ phiEuclidean s (u y) * phiEuclidean s (v y) * ‖u y - v y‖ ^ 2)
      ((innerSL ℝ (pairFirstGradient s (u x) (v x))).comp u' +
        (innerSL ℝ (pairFirstGradient s (v x) (u x))).comp v') x := by
  have hau := (hasFDerivAt_phiEuclidean hs (u x)).comp x hu
  have hav := (hasFDerivAt_phiEuclidean hs (v x)).comp x hv
  have hd := (hau.mul hav).mul ((hu.sub hv).norm_sq)
  convert! hd using 1
  ext t
  simp only [pairFirstGradient, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, inner_smul_left, inner_add_left, inner_sub_left, inner_sub_right,
    conj_trivial, smul_eq_mul, sub_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
  rw [norm_sub_rev (v x) (u x)]
  ring

/-- The zero-supported bundle contains the cutoff and its weighted chart
coordinate. Its chart germ proves the actual pair germ without assuming the
raw centered-coordinate map is continuous at a chart boundary. -/
private theorem cutoff_chart_germ {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    ∀ᶠ y : PlanarSpace in 𝓝 x,
      phi ξ s (torusQuotient y) = phiEuclidean s (y + (chartPosition ξ (torusQuotient x) - x)) ∧
      (phi ξ s (torusQuotient y) = 0 ∨
        chartPosition ξ (torusQuotient y) = y + (chartPosition ξ (torusQuotient x) - x)) := by
  let f : PlanarSpace → ℝ × PlanarSpace := fun u ↦ (phiEuclidean s u, phiEuclidean s u • u)
  have hz (u : PlanarSpace) (hu : 4 * s ≤ ‖u‖) : f u = 0 := by
    simp only [f, phiEuclidean, phiProfile_eq_zero hs hu, zero_smul]
    rfl
  have hg := chart_germ hz (by linarith : 4 * s < 1 / 2) ξ x
  filter_upwards [hg] with y hy
  have hφ (z : Torus) : phiEuclidean s (chartPosition ξ z) = phi ξ s z := by
    simp only [phiEuclidean, norm_chartPosition, phi]
  have h1 := congrArg Prod.fst hy
  change phiEuclidean s (chartPosition ξ (torusQuotient y)) =
    phiEuclidean s (y + (chartPosition ξ (torusQuotient x) - x)) at h1
  rw [hφ] at h1
  refine ⟨h1, ?_⟩
  by_cases hn : phi ξ s (torusQuotient y) = 0
  · exact Or.inl hn
  · apply Or.inr
    have h2 := congrArg Prod.snd hy
    change phiEuclidean s (chartPosition ξ (torusQuotient y)) • chartPosition ξ (torusQuotient y) =
      phiEuclidean s (y + (chartPosition ξ (torusQuotient x) - x)) •
        (y + (chartPosition ξ (torusQuotient x) - x)) at h2
    rw [hφ, ← h1] at h2
    have hc := congrArg (fun w : PlanarSpace ↦ (phi ξ s (torusQuotient y))⁻¹ • w) h2
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hc

private theorem pair_configuration_germ {N : ℕ} {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (Y : Gradient N) (i j : Fin N) :
    (fun Z : Gradient N ↦ pairSecondMoment ξ s (configurationQuotient N Z i)
      (configurationQuotient N Z j)) =ᶠ[𝓝 Y]
    (fun Z ↦
      let u := sourceProjection i Z + (chartPosition ξ (configurationQuotient N Y i) - sourceProjection i Y)
      let v := sourceProjection j Z + (chartPosition ξ (configurationQuotient N Y j) - sourceProjection j Y)
      phiEuclidean s u * phiEuclidean s v * ‖u - v‖ ^ 2) := by
  have hi := (sourceProjection i).continuous.continuousAt.eventually
    (cutoff_chart_germ hs hsmall ξ (sourceProjection i Y))
  have hj := (sourceProjection j).continuous.continuousAt.eventually
    (cutoff_chart_germ hs hsmall ξ (sourceProjection j Y))
  filter_upwards [hi, hj] with Z hZi hZj
  change phi ξ s (configurationQuotient N Z i) = phiEuclidean s
      (sourceProjection i Z + (chartPosition ξ (configurationQuotient N Y i) - sourceProjection i Y)) ∧
    (phi ξ s (configurationQuotient N Z i) = 0 ∨
      chartPosition ξ (configurationQuotient N Z i) = sourceProjection i Z +
        (chartPosition ξ (configurationQuotient N Y i) - sourceProjection i Y)) at hZi
  change phi ξ s (configurationQuotient N Z j) = phiEuclidean s
      (sourceProjection j Z + (chartPosition ξ (configurationQuotient N Y j) - sourceProjection j Y)) ∧
    (phi ξ s (configurationQuotient N Z j) = 0 ∨
      chartPosition ξ (configurationQuotient N Z j) = sourceProjection j Z +
        (chartPosition ξ (configurationQuotient N Y j) - sourceProjection j Y)) at hZj
  rcases hZi.2 with hzero | he
  · simp only [pairSecondMoment, hzero, ← hZi.1, zero_mul]
  · rcases hZj.2 with hzero | hf
    · simp only [pairSecondMoment, hzero, ← hZj.1, mul_zero, zero_mul]
    · simp only [pairSecondMoment, hZi.1, hZj.1, he, hf]

theorem hasFDerivAt_pairSecondMoment_configuration {N : ℕ} {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (Y : Gradient N) (i j : Fin N) :
    HasFDerivAt (fun Z : Gradient N ↦ pairSecondMoment ξ s (configurationQuotient N Z i)
      (configurationQuotient N Z j))
      ((innerSL ℝ (pairFirstGradient s (chartPosition ξ (configurationQuotient N Y i))
        (chartPosition ξ (configurationQuotient N Y j)))).comp (sourceProjection i) +
      (innerSL ℝ (pairFirstGradient s (chartPosition ξ (configurationQuotient N Y j))
        (chartPosition ξ (configurationQuotient N Y i)))).comp (sourceProjection j)) Y := by
  let ai := chartPosition ξ (configurationQuotient N Y i) - sourceProjection i Y
  let aj := chartPosition ξ (configurationQuotient N Y j) - sourceProjection j Y
  have hi : sourceProjection i Y + ai = chartPosition ξ (configurationQuotient N Y i) := by
    dsimp [ai]; abel
  have hj : sourceProjection j Y + aj = chartPosition ξ (configurationQuotient N Y j) := by
    dsimp [aj]; abel
  have hd := hasFDerivAt_euclideanPair hs (x := Y)
    ((sourceProjection i).hasFDerivAt.add_const ai)
    ((sourceProjection j).hasFDerivAt.add_const aj)
  rw [hi, hj] at hd
  exact hd.congr_of_eventuallyEq (pair_configuration_germ hs hsmall ξ Y i j)

/-- The global source vector field, expressed without division by the mass.
This is the same formula when the mass is positive and is automatically zero
when every cutoff weight vanishes. -/
def G {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (z : Torus) : PlanarSpace :=
  (1 / (N : ℝ)) • ∑ j : Fin N,
    pairFirstGradient s (chartPosition ξ z) (chartPosition ξ (X j))

theorem G_eq_zero_outer {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) {z : Torus} (hz : 4 * s ≤ torusEuclideanDist z ξ) : G ξ s X z = 0 := by
  have hu : 4 * s ≤ ‖chartPosition ξ z‖ := by simpa only [norm_chartPosition] using hz
  simp only [G, pairFirstGradient_eq_zero_outer hs hu,
    Finset.sum_const_zero, smul_zero]

theorem contDiff_G_lift {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (X : Configuration N) :
    ContDiff ℝ 1 (fun y : PlanarSpace ↦ G ξ s X (torusQuotient y)) := by
  let f : PlanarSpace → PlanarSpace := fun u ↦ (1 / (N : ℝ)) • ∑ j : Fin N,
    pairFirstGradient s u (chartPosition ξ (X j))
  have hf : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (fun u : PlanarSpace ↦ (1 / (N : ℝ)) •
      ∑ j : Fin N, pairFirstGradient s u (chartPosition ξ (X j)))
    apply ContDiff.const_smul
    exact ContDiff.sum fun j _ ↦ contDiff_pairFirstGradient hs _
  have hz (u : PlanarSpace) (hu : 4 * s ≤ ‖u‖) : f u = 0 := by
    simp only [f, pairFirstGradient_eq_zero_outer hs hu, Finset.sum_const_zero, smul_zero]
  exact contDiff_chart_lift hf hz (by linarith : 4 * s < 1 / 2) ξ

theorem continuous_G {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (X : Configuration N) : Continuous (G ξ s X) := by
  apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
  exact (contDiff_G_lift hs hsmall ξ X).continuous

theorem hasFDerivAt_Q_lift {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (Y : Gradient N) :
    HasFDerivAt (fun Z : Gradient N ↦ Q ξ s (configurationQuotient N Z))
      (innerSL ℝ (fullGradient (fun i : Fin N ↦
        G ξ s (configurationQuotient N Y) (configurationQuotient N Y i)))) Y := by
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    HasFDerivAt.fun_sum (u := Finset.univ) fun j _ ↦
      hasFDerivAt_pairSecondMoment_configuration hs hsmall ξ Y i j).const_mul
        (1 / (2 * (N : ℝ)))
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert! hd using 1
  ext v
  simp only [innerSL_apply_apply, fullGradient_inner, G, inner_smul_left, conj_trivial,
    sum_inner, smul_apply, sum_apply, add_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, Finset.sum_add_distrib]
  have hswap : (∑ i : Fin N, ∑ j : Fin N,
      inner ℝ (pairFirstGradient s (chartPosition ξ (configurationQuotient N Y j))
        (chartPosition ξ (configurationQuotient N Y i))) (sourceProjection j v)) =
    ∑ i : Fin N, ∑ j : Fin N,
      inner ℝ (pairFirstGradient s (chartPosition ξ (configurationQuotient N Y i))
        (chartPosition ξ (configurationQuotient N Y j))) (sourceProjection i v) := by
    rw [Finset.sum_comm]
  rw [hswap, ← Finset.mul_sum]
  field_simp [hn]
  ring

theorem QFunction_gradient {N : ℕ} (hN : 0 < N) {s : ℝ} (ξ : Torus)
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (X : Configuration N) :
    (QFunction ξ hs hsmall).gradient X = fullGradient (fun i : Fin N ↦ G ξ s X (X i)) := by
  obtain ⟨Y, rfl⟩ := configurationQuotient_surjective N X
  have hd := hasFDerivAt_Q_lift hN hs hsmall ξ Y
  have he := ((QFunction ξ hs hsmall).differential Y).unique hd
  apply ext_inner_right ℝ
  intro v
  exact congrArg (fun L : Gradient N →L[ℝ] ℝ ↦ L v) he

theorem QFunction_particleGradient {N : ℕ} (hN : 0 < N) {s : ℝ} (ξ : Torus)
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (X : Configuration N) (i : Fin N) :
    (QFunction ξ hs hsmall).particleGradient i X = G ξ s X (X i) := by
  rw [C2Function.particleGradient, QFunction_gradient hN,
    MovingPoleDerivativeIdentification.sourceProjection_fullGradient]

/-- The source polynomial S, for a fixed actual configuration. -/
def S {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) : ℝ :=
  ∑ j : Fin N, phi ξ s (X j) * ‖u - chartPosition ξ (X j)‖ ^ 2

/-- The weighted displacement sum; when mass is positive it is M times
the displacement from the source weighted center. -/
def D {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) : PlanarSpace :=
  ∑ j : Fin N, phi ξ s (X j) • (u - chartPosition ξ (X j))

theorem G_formula {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (z : Torus) :
    G ξ s X z = (1 / (N : ℝ)) •
      (S ξ s X (chartPosition ξ z) • phiGradientEuclidean s (chartPosition ξ z) +
        (2 * phi ξ s z) • D ξ s X (chartPosition ξ z)) := by
  simp only [G, S, D, pairFirstGradient, phiEuclidean_chart, smul_add, smul_smul,
    Finset.sum_add_distrib, Finset.sum_smul, Finset.smul_sum, mul_comm]

theorem G_eq_zero_of_mass_eq_zero {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (hM : mass ξ s X = 0) (z : Torus) : G ξ s X z = 0 := by
  have hφ (i : Fin N) : phi ξ s (X i) = 0 := by
    have hi : phi ξ s (X i) ≤ mass ξ s X :=
      Finset.single_le_sum (fun j _ ↦ (phi_mem_Icc ξ s (X j)).1) (Finset.mem_univ i)
    rw [hM] at hi
    exact le_antisymm hi (phi_mem_Icc ξ s (X i)).1
  simp only [G, pairFirstGradient, phiEuclidean_chart, hφ, zero_smul,
    Finset.sum_const_zero, smul_zero]

theorem S_nonneg {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) :
    0 ≤ S ξ s X u := Finset.sum_nonneg fun j _ ↦
      mul_nonneg (phi_mem_Icc ξ s (X j)).1 (sq_nonneg _)

private theorem norm_displacement_le {s : ℝ} (hs : 0 < s) (ξ z : Torus)
    {u : PlanarSpace} (hu : ‖u‖ ≤ 4 * s) (hz : phi ξ s z ≠ 0) :
    ‖u - chartPosition ξ z‖ ≤ 8 * s := by
  have hr : torusEuclideanDist z ξ < 4 * s :=
    lt_of_not_ge fun h ↦ hz (phi_eq_zero hs h)
  have h := norm_sub_le u (chartPosition ξ z)
  rw [norm_chartPosition] at h
  linarith

theorem S_le {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus) (X : Configuration N)
    {u : PlanarSpace} (hu : ‖u‖ ≤ 4 * s) : S ξ s X u ≤ 64 * s ^ 2 * mass ξ s X := by
  calc
    _ ≤ ∑ j : Fin N, 64 * s ^ 2 * phi ξ s (X j) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hz : phi ξ s (X j) = 0
      · simp only [hz, zero_mul, mul_zero, le_refl]
      · have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_displacement_le hs ξ (X j) hu hz) 2
        calc
          phi ξ s (X j) * ‖u - chartPosition ξ (X j)‖ ^ 2 ≤
              phi ξ s (X j) * (8 * s) ^ 2 :=
            mul_le_mul_of_nonneg_left hb (phi_mem_Icc ξ s (X j)).1
          _ = _ := by ring
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem norm_D_le {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus) (X : Configuration N)
    {u : PlanarSpace} (hu : ‖u‖ ≤ 4 * s) : ‖D ξ s X u‖ ≤ 8 * s * mass ξ s X := by
  calc
    _ ≤ ∑ j : Fin N, ‖phi ξ s (X j) • (u - chartPosition ξ (X j))‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin N, 8 * s * phi ξ s (X j) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hz : phi ξ s (X j) = 0
      · simp only [hz, zero_smul, norm_zero, mul_zero, le_refl]
      · rw [norm_smul, Real.norm_of_nonneg (phi_mem_Icc ξ s (X j)).1]
        calc
          _ ≤ phi ξ s (X j) * (8 * s) := mul_le_mul_of_nonneg_left
            (norm_displacement_le hs ξ (X j) hu hz) (phi_mem_Icc ξ s (X j)).1
          _ = _ := mul_comm _ _
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem norm_firstSummand_le {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) {u : PlanarSpace} (hu : ‖u‖ ≤ 4 * s) :
    ‖S ξ s X u • phiGradientEuclidean s u‖ ≤ 64 * s * mass ξ s X := by
  have hM := mass_nonneg ξ s X
  rw [norm_smul, Real.norm_of_nonneg (S_nonneg ξ s X u)]
  calc
    _ ≤ (64 * s ^ 2 * mass ξ s X) * (1 / s) :=
      mul_le_mul (S_le hs ξ X hu) (norm_phiGradientEuclidean_le hs u)
        (norm_nonneg _) (by positivity)
    _ = _ := by field_simp [hs.ne']

/-- Exact source supremum bound for the actual extended field. -/
theorem norm_G_le {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) (z : Torus) : ‖G ξ s X z‖ ≤ 80 * s * mass ξ s X / N := by
  have hM := mass_nonneg ξ s X
  by_cases hz : torusEuclideanDist z ξ < 4 * s
  · have hu : ‖chartPosition ξ z‖ ≤ 4 * s := by rw [norm_chartPosition]; exact hz.le
    have hA := norm_firstSummand_le hs ξ X hu
    have hB : ‖(2 * phi ξ s z) • D ξ s X (chartPosition ξ z)‖ ≤ 16 * s * mass ξ s X := by
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (by norm_num) (phi_mem_Icc ξ s z).1)]
      calc
        _ ≤ 2 * (8 * s * mass ξ s X) :=
          mul_le_mul (by linarith [(phi_mem_Icc ξ s z).2]) (norm_D_le hs ξ X hu)
            (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    have hnum : ‖S ξ s X (chartPosition ξ z) • phiGradientEuclidean s (chartPosition ξ z) +
        (2 * phi ξ s z) • D ξ s X (chartPosition ξ z)‖ ≤ 80 * s * mass ξ s X :=
      (norm_add_le _ _).trans (by linarith)
    rw [G_formula, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
    calc
      _ ≤ (1 / (N : ℝ)) * (80 * s * mass ξ s X) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = _ := by ring
  · rw [G_eq_zero_outer hs ξ X (le_of_not_gt hz), norm_zero]
    positivity

/-- The source inner count includes the plateau boundary. -/
def innerCount {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : ℕ :=
  (Finset.univ.filter fun i : Fin N ↦ torusEuclideanDist (X i) ξ ≤ 2 * s).card

/-- The source difference of actual hard counts. -/
def annulusCount {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : ℕ :=
  ballCount ξ (4 * s) X - innerCount ξ s X

def nearShellCount {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) : ℕ :=
  (Finset.univ.filter fun i : Fin N ↦
    4 * s ≤ torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < K * s).card

def shellCount {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) : ℕ :=
  annulusCount ξ s X + nearShellCount ξ s K X

theorem innerCount_real_eq {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    (innerCount ξ s X : ℝ) =
      ∑ i : Fin N, if torusEuclideanDist (X i) ξ ≤ 2 * s then (1 : ℝ) else 0 := by
  simpa only [innerCount] using!
    (Finset.natCast_card_filter (R := ℝ)
      (fun i : Fin N ↦ torusEuclideanDist (X i) ξ ≤ 2 * s) Finset.univ)

theorem innerCount_le_outerCount {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) : innerCount ξ s X ≤ ballCount ξ (4 * s) X := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  linarith

theorem annulusCount_eq_card {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) : annulusCount ξ s X =
      (Finset.univ.filter fun i : Fin N ↦
        2 * s < torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < 4 * s).card := by
  have hsub : (Finset.univ.filter fun i : Fin N ↦ torusEuclideanDist (X i) ξ ≤ 2 * s) ⊆
      (Finset.univ.filter fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith
  have he : (Finset.univ.filter fun i : Fin N ↦ torusEuclideanDist (X i) ξ < 4 * s) \
      (Finset.univ.filter fun i : Fin N ↦ torusEuclideanDist (X i) ξ ≤ 2 * s) =
      (Finset.univ.filter fun i : Fin N ↦
        2 * s < torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < 4 * s) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact and_comm
  unfold annulusCount ballCount innerCount
  rw [← Finset.card_sdiff_of_subset hsub, he]

theorem annulusCount_real_eq {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) : (annulusCount ξ s X : ℝ) =
      ∑ i : Fin N, if 2 * s < torusEuclideanDist (X i) ξ ∧
        torusEuclideanDist (X i) ξ < 4 * s then (1 : ℝ) else 0 := by
  rw [annulusCount_eq_card hs]
  exact Finset.natCast_card_filter (R := ℝ) _ _

theorem nearShellCount_real_eq {N : ℕ} (ξ : Torus) (s K : ℝ) (X : Configuration N) :
    (nearShellCount ξ s K X : ℝ) =
      ∑ i : Fin N, if 4 * s ≤ torusEuclideanDist (X i) ξ ∧
        torusEuclideanDist (X i) ξ < K * s then (1 : ℝ) else 0 := by
  simpa only [nearShellCount] using!
    (Finset.natCast_card_filter (R := ℝ)
      (fun i : Fin N ↦ 4 * s ≤ torusEuclideanDist (X i) ξ ∧
        torusEuclideanDist (X i) ξ < K * s) Finset.univ)

theorem innerCount_le_mass {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) : (innerCount ξ s X : ℝ) ≤ mass ξ s X := by
  rw [innerCount_real_eq]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · rw [phi_eq_one hs hi]
  · exact (phi_mem_Icc ξ s (X i)).1

theorem mass_le_outerCount {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) : mass ξ s X ≤ (ballCount ξ (4 * s) X : ℝ) := by
  rw [ballCount_real_eq]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact (phi_mem_Icc ξ s (X i)).2
  · rw [phi_eq_zero hs (le_of_not_gt hi)]

theorem outerCount_eq_inner_add_annulus {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) : ballCount ξ (4 * s) X =
      innerCount ξ s X + annulusCount ξ s X := by
  exact (Nat.add_sub_of_le (innerCount_le_outerCount hs ξ X)).symm

theorem outerCount_le_mass_add_annulus {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) : (ballCount ξ (4 * s) X : ℝ) ≤
      mass ξ s X + annulusCount ξ s X := by
  rw [outerCount_eq_inner_add_annulus hs, Nat.cast_add]
  exact add_le_add (innerCount_le_mass hs ξ X) le_rfl

theorem shellCount_real_eq {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 4 ≤ K)
    (ξ : Torus) (X : Configuration N) : (shellCount ξ s K X : ℝ) =
      ∑ i : Fin N, if 2 * s < torusEuclideanDist (X i) ξ ∧
        torusEuclideanDist (X i) ξ < K * s then (1 : ℝ) else 0 := by
  rw [shellCount, Nat.cast_add, annulusCount_real_eq hs, nearShellCount_real_eq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hKs : 4 * s ≤ K * s := mul_le_mul_of_nonneg_right hK hs.le
  by_cases h2 : 2 * s < torusEuclideanDist (X i) ξ
  · by_cases h4 : torusEuclideanDist (X i) ξ < 4 * s
    · have hk : torusEuclideanDist (X i) ξ < K * s := h4.trans_le hKs
      simp only [h2, h4, hk, not_le.mpr h4, and_self, ite_true, false_and, ite_false, add_zero]
    · simp only [h2, h4, le_of_not_gt h4, true_and, and_false, ite_false, zero_add]
  · have h4 : ¬4 * s ≤ torusEuclideanDist (X i) ξ := by
      have h := le_of_not_gt h2
      linarith
    simp only [h2, h4, false_and, ite_false, zero_add]

theorem shellCount_le_shellMass {N : ℕ} {s K : ℝ} (hs : 0 < s) (hK : 4 ≤ K)
    (ξ : Torus) (X : Configuration N) : (shellCount ξ s K X : ℝ) ≤ shellMass ξ s K X := by
  rw [shellCount_real_eq hs hK]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · rw [omega_eq_one hs (by linarith : 2 ≤ K) hi.1.le hi.2.le]
  · exact (omega_mem_Icc ξ s K (X i)).1

theorem innerCount_eq_zero_of_mass_lt_one {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (hM : mass ξ s X < 1) : innerCount ξ s X = 0 := by
  have hr : (innerCount ξ s X : ℝ) < 1 := (innerCount_le_mass hs ξ X).trans_lt hM
  have hn : innerCount ξ s X < 1 := by exact_mod_cast hr
  omega

theorem outerCount_pos_of_mass_pos {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (hM : 0 < mass ξ s X) : 0 < ballCount ξ (4 * s) X := by
  exact_mod_cast hM.trans_le (mass_le_outerCount hs ξ X)

/-- The actual cutoff-weighted first chart moment. -/
def firstMoment {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : PlanarSpace :=
  ∑ i : Fin N, phi ξ s (X i) • chartPosition ξ (X i)

def barycenter {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) : PlanarSpace :=
  (mass ξ s X)⁻¹ • firstMoment ξ s X

theorem D_eq_mass_smul_sub {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (u : PlanarSpace) : D ξ s X u = mass ξ s X • u - firstMoment ξ s X := by
  simp only [D, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, mass, firstMoment]

theorem D_eq_barycenter {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (hM : 0 < mass ξ s X) (u : PlanarSpace) :
    D ξ s X u = mass ξ s X • (u - barycenter ξ s X) := by
  rw [D_eq_mass_smul_sub, barycenter, smul_sub, smul_smul, mul_inv_cancel₀ hM.ne', one_smul]

theorem G_formula_barycenter {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N)
    (hM : 0 < mass ξ s X) (z : Torus) : G ξ s X z = (1 / (N : ℝ)) •
      (S ξ s X (chartPosition ξ z) • phiGradientEuclidean s (chartPosition ξ z) +
        (2 * mass ξ s X * phi ξ s z) • (chartPosition ξ z - barycenter ξ s X)) := by
  rw [G_formula, D_eq_barycenter ξ s X hM, smul_smul]
  congr 2
  congr 1
  ring

theorem sum_weighted_D_eq_zero {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    ∑ i : Fin N, phi ξ s (X i) • D ξ s X (chartPosition ξ (X i)) = 0 := by
  simp only [D_eq_mass_smul_sub, smul_sub, Finset.sum_sub_distrib]
  have he : (∑ i : Fin N, phi ξ s (X i) • (mass ξ s X • chartPosition ξ (X i))) =
      mass ξ s X • firstMoment ξ s X := by
    simp only [firstMoment, Finset.smul_sum, smul_smul, mul_comm]
  rw [he, ← Finset.sum_smul]
  change mass ξ s X • firstMoment ξ s X - mass ξ s X • firstMoment ξ s X = 0
  exact sub_self _

theorem sum_G_eq {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) :
    ∑ i : Fin N, G ξ s X (X i) = (1 / (N : ℝ)) •
      ∑ i : Fin N, S ξ s X (chartPosition ξ (X i)) •
        phiGradientEuclidean s (chartPosition ξ (X i)) := by
  simp only [G_formula, ← Finset.smul_sum, Finset.sum_add_distrib]
  have he : (∑ i : Fin N, (2 * phi ξ s (X i)) • D ξ s X (chartPosition ξ (X i))) = 0 := by
    rw [show (∑ i : Fin N, (2 * phi ξ s (X i)) • D ξ s X (chartPosition ξ (X i))) =
        (2 : ℝ) • ∑ i : Fin N, phi ξ s (X i) • D ξ s X (chartPosition ξ (X i)) by
      simp only [Finset.smul_sum, smul_smul]]
    rw [sum_weighted_D_eq_zero, smul_zero]
  rw [he, add_zero]

theorem norm_sum_G_le {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus) (X : Configuration N) :
    ‖∑ i : Fin N, G ξ s X (X i)‖ ≤ 64 * s * mass ξ s X * annulusCount ξ s X / N := by
  have hM := mass_nonneg ξ s X
  have hp (i : Fin N) : ‖S ξ s X (chartPosition ξ (X i)) •
      phiGradientEuclidean s (chartPosition ξ (X i))‖ ≤
      if 2 * s < torusEuclideanDist (X i) ξ ∧ torusEuclideanDist (X i) ξ < 4 * s
        then 64 * s * mass ξ s X else 0 := by
    split_ifs with hi
    · exact norm_firstSummand_le hs ξ X (by rw [norm_chartPosition]; exact hi.2.le)
    · have hz : phiGradientEuclidean s (chartPosition ξ (X i)) = 0 := by
        by_cases hinner : torusEuclideanDist (X i) ξ ≤ 2 * s
        · exact phiGradientEuclidean_eq_zero_inner hs (by simpa only [norm_chartPosition] using hinner)
        · have hout : 4 * s ≤ torusEuclideanDist (X i) ξ := by
            by_contra ho
            exact hi ⟨lt_of_not_ge hinner, lt_of_not_ge ho⟩
          exact phiGradientEuclidean_eq_zero_outer hs (by simpa only [norm_chartPosition] using hout)
      simp only [hz, smul_zero, norm_zero, le_refl]
  have hsum : ‖∑ i : Fin N, S ξ s X (chartPosition ξ (X i)) •
      phiGradientEuclidean s (chartPosition ξ (X i))‖ ≤
      64 * s * mass ξ s X * annulusCount ξ s X := by
    calc
      _ ≤ ∑ i : Fin N, ‖S ξ s X (chartPosition ξ (X i)) •
          phiGradientEuclidean s (chartPosition ξ (X i))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin N, if 2 * s < torusEuclideanDist (X i) ξ ∧
          torusEuclideanDist (X i) ξ < 4 * s then 64 * s * mass ξ s X else 0 :=
        Finset.sum_le_sum fun i _ ↦ hp i
      _ = _ := by
        rw [annulusCount_real_eq hs, Finset.mul_sum]
        simp only [mul_ite, mul_one, mul_zero]
  rw [sum_G_eq, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
  calc
    _ ≤ (1 / (N : ℝ)) * (64 * s * mass ξ s X * annulusCount ξ s X) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The original full product gradient and the source constant 6400. -/
theorem QFunction_norm_gradient_sq_le {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) (X : Configuration N) :
    ‖(QFunction ξ hs hsmall).gradient X‖ ^ 2 ≤ 6400 * N * s ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp (i : Fin N) : ‖G ξ s X (X i)‖ ≤ 80 * s := by
    apply (norm_G_le hs ξ X (X i)).trans
    apply (div_le_iff₀ hNr).2
    exact mul_le_mul_of_nonneg_left (mass_le_N ξ s X) (by positivity)
  have hproj (i : Fin N) : SmoothOccupations.particleProjection N i
      ((QFunction ξ hs hsmall).gradient X) = G ξ s X (X i) := by
    have he : SmoothOccupations.particleProjection N i = sourceProjection i := by
      ext y k
      rfl
    rw [he, QFunction_gradient hN,
      MovingPoleDerivativeIdentification.sourceProjection_fullGradient]
  rw [← SmoothOccupations.sum_particleProjection_norm_sq]
  simp only [hproj]
  calc
    _ ≤ ∑ _i : Fin N, (80 * s) ^ 2 := Finset.sum_le_sum fun i _ ↦
      pow_le_pow_left₀ (norm_nonneg _) (hp i) 2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem contDiff_S {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) {n : ℕ∞ω} :
    ContDiff ℝ n (S ξ s X) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)

theorem contDiff_D {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) {n : ℕ∞ω} :
    ContDiff ℝ n (D ξ s X) := by
  have he : D ξ s X = fun u ↦ mass ξ s X • u - firstMoment ξ s X :=
    funext (D_eq_mass_smul_sub ξ s X)
  rw [he]
  exact (contDiff_id.const_smul _).sub contDiff_const

theorem hasFDerivAt_S {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) :
    HasFDerivAt (S ξ s X) ((2 : ℝ) • innerSL ℝ (D ξ s X u)) u := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) fun j (_ : j ∈ Finset.univ) ↦
    (((hasFDerivAt_id u).sub_const (chartPosition ξ (X j))).norm_sq).const_mul (phi ξ s (X j))
  convert! hd using 1
  ext v
  simp only [D, sum_inner, inner_smul_left, conj_trivial, smul_apply, sum_apply,
    innerSL_apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, id_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasFDerivAt_D {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) :
    HasFDerivAt (D ξ s X) (mass ξ s X • ContinuousLinearMap.id ℝ PlanarSpace) u := by
  have he : D ξ s X = fun v ↦ mass ξ s X • v - firstMoment ξ s X :=
    funext (D_eq_mass_smul_sub ξ s X)
  rw [he]
  exact ((hasFDerivAt_id u).const_smul (mass ξ s X)).sub_const (firstMoment ξ s X)

theorem norm_fderiv_D {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) :
    ‖fderiv ℝ (D ξ s X) u‖ = mass ξ s X := by
  rw [(hasFDerivAt_D ξ s X u).fderiv, norm_smul, ContinuousLinearMap.norm_id,
    Real.norm_of_nonneg (mass_nonneg ξ s X), mul_one]

theorem norm_fderiv_S_le {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus) (X : Configuration N)
    {u : PlanarSpace} (hu : ‖u‖ ≤ 4 * s) : ‖fderiv ℝ (S ξ s X) u‖ ≤ 16 * s * mass ξ s X := by
  rw [(hasFDerivAt_S ξ s X u).fderiv, norm_smul, innerSL_apply_norm]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (8 * s * mass ξ s X) := mul_le_mul_of_nonneg_left (norm_D_le hs ξ X hu) (by norm_num)
    _ = _ := by ring

/-- The derivative of the genuine Riesz gradient is the Riesz image of the
ordinary second derivative. -/
theorem fderiv_phiGradientEuclidean_apply {s : ℝ} (hs : 0 < s) (u v : PlanarSpace) :
    fderiv ℝ (phiGradientEuclidean s) u v =
      (InnerProductSpace.toDual ℝ PlanarSpace).symm (fderiv ℝ (fderiv ℝ (phiEuclidean s)) u v) := by
  let R : (PlanarSpace →L[ℝ] ℝ) →L[ℝ] PlanarSpace :=
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd := R.hasFDerivAt.comp u
    ((((contDiff_phiEuclidean hs).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) u).hasFDerivAt)
  change fderiv ℝ (R ∘ fderiv ℝ (phiEuclidean s)) u v = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  rfl

theorem norm_fderiv_phiGradientEuclidean_le {s : ℝ} (hs : 0 < s) (u : PlanarSpace) :
    ‖fderiv ℝ (phiGradientEuclidean s) u‖ ≤ 2 / s ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_phiGradientEuclidean_apply hs, (InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map]
  exact ((fderiv ℝ (fderiv ℝ (phiEuclidean s)) u).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_second_fderiv_phiEuclidean_le hs u) (norm_nonneg v))

theorem fderiv_phiGradientEuclidean_eq_zero_outer {s : ℝ} (hs : 0 < s)
    {u : PlanarSpace} (hu : 4 * s ≤ ‖u‖) : fderiv ℝ (phiGradientEuclidean s) u = 0 := by
  have hne : u ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < 4 * s) hu)
  have hh : fderiv ℝ (fderiv ℝ (phiEuclidean s)) u = 0 := by
    ext v w
    simp only [second_fderiv_phiEuclidean hne, deriv_phiProfile_eq_zero_outer hs hu,
      second_deriv_phiProfile_eq_zero_outer hs hu, zero_div, sub_self, zero_mul,
      add_zero, zero_apply]
  ext v
  rw [fderiv_phiGradientEuclidean_apply hs, hh]
  simp only [zero_apply, map_zero]

def firstSummand {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) : PlanarSpace :=
  S ξ s X u • phiGradientEuclidean s u

def secondSummand {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) : PlanarSpace :=
  (2 * phiEuclidean s u) • D ξ s X u

def GEuclidean {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (u : PlanarSpace) : PlanarSpace :=
  (1 / (N : ℝ)) • (firstSummand ξ s X u + secondSummand ξ s X u)

theorem G_eq_GEuclidean_chart {N : ℕ} (ξ : Torus) (s : ℝ) (X : Configuration N) (z : Torus) :
    G ξ s X z = GEuclidean ξ s X (chartPosition ξ z) := by
  rw [G_formula]
  simp only [GEuclidean, firstSummand, secondSummand, phiEuclidean_chart]

theorem contDiff_firstSummand {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus) (X : Configuration N) :
    ContDiff ℝ 1 (firstSummand ξ s X) :=
  (contDiff_S ξ s X).smul (contDiff_phiGradientEuclidean hs)

theorem contDiff_secondSummand {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus) (X : Configuration N) :
    ContDiff ℝ 1 (secondSummand ξ s X) :=
  (contDiff_const.mul ((contDiff_phiEuclidean hs).of_le (by norm_num))).smul (contDiff_D ξ s X)

private theorem norm_fderiv_scalar_smul_le {c : PlanarSpace → ℝ} {f : PlanarSpace → PlanarSpace}
    {u : PlanarSpace} (hc : DifferentiableAt ℝ c u) (hf : DifferentiableAt ℝ f u) :
    ‖fderiv ℝ (fun v ↦ c v • f v) u‖ ≤
      ‖c u‖ * ‖fderiv ℝ f u‖ + ‖fderiv ℝ c u‖ * ‖f u‖ := by
  rw [fderiv_fun_smul hc hf]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply])

/-- The exact first source constant, proved on the entire zero-extended
Euclidean field and hence in particular on the source ball. -/
theorem norm_fderiv_firstSummand_le {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (u : PlanarSpace) :
    ‖fderiv ℝ (firstSummand ξ s X) u‖ ≤ 144 * mass ξ s X := by
  have hM := mass_nonneg ξ s X
  have hb := norm_fderiv_scalar_smul_le
    ((contDiff_S ξ s X (n := 1)).differentiable (by norm_num) u)
    ((contDiff_phiGradientEuclidean hs).differentiable (by norm_num) u)
  change ‖fderiv ℝ (firstSummand ξ s X) u‖ ≤ _ at hb
  by_cases hu : ‖u‖ ≤ 4 * s
  · apply hb.trans
    rw [Real.norm_of_nonneg (S_nonneg ξ s X u)]
    calc
      _ ≤ (64 * s ^ 2 * mass ξ s X) * (2 / s ^ 2) +
          (16 * s * mass ξ s X) * (1 / s) :=
        add_le_add
          (mul_le_mul (S_le hs ξ X hu) (norm_fderiv_phiGradientEuclidean_le hs u)
            (norm_nonneg _) (by positivity))
          (mul_le_mul (norm_fderiv_S_le hs ξ X hu) (norm_phiGradientEuclidean_le hs u)
            (norm_nonneg _) (by positivity))
      _ = _ := by field_simp [hs.ne']; ring
  · have hout : 4 * s ≤ ‖u‖ := (lt_of_not_ge hu).le
    simp only [phiGradientEuclidean_eq_zero_outer hs hout,
      fderiv_phiGradientEuclidean_eq_zero_outer hs hout, norm_zero, mul_zero, add_zero] at hb
    exact hb.trans (by positivity)

theorem norm_fderiv_secondSummand_le {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (u : PlanarSpace) :
    ‖fderiv ℝ (secondSummand ξ s X) u‖ ≤ 18 * mass ξ s X := by
  have hM := mass_nonneg ξ s X
  have hd : HasFDerivAt (fun v : PlanarSpace ↦ 2 * phiEuclidean s v)
      ((2 : ℝ) • innerSL ℝ (phiGradientEuclidean s u)) u :=
    (hasFDerivAt_phiEuclidean hs u).const_mul 2
  have hb := norm_fderiv_scalar_smul_le hd.differentiableAt (hasFDerivAt_D ξ s X u).differentiableAt
  change ‖fderiv ℝ (secondSummand ξ s X) u‖ ≤ _ at hb
  by_cases hu : ‖u‖ ≤ 4 * s
  · have hφ : 0 ≤ phiEuclidean s u ∧ phiEuclidean s u ≤ 1 := phiProfile_mem_Icc s ‖u‖
    have hc : ‖2 * phiEuclidean s u‖ ≤ 2 := by
      rw [Real.norm_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hφ.1)]
      linarith [hφ.2]
    have hdc : ‖fderiv ℝ (fun v : PlanarSpace ↦ 2 * phiEuclidean s v) u‖ ≤ 2 / s := by
      rw [hd.fderiv, norm_smul, innerSL_apply_norm]
      norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        _ ≤ 2 * (1 / s) := mul_le_mul_of_nonneg_left (norm_phiGradientEuclidean_le hs u) (by norm_num)
        _ = _ := by ring
    apply hb.trans
    rw [norm_fderiv_D]
    calc
      _ ≤ 2 * mass ξ s X + (2 / s) * (8 * s * mass ξ s X) :=
        add_le_add (mul_le_mul_of_nonneg_right hc hM)
          (mul_le_mul hdc (norm_D_le hs ξ X hu) (norm_nonneg _) (by positivity))
      _ = _ := by field_simp [hs.ne']; ring
  · have hout : 4 * s ≤ ‖u‖ := (lt_of_not_ge hu).le
    have hφ : phiEuclidean s u = 0 := phiProfile_eq_zero hs hout
    simp only [hφ, hd.fderiv, phiGradientEuclidean_eq_zero_outer hs hout, map_zero,
      smul_zero, norm_zero, mul_zero, zero_mul, zero_add] at hb
    exact hb.trans (by positivity)

theorem firstSummand_lipschitz {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) (u v : PlanarSpace) :
    ‖firstSummand ξ s X u - firstSummand ξ s X v‖ ≤ 144 * mass ξ s X * ‖u - v‖ := by
  exact (convex_univ : Convex ℝ (Set.univ : Set PlanarSpace)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ (contDiff_firstSummand hs ξ X).differentiable (by norm_num) y)
    (fun y _ ↦ norm_fderiv_firstSummand_le hs ξ X y) (Set.mem_univ v) (Set.mem_univ u)

theorem GEuclidean_eq_zero_outer {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) (u : PlanarSpace) (hu : 4 * s ≤ ‖u‖) : GEuclidean ξ s X u = 0 := by
  simp only [GEuclidean, firstSummand, secondSummand, phiGradientEuclidean_eq_zero_outer hs hu,
    phiEuclidean, phiProfile_eq_zero hs hu, mul_zero, zero_smul, smul_zero, add_zero]

theorem norm_fderiv_GEuclidean_le {N : ℕ} {s : ℝ} (hs : 0 < s)
    (ξ : Torus) (X : Configuration N) (u : PlanarSpace) :
    ‖fderiv ℝ (GEuclidean ξ s X) u‖ ≤ 162 * mass ξ s X / N := by
  have hd : HasFDerivAt (GEuclidean ξ s X)
      ((1 / (N : ℝ)) • (fderiv ℝ (firstSummand ξ s X) u + fderiv ℝ (secondSummand ξ s X) u)) u := by
    exact (((contDiff_firstSummand hs ξ X).differentiable (by norm_num) u).hasFDerivAt.add
      ((contDiff_secondSummand hs ξ X).differentiable (by norm_num) u).hasFDerivAt).const_smul
        (1 / (N : ℝ))
  rw [hd.fderiv, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
  calc
    _ ≤ (1 / (N : ℝ)) * (144 * mass ξ s X + 18 * mass ξ s X) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add (norm_fderiv_firstSummand_le hs ξ X u)
          (norm_fderiv_secondSummand_le hs ξ X u))) (by positivity)
    _ = _ := by ring

theorem norm_fderiv_G_lift_le {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (X : Configuration N) (y : PlanarSpace) :
    ‖fderiv ℝ (fun z : PlanarSpace ↦ G ξ s X (torusQuotient z)) y‖ ≤ 162 * mass ξ s X / N := by
  have he : (fun z : PlanarSpace ↦ G ξ s X (torusQuotient z)) =
      fun z ↦ GEuclidean ξ s X (chartPosition ξ (torusQuotient z)) := by
    funext z
    exact G_eq_GEuclidean_chart ξ s X _
  rw [he, chart_lift_fderiv (GEuclidean_eq_zero_outer hs ξ X) (by linarith : 4 * s < 1 / 2)]
  exact norm_fderiv_GEuclidean_le hs ξ X _

/-- The source physical torus-distance bound, with original particle number. -/
theorem G_lipschitz {N : ℕ} {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (ξ : Torus) (X : Configuration N) (z w : Torus) :
    ‖G ξ s X z - G ξ s X w‖ ≤ (162 * mass ξ s X / N) * torusEuclideanDist z w := by
  let a := centeredLift w
  let b := a + centeredLift (z - w)
  have ha : torusQuotient a = w := torusQuotient_centeredLift w
  have hb : torusQuotient b = z := by
    dsimp [b]
    rw [torusQuotient_add, ha, torusQuotient_centeredLift]
    abel
  have h := (convex_univ : Convex ℝ (Set.univ : Set PlanarSpace)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ (contDiff_G_lift hs hsmall ξ X).differentiable (by norm_num) y)
    (fun y _ ↦ norm_fderiv_G_lift_le hs hsmall ξ X y) (Set.mem_univ a) (Set.mem_univ b)
  rw [ha, hb] at h
  have he : b - a = centeredLift (z - w) := by dsimp [b]; abel
  simpa only [he, norm_centeredLift, torusEuclideanDist] using h

theorem QFunction_pairGradientBound {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 64) (ξ : Torus) :
    (QFunction (N := N) ξ hs hsmall).PairGradientBound 162 := by
  intro X i j _
  rw [QFunction_particleGradient hN, QFunction_particleGradient hN]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 162 * mass ξ s X / N ≤ 162 := (div_le_iff₀ hn).2
    (mul_le_mul_of_nonneg_left (mass_le_N ξ s X) (by norm_num))
  exact (G_lipschitz hs hsmall ξ X (X i) (X j)).trans
    (mul_le_mul_of_nonneg_right hc (torusEuclideanNorm_nonneg _))

/-- The weighted center is within the same displacement bound used by the
source inside-pair estimate. Positivity of the actual mass justifies cancellation. -/
theorem norm_sub_barycenter_le {N : ℕ} {s : ℝ} (hs : 0 < s) (ξ : Torus)
    (X : Configuration N) (hM : 0 < mass ξ s X) {u : PlanarSpace} (hu : ‖u‖ ≤ 4 * s) :
    ‖u - barycenter ξ s X‖ ≤ 8 * s := by
  have h := norm_D_le hs ξ X hu
  rw [D_eq_barycenter ξ s X hM, norm_smul, Real.norm_of_nonneg hM.le] at h
  exact (mul_le_mul_iff_right₀ hM).mp (by simpa only [mul_comm] using h)

theorem chart_pair_distance {s : ℝ} (hsmall : s ≤ 1 / 64) (ξ z w : Torus)
    (hz : torusEuclideanDist z ξ ≤ 4 * s) (hw : torusEuclideanDist w ξ ≤ 4 * s) :
    ‖chartPosition ξ z - chartPosition ξ w‖ = torusEuclideanDist z w := by
  have hn : ‖chartPosition ξ z - chartPosition ξ w‖ < (1 / 2 : ℝ) := by
    have h := norm_sub_le (chartPosition ξ z) (chartPosition ξ w)
    rw [norm_chartPosition, norm_chartPosition] at h
    linarith
  have he : torusQuotient (chartPosition ξ z - chartPosition ξ w) = z - w := by
    rw [torusQuotient_sub, quotient_chartPosition, quotient_chartPosition]
    abel
  have h := torusEuclideanNorm_quotient_eq_of_norm_lt_half hn
  simpa only [he, torusEuclideanDist] using h.symm

end PeriodicAttractiveLogGas.CollectiveSecondMoment
