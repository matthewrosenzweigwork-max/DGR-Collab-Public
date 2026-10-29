import LeanResearch.PeriodicAttractiveLogGas.RegularizedNormalization
import LeanResearch.PeriodicAttractiveLogGas.GreenRegularizationL1
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationLipschitzDomain
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationSections
import LeanResearch.PeriodicAttractiveLogGas.GreenFarOscillation
import LeanResearch.PeriodicAttractiveLogGas.MovingPoleDerivativeIdentification
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Construction for source Lemma `lem:collective-ibp`
and Proposition `prop:positive-test`.
Finite differentiability is retained: the observable has a C2 Euclidean
lift. C1 functions below carry actual continuous derivatives and are
constructed from ordinary scalar regularity. No weighted integration by
parts or collision limit is included as a field. The development record
`research/reviews/collective-integration-by-parts-development.md` tracks
the exact central checks separately from semantic review and isolated replay.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators NNReal ENNReal RealInnerProductSpace

namespace PeriodicAttractiveLogGas.CollectiveIntegrationByParts

open MovingPoleNumerators GreenFarOscillation

/-- Only genuine first derivative data, without an integration identity. -/
structure C1Function (N : ℕ) where
  value : C(Configuration N, ℝ)
  gradient : C(Configuration N, Gradient N)
  differential : ∀ y : Gradient N,
    HasFDerivAt (fun w ↦ value (configurationQuotient N w))
      (innerSL ℝ (gradient (configurationQuotient N y))) y

theorem continuous_descendedGradient_of_contDiff_one {N : ℕ}
    (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ 1 (fun y ↦ f (configurationQuotient N y))) :
    Continuous (descendedLiftGradient f) := by
  apply (isOpenQuotientMap_configurationQuotient N).isQuotientMap.continuous_iff.mpr
  have h := (InnerProductSpace.toDual ℝ (Gradient N)).symm.continuous.comp
    (hf.continuous_fderiv (by norm_num))
  simpa only [Function.comp_def, descendedLiftGradient_configurationQuotient,
    euclideanLiftGradient] using h

def C1Function.ofContDiffLift {N : ℕ} (f : C(Configuration N, ℝ))
    (hf : ContDiff ℝ 1 (fun y ↦ f (configurationQuotient N y))) : C1Function N where
  value := f
  gradient := ⟨descendedLiftGradient f, continuous_descendedGradient_of_contDiff_one f hf⟩
  differential := by
    intro y
    change HasFDerivAt (fun w ↦ f (configurationQuotient N w))
      (innerSL ℝ (descendedLiftGradient f (configurationQuotient N y))) y
    rw [innerSL_descendedLiftGradient, descendedLiftDifferential_configurationQuotient]
    exact (hf.differentiable (by norm_num) y).hasFDerivAt

def C1Function.ofSmoothPair {N : ℕ} (f : SmoothPair N) : C1Function N :=
  ⟨f.value, f.gradient, f.differential⟩

theorem C1Function.inner_gradient_lift {N : ℕ} (f : C1Function N)
    (y v : Gradient N) :
    inner ℝ (f.gradient (configurationQuotient N y)) v =
      fderiv ℝ (fun w ↦ f.value (configurationQuotient N w)) y v := by
  have h := congrArg (fun L : Gradient N →L[ℝ] ℝ ↦ L v) (f.differential y).fderiv
  simpa only [innerSL_apply_apply] using h.symm

theorem C1Function.gradient_eq_descended {N : ℕ} (f : C1Function N) (X : Configuration N) :
    f.gradient X = descendedLiftGradient f.value X := by
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N X
  apply ext_inner_right ℝ
  intro v
  rw [f.inner_gradient_lift, descendedLiftGradient_configurationQuotient,
    euclideanLiftGradient, InnerProductSpace.toDual_symm_apply]

def C1Function.mul {N : ℕ} (f g : C1Function N) : C1Function N where
  value := f.value * g.value
  gradient := ⟨fun X ↦ g.value X • f.gradient X + f.value X • g.gradient X, by fun_prop⟩
  differential := by
    intro y
    convert (f.differential y).mul (g.differential y) using 1
    ext v
    simp [innerSL_apply_apply, add_comm]

theorem C1Function.hasDerivAt_translate {N : ℕ} (f : C1Function N)
    (v : Gradient N) (X : Configuration N) (t : ℝ) :
    HasDerivAt (fun s ↦ f.value (configurationQuotient N (s • v) + X))
      (inner ℝ (f.gradient (configurationQuotient N (t • v) + X)) v) t := by
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N X
  have hline : HasDerivAt (fun s : ℝ ↦ s • v + y) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).add_const y
  have h := (f.differential (t • v + y)).comp_hasDerivAt t hline
  simpa only [configurationQuotient_add, innerSL_apply_apply] using! h

/-- Translation invariance of the actual normalized reference measure.
Only the continuous first derivative is needed in this argument. -/
theorem C1Function.integral_gradient_inner_eq_zero {N : ℕ} (f : C1Function N)
    (v : Gradient N) : ∫ X, inner ℝ (f.gradient X) v ∂referenceMeasure N = 0 := by
  let F (t : ℝ) (X : Configuration N) := f.value (configurationQuotient N (t • v) + X)
  let D (t : ℝ) (X : Configuration N) :=
    inner ℝ (f.gradient (configurationQuotient N (t • v) + X)) v
  have hFc (t : ℝ) : Continuous (F t) := by dsimp [F]; fun_prop
  have hDc (t : ℝ) : Continuous (D t) := by dsimp [D]; fun_prop
  have hFi : Integrable (F 0) (referenceMeasure N) :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := referenceMeasure N)
      (p := 1) ℝ ⟨F 0, hFc 0⟩)
  have hb : ∀ᵐ X ∂referenceMeasure N, ∀ t ∈ (Set.univ : Set ℝ),
      ‖D t X‖ ≤ ‖f.gradient‖ * ‖v‖ := by
    exact Eventually.of_forall fun X t _ ↦ (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (f.gradient.norm_coe_le_norm _) (norm_nonneg v))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := referenceMeasure N) (F := F) (F' := D) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ ↦ ‖f.gradient‖ * ‖v‖) Filter.univ_mem
    (Eventually.of_forall fun t ↦ (hFc t).aestronglyMeasurable)
    hFi (hDc 0).aestronglyMeasurable hb (integrable_const _)
    (Eventually.of_forall fun X t _ ↦ f.hasDerivAt_translate v X t)
  have hc : (fun t : ℝ ↦ ∫ X, F t X ∂referenceMeasure N) =
      fun _ ↦ ∫ X, f.value X ∂referenceMeasure N := by
    funext t
    exact integral_add_left_eq_self f.value (configurationQuotient N (t • v))
  have he := hd.2.unique (hc ▸ hasDerivAt_const (0 : ℝ)
    (∫ X, f.value X ∂referenceMeasure N))
  simpa only [D, zero_smul, configurationQuotient_zero, zero_add] using he

private theorem continuous_integrable {N : ℕ} {f : Configuration N → ℝ}
    (hf : Continuous f) : Integrable f (referenceMeasure N) :=
  memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := referenceMeasure N)
    (p := 1) ℝ ⟨f, hf⟩)

theorem C1Function.integration_by_parts {N : ℕ} (f g : C1Function N) (v : Gradient N) :
    (∫ X, g.value X * inner ℝ (f.gradient X) v ∂referenceMeasure N) =
      -(∫ X, f.value X * inner ℝ (g.gradient X) v ∂referenceMeasure N) := by
  have hi : Integrable (fun X ↦ g.value X * inner ℝ (f.gradient X) v)
      (referenceMeasure N) := continuous_integrable
    (g.value.continuous.mul (f.gradient.continuous.inner continuous_const))
  have hj : Integrable (fun X ↦ f.value X * inner ℝ (g.gradient X) v)
      (referenceMeasure N) := continuous_integrable
    (f.value.continuous.mul (g.gradient.continuous.inner continuous_const))
  have h := (f.mul g).integral_gradient_inner_eq_zero v
  simp only [C1Function.mul, ContinuousMap.coe_mk, inner_add_left, inner_smul_left,
    conj_trivial] at h
  rw [integral_add hi hj] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Exactly a scalar C2 function on the product torus, represented by its
ordinary Euclidean lift. No derivative, Laplacian, or IBP formula is a field. -/
structure C2Function (N : ℕ) where
  value : C(Configuration N, ℝ)
  regularity : ContDiff ℝ 2 (fun y ↦ value (configurationQuotient N y))

def C2Function.toC1 {N : ℕ} (V : C2Function N) : C1Function N :=
  C1Function.ofContDiffLift V.value (V.regularity.of_le (by norm_num))

def C2Function.gradient {N : ℕ} (V : C2Function N) : C(Configuration N, Gradient N) :=
  V.toC1.gradient

theorem C2Function.differential {N : ℕ} (V : C2Function N) (y : Gradient N) :
    HasFDerivAt (fun w ↦ V.value (configurationQuotient N w))
      (innerSL ℝ (V.gradient (configurationQuotient N y))) y := V.toC1.differential y

def C2Function.directionalValue {N : ℕ} (V : C2Function N) (v : Gradient N) :
    C(Configuration N, ℝ) := ⟨fun X ↦ inner ℝ (V.gradient X) v, by fun_prop⟩

theorem C2Function.directionalValue_regularity {N : ℕ} (V : C2Function N) (v : Gradient N) :
    ContDiff ℝ 1 (fun y ↦ V.directionalValue v (configurationQuotient N y)) := by
  have h := (V.regularity.fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiff_const : ContDiff ℝ 1 (fun _ : Gradient N ↦ v))
  have he : (fun y ↦ V.directionalValue v (configurationQuotient N y)) =
      fun y ↦ fderiv ℝ (fun w ↦ V.value (configurationQuotient N w)) y v := by
    funext y
    exact V.toC1.inner_gradient_lift y v
  rw [he]
  exact h

def C2Function.directional {N : ℕ} (V : C2Function N) (v : Gradient N) : C1Function N :=
  C1Function.ofContDiffLift (V.directionalValue v) (V.directionalValue_regularity v)

@[simp] theorem C2Function.directional_value {N : ℕ} (V : C2Function N)
    (v : Gradient N) (X : Configuration N) :
    (V.directional v).value X = inner ℝ (V.gradient X) v := rfl

def C2Function.laplacian {N : ℕ} (V : C2Function N) : C(Configuration N, ℝ) :=
  ⟨fun X ↦ ∑ ik : Fin N × Fin 2,
      inner ℝ ((V.directional (EuclideanSpace.single ik 1)).gradient X)
        (EuclideanSpace.single ik 1), by fun_prop⟩

theorem C2Function.laplacian_lift {N : ℕ} (V : C2Function N) (y : Gradient N) :
    V.laplacian (configurationQuotient N y) = ∑ ik : Fin N × Fin 2,
      fderiv ℝ (fun z ↦ fderiv ℝ (fun w ↦ V.value (configurationQuotient N w)) z
        (EuclideanSpace.single ik 1)) y (EuclideanSpace.single ik 1) := by
  change (∑ ik : Fin N × Fin 2,
    inner ℝ ((V.directional (EuclideanSpace.single ik 1)).gradient
      (configurationQuotient N y)) (EuclideanSpace.single ik 1)) = _
  apply Finset.sum_congr rfl
  intro ik _
  rw [(V.directional (EuclideanSpace.single ik 1)).inner_gradient_lift]
  have he : (fun z ↦ (V.directional (EuclideanSpace.single ik 1)).value
      (configurationQuotient N z)) = fun z ↦ fderiv ℝ
        (fun w ↦ V.value (configurationQuotient N w)) z (EuclideanSpace.single ik 1) := by
    funext z
    exact V.toC1.inner_gradient_lift z (EuclideanSpace.single ik 1)
  rw [he]

private theorem inner_sum_basis {N : ℕ} (v w : Gradient N) :
    (∑ ik : Fin N × Fin 2, inner ℝ v (EuclideanSpace.single ik 1) *
      inner ℝ w (EuclideanSpace.single ik 1)) = inner ℝ v w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- Weighted C1/C2 integration by parts before choosing a Gibbs weight.
Both scalar factors and all derivatives are actual continuous functions. -/
theorem C2Function.weighted_integration_by_parts_C1 {N : ℕ} (V : C2Function N)
    (G W : C1Function N) :
    (∫ X, G.value X * (V.laplacian X * W.value X +
      inner ℝ (W.gradient X) (V.gradient X)) ∂referenceMeasure N) =
      -(∫ X, inner ℝ (G.gradient X) (V.gradient X) * W.value X ∂referenceMeasure N) := by
  have h (ik : Fin N × Fin 2) :
      (∫ X, G.value X * W.value X *
        inner ℝ ((V.directional (EuclideanSpace.single ik 1)).gradient X)
          (EuclideanSpace.single ik 1) ∂referenceMeasure N) =
      -(∫ X, inner ℝ (V.gradient X) (EuclideanSpace.single ik 1) *
        (W.value X * inner ℝ (G.gradient X) (EuclideanSpace.single ik 1) +
          G.value X * inner ℝ (W.gradient X) (EuclideanSpace.single ik 1))
        ∂referenceMeasure N) := by
    simpa only [C1Function.mul, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
      C2Function.directional_value, inner_add_left, inner_smul_left, conj_trivial] using
      (V.directional (EuclideanSpace.single ik 1)).integration_by_parts (G.mul W)
        (EuclideanSpace.single ik 1)
  have hi (ik : Fin N × Fin 2) : Integrable
      (fun X ↦ G.value X * W.value X *
        inner ℝ ((V.directional (EuclideanSpace.single ik 1)).gradient X)
          (EuclideanSpace.single ik 1)) (referenceMeasure N) := by
    apply continuous_integrable
    fun_prop
  have hj (ik : Fin N × Fin 2) : Integrable
      (fun X ↦ inner ℝ (V.gradient X) (EuclideanSpace.single ik 1) *
        (W.value X * inner ℝ (G.gradient X) (EuclideanSpace.single ik 1) +
          G.value X * inner ℝ (W.gradient X) (EuclideanSpace.single ik 1)))
      (referenceMeasure N) := by
    apply continuous_integrable
    fun_prop
  have hs := congrArg (fun f : (Fin N × Fin 2) → ℝ ↦ ∑ ik, f ik) (funext h)
  simp only [Finset.sum_neg_distrib] at hs
  rw [← integral_finsetSum Finset.univ (fun ik _ ↦ hi ik),
    ← integral_finsetSum Finset.univ (fun ik _ ↦ hj ik)] at hs
  have he1 (X : Configuration N) :
      (∑ ik : Fin N × Fin 2, G.value X * W.value X *
        inner ℝ ((V.directional (EuclideanSpace.single ik 1)).gradient X)
          (EuclideanSpace.single ik 1)) = G.value X * W.value X * V.laplacian X := by
    simp only [C2Function.laplacian, ContinuousMap.coe_mk, Finset.mul_sum]
  have he2 (X : Configuration N) :
      (∑ ik : Fin N × Fin 2, inner ℝ (V.gradient X) (EuclideanSpace.single ik 1) *
        (W.value X * inner ℝ (G.gradient X) (EuclideanSpace.single ik 1) +
          G.value X * inner ℝ (W.gradient X) (EuclideanSpace.single ik 1))) =
      W.value X * inner ℝ (G.gradient X) (V.gradient X) +
        G.value X * inner ℝ (W.gradient X) (V.gradient X) := by
    simp only [mul_add, Finset.sum_add_distrib]
    have hterm (c : ℝ) (a b : Gradient N) :
        (∑ ik : Fin N × Fin 2, inner ℝ a (EuclideanSpace.single ik 1) *
          (c * inner ℝ b (EuclideanSpace.single ik 1))) = c * inner ℝ b a := by
      rw [← inner_sum_basis b a, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ik _
      ring
    rw [hterm, hterm]
  simp_rw [he1, he2] at hs
  rw [integral_add (continuous_integrable (by fun_prop))
    (continuous_integrable (by fun_prop))] at hs
  have hexpand : (∫ X, G.value X * (V.laplacian X * W.value X +
      inner ℝ (W.gradient X) (V.gradient X)) ∂referenceMeasure N) =
      (∫ X, G.value X * W.value X * V.laplacian X ∂referenceMeasure N) +
      ∫ X, G.value X * inner ℝ (W.gradient X) (V.gradient X) ∂referenceMeasure N := by
    rw [← integral_add (continuous_integrable (by fun_prop))
      (continuous_integrable (by fun_prop))]
    apply integral_congr_ae
    exact Eventually.of_forall fun X ↦ by ring
  rw [hexpand]
  have hm : (∫ X, W.value X * inner ℝ (G.gradient X) (V.gradient X) ∂referenceMeasure N) =
      ∫ X, inner ℝ (G.gradient X) (V.gradient X) * W.value X ∂referenceMeasure N := by
    apply integral_congr_ae
    exact Eventually.of_forall fun X ↦ mul_comm _ _
  rw [hm] at hs
  linarith

private theorem smoothApprox_value_bound {N : ℕ} (G : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hG : LipschitzWith K (fun y ↦ G (configurationQuotient N y)))
    (n : ℕ) (X : Configuration N) :
    ‖(configurationLipschitzSmoothApprox G n).value X‖ ≤ ‖G‖ + K := by
  have he := norm_configurationMollifiedSmoothPair_value_sub_le
    (configurationSmoothingScale n) (configurationSmoothingScale_pos n) G hG X
  change ‖(configurationLipschitzSmoothApprox G n).value X - G X‖ ≤
    (K : ℝ) * configurationSmoothingScale n at he
  have hs := mul_le_mul_of_nonneg_left (configurationSmoothingScale_le_one n) K.coe_nonneg
  have ht := norm_add_le ((configurationLipschitzSmoothApprox G n).value X - G X) (G X)
  rw [sub_add_cancel] at ht
  exact ht.trans (by nlinarith [G.norm_coe_le_norm X])

private theorem tendsto_integral_smoothApprox_mul {N : ℕ}
    (G A : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hG : LipschitzWith K (fun y ↦ G (configurationQuotient N y))) :
    Tendsto (fun n ↦ ∫ X, (configurationLipschitzSmoothApprox G n).value X * A X
      ∂referenceMeasure N) atTop (𝓝 (∫ X, G X * A X ∂referenceMeasure N)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (‖G‖ + K) * ‖A‖)
    (fun n ↦ ((configurationLipschitzSmoothApprox G n).value.continuous.mul
      A.continuous).aestronglyMeasurable) (integrable_const _)
  · intro n
    exact Eventually.of_forall fun X ↦ by
      simp only [Pi.mul_apply]
      rw [norm_mul]
      exact mul_le_mul (smoothApprox_value_bound G hG n X) (A.norm_coe_le_norm X)
        (norm_nonneg _) (by positivity)
  · exact Eventually.of_forall fun X ↦
      (tendsto_configurationLipschitzSmoothApprox_value G hG X).mul_const (A X)

private theorem tendsto_integral_smoothApprox_gradient_inner {N : ℕ}
    (G : C(Configuration N, ℝ)) (B : C(Configuration N, Gradient N)) {K : ℝ≥0}
    (hG : LipschitzWith K (fun y ↦ G (configurationQuotient N y))) :
    Tendsto (fun n ↦ ∫ X, inner ℝ ((configurationLipschitzSmoothApprox G n).gradient X)
      (B X) ∂referenceMeasure N) atTop
      (𝓝 (∫ X, inner ℝ (descendedLiftGradient G X) (B X) ∂referenceMeasure N)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (K : ℝ) * ‖B‖)
    (fun n ↦ ((configurationLipschitzSmoothApprox G n).gradient.continuous.inner
      B.continuous).aestronglyMeasurable) (integrable_const _)
  · intro n
    exact Eventually.of_forall fun X ↦ (norm_inner_le_norm _ _).trans
      (mul_le_mul (norm_configurationMollifiedSmoothPair_gradient_le
        _ (configurationSmoothingScale_pos n) G hG X) (B.norm_coe_le_norm X)
        (norm_nonneg _) K.coe_nonneg)
  · filter_upwards [ae_differentiableAt_configurationLift_centered G hG] with X hX
    exact (tendsto_configurationLipschitzSmoothApprox_gradient_at G hG hX).inner
      tendsto_const_nhds

/-- The Lipschitz test is unrestricted on the collision set. Rademacher
and the concrete configuration mollifier prove the two limiting passages. -/
theorem C2Function.weighted_integration_by_parts_lipschitz {N : ℕ}
    (V : C2Function N) (W : C1Function N) (G : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hG : LipschitzWith K (fun y ↦ G (configurationQuotient N y))) :
    (∫ X, G X * (V.laplacian X * W.value X +
      inner ℝ (W.gradient X) (V.gradient X)) ∂referenceMeasure N) =
      -(∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X) * W.value X
        ∂referenceMeasure N) := by
  let A : C(Configuration N, ℝ) :=
    ⟨fun X ↦ V.laplacian X * W.value X + inner ℝ (W.gradient X) (V.gradient X),
      by fun_prop⟩
  let B : C(Configuration N, Gradient N) :=
    ⟨fun X ↦ W.value X • V.gradient X, by fun_prop⟩
  have hleft := tendsto_integral_smoothApprox_mul G A hG
  have hright := (tendsto_integral_smoothApprox_gradient_inner G B hG).neg
  have heq (n : ℕ) : (∫ X, (configurationLipschitzSmoothApprox G n).value X * A X
      ∂referenceMeasure N) = -(∫ X,
      inner ℝ ((configurationLipschitzSmoothApprox G n).gradient X) (B X)
        ∂referenceMeasure N) := by
    simpa only [A, B, ContinuousMap.coe_mk, inner_smul_right, mul_comm,
      C1Function.ofSmoothPair] using
      V.weighted_integration_by_parts_C1
        (C1Function.ofSmoothPair (configurationLipschitzSmoothApprox G n)) W
  have h := tendsto_nhds_unique (hleft.congr fun n ↦ heq n) hright
  simpa only [A, B, ContinuousMap.coe_mk, inner_smul_right, mul_comm] using h

open MovingPoleDerivativeIdentification

/-- Coordinate gradients are actual particle blocks of the ordinary
Euclidean gradient. This definition inserts no particle-number factor. -/
def C2Function.particleGradient {N : ℕ} (V : C2Function N) (i : Fin N)
    (X : Configuration N) : PlanarSpace := sourceProjection i (V.gradient X)

private theorem configurationQuotient_variation {N : ℕ} (i : Fin N)
    (y : Gradient N) (z : PlanarSpace) :
    configurationQuotient N (sourceVariation i y z) =
      Function.update (configurationQuotient N y) i (torusQuotient z) := by
  classical
  funext k j
  change ((sourceVariation i y z (k, j) : ℝ) : UnitAddCircle) = _
  rw [sourceVariation_apply]
  by_cases h : k = i
  · subst k
    simp only [ite_true, Function.update_self]
    rfl
  · simp only [ite_eq_right h, Function.update_of_ne h]
    rfl

theorem C2Function.particleGradient_eq_ordinary {N : ℕ} (V : C2Function N)
    (i : Fin N) (X : Configuration N) :
    V.particleGradient i X = coordinateOrdinaryGradient V.value i X := by
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N X
  have hd := hasFDerivAt_sourceBlock (V.differential y) i
  have hd' : HasFDerivAt (fun z : PlanarSpace ↦
      V.value (Function.update (configurationQuotient N y) i (torusQuotient z)))
      (InnerProductSpace.toDual ℝ PlanarSpace
        (sourceProjection i (V.gradient (configurationQuotient N y))))
      (sourceProjection i y) := by
    simpa only [configurationQuotient_variation] using hd
  change _ = torusOrdinaryGradient
    (fun z ↦ V.value (Function.update (configurationQuotient N y) i z))
      (torusQuotient (sourceProjection i y))
  rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient, hd'.fderiv]
  exact ((InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _).symm

/-- This is the manuscript's quantitative assumption, with every ambient
configuration included, in particular configurations on collision diagonals. -/
def C2Function.PairGradientBound {N : ℕ} (V : C2Function N) (K : ℝ) : Prop :=
  ∀ X : Configuration N, ∀ i j : Fin N, i ≠ j →
    ‖V.particleGradient i X - V.particleGradient j X‖ ≤
      K * torusEuclideanNorm (X i - X j)

theorem C2Function.pairGradientBound_iff_ordinary {N : ℕ} (V : C2Function N) (K : ℝ) :
    V.PairGradientBound K ↔ ∀ X : Configuration N, ∀ i j : Fin N, i ≠ j →
      ‖coordinateOrdinaryGradient V.value i X - coordinateOrdinaryGradient V.value j X‖ ≤
        K * torusEuclideanDist (X i) (X j) := by
  simp only [C2Function.PairGradientBound, V.particleGradient_eq_ordinary,
    torusEuclideanDist]

/-- The canonical orientation is exactly the existing `pairEnergy` indexing. -/
def C2Function.pairDrift {N : ℕ} (V : C2Function N) (H : Torus → PlanarSpace)
    (β : ℝ) (X : Configuration N) : ℝ :=
  (β / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i,
    inner ℝ (H (X i - X j)) (V.particleGradient i X - V.particleGradient j X)

def C2Function.generator {N : ℕ} (V : C2Function N) (β : ℝ)
    (X : Configuration N) : ℝ := V.laplacian X + V.pairDrift greenGradient β X

def C2Function.regularizedGenerator {N : ℕ} (V : C2Function N)
    (β ε : ℝ) (hε : 0 < ε) (X : Configuration N) : ℝ :=
  V.laplacian X + V.pairDrift (regularizedGreenGradient ε hε) β X

private theorem projection_quotient {N : ℕ} (i : Fin N) (y : Gradient N) :
    torusQuotient (sourceProjection i y) = configurationQuotient N y i := rfl

private def pairProjection {N : ℕ} (i j : Fin N) : Gradient N →L[ℝ] PlanarSpace :=
  sourceProjection i - sourceProjection j

private theorem pairProjection_quotient {N : ℕ} (i j : Fin N) (y : Gradient N) :
    torusQuotient (pairProjection i j y) =
      configurationQuotient N y i - configurationQuotient N y j := by
  simp only [pairProjection, sub_apply, torusQuotient_sub,
    projection_quotient]

private theorem regularized_pair_differential {N : ℕ} (i j : Fin N)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (y : Gradient N) :
    HasFDerivAt (fun z ↦ regularizedGreen ε hε
      (configurationQuotient N z i - configurationQuotient N z j))
      ((regularizedGreenDifferential ε hε
        (configurationQuotient N y i - configurationQuotient N y j)).comp
          (pairProjection i j)) y := by
  have h := ((contDiff_regularizedGreen_lift ε hε hs).differentiable (by simp)
    (pairProjection i j y)).hasFDerivAt.comp y (pairProjection i j).hasFDerivAt
  rw [← regularizedGreenDifferential_lift] at h
  simpa only [Function.comp_def, pairProjection_quotient] using h

private def regularizedLogGradient (N : ℕ) (β ε : ℝ) (hε : 0 < ε)
    (X : Configuration N) : Gradient N :=
  (β / (N : ℝ)) • ∑ i : Fin N, ∑ j ∈ Finset.Ioi i,
    (pairProjection i j).adjoint (regularizedGreenGradient ε hε (X i - X j))

private theorem regularizedLogGradient_inner (N : ℕ) (β ε : ℝ) (hε : 0 < ε)
    (X : Configuration N) (v : Gradient N) :
    inner ℝ (regularizedLogGradient N β ε hε X) v =
      (β / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.Ioi i,
        inner ℝ (regularizedGreenGradient ε hε (X i - X j))
          (sourceProjection i v - sourceProjection j v) := by
  simp only [regularizedLogGradient, inner_smul_left, conj_trivial, sum_inner,
    ContinuousLinearMap.adjoint_inner_left, pairProjection, sub_apply]

private theorem continuous_regularizedLogGradient (N : ℕ) (β ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) : Continuous (regularizedLogGradient N β ε hε) := by
  have hc : Continuous (fun X : Configuration N ↦ ∑ i : Fin N, ∑ j ∈ Finset.Ioi i,
      (pairProjection i j).adjoint (regularizedGreenGradient ε hε (X i - X j))) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (pairProjection i j).adjoint.continuous.comp
      ((continuous_regularizedGreenGradient ε hε hs).comp
        ((continuous_apply i).sub (continuous_apply j)))
  change Continuous ((β / (N : ℝ)) • (fun X : Configuration N ↦
    ∑ i : Fin N, ∑ j ∈ Finset.Ioi i,
      (pairProjection i j).adjoint (regularizedGreenGradient ε hε (X i - X j))))
  exact hc.const_smul (β / (N : ℝ))

private theorem continuous_regularizedWeight (N : ℕ) (β ε : ℝ) (hε : 0 < ε) :
    Continuous (gibbsWeight (regularizedGreen ε hε) N β) := by
  unfold gibbsWeight pairEnergy
  apply Real.continuous_exp.comp
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (continuous_regularizedGreen ε hε).comp
    ((continuous_apply i).sub (continuous_apply j))

/-- The regularized density is genuinely smooth; this follows by composing
the already constructed smooth Green lift with the literal pair projections. -/
theorem regularizedWeight_contDiff_lift (N : ℕ) (β ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) : ContDiff ℝ ∞ (fun y : Gradient N ↦
      gibbsWeight (regularizedGreen ε hε) N β (configurationQuotient N y)) := by
  unfold gibbsWeight pairEnergy
  apply ContDiff.exp
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  simpa only [Function.comp_def, pairProjection_quotient] using
    (contDiff_regularizedGreen_lift ε hε hs).comp (pairProjection i j).contDiff

private theorem regularizedWeight_differential (N : ℕ) (β ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) (y : Gradient N) :
    HasFDerivAt (fun z ↦ gibbsWeight (regularizedGreen ε hε) N β
      (configurationQuotient N z))
      (innerSL ℝ (gibbsWeight (regularizedGreen ε hε) N β (configurationQuotient N y) •
        regularizedLogGradient N β ε hε (configurationQuotient N y))) y := by
  have hd : HasFDerivAt (fun z : Gradient N ↦
      (β / (N : ℝ)) * pairEnergy (regularizedGreen ε hε) N (configurationQuotient N z))
      ((β / (N : ℝ)) • ∑ i : Fin N, ∑ j ∈ Finset.Ioi i,
        (regularizedGreenDifferential ε hε
          (configurationQuotient N y i - configurationQuotient N y j)).comp
            (pairProjection i j)) y := by
    exact (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
      HasFDerivAt.fun_sum (u := Finset.Ioi i) fun j _ ↦
        regularized_pair_differential i j ε hε hs y).const_mul (β / (N : ℝ))
  convert! hd.exp using 1
  ext v
  simp only [innerSL_apply_apply, inner_smul_left, conj_trivial,
    regularizedLogGradient_inner, smul_apply,
    sum_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, pairProjection, sub_apply,
    regularizedGreenGradient_inner, gibbsWeight]

/-- The record is constructed from the actual weight and its proved
ordinary differential, rather than a smooth-density interface hypothesis. -/
def regularizedWeightC1 (N : ℕ) (β ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) : C1Function N where
  value := ⟨gibbsWeight (regularizedGreen ε hε) N β,
    continuous_regularizedWeight N β ε hε⟩
  gradient := ⟨fun X ↦ gibbsWeight (regularizedGreen ε hε) N β X •
    regularizedLogGradient N β ε hε X,
      (continuous_regularizedWeight N β ε hε).smul
        (continuous_regularizedLogGradient N β ε hε hs)⟩
  differential := regularizedWeight_differential N β ε hε hs

theorem C2Function.regularized_integration_by_parts {N : ℕ} (V : C2Function N)
    (β ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (G : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hG : LipschitzWith K (fun y ↦ G (configurationQuotient N y))) :
    (∫ X, G X * V.regularizedGenerator β ε hε X *
      gibbsWeight (regularizedGreen ε hε) N β X ∂referenceMeasure N) =
      -(∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X) *
        gibbsWeight (regularizedGreen ε hε) N β X ∂referenceMeasure N) := by
  have h := V.weighted_integration_by_parts_lipschitz
    (regularizedWeightC1 N β ε hε hs) G hG
  calc
    _ = ∫ X, G X * (V.laplacian X * (regularizedWeightC1 N β ε hε hs).value X +
        inner ℝ ((regularizedWeightC1 N β ε hε hs).gradient X) (V.gradient X))
          ∂referenceMeasure N := by
      apply integral_congr_ae
      exact Eventually.of_forall fun X ↦ by
        simp only [regularizedWeightC1, ContinuousMap.coe_mk, inner_smul_left,
          conj_trivial, regularizedLogGradient_inner, C2Function.regularizedGenerator,
          C2Function.pairDrift, C2Function.particleGradient]
        ring
    _ = _ := h

def collisionSmoothingScale (n : ℕ) : ℝ := (1 / 16) * configurationSmoothingScale n

theorem collisionSmoothingScale_pos (n : ℕ) : 0 < collisionSmoothingScale n :=
  mul_pos (by norm_num) (configurationSmoothingScale_pos n)

theorem collisionSmoothingScale_small (n : ℕ) : collisionSmoothingScale n ≤ (1 / 16 : ℝ) := by
  simpa only [collisionSmoothingScale, mul_one] using
    mul_le_mul_of_nonneg_left (configurationSmoothingScale_le_one n)
      (by norm_num : (0 : ℝ) ≤ 1 / 16)

theorem tendsto_collisionSmoothingScale : Tendsto collisionSmoothingScale atTop (𝓝 0) := by
  change Tendsto (fun n ↦ (1 / 16 : ℝ) * configurationSmoothingScale n) atTop (𝓝 0)
  simpa only [mul_zero] using
    tendsto_configurationSmoothingScale.const_mul (1 / 16 : ℝ)

/-- Differentiating the actual even regularized kernel proves oddness;
oddness of the gradient is not an additional kernel hypothesis. -/
theorem regularizedGradient_odd (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (z : Torus) : regularizedGreenGradient ε hε (-z) = -regularizedGreenGradient ε hε z := by
  let F : PlanarSpace → ℝ := fun y ↦ regularizedGreen ε hε (torusQuotient y)
  have hd (y : PlanarSpace) : HasFDerivAt F
      (regularizedGreenDifferential ε hε (torusQuotient y)) y := by
    rw [regularizedGreenDifferential_lift]
    exact ((contDiff_regularizedGreen_lift ε hε hs).differentiable (by simp) y).hasFDerivAt
  have heven : (fun y ↦ F (-y)) = F := by
    funext y
    exact (by simpa only [F, torusQuotient_neg] using
      regularizedGreen_even ε hε (torusQuotient y))
  have hc := (hd (-centeredLift z)).comp (centeredLift z)
    ((hasFDerivAt_id (centeredLift z)).neg)
  have hc' : HasFDerivAt F (-(regularizedGreenDifferential ε hε (-z)))
      (centeredLift z) := by
    simpa only [Function.comp_def, heven, torusQuotient_neg, torusQuotient_centeredLift,
      ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] using hc
  have hu := (hd (centeredLift z)).unique hc'
  rw [torusQuotient_centeredLift] at hu
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun L : PlanarSpace →L[ℝ] ℝ ↦ L v) hu
  simp only [neg_apply] at hv
  rw [regularizedGreenGradient_inner, inner_neg_left, regularizedGreenGradient_inner]
  linarith

theorem greenGradient_odd_off_origin {z : Torus} (hz : z ≠ 0) :
    greenGradient (-z) = -greenGradient z := by
  have h1 := eventually_regularizedGreenGradient_eq collisionSmoothingScale_pos
    collisionSmoothingScale_small tendsto_collisionSmoothingScale hz
  have h2 := eventually_regularizedGreenGradient_eq collisionSmoothingScale_pos
    collisionSmoothingScale_small tendsto_collisionSmoothingScale (neg_ne_zero.mpr hz)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  rw [← hn1, ← hn2]
  exact regularizedGradient_odd _ (collisionSmoothingScale_pos n)
    (collisionSmoothingScale_small n) z

private theorem pairSum_eq_planarOrderedPairs {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ i : Fin N, ∑ j ∈ Finset.Ioi i, f i j) =
      ∑ ij ∈ planarOrderedPairs N, f ij.1 ij.2 := by
  unfold planarOrderedPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  have heq : Finset.Ioi i = Finset.univ.filter (fun j : Fin N ↦ i < j) := by
    ext j
    simp
  rw [heq, Finset.sum_filter]

private theorem two_mul_pairSum {N : ℕ} (f : Fin N → Fin N → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    2 * (∑ i : Fin N, ∑ j ∈ Finset.Ioi i, f i j) =
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else f i j := by
  classical
  have hs (i j : Fin N) : (if i = j then 0 else f i j) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    by_cases hij : i = j
    · subst j
      simp
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · simp [hij, hlt, not_lt_of_ge hlt.le]
      · simp [hij, hgt, not_lt_of_ge hgt.le, hf j i]
  have hI (i : Fin N) : (∑ j ∈ Finset.Ioi i, f i j) =
      ∑ j : Fin N, if i < j then f i j else 0 := by
    have heq : Finset.Ioi i = Finset.univ.filter (fun j : Fin N ↦ i < j) := by
      ext j
      simp
    rw [heq, Finset.sum_filter]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N ↦ if j < i then f j i else 0)]
  simp_rw [hI]
  ring

/-- Exact source symmetrization, including its coefficient and original N. -/
theorem C2Function.pairDrift_eq_symmetrized {N : ℕ} (V : C2Function N)
    (hN : 0 < N) (H : Torus → PlanarSpace)
    (hH : ∀ z : Torus, z ≠ 0 → H (-z) = -H z) (β : ℝ)
    {X : Configuration N} (hX : X ∉ collisionSet N) :
    V.pairDrift H β X = (β / (2 * (N : ℝ))) *
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
        inner ℝ (H (X i - X j)) (V.particleGradient i X - V.particleGradient j X) := by
  let f (i j : Fin N) :=
    inner ℝ (H (X i - X j)) (V.particleGradient i X - V.particleGradient j X)
  have hsym : ∀ i j, f i j = f j i := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hz : X i - X j ≠ 0 := fun h ↦ hX ⟨i, j, hij, sub_eq_zero.mp h⟩
      have hodd : H (X j - X i) = -H (X i - X j) := by
        simpa only [neg_sub] using hH (X i - X j) hz
      dsimp [f]
      have hg : V.particleGradient j X - V.particleGradient i X =
          -(V.particleGradient i X - V.particleGradient j X) := by abel
      rw [hodd, hg, inner_neg_left, inner_neg_right, neg_neg]
  have hp := two_mul_pairSum f hsym
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  change (β / (N : ℝ)) * (∑ i, ∑ j ∈ Finset.Ioi i, f i j) = _
  rw [← hp]
  field_simp [hn]

theorem C2Function.generator_eq_source {N : ℕ} (V : C2Function N) (hN : 0 < N)
    (β : ℝ) {X : Configuration N} (hX : X ∉ collisionSet N) :
    V.generator β X = V.laplacian X + (β / (2 * (N : ℝ))) *
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
        inner ℝ (greenGradient (X i - X j))
          (coordinateOrdinaryGradient V.value i X - coordinateOrdinaryGradient V.value j X) := by
  rw [C2Function.generator, V.pairDrift_eq_symmetrized hN greenGradient
    (fun _ hz ↦ greenGradient_odd_off_origin hz) β hX]
  simp only [V.particleGradient_eq_ordinary]

theorem C2Function.PairGradientBound.nonneg {N : ℕ} {V : C2Function N} {K : ℝ}
    (hpair : V.PairGradientBound K) (hN : 2 ≤ N) : 0 ≤ K := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let z : Torus := torusQuotient (EuclideanSpace.single (0 : Fin 2) (1 / 4 : ℝ))
  let X : Configuration N := Function.update (fun _ ↦ (0 : Torus)) i z
  have hr : 0 < torusEuclideanNorm z := by
    have hn : ‖EuclideanSpace.single (0 : Fin 2) (1 / 4 : ℝ)‖ < (1 / 2 : ℝ) := by
      norm_num [EuclideanSpace.single, PiLp.norm_single]
    rw [torusEuclideanNorm_quotient_eq_of_norm_lt_half hn]
    norm_num [EuclideanSpace.single, PiLp.norm_single]
  have hp := hpair X i j hij
  simp only [X, Function.update_self, Function.update_of_ne hij.symm, sub_zero] at hp
  exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hp) hr

/-- Cancellation is pointwise even on the diagonals: there the gradient
difference is zero by the quantitative hypothesis. -/
theorem C2Function.pair_contribution_bound {N : ℕ} (V : C2Function N)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hpair : V.PairGradientBound K)
    (H : Torus → PlanarSpace)
    (hH : ∀ z : Torus, z ≠ 0 → ‖H z‖ ≤ C / torusEuclideanNorm z)
    (X : Configuration N) {i j : Fin N} (hij : i ≠ j) :
    ‖inner ℝ (H (X i - X j)) (V.particleGradient i X - V.particleGradient j X)‖ ≤ C * K := by
  by_cases hz : X i - X j = 0
  · have hd := hpair X i j hij
    rw [hz, torusEuclideanNorm_zero, mul_zero] at hd
    have he : V.particleGradient i X - V.particleGradient j X = 0 :=
      norm_eq_zero.mp (le_antisymm hd (norm_nonneg _))
    simp only [he, inner_zero_right, norm_zero]
    exact mul_nonneg hC hK
  · have hr := (torusEuclideanNorm_pos_iff _).mpr hz
    calc
      ‖inner ℝ (H (X i - X j)) (V.particleGradient i X - V.particleGradient j X)‖ ≤
          ‖H (X i - X j)‖ * ‖V.particleGradient i X - V.particleGradient j X‖ :=
        norm_inner_le_norm _ _
      _ ≤ (C / torusEuclideanNorm (X i - X j)) *
          (K * torusEuclideanNorm (X i - X j)) :=
        mul_le_mul (hH _ hz) (hpair X i j hij) (norm_nonneg _) (div_nonneg hC hr.le)
      _ = C * K := by field_simp [hr.ne']

/-- The exact pair count yields the source coefficient, without a factor N
loss and with no hidden dependence on the regularization scale. -/
theorem C2Function.pairDrift_bound {N : ℕ} (V : C2Function N) (hN : 2 ≤ N)
    {β K C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) (hpair : V.PairGradientBound K)
    (H : Torus → PlanarSpace)
    (hH : ∀ z : Torus, z ≠ 0 → ‖H z‖ ≤ C / torusEuclideanNorm z)
    (X : Configuration N) :
    ‖V.pairDrift H β X‖ ≤ β * ((N : ℝ) - 1) * C * K / 2 := by
  have hK := hpair.nonneg hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [C2Function.pairDrift, norm_mul, Real.norm_of_nonneg (div_nonneg hβ hn.le),
    pairSum_eq_planarOrderedPairs]
  calc
    (β / (N : ℝ)) * ‖∑ ij ∈ planarOrderedPairs N,
        inner ℝ (H (X ij.1 - X ij.2))
          (V.particleGradient ij.1 X - V.particleGradient ij.2 X)‖ ≤
        (β / (N : ℝ)) * ∑ ij ∈ planarOrderedPairs N, C * K := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hβ hn.le)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ij hij
      exact V.pair_contribution_bound hK hC hpair H hH X
        (ne_of_lt ((mem_planarOrderedPairs ij).mp hij))
    _ = β * ((N : ℝ) - 1) * C * K / 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, card_planarOrderedPairs, Nat.cast_choose_two]
      field_simp [hn.ne']

theorem C2Function.generator_bound {N : ℕ} (V : C2Function N) (hN : 2 ≤ N)
    {β K C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) (hpair : V.PairGradientBound K)
    (hkernel : KernelGradientBound C) (X : Configuration N) :
    ‖V.generator β X‖ ≤ ‖V.laplacian‖ + β * ((N : ℝ) - 1) * C * K / 2 :=
  (norm_add_le _ _).trans (add_le_add (V.laplacian.norm_coe_le_norm X)
    (V.pairDrift_bound hN hβ hC hpair greenGradient hkernel X))

theorem C2Function.regularizedGenerator_bound {N : ℕ} (V : C2Function N) (hN : 2 ≤ N)
    {β K C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) (hpair : V.PairGradientBound K)
    (hkernel : ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) → ∀ z : Torus,
      z ≠ 0 → ‖regularizedGreenGradient ε hε z‖ ≤ C / torusEuclideanNorm z)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (X : Configuration N) :
    ‖V.regularizedGenerator β ε hε X‖ ≤
      ‖V.laplacian‖ + β * ((N : ℝ) - 1) * C * K / 2 :=
  (norm_add_le _ _).trans (add_le_add (V.laplacian.norm_coe_le_norm X)
    (V.pairDrift_bound hN hβ hC hpair _ (hkernel ε hε hs) X))

theorem C2Function.measurable_pairDrift {N : ℕ} (V : C2Function N)
    {H : Torus → PlanarSpace} (hH : Measurable H) (β : ℝ) :
    Measurable (V.pairDrift H β) := by
  unfold C2Function.pairDrift
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  apply (hH.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))).inner
  exact (((sourceProjection i).continuous.comp V.gradient.continuous).sub
    ((sourceProjection j).continuous.comp V.gradient.continuous)).measurable

theorem C2Function.measurable_generator {N : ℕ} (V : C2Function N) (β : ℝ) :
    Measurable (V.generator β) :=
  V.laplacian.continuous.measurable.add (V.measurable_pairDrift measurable_greenGradient β)

theorem C2Function.continuous_regularizedGenerator {N : ℕ} (V : C2Function N)
    (β ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) :
    Continuous (V.regularizedGenerator β ε hε) := by
  unfold C2Function.regularizedGenerator C2Function.pairDrift C2Function.particleGradient
  apply V.laplacian.continuous.add
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_regularizedGreenGradient ε hε hs).comp
    ((continuous_apply i).sub (continuous_apply j))).inner
      (((sourceProjection i).continuous.comp V.gradient.continuous).sub
        ((sourceProjection j).continuous.comp V.gradient.continuous))

theorem C2Function.eventually_regularizedGenerator_eq {N : ℕ} (V : C2Function N)
    (β : ℝ) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε atTop (𝓝 0)) {X : Configuration N} (hX : X ∉ collisionSet N) :
    ∀ᶠ n in atTop, V.regularizedGenerator β (ε n) (hε n) X = V.generator β X := by
  have hp : ∀ i j : Fin N, ∀ᶠ n in atTop, i < j →
      regularizedGreenGradient (ε n) (hε n) (X i - X j) = greenGradient (X i - X j) := by
    intro i j
    by_cases hij : i < j
    · have hz : X i - X j ≠ 0 := fun h ↦ hX ⟨i, j, hij.ne, sub_eq_zero.mp h⟩
      exact (eventually_regularizedGreenGradient_eq hε hs ht hz).mono fun n hn _ ↦ hn
    · exact Eventually.of_forall fun _ h ↦ (hij h).elim
  have hall : ∀ᶠ n in atTop, ∀ i j : Fin N, i < j →
      regularizedGreenGradient (ε n) (hε n) (X i - X j) = greenGradient (X i - X j) := by
    exact (eventually_all.mpr fun i ↦ eventually_all.mpr (hp i))
  filter_upwards [hall] with n hn
  unfold C2Function.regularizedGenerator C2Function.generator C2Function.pairDrift
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [hn i j (Finset.mem_Ioi.mp hj)]

private theorem integrable_of_measurable_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {F : α → ℝ}
    (hF : Measurable F) {B : ℝ} (hB : ∀ X, ‖F X‖ ≤ B) : Integrable F μ :=
  memLp_one_iff_integrable.mp (MemLp.of_bound hF.aestronglyMeasurable B
    (Eventually.of_forall hB))

private theorem integrable_continuous_sq {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (F : C(Configuration N, ℝ)) :
    Integrable (fun X ↦ F X ^ 2) μ := by
  refine integrable_of_measurable_bound μ (F := fun X ↦ F X ^ 2)
    (F.continuous.measurable.pow_const 2) (B := ‖F‖ ^ 2) ?_
  intro X
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (F.norm_coe_le_norm X) 2

private theorem integrable_descended_gradient_sq {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) :
    Integrable (fun X ↦ ‖descendedLiftGradient F X‖ ^ 2) μ := by
  refine integrable_of_measurable_bound μ (F := fun X ↦ ‖descendedLiftGradient F X‖ ^ 2)
    ((measurable_descendedLiftGradient F).norm.pow_const 2) (B := (L : ℝ) ^ 2) ?_
  intro X
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_descendedLiftGradient_le F hF X) 2

theorem C2Function.integrable_gradient_inner {N : ℕ} (V : C2Function N)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (G : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hG : LipschitzWith L (fun y ↦ G (configurationQuotient N y))) :
    Integrable (fun X ↦ inner ℝ (descendedLiftGradient G X) (V.gradient X)) μ := by
  apply integrable_of_measurable_bound μ
    ((measurable_descendedLiftGradient G).inner V.gradient.continuous.measurable)
    (B := (L : ℝ) * ‖V.gradient‖)
  intro X
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_descendedLiftGradient_le G hG X)
    (V.gradient.norm_coe_le_norm X) (norm_nonneg _) L.coe_nonneg)

theorem C2Function.integrable_generator_mul {N : ℕ} (V : C2Function N) (hN : 2 ≤ N)
    {β K : ℝ} (hβ : 0 ≤ β) (hpair : V.PairGradientBound K)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (G : C(Configuration N, ℝ)) :
    Integrable (fun X ↦ G X * V.generator β X) μ := by
  obtain ⟨C, hC, hkernel⟩ := exists_kernelGradientBound
  let B := ‖V.laplacian‖ + β * ((N : ℝ) - 1) * C * K / 2
  apply integrable_of_measurable_bound μ
    (G.continuous.measurable.mul (V.measurable_generator β)) (B := ‖G‖ * B)
  intro X
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul (G.norm_coe_le_norm X)
    (V.generator_bound hN hβ hC.le hpair hkernel X) (norm_nonneg _) (norm_nonneg _)

/-- The two unnormalized singular integrands are genuinely integrable
before the limiting identity is normalized. -/
theorem C2Function.integrable_singular_weighted_terms {N : ℕ} (V : C2Function N)
    (hN : 2 ≤ N) {β K : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hpair : V.PairGradientBound K) (G : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hG : LipschitzWith L (fun y ↦ G (configurationQuotient N y))) :
    Integrable (fun X ↦ G X * V.generator β X * gibbsWeight regularGreenRepresentative N β X)
      (referenceMeasure N) ∧
    Integrable (fun X ↦ inner ℝ (descendedLiftGradient G X) (V.gradient X) *
      gibbsWeight regularGreenRepresentative N β X) (referenceMeasure N) := by
  obtain ⟨C, hC, hkernel⟩ := exists_kernelGradientBound
  let B := ‖V.laplacian‖ + β * ((N : ℝ) - 1) * C * K / 2
  have hw := integrable_regularGreen_gibbsWeight N hN hβ hsub
  have hwm := measurable_gibbsWeight regularGreenRepresentative_measurable N β
  constructor
  · apply (hw.const_mul (‖G‖ * B)).mono'
      ((G.continuous.measurable.mul (V.measurable_generator β)).mul hwm).aestronglyMeasurable
    exact Eventually.of_forall fun X ↦ by
      simp only [Pi.mul_apply]
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (gibbsWeight_pos _ _ _ _).le]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (G.norm_coe_le_norm X)
          (V.generator_bound hN hβ hC.le hpair hkernel X)
          (norm_nonneg _) (norm_nonneg _)) (gibbsWeight_pos _ _ _ _).le
  · apply (hw.const_mul ((L : ℝ) * ‖V.gradient‖)).mono'
      (((measurable_descendedLiftGradient G).inner V.gradient.continuous.measurable).mul
        hwm).aestronglyMeasurable
    exact Eventually.of_forall fun X ↦ by
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_of_nonneg (gibbsWeight_pos _ _ _ _).le]
      apply mul_le_mul_of_nonneg_right _ (gibbsWeight_pos _ _ _ _).le
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_descendedLiftGradient_le G hG X)
        (V.gradient.norm_coe_le_norm X) (norm_nonneg _) L.coe_nonneg)

/-- Both dominated-convergence passages use the established common majorant
for the actual attractive weights. The fixed-N pair cancellation supplies the
scale-independent generator bound, and no assertion about a weighted limit is
assumed in this theorem. -/
theorem C2Function.unnormalized_integration_by_parts {N : ℕ} (V : C2Function N)
    (hN : 2 ≤ N) {β K : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hpair : V.PairGradientBound K) (G : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hG : LipschitzWith L (fun y ↦ G (configurationQuotient N y))) :
    (∫ X, G X * V.generator β X * gibbsWeight regularGreenRepresentative N β X
      ∂referenceMeasure N) = -(∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X) *
        gibbsWeight regularGreenRepresentative N β X ∂referenceMeasure N) := by
  obtain ⟨C, hC, hkernel⟩ := exists_regularizedGreenGradient_bound
  obtain ⟨M, hMi, _hM, _hMsing, hMreg⟩ :=
    exists_regularized_green_common_majorant N hN hβ hsub
  let ε := collisionSmoothingScale
  let hε : ∀ n, 0 < ε n := collisionSmoothingScale_pos
  let hs : ∀ n, ε n ≤ (1 / 16 : ℝ) := collisionSmoothingScale_small
  let B := ‖V.laplacian‖ + β * ((N : ℝ) - 1) * C * K / 2
  have hB : 0 ≤ B := by
    have hK := hpair.nonneg hN
    have hn : 0 ≤ (N : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ N by omega))
    dsimp [B]
    positivity
  have hbound (n : ℕ) (X : Configuration N) :
      ‖V.regularizedGenerator β (ε n) (hε n) X‖ ≤ B :=
    V.regularizedGenerator_bound hN hβ hC.le hpair hkernel _ (hε n) (hs n) X
  have hae : ∀ᵐ X ∂referenceMeasure N, X ∉ collisionSet N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
  have hleft : Tendsto (fun n ↦ ∫ X,
      G X * V.regularizedGenerator β (ε n) (hε n) X *
        gibbsWeight (regularizedGreen (ε n) (hε n)) N β X ∂referenceMeasure N) atTop
      (𝓝 (∫ X, G X * V.generator β X * gibbsWeight regularGreenRepresentative N β X
        ∂referenceMeasure N)) := by
    apply tendsto_integral_of_dominated_convergence (fun X ↦ (‖G‖ * B) * M X)
      (fun n ↦ ((G.continuous.mul (V.continuous_regularizedGenerator β _ (hε n) (hs n))).mul
        (continuous_regularizedWeight N β _ (hε n))).aestronglyMeasurable)
      (hMi.const_mul (‖G‖ * B))
    · intro n
      filter_upwards [hMreg (ε n) (hε n) (hs n) β hβ le_rfl] with X hX
      simp only [Pi.mul_apply]
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (gibbsWeight_pos _ _ _ _).le]
      exact mul_le_mul (mul_le_mul (G.norm_coe_le_norm X) (hbound n X)
        (norm_nonneg _) (norm_nonneg _)) hX (gibbsWeight_pos _ _ _ _).le
          (mul_nonneg (norm_nonneg _) hB)
    · filter_upwards [hae] with X hX
      have hgen : Tendsto (fun n ↦ V.regularizedGenerator β (ε n) (hε n) X)
          atTop (𝓝 (V.generator β X)) :=
        tendsto_const_nhds.congr' (Filter.EventuallyEq.symm
          (V.eventually_regularizedGenerator_eq β hε hs tendsto_collisionSmoothingScale hX))
      exact (hgen.const_mul (G X)).mul
        (tendsto_regularizedGreen_gibbsWeight N tendsto_const_nhds hε hs
          tendsto_collisionSmoothingScale hX)
  have hright : Tendsto (fun n ↦ ∫ X,
      inner ℝ (descendedLiftGradient G X) (V.gradient X) *
        gibbsWeight (regularizedGreen (ε n) (hε n)) N β X ∂referenceMeasure N) atTop
      (𝓝 (∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X) *
        gibbsWeight regularGreenRepresentative N β X ∂referenceMeasure N)) := by
    apply tendsto_integral_of_dominated_convergence (fun X ↦ ((L : ℝ) * ‖V.gradient‖) * M X)
      (fun n ↦ (((measurable_descendedLiftGradient G).inner
        V.gradient.continuous.measurable).mul
          (continuous_regularizedWeight N β _ (hε n)).measurable).aestronglyMeasurable)
      (hMi.const_mul ((L : ℝ) * ‖V.gradient‖))
    · intro n
      filter_upwards [hMreg (ε n) (hε n) (hs n) β hβ le_rfl] with X hX
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_of_nonneg (gibbsWeight_pos _ _ _ _).le]
      apply mul_le_mul _ hX (gibbsWeight_pos _ _ _ _).le (by positivity)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (norm_descendedLiftGradient_le G hG X)
        (V.gradient.norm_coe_le_norm X) (norm_nonneg _) L.coe_nonneg)
    · filter_upwards [hae] with X hX
      exact (tendsto_regularizedGreen_gibbsWeight N tendsto_const_nhds hε hs
        tendsto_collisionSmoothingScale hX).const_mul
          (inner ℝ (descendedLiftGradient G X) (V.gradient X))
  have heq (n : ℕ) := V.regularized_integration_by_parts β (ε n) (hε n) (hs n) G hG
  exact tendsto_nhds_unique (hleft.congr fun n ↦ heq n) hright.neg

/-- Literal normalization of the existing Gibbs definition. The imported
subcritical normalization theorems establish its positive finite denominator. -/
theorem integral_gibbs_eq_normalized_weight {g : Torus → ℝ} (hg : Measurable g)
    (N : ℕ) (β : ℝ) (F : Configuration N → ℝ) :
    (∫ X, F X ∂gibbsMeasure g N β) = (partitionFunction g N β).toReal⁻¹ *
      ∫ X, F X * gibbsWeight g N β X ∂referenceMeasure N := by
  rw [gibbsMeasure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_gibbsWeight hg N β).ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
    ENNReal.toReal_inv, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun X ↦ by
    change (ENNReal.ofReal (gibbsWeight g N β X)).toReal • F X = F X * gibbsWeight g N β X
    rw [ENNReal.toReal_ofReal (gibbsWeight_pos g N β X).le, smul_eq_mul, mul_comm]

/-- Lemma `lem:collective-ibp` for the original named attractive Gibbs law.
The class is the full C2 scalar class and every ambient real Lipschitz test.
No permutation symmetry or vanishing condition at collisions occurs. -/
theorem C2Function.integration_by_parts {N : ℕ} (V : C2Function N)
    (hN : 2 ≤ N) {β K : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hpair : V.PairGradientBound K) (G : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hG : LipschitzWith L (fun y ↦ G (configurationQuotient N y))) :
    (∫ X, G X * V.generator β X ∂gibbsMeasure greenRealRepresentative N β) =
      -(∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X)
        ∂gibbsMeasure greenRealRepresentative N β) := by
  rw [← regularGreen_gibbsMeasure_eq N β,
    integral_gibbs_eq_normalized_weight regularGreenRepresentative_measurable,
    integral_gibbs_eq_normalized_weight regularGreenRepresentative_measurable,
    V.unnormalized_integration_by_parts hN hβ hsub hpair G hG, mul_neg]

/-- Source statement packaged with boundedness and genuine integrability of
both displayed integrands. The generator's off-collision source formula is
`C2Function.generator_eq_source`; the ordinary-gradient correspondence is
`C2Function.particleGradient_eq_ordinary`. -/
theorem collectiveIntegrationByParts {N : ℕ} (V : C2Function N)
    (hN : 2 ≤ N) {β K : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hpair : V.PairGradientBound K) (G : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hG : LipschitzWith L (fun y ↦ G (configurationQuotient N y))) :
    (∃ B : ℝ, ∀ X : Configuration N, X ∉ collisionSet N → ‖V.generator β X‖ ≤ B) ∧
      Integrable (fun X ↦ G X * V.generator β X) (gibbsMeasure greenRealRepresentative N β) ∧
      Integrable (fun X ↦ inner ℝ (descendedLiftGradient G X) (V.gradient X))
        (gibbsMeasure greenRealRepresentative N β) ∧
      (∫ X, G X * V.generator β X ∂gibbsMeasure greenRealRepresentative N β) =
        -(∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X)
          ∂gibbsMeasure greenRealRepresentative N β) := by
  refine ⟨?_, V.integrable_generator_mul hN hβ hpair _ G,
    V.integrable_gradient_inner _ G hG, V.integration_by_parts hN hβ hsub hpair G hG⟩
  obtain ⟨C, hC, hkernel⟩ := exists_kernelGradientBound
  exact ⟨_, fun X _ ↦ V.generator_bound hN hβ hC.le hpair hkernel X⟩

/-- The same endpoint stated with the actual Euclidean quotient metric,
instead of choosing a Euclidean lift in the public Lipschitz hypothesis. -/
theorem collectiveIntegrationByParts_physical {N : ℕ} (V : C2Function N)
    (hN : 2 ≤ N) {β K : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hpair : V.PairGradientBound K) (G : Configuration N → ℝ) {L : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith L G) :
    (∫ X, G X * V.generator β X ∂gibbsMeasure greenRealRepresentative N β) =
      -(∫ X, inner ℝ (descendedLiftGradient ⟨G, hG.continuous⟩ X) (V.gradient X)
        ∂gibbsMeasure greenRealRepresentative N β) :=
  V.integration_by_parts hN hβ hsub hpair ⟨G, hG.continuous⟩
    (configurationEuclideanLipschitzWith_iff_lift.mp hG)

theorem C1Function.lipschitz_lift {N : ℕ} (f : C1Function N) :
    LipschitzWith ‖f.gradient‖₊ (fun y ↦ f.value (configurationQuotient N y)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun y ↦ (f.differential y).differentiableAt)
  intro y
  have h : ‖fderiv ℝ (fun w ↦ f.value (configurationQuotient N w)) y‖ ≤ ‖f.gradient‖ := by
    rw [(f.differential y).fderiv, innerSL_apply_norm]
    exact f.gradient.norm_coe_le_norm _
  exact_mod_cast h

theorem C2Function.positive_minimum {N : ℕ} (V : C2Function N)
    (hV : ∀ X, 0 < V.value X) : ∃ m : ℝ, 0 < m ∧ ∀ X, m ≤ V.value X := by
  obtain ⟨X, _, hmin⟩ := (isCompact_univ : IsCompact (univ : Set (Configuration N))).exists_isMinOn
    (Set.univ_nonempty) V.value.continuous.continuousOn
  exact ⟨V.value X, hV X, isMinOn_univ_iff.mp hmin⟩

/-- An actual C1 reciprocal, constructed by differentiating the reciprocal
of a nowhere-zero scalar function. Global positivity supplies every division. -/
def C2Function.inverseC1 {N : ℕ} (V : C2Function N)
    (hV : ∀ X, 0 < V.value X) : C1Function N where
  value := ⟨fun X ↦ (V.value X)⁻¹,
    V.value.continuous.inv₀ (fun X ↦ (hV X).ne')⟩
  gradient := ⟨fun X ↦ (-(V.value X ^ 2)⁻¹) • V.gradient X, by
    have hi : Continuous (fun X ↦ -(V.value X ^ 2)⁻¹) :=
      ((V.value.continuous.pow 2).inv₀ (fun X ↦ pow_ne_zero 2 (hV X).ne')).neg
    simpa only [Pi.smul_apply] using! hi.smul V.gradient.continuous⟩
  differential := by
    intro y
    have h := (hasDerivAt_inv (hV (configurationQuotient N y)).ne').comp_hasFDerivAt y
      (V.differential y)
    convert! h using 1
    ext v
    simp only [ContinuousMap.coe_mk, innerSL_apply_apply, inner_smul_left, conj_trivial,
      smul_apply, smul_eq_mul]

private theorem lipschitz_lift_mul {N : ℕ} (f g : C(Configuration N, ℝ)) {K L : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y)))
    (hg : LipschitzWith L (fun y ↦ g (configurationQuotient N y))) :
    LipschitzWith (‖f‖₊ * L + K * ‖g‖₊)
      (fun y ↦ (f * g) (configurationQuotient N y)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro y z
  change ‖f (configurationQuotient N y) * g (configurationQuotient N y) -
      f (configurationQuotient N z) * g (configurationQuotient N z)‖ ≤ _
  calc
    _ = ‖f (configurationQuotient N y) *
        (g (configurationQuotient N y) - g (configurationQuotient N z)) +
        (f (configurationQuotient N y) - f (configurationQuotient N z)) *
          g (configurationQuotient N z)‖ := by congr 1; ring
    _ ≤ ‖f (configurationQuotient N y) *
        (g (configurationQuotient N y) - g (configurationQuotient N z))‖ +
        ‖(f (configurationQuotient N y) - f (configurationQuotient N z)) *
          g (configurationQuotient N z)‖ := norm_add_le _ _
    _ = ‖f (configurationQuotient N y)‖ *
        ‖g (configurationQuotient N y) - g (configurationQuotient N z)‖ +
        ‖f (configurationQuotient N y) - f (configurationQuotient N z)‖ *
          ‖g (configurationQuotient N z)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖f‖ * ((L : ℝ) * ‖y - z‖) + ((K : ℝ) * ‖y - z‖) * ‖g‖ :=
      add_le_add
        (mul_le_mul (f.norm_coe_le_norm _)
          (lipschitzWith_iff_norm_sub_le.mp hg y z) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (lipschitzWith_iff_norm_sub_le.mp hf y z)
          (g.norm_coe_le_norm _) (norm_nonneg _) (by positivity))
    _ = _ := by
      change _ = (‖f‖ * (L : ℝ) + (K : ℝ) * ‖g‖) * ‖y - z‖
      ring

def C2Function.positiveTestRatio {N : ℕ} (V : C2Function N)
    (hV : ∀ X, 0 < V.value X) (F : C(Configuration N, ℝ)) : C(Configuration N, ℝ) :=
  (F * F) * (V.inverseC1 hV).value

theorem C2Function.positiveTestRatio_apply {N : ℕ} (V : C2Function N)
    (hV : ∀ X, 0 < V.value X) (F : C(Configuration N, ℝ)) (X : Configuration N) :
    V.positiveTestRatio hV F X = F X ^ 2 / V.value X := by
  simp only [C2Function.positiveTestRatio, ContinuousMap.mul_apply, C2Function.inverseC1,
    ContinuousMap.coe_mk, pow_two, div_eq_mul_inv]

theorem C2Function.positiveTestRatio_lipschitz {N : ℕ} (V : C2Function N)
    (hV : ∀ X, 0 < V.value X) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun y ↦ V.positiveTestRatio hV F (configurationQuotient N y)) :=
  ⟨_, lipschitz_lift_mul (F * F) (V.inverseC1 hV).value
    (lipschitz_lift_mul F F hF hF) (V.inverseC1 hV).lipschitz_lift⟩

/-- The actual quotient derivative follows from the product rule on the
Rademacher full set for F. There is no derivative or support assumption on F
at collisions, or on the boundary of its support. -/
theorem C2Function.positiveTestRatio_gradient_ae {N : ℕ} (V : C2Function N)
    (hV : ∀ X, 0 < V.value X) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (g : Torus → ℝ) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure g N β, descendedLiftGradient (V.positiveTestRatio hV F) X =
      (2 * F X / V.value X) • descendedLiftGradient F X -
        (F X ^ 2 / V.value X ^ 2) • V.gradient X := by
  filter_upwards [ae_hasFDerivAt_configurationLift_gibbs g β F hF] with X hX
  have hDF := hX (configurationCenteredLift X) (configurationQuotient_centeredLift X)
  have hDI := (V.inverseC1 hV).differential (configurationCenteredLift X)
  rw [configurationQuotient_centeredLift] at hDI
  have hD := (hDF.mul hDF).mul hDI
  simp only [Pi.mul_apply] at hD
  apply ext_inner_right ℝ
  intro v
  have hg : inner ℝ (descendedLiftGradient (V.positiveTestRatio hV F) X) v =
      fderiv ℝ (fun y ↦ V.positiveTestRatio hV F (configurationQuotient N y))
        (configurationCenteredLift X) v := by
    rw [← innerSL_apply_apply, innerSL_descendedLiftGradient, descendedLiftDifferential]
  rw [hg]
  change fderiv ℝ
      (((fun y : Gradient N ↦ F (configurationQuotient N y)) *
          (fun y : Gradient N ↦ F (configurationQuotient N y))) *
        (fun y : Gradient N ↦ (V.inverseC1 hV).value (configurationQuotient N y)))
      (configurationCenteredLift X) v = _
  rw [hD.fderiv]
  simp only [add_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul, C2Function.inverseC1, ContinuousMap.coe_mk,
    configurationQuotient_centeredLift, inner_sub_left, inner_smul_left, conj_trivial,
    div_eq_mul_inv]
  ring

private theorem positiveTest_inner_le {N : ℕ} (a b : Gradient N) (f v : ℝ) :
    inner ℝ ((2 * f / v) • a - (f ^ 2 / v ^ 2) • b) b ≤ ‖a‖ ^ 2 := by
  have h := sq_nonneg ‖a - (f / v) • b‖
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, div_pow] at h
  simp only [inner_sub_left, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

private theorem C2Function.positiveTestRatio_generator_lower_ae {N : ℕ}
    (V : C2Function N) {β κ : ℝ} (hV : ∀ X, 0 < V.value X)
    (U : Set (Configuration N)) (hU : IsOpen U)
    (hLV : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      κ * V.value X ≤ -V.generator β X)
    (F : C(Configuration N, ℝ)) (hsupport : ∀ X, X ∉ U → F X = 0) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      κ * F X ^ 2 ≤ -(V.positiveTestRatio hV F X * V.generator β X) := by
  have hLV' : ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      X ∈ U → κ * V.value X ≤ -V.generator β X :=
    (ae_restrict_iff' hU.measurableSet).mp hLV
  filter_upwards [hLV'] with X hX
  rw [V.positiveTestRatio_apply]
  by_cases hu : X ∈ U
  · have hm := mul_le_mul_of_nonneg_left (hX hu)
      (div_nonneg (sq_nonneg (F X)) (hV X).le)
    have hc : (F X ^ 2 / V.value X) * (κ * V.value X) = κ * F X ^ 2 := by
      field_simp [(hV X).ne']
    rw [hc, mul_neg] at hm
    exact hm
  · rw [hsupport X hu]
    norm_num

private theorem C2Function.positiveTestRatio_pairing_bound_ae {N : ℕ}
    (V : C2Function N) (hV : ∀ X, 0 < V.value X)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      inner ℝ (descendedLiftGradient (V.positiveTestRatio hV F) X) (V.gradient X) ≤
        ‖descendedLiftGradient F X‖ ^ 2 := by
  filter_upwards [V.positiveTestRatio_gradient_ae hV F hF greenRealRepresentative β] with X hX
  rw [hX]
  exact positiveTest_inner_le _ _ _ _

/-- Source Proposition `prop:positive-test`, with the original Gibbs law,
the actual ordinary Lipschitz energy, and the full support hypothesis. -/
theorem C2Function.positive_test {N : ℕ} (V : C2Function N) (hN : 2 ≤ N)
    {β K κ : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (hpair : V.PairGradientBound K)
    (hV : ∀ X, 0 < V.value X) (U : Set (Configuration N)) (hU : IsOpen U)
    (hκ : 0 < κ)
    (hLV : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      κ * V.value X ≤ -V.generator β X)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, X ∉ U → F X = 0) :
    (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) ≤
      (1 / κ) * ∫ X, ‖descendedLiftGradient F X‖ ^ 2
        ∂gibbsMeasure greenRealRepresentative N β := by
  let μ : Measure (Configuration N) := gibbsMeasure greenRealRepresentative N β
  let G : C(Configuration N, ℝ) := V.positiveTestRatio hV F
  obtain ⟨LG, hG⟩ := V.positiveTestRatio_lipschitz hV F hF
  change LipschitzWith LG (fun y ↦ G (configurationQuotient N y)) at hG
  have hF2 : Integrable (fun X ↦ F X ^ 2) μ :=
    integrable_continuous_sq μ F
  have hE : Integrable (fun X ↦ ‖descendedLiftGradient F X‖ ^ 2) μ :=
    integrable_descended_gradient_sq μ F hF
  have hGL : Integrable (fun X ↦ G X * V.generator β X) μ :=
    V.integrable_generator_mul hN hβ hpair μ G
  have hGI : Integrable (fun X ↦ inner ℝ (descendedLiftGradient G X) (V.gradient X)) μ :=
    V.integrable_gradient_inner μ G hG
  have hpoint : ∀ᵐ X ∂μ, κ * F X ^ 2 ≤ -(G X * V.generator β X) :=
    V.positiveTestRatio_generator_lower_ae hV U hU hLV F hsupport
  have hfirst := integral_mono_ae (hF2.const_mul κ) hGL.neg hpoint
  simp only [Pi.neg_apply] at hfirst
  rw [integral_const_mul, integral_neg] at hfirst
  have hibp := V.integration_by_parts hN hβ hsub hpair G hG
  change (∫ X, G X * V.generator β X ∂μ) =
    -(∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X) ∂μ) at hibp
  rw [hibp, neg_neg] at hfirst
  have hsecond : (∫ X, inner ℝ (descendedLiftGradient G X) (V.gradient X) ∂μ) ≤
      ∫ X, ‖descendedLiftGradient F X‖ ^ 2 ∂μ := by
    exact integral_mono_ae hGI hE (V.positiveTestRatio_pairing_bound_ae hV F hF β)
  have hc := hfirst.trans hsecond
  have hdiv : (∫ X, F X ^ 2 ∂μ) ≤
      (∫ X, ‖descendedLiftGradient F X‖ ^ 2 ∂μ) / κ :=
    (le_div_iff₀ hκ).mpr (by simpa only [mul_comm] using hc)
  rw [one_div]
  simpa only [μ, div_eq_mul_inv, mul_comm] using hdiv

/-- The right-hand side is exactly the energy of the existing ambient
closed-form inclusion of the Lipschitz observable; no new energy is defined. -/
theorem C2Function.positive_test_ambientEnergy {N : ℕ} (V : C2Function N) (hN : 2 ≤ N)
    {β K κ : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (hpair : V.PairGradientBound K)
    (hV : ∀ X, 0 < V.value X) (U : Set (Configuration N)) (hU : IsOpen U)
    (hκ : 0 < κ)
    (hLV : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      κ * V.value X ≤ -V.generator β X)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, X ∉ U → F X = 0) :
    (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) ≤ (1 / κ) *
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  rw [configurationLipschitzAmbient_energy_eq_integral]
  exact V.positive_test hN hβ hsub hpair hV U hU hκ hLV F hF hsupport

end PeriodicAttractiveLogGas.CollectiveIntegrationByParts
