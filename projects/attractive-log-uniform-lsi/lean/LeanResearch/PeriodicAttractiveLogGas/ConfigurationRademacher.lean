import LeanResearch.PeriodicAttractiveLogGas.SmoothRepresentation
import LeanResearch.PeriodicAttractiveLogGas.TorusCollisionIntegrability
import LeanResearch.PeriodicAttractiveLogGas.GreenNormalization
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! The Rademacher and measurable-gradient ingredients of source
Proposition 2.6, for the actual labelled reference measure.

The physical covering space is `Gradient N`, with its Euclidean norm on all
`2 * N` coordinates. A finite-dimensional linear regrouping permits an
auxiliary application of Rademacher on the product of planar spaces. Its
operator norm is used only to obtain an auxiliary Lipschitz constant for
that application. The resulting derivative is transferred back through the
inverse linear equivalence before taking any physical derivative norm.

The checked product fundamental-box quotient transports restricted product
Lebesgue measure to `referenceMeasure N`. This is the only quotient measure
transport used below: the quotient of the whole Euclidean space is not
asserted to preserve volume. The box normalization is exactly the existing
product of the mass-one planar quotient-box normalizations.

A measurable centered section makes the descended ordinary differential
measurable. Fiber invariance proves independence of every chosen section.
The Riesz vector is the existing `descendedLiftGradient`, and its norm is
exactly the physical Euclidean differential norm. Gibbs almost-everywhere
transfer uses actual absolute continuity. Weighted form-domain membership
and identification with a distributional gradient are separate obligations.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas

/-- Regrouping coordinates is linear. The source and target norms are
explicitly different; this declaration makes no isometry assertion. -/
def configurationRegroupLinearEquiv (N : ℕ) :
    (Fin N → PlanarSpace) ≃ₗ[ℝ] Gradient N where
  toFun := fun w ↦ WithLp.toLp 2 (fun ik ↦ w ik.1 ik.2)
  invFun := fun y i ↦ WithLp.toLp 2 (fun k ↦ y (i, k))
  left_inv := by
    intro w
    funext i
    ext k
    rfl
  right_inv := by
    intro y
    ext ik
    rfl
  map_add' := by
    intro w v
    ext ik
    rfl
  map_smul' := by
    intro c w
    ext ik
    rfl

def configurationRegroupEquiv (N : ℕ) :
    (Fin N → PlanarSpace) ≃L[ℝ] Gradient N :=
  (configurationRegroupLinearEquiv N).toContinuousLinearEquiv

@[simp] theorem configurationRegroupEquiv_apply (N : ℕ)
    (w : Fin N → PlanarSpace) (ik : Fin N × Fin 2) :
    configurationRegroupEquiv N w ik = w ik.1 ik.2 := rfl

@[simp] theorem configurationRegroupEquiv_symm_apply (N : ℕ)
    (y : Gradient N) (i : Fin N) (k : Fin 2) :
    (configurationRegroupEquiv N).symm y i k = y (i, k) := rfl

@[simp] theorem configurationQuotient_regroup (N : ℕ) (w : Fin N → PlanarSpace) :
    configurationQuotient N (configurationRegroupEquiv N w) =
      planarConfigurationQuotient N w := rfl

/-- Coordinatewise centered representatives, regarded as one physical
Euclidean vector. This section is measurable, with the specified half-open
box convention inherited from `centeredLift`. -/
def configurationCenteredLift {N : ℕ} (X : Configuration N) : Gradient N :=
  configurationRegroupEquiv N (fun i ↦ centeredLift (X i))

@[simp] theorem configurationCenteredLift_apply {N : ℕ}
    (X : Configuration N) (i : Fin N) (k : Fin 2) :
    configurationCenteredLift X (i, k) = centeredLift (X i) k := rfl

@[simp] theorem configurationQuotient_centeredLift {N : ℕ} (X : Configuration N) :
    configurationQuotient N (configurationCenteredLift X) = X := by
  change planarConfigurationQuotient N (fun i ↦ centeredLift (X i)) = X
  funext i
  exact torusQuotient_centeredLift (X i)

theorem measurable_configurationCenteredLift (N : ℕ) :
    Measurable (configurationCenteredLift : Configuration N → Gradient N) := by
  exact (configurationRegroupEquiv N).continuous.measurable.comp
    (measurable_pi_iff.mpr (fun i ↦ measurable_centeredLift.comp (measurable_pi_apply i)))

theorem configurationCenteredLift_mem_planarBox {N : ℕ} (X : Configuration N) :
    (configurationRegroupEquiv N).symm (configurationCenteredLift X) ∈
      planarConfigurationFundamentalBox N := by
  change (configurationRegroupEquiv N).symm
    (configurationRegroupEquiv N (fun i ↦ centeredLift (X i))) ∈ _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  intro i _
  exact centeredLift_mem_fundamentalBox (X i)

/-- The continuity needed to package a configuration function as a
`ContinuousMap` follows from the Lipschitz lift and the actual quotient map. -/
theorem continuous_configurationFunction_of_lipschitz_lift {N : ℕ}
    {f : Configuration N → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) : Continuous f := by
  apply (isOpenQuotientMap_configurationQuotient N).isQuotientMap.continuous_iff.mpr
  exact hf.continuous

/-- Differentiability itself, as well as the totalized derivative, is
invariant on quotient fibers. -/
theorem differentiableAt_lift_iff_of_configurationQuotient_eq {N : ℕ}
    (f : C(Configuration N, ℝ)) {y z : Gradient N}
    (hyz : configurationQuotient N y = configurationQuotient N z) :
    DifferentiableAt ℝ (fun w ↦ f (configurationQuotient N w)) y ↔
      DifferentiableAt ℝ (fun w ↦ f (configurationQuotient N w)) z := by
  let F : Gradient N → ℝ := fun w ↦ f (configurationQuotient N w)
  change DifferentiableAt ℝ F y ↔ DifferentiableAt ℝ F z
  have hperiod : (fun w ↦ F (w + (z - y))) = F := by
    funext w
    dsimp [F]
    rw [configurationQuotient_add, configurationQuotient_sub, ← hyz]
    simp
  have hshift : y + (z - y) = z := by
    rw [add_comm, sub_add_cancel]
  have h := differentiableAt_comp_add_right (𝕜 := ℝ) (f := F) (x := y) (z - y)
  rw [hperiod] at h
  simpa only [hshift] using h

/-- Direct Rademacher theorem in the physical Euclidean covering space. -/
theorem ae_differentiableAt_configurationLift_volume {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∀ᵐ y : Gradient N ∂volume,
      DifferentiableAt ℝ (fun w ↦ f (configurationQuotient N w)) y :=
  hf.ae_differentiableAt

/-- Rademacher in product coordinates followed by the inverse linear
equivalence gives the same ordinary physical derivative. The enlarged
auxiliary Lipschitz constant is not used in the final norm estimate. -/
theorem ae_differentiableAt_configurationLift_regroup {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∀ᵐ w : Fin N → PlanarSpace ∂volume,
      DifferentiableAt ℝ (fun y ↦ f (configurationQuotient N y))
        (configurationRegroupEquiv N w) := by
  let F : Gradient N → ℝ := fun y ↦ f (configurationQuotient N y)
  let e := configurationRegroupEquiv N
  have hcomp : LipschitzWith (K * ‖e.toContinuousLinearMap‖₊) (F ∘ e) :=
    hf.comp e.lipschitzWith
  have hae : ∀ᵐ w : Fin N → PlanarSpace ∂volume,
      DifferentiableAt ℝ (F ∘ e) w := hcomp.ae_differentiableAt
  filter_upwards [hae] with w hw
  exact e.comp_right_differentiableAt_iff.mp hw

/-- The normalized fundamental-box quotient, not a quotient of unrestricted
Euclidean volume, transfers the differentiability statement to Haar probability. -/
theorem ae_differentiableAt_configurationLift_centered {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∀ᵐ X ∂referenceMeasure N,
      DifferentiableAt ℝ (fun y ↦ f (configurationQuotient N y))
        (configurationCenteredLift X) := by
  have hm : MeasurableSet {X : Configuration N |
      DifferentiableAt ℝ (fun y ↦ f (configurationQuotient N y))
        (configurationCenteredLift X)} :=
    (measurableSet_of_differentiableAt ℝ
      (fun y ↦ f (configurationQuotient N y))).preimage
        (measurable_configurationCenteredLift N)
  have hp := measurePreserving_planarConfigurationQuotient_box N
  rw [← hp.map_eq]
  apply (ae_map_iff hp.measurable.aemeasurable hm).mpr
  filter_upwards [ae_restrict_of_ae (ae_differentiableAt_configurationLift_regroup f hf)]
    with w hw
  apply (differentiableAt_lift_iff_of_configurationQuotient_eq f
    (show configurationQuotient N (configurationRegroupEquiv N w) =
      configurationQuotient N (configurationCenteredLift (planarConfigurationQuotient N w)) by
        rw [configurationQuotient_regroup, configurationQuotient_centeredLift])).mp hw

/-- One Haar-full set works for every Euclidean representative of each
configuration; this avoids a section-dependent exceptional set. -/
theorem ae_differentiableAt_configurationLift_all_representatives {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∀ᵐ X ∂referenceMeasure N, ∀ y : Gradient N, configurationQuotient N y = X →
      DifferentiableAt ℝ (fun w ↦ f (configurationQuotient N w)) y := by
  filter_upwards [ae_differentiableAt_configurationLift_centered f hf] with X hX
  intro y hy
  exact (differentiableAt_lift_iff_of_configurationQuotient_eq f
    ((configurationQuotient_centeredLift X).trans hy.symm)).mp hX

/-- In particular this holds for every measurable section; no measurability
assumption is needed for this implication, because the full set works for all lifts. -/
theorem ae_differentiableAt_configurationLift_section {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y)))
    (s : Configuration N → Gradient N) (hs : ∀ X, configurationQuotient N (s X) = X) :
    ∀ᵐ X ∂referenceMeasure N,
      DifferentiableAt ℝ (fun y ↦ f (configurationQuotient N y)) (s X) :=
  (ae_differentiableAt_configurationLift_all_representatives f hf).mono
    (fun X hX ↦ hX (s X) (hs X))

/-- The ordinary continuous-linear-map-valued differential, evaluated at a
measurable section. At nondifferentiability points `fderiv` is totalized as zero. -/
def descendedLiftDifferential {N : ℕ} (f : C(Configuration N, ℝ))
    (X : Configuration N) : Gradient N →L[ℝ] ℝ :=
  fderiv ℝ (fun y ↦ f (configurationQuotient N y)) (configurationCenteredLift X)

@[simp] theorem descendedLiftDifferential_configurationQuotient {N : ℕ}
    (f : C(Configuration N, ℝ)) (y : Gradient N) :
    descendedLiftDifferential f (configurationQuotient N y) =
      fderiv ℝ (fun w ↦ f (configurationQuotient N w)) y :=
  fderiv_lift_eq_of_configurationQuotient_eq f (configurationQuotient_centeredLift _)

theorem descendedLiftDifferential_eq_of_section {N : ℕ}
    (f : C(Configuration N, ℝ)) (s : Configuration N → Gradient N)
    (hs : ∀ X, configurationQuotient N (s X) = X) (X : Configuration N) :
    descendedLiftDifferential f X =
      fderiv ℝ (fun y ↦ f (configurationQuotient N y)) (s X) := by
  simpa only [hs X] using descendedLiftDifferential_configurationQuotient f (s X)

theorem measurable_descendedLiftDifferential {N : ℕ} (f : C(Configuration N, ℝ)) :
    Measurable (descendedLiftDifferential f) :=
  (measurable_fderiv ℝ (fun y ↦ f (configurationQuotient N y))).comp
    (measurable_configurationCenteredLift N)

theorem descendedLiftGradient_eq_riesz_differential {N : ℕ}
    (f : C(Configuration N, ℝ)) (X : Configuration N) :
    descendedLiftGradient f X =
      (InnerProductSpace.toDual ℝ (Gradient N)).symm (descendedLiftDifferential f X) := by
  have h := descendedLiftGradient_configurationQuotient f (configurationCenteredLift X)
  rw [configurationQuotient_centeredLift] at h
  exact h

theorem measurable_descendedLiftGradient {N : ℕ} (f : C(Configuration N, ℝ)) :
    Measurable (descendedLiftGradient f) := by
  have h := (InnerProductSpace.toDual ℝ (Gradient N)).symm.continuous.measurable.comp
    (measurable_descendedLiftDifferential f)
  simpa only [Function.comp_def, ← descendedLiftGradient_eq_riesz_differential] using h

theorem innerSL_descendedLiftGradient {N : ℕ} (f : C(Configuration N, ℝ))
    (X : Configuration N) :
    innerSL ℝ (descendedLiftGradient f X) = descendedLiftDifferential f X := by
  ext v
  rw [innerSL_apply_apply, descendedLiftGradient_eq_riesz_differential,
    InnerProductSpace.toDual_symm_apply]

theorem norm_descendedLiftGradient_eq_differential {N : ℕ}
    (f : C(Configuration N, ℝ)) (X : Configuration N) :
    ‖descendedLiftGradient f X‖ = ‖descendedLiftDifferential f X‖ := by
  rw [descendedLiftGradient_eq_riesz_differential]
  exact (InnerProductSpace.toDual ℝ (Gradient N)).symm.norm_map _

/-- This bound uses precisely the original Lipschitz constant in the
physical Euclidean norm, including the totalized zero derivative off its domain. -/
theorem norm_descendedLiftDifferential_le {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) (X : Configuration N) :
    ‖descendedLiftDifferential f X‖ ≤ (K : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ hf

theorem norm_descendedLiftGradient_le {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) (X : Configuration N) :
    ‖descendedLiftGradient f X‖ ≤ (K : ℝ) := by
  rw [norm_descendedLiftGradient_eq_differential]
  exact norm_descendedLiftDifferential_le f hf X

theorem ae_hasFDerivAt_configurationLift_descendedGradient {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∀ᵐ X ∂referenceMeasure N, ∀ y : Gradient N, configurationQuotient N y = X →
      HasFDerivAt (fun w ↦ f (configurationQuotient N w))
        (innerSL ℝ (descendedLiftGradient f X)) y := by
  filter_upwards [ae_differentiableAt_configurationLift_all_representatives f hf] with X hX
  intro y hy
  rw [innerSL_descendedLiftGradient, ← hy, descendedLiftDifferential_configurationQuotient]
  exact (hX y hy).hasFDerivAt

/-- Any measure absolutely continuous with respect to the actual reference
measure inherits the single full set for all representatives. -/
theorem ae_hasFDerivAt_configurationLift_of_absolutelyContinuous {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y)))
    {μ : Measure (Configuration N)} (hμ : μ ≪ referenceMeasure N) :
    ∀ᵐ X ∂μ, ∀ y : Gradient N, configurationQuotient N y = X →
      HasFDerivAt (fun w ↦ f (configurationQuotient N w))
        (innerSL ℝ (descendedLiftGradient f X)) y :=
  hμ.ae_le (ae_hasFDerivAt_configurationLift_descendedGradient f hf)

/-- Actual Gibbs transfer uses the checked density definition's absolute
continuity, without adding a null-set or differentiability assumption. -/
theorem ae_hasFDerivAt_configurationLift_gibbs {N : ℕ}
    (g : Torus → ℝ) (β : ℝ) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∀ᵐ X ∂gibbsMeasure g N β, ∀ y : Gradient N, configurationQuotient N y = X →
      HasFDerivAt (fun w ↦ f (configurationQuotient N w))
        (innerSL ℝ (descendedLiftGradient f X)) y :=
  ae_hasFDerivAt_configurationLift_of_absolutelyContinuous f hf
    (gibbsMeasure_absolutelyContinuous g N β)

theorem descendedLiftGradient_memLp {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    MemLp (descendedLiftGradient f) 2 μ :=
  MemLp.of_bound (measurable_descendedLiftGradient f).aestronglyMeasurable (K : ℝ)
    (Eventually.of_forall (norm_descendedLiftGradient_le f hf))

/-- The actual physical Euclidean L2 vector, before asserting form-domain
membership or identification as an unweighted distributional gradient. -/
def configurationLipschitzGradientL2 {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) : Lp (Gradient N) 2 μ :=
  (descendedLiftGradient_memLp μ f hf).toLp (descendedLiftGradient f)

theorem configurationLipschitzGradientL2_coe {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    configurationLipschitzGradientL2 μ f hf =ᵐ[μ] descendedLiftGradient f :=
  (descendedLiftGradient_memLp μ f hf).coeFn_toLp

/-- Coordinate energy has the physical sum of all `2 * N` squares and no
particle-number factor or product supremum norm. -/
theorem descendedLiftGradient_norm_sq {N : ℕ}
    (f : C(Configuration N, ℝ)) (X : Configuration N) :
    ‖descendedLiftGradient f X‖ ^ 2 =
      ∑ i : Fin N, ∑ k : Fin 2, (descendedLiftGradient f X (i, k)) ^ 2 :=
  gradient_norm_sq N _

theorem integrable_sq_norm_descendedLiftGradient {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    Integrable (fun X ↦ ‖descendedLiftGradient f X‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm
    (measurable_descendedLiftGradient f).aestronglyMeasurable).mp
      (descendedLiftGradient_memLp μ f hf)

theorem configurationLipschitzGradientL2_norm_sq {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    (∫ X, ‖descendedLiftGradient f X‖ ^ 2 ∂μ) =
      ‖configurationLipschitzGradientL2 μ f hf‖ ^ 2 := by
  calc
    (∫ X, ‖descendedLiftGradient f X‖ ^ 2 ∂μ) =
        ∫ X, ‖configurationLipschitzGradientL2 μ f hf X‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [configurationLipschitzGradientL2_coe μ f hf] with X hX
      rw [hX]
    _ = ‖configurationLipschitzGradientL2 μ f hf‖ ^ 2 := by
      simpa only [L2.inner_def, real_inner_self_eq_norm_sq] using
        real_inner_self_eq_norm_sq (configurationLipschitzGradientL2 μ f hf)

/-- Membership for the specified singular Green Gibbs law. The finite-measure
instance suffices here; its actual subcritical probability normalization is
proved separately in `isProbabilityMeasure_greenGibbs`. -/
theorem descendedLiftGradient_memLp_greenGibbs (N : ℕ) (_hN : 2 ≤ N)
    {β : ℝ} (_hβ : 0 ≤ β) (_hsubcritical : β < 4)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    MemLp (descendedLiftGradient f) 2 (gibbsMeasure greenRealRepresentative N β) := by
  exact descendedLiftGradient_memLp _ f hf

end PeriodicAttractiveLogGas
