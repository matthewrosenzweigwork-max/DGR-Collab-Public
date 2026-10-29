import LeanResearch.PeriodicAttractiveLogGas.ConfigurationRademacher
import Mathlib.Topology.MetricSpace.Lipschitz

/-! The physical Euclidean quotient metric on the labelled configuration torus.

The existing metric instance on `Configuration N` is the iterated Pi supremum
metric. It is retained. The norm and distance below combine all `2 * N` circle
coordinates in L2, and the centered lift attains their Euclidean minimum.
The physical Lipschitz condition is stated explicitly and is proved equivalent,
with the identical constant, to Lipschitz continuity of the ordinary lift to
`Gradient N`. In the reverse implication the two comparison lifts differ by
the centered lift of `X - Y`; differences of independent sections are not used.

For support control, the default metric is bounded by the physical distance.
Thus every Euclidean displacement of norm at most `r` moves a configuration
by default distance at most `r`, with no particle-dependent factor.
-/

noncomputable section
open Set
open scoped BigOperators Topology NNReal

namespace PeriodicAttractiveLogGas

/-- The genuine L2 combination of all circle quotient norms. -/
def configurationEuclideanNorm {N : ℕ} (X : Configuration N) : ℝ :=
  Real.sqrt (∑ ik : Fin N × Fin 2, ‖X ik.1 ik.2‖ ^ 2)

theorem configurationEuclideanNorm_eq_piLp_norm {N : ℕ} (X : Configuration N) :
    configurationEuclideanNorm X =
      ‖(WithLp.toLp 2 (fun ik : Fin N × Fin 2 ↦ X ik.1 ik.2) :
        PiLp 2 (fun _ : Fin N × Fin 2 ↦ UnitAddCircle))‖ := by
  exact (PiLp.norm_eq_of_L2
    (WithLp.toLp 2 (fun ik : Fin N × Fin 2 ↦ X ik.1 ik.2) :
      PiLp 2 (fun _ : Fin N × Fin 2 ↦ UnitAddCircle))).symm

theorem configurationEuclideanNorm_nonneg {N : ℕ} (X : Configuration N) :
    0 ≤ configurationEuclideanNorm X := Real.sqrt_nonneg _

theorem configurationEuclideanNorm_sq {N : ℕ} (X : Configuration N) :
    configurationEuclideanNorm X ^ 2 =
      ∑ i : Fin N, ∑ k : Fin 2, ‖X i k‖ ^ 2 := by
  unfold configurationEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
  exact Finset.sum_product ..

@[simp] theorem configurationEuclideanNorm_zero (N : ℕ) :
    configurationEuclideanNorm (0 : Configuration N) = 0 := by
  simp [configurationEuclideanNorm]

@[simp] theorem configurationEuclideanNorm_eq_zero_iff {N : ℕ} (X : Configuration N) :
    configurationEuclideanNorm X = 0 ↔ X = 0 := by
  rw [configurationEuclideanNorm_eq_piLp_norm, norm_eq_zero, WithLp.toLp_eq_zero]
  constructor
  · intro h
    funext i k
    exact congrFun h (i, k)
  · intro h
    subst X
    rfl

@[simp] theorem configurationEuclideanNorm_neg {N : ℕ} (X : Configuration N) :
    configurationEuclideanNorm (-X) = configurationEuclideanNorm X := by
  simp only [configurationEuclideanNorm, Pi.neg_apply, norm_neg]

theorem configurationEuclideanNorm_add_le {N : ℕ} (X Y : Configuration N) :
    configurationEuclideanNorm (X + Y) ≤
      configurationEuclideanNorm X + configurationEuclideanNorm Y := by
  simp only [configurationEuclideanNorm_eq_piLp_norm]
  change ‖(WithLp.toLp 2 (fun ik : Fin N × Fin 2 ↦ X ik.1 ik.2) :
      PiLp 2 (fun _ : Fin N × Fin 2 ↦ UnitAddCircle)) +
        WithLp.toLp 2 (fun ik : Fin N × Fin 2 ↦ Y ik.1 ik.2)‖ ≤ _
  exact norm_add_le _ _

theorem continuous_configurationEuclideanNorm (N : ℕ) :
    Continuous (configurationEuclideanNorm : Configuration N → ℝ) := by
  exact (continuous_finsetSum Finset.univ (fun ik _ ↦
    (((continuous_apply ik.2).comp (continuous_apply ik.1)).norm.pow 2))).sqrt

/-- The chosen section realizes the physical quotient norm, even at the
half-period endpoints and in the zero-dimensional case. -/
theorem norm_configurationCenteredLift {N : ℕ} (X : Configuration N) :
    ‖configurationCenteredLift X‖ = configurationEuclideanNorm X := by
  rw [EuclideanSpace.norm_eq, configurationEuclideanNorm]
  congr 1
  apply Finset.sum_congr rfl
  intro ik _
  change ‖centeredLift (X ik.1) ik.2‖ ^ 2 = ‖X ik.1 ik.2‖ ^ 2
  rw [norm_centeredLift_apply]

/-- Projection is a contraction from the physical Euclidean covering space. -/
theorem configurationEuclideanNorm_quotient_le {N : ℕ} (y : Gradient N) :
    configurationEuclideanNorm (configurationQuotient N y) ≤ ‖y‖ := by
  rw [configurationEuclideanNorm, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro ik _
  have h : ‖(y ik : UnitAddCircle)‖ ≤ ‖y ik‖ := QuotientAddGroup.norm_mk_le_norm
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem configurationEuclideanNorm_le_norm_of_lift {N : ℕ}
    {X : Configuration N} {y : Gradient N} (hy : configurationQuotient N y = X) :
    configurationEuclideanNorm X ≤ ‖y‖ := by
  simpa only [hy] using configurationEuclideanNorm_quotient_le y

theorem norm_configurationCenteredLift_le_norm_of_lift {N : ℕ}
    {X : Configuration N} {y : Gradient N} (hy : configurationQuotient N y = X) :
    ‖configurationCenteredLift X‖ ≤ ‖y‖ := by
  rw [norm_configurationCenteredLift]
  exact configurationEuclideanNorm_le_norm_of_lift hy

theorem configurationEuclideanNorm_isLeast {N : ℕ} (X : Configuration N) :
    IsLeast {r : ℝ | ∃ y : Gradient N, configurationQuotient N y = X ∧ ‖y‖ = r}
      (configurationEuclideanNorm X) := by
  refine ⟨⟨configurationCenteredLift X, configurationQuotient_centeredLift X,
    norm_configurationCenteredLift X⟩, ?_⟩
  rintro r ⟨y, hy, rfl⟩
  exact configurationEuclideanNorm_le_norm_of_lift hy

/-- Source configuration distance, with the existing metric instance untouched. -/
def configurationEuclideanDist {N : ℕ} (X Y : Configuration N) : ℝ :=
  configurationEuclideanNorm (X - Y)

theorem configurationEuclideanDist_eq_sqrt_sum_dist_sq {N : ℕ} (X Y : Configuration N) :
    configurationEuclideanDist X Y =
      Real.sqrt (∑ ik : Fin N × Fin 2, dist (X ik.1 ik.2) (Y ik.1 ik.2) ^ 2) := by
  simp only [configurationEuclideanDist, configurationEuclideanNorm, Pi.sub_apply, dist_eq_norm]

theorem configurationEuclideanDist_nonneg {N : ℕ} (X Y : Configuration N) :
    0 ≤ configurationEuclideanDist X Y := configurationEuclideanNorm_nonneg _

@[simp] theorem configurationEuclideanDist_eq_zero_iff {N : ℕ} (X Y : Configuration N) :
    configurationEuclideanDist X Y = 0 ↔ X = Y := by
  simp only [configurationEuclideanDist, configurationEuclideanNorm_eq_zero_iff, sub_eq_zero]

@[simp] theorem configurationEuclideanDist_self {N : ℕ} (X : Configuration N) :
    configurationEuclideanDist X X = 0 :=
  (configurationEuclideanDist_eq_zero_iff X X).mpr rfl

theorem configurationEuclideanDist_comm {N : ℕ} (X Y : Configuration N) :
    configurationEuclideanDist X Y = configurationEuclideanDist Y X := by
  unfold configurationEuclideanDist
  rw [← configurationEuclideanNorm_neg, neg_sub]

theorem configurationEuclideanDist_triangle {N : ℕ} (X Y Z : Configuration N) :
    configurationEuclideanDist X Z ≤
      configurationEuclideanDist X Y + configurationEuclideanDist Y Z := by
  have h := configurationEuclideanNorm_add_le (X - Y) (Y - Z)
  simpa only [sub_add_sub_cancel, configurationEuclideanDist] using h

theorem continuous_configurationEuclideanDist (N : ℕ) :
    Continuous (fun p : Configuration N × Configuration N ↦
      configurationEuclideanDist p.1 p.2) :=
  (continuous_configurationEuclideanNorm N).comp (continuous_fst.sub continuous_snd)

theorem configurationEuclideanDist_quotient_le {N : ℕ} (y z : Gradient N) :
    configurationEuclideanDist (configurationQuotient N y) (configurationQuotient N z) ≤
      dist y z := by
  rw [configurationEuclideanDist, ← configurationQuotient_sub, dist_eq_norm]
  exact configurationEuclideanNorm_quotient_le (y - z)

/-- The distance is an attained minimum over all pairs of Euclidean lifts. -/
theorem configurationEuclideanDist_isLeast {N : ℕ} (X Y : Configuration N) :
    IsLeast {r : ℝ | ∃ y z : Gradient N,
      configurationQuotient N y = X ∧ configurationQuotient N z = Y ∧ dist y z = r}
      (configurationEuclideanDist X Y) := by
  refine ⟨⟨configurationCenteredLift (X - Y) + configurationCenteredLift Y,
    configurationCenteredLift Y, ?_, configurationQuotient_centeredLift Y, ?_⟩, ?_⟩
  · rw [configurationQuotient_add, configurationQuotient_centeredLift,
      configurationQuotient_centeredLift, sub_add_cancel]
  · rw [dist_eq_norm, add_sub_cancel_right, norm_configurationCenteredLift]
    rfl
  · rintro r ⟨y, z, hy, hz, rfl⟩
    simpa only [hy, hz] using configurationEuclideanDist_quotient_le y z

/-- Each coordinate is bounded by the genuine Euclidean quotient norm. -/
theorem norm_configuration_coordinate_le {N : ℕ} (X : Configuration N)
    (i : Fin N) (k : Fin 2) : ‖X i k‖ ≤ configurationEuclideanNorm X := by
  rw [configurationEuclideanNorm_eq_piLp_norm]
  exact PiLp.norm_apply_le
    (WithLp.toLp 2 (fun ik : Fin N × Fin 2 ↦ X ik.1 ik.2) :
      PiLp 2 (fun _ : Fin N × Fin 2 ↦ UnitAddCircle)) (i, k)

theorem norm_configuration_le_configurationEuclideanNorm {N : ℕ} (X : Configuration N) :
    ‖X‖ ≤ configurationEuclideanNorm X := by
  apply (pi_norm_le_iff_of_nonneg (configurationEuclideanNorm_nonneg X)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (configurationEuclideanNorm_nonneg X)).mpr
  exact norm_configuration_coordinate_le X i

theorem dist_default_le_configurationEuclideanDist {N : ℕ} (X Y : Configuration N) :
    dist X Y ≤ configurationEuclideanDist X Y := by
  rw [dist_eq_norm, configurationEuclideanDist]
  exact norm_configuration_le_configurationEuclideanNorm (X - Y)

theorem dist_configurationQuotient_le {N : ℕ} (y z : Gradient N) :
    dist (configurationQuotient N y) (configurationQuotient N z) ≤ dist y z :=
  (dist_default_le_configurationEuclideanDist _ _).trans
    (configurationEuclideanDist_quotient_le y z)

theorem lipschitzWith_configurationQuotient (N : ℕ) :
    LipschitzWith 1 (configurationQuotient N) :=
  LipschitzWith.mk_one dist_configurationQuotient_le

/-- The default configuration topology can be used for support margins without
enlarging the Euclidean displacement radius. -/
theorem dist_configuration_sub_quotient_le {N : ℕ} (X : Configuration N) (y : Gradient N) :
    dist X (X - configurationQuotient N y) ≤ ‖y‖ := by
  rw [dist_eq_norm, sub_sub_cancel]
  exact (norm_configuration_le_configurationEuclideanNorm _).trans
    (configurationEuclideanNorm_quotient_le y)

/-- Lipschitz continuity in the physical quotient metric, stated without
replacing the existing Pi metric instance. -/
def ConfigurationEuclideanLipschitzWith {N : ℕ} {A : Type*} [PseudoMetricSpace A]
    (K : ℝ≥0) (f : Configuration N → A) : Prop :=
  ∀ X Y, dist (f X) (f Y) ≤ (K : ℝ) * configurationEuclideanDist X Y

theorem configurationEuclideanLipschitzWith_iff_lift {N : ℕ} {A : Type*}
    [PseudoMetricSpace A] {K : ℝ≥0} {f : Configuration N → A} :
    ConfigurationEuclideanLipschitzWith K f ↔
      LipschitzWith K (fun y : Gradient N ↦ f (configurationQuotient N y)) := by
  constructor
  · intro hf
    apply LipschitzWith.of_dist_le_mul
    intro y z
    exact (hf _ _).trans
      (mul_le_mul_of_nonneg_left (configurationEuclideanDist_quotient_le y z) K.coe_nonneg)
  · intro hf X Y
    let d := configurationCenteredLift (X - Y)
    let y := configurationCenteredLift Y
    have hqy : configurationQuotient N y = Y := configurationQuotient_centeredLift Y
    have hqxy : configurationQuotient N (d + y) = X := by
      rw [configurationQuotient_add]
      change configurationQuotient N (configurationCenteredLift (X - Y)) +
        configurationQuotient N (configurationCenteredLift Y) = X
      rw [configurationQuotient_centeredLift, configurationQuotient_centeredLift, sub_add_cancel]
    have h := hf.dist_le_mul (d + y) y
    rw [hqxy, hqy] at h
    simpa only [dist_eq_norm, add_sub_cancel_right, d, norm_configurationCenteredLift,
      configurationEuclideanDist] using h

theorem ConfigurationEuclideanLipschitzWith.lift {N : ℕ} {A : Type*}
    [PseudoMetricSpace A] {K : ℝ≥0} {f : Configuration N → A}
    (hf : ConfigurationEuclideanLipschitzWith K f) :
    LipschitzWith K (fun y : Gradient N ↦ f (configurationQuotient N y)) :=
  configurationEuclideanLipschitzWith_iff_lift.mp hf

theorem ConfigurationEuclideanLipschitzWith.continuous {N : ℕ} {A : Type*}
    [PseudoMetricSpace A] {K : ℝ≥0} {f : Configuration N → A}
    (hf : ConfigurationEuclideanLipschitzWith K f) : Continuous f := by
  apply (isOpenQuotientMap_configurationQuotient N).isQuotientMap.continuous_iff.mpr
  exact hf.lift.continuous

end PeriodicAttractiveLogGas
