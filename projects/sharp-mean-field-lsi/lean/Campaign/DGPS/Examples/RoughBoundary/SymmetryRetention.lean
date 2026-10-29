import DGPS.Examples.RoughBoundary.Semicontinuity
import DGPS.Examples.RoughBoundary.FeatureMoments

/-!
# Symmetry retained by all smoothing and amplitude families (SEM007)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 8.2 and the final audit report NB-01.

For every `L > 0`, amplitude `η` and every measurable circle profile `f` (in particular every
periodic mollification `g_h` of the spike primitive), the feature `U_f = UfeatF L η f` satisfies
`U(x + 1/6) = R_{2π/3} U(x)` and `U(x + 1/2) = U(x)`, both on the real line and on the circle;
consequently `∫ U = 0`, `∫ U Uᵀ = I₂/2`, and for every `κ` the feature potential
`Ψ(t) = ‖t‖² / (2κ) - log ∫ exp ⟨t, U⟩ dm` satisfies `Ψ(R_{2π/3} t) = Ψ(t)`.
-/

open MeasureTheory Set
open scoped Real

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Examples.RoughBoundary.Spikes (pt)
open DGPS.Examples.RoughBoundary.Feature (rot120 UrealGen UtorGen
  UrealGen_add_sixth UrealGen_add_half moments_gen pt_secT)

/-- The log partition `Λ_U(t) = log ∫ exp ⟨t, U(y)⟩ dm(y)` of a circle feature `U`. -/
noncomputable def featureLogPartition (U : Torus 1 → EuclideanSpace ℝ (Fin 2))
    (t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.log (∫ y, Real.exp (inner ℝ t (U y)) ∂DGPS.haar 1)

/-- The feature potential `Ψ(t) = ‖t‖² / (2κ) - Λ_U(t)`. -/
noncomputable def featurePotential (κ : ℝ) (U : Torus 1 → EuclideanSpace ℝ (Fin 2))
    (t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖t‖ ^ 2 / (2 * κ) - featureLogPartition U t

lemma inner_rot120 (a b : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (rot120 a) (rot120 b) = inner ℝ a b := by
  have h := Real.sin_sq_add_cos_sq (2 * π / 3)
  simp only [rot120, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  simp
  linear_combination (b.ofLp 0 * a.ofLp 0 + b.ofLp 1 * a.ofLp 1) * h

lemma norm_rot120 (a : EuclideanSpace ℝ (Fin 2)) : ‖rot120 a‖ = ‖a‖ := by
  have h := inner_rot120 a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (rot120 a), norm_nonneg a, sq_nonneg (‖rot120 a‖ - ‖a‖),
    sq_nonneg (‖rot120 a‖ + ‖a‖)]

lemma spt_add (x y : ℝ) : pt (x + y) = pt x + pt y :=
  DGPS.Analysis.PeriodicMollification.pt_add x y

/-- A feature with `U(y + s) = R U(y)` has a rotation-invariant log partition. -/
lemma featureLogPartition_rot {U : Torus 1 → EuclideanSpace ℝ (Fin 2)} {s : Torus 1}
    (hU : ∀ y, U (y + s) = rot120 (U y)) (t : EuclideanSpace ℝ (Fin 2)) :
    featureLogPartition U (rot120 t) = featureLogPartition U t := by
  unfold featureLogPartition
  congr 1
  have h1 : ∀ y, inner ℝ (rot120 t) (U y) = inner ℝ t (U (y - s)) := by
    intro y
    have := hU (y - s)
    rw [sub_add_cancel] at this
    rw [this, inner_rot120]
  simp_rw [h1]
  exact MeasureTheory.integral_sub_right_eq_self
    (fun y => Real.exp (inner ℝ t (U y))) s

/-- **SEM007.**  Both exact shift symmetries, the mean-zero / covariance `I₂/2` moment identities
and the exact rotation invariance of every corresponding potential survive for every
measurable (e.g. smooth periodic mollified) profile `f` and every amplitude `η`. -/
theorem symmetry_retained_by_all_smoothing_and_amplitude_families
    {L : ℝ} (hL : 0 < L) (η : ℝ) {f : Torus 1 → ℝ} (hf : Measurable f) :
    ((∀ x, UrealF L η f (x + 1 / 6) = rot120 (UrealF L η f x)) ∧
      (∀ x, UrealF L η f (x + 1 / 2) = UrealF L η f x)) ∧
    ((∀ y, UfeatF L η f (y + pt (1 / 6)) = rot120 (UfeatF L η f y)) ∧
      (∀ y, UfeatF L η f (y + pt (1 / 2)) = UfeatF L η f y)) ∧
    (∀ κ : ℝ, ∀ t : EuclideanSpace ℝ (Fin 2),
      featurePotential κ (UfeatF L η f) (rot120 t) = featurePotential κ (UfeatF L η f) t) ∧
    ∫ y, UfeatF L η f y ∂DGPS.haar 1 = 0 ∧
    ∀ i j : Fin 2, ∫ y, UfeatF L η f y i * UfeatF L η f y j ∂DGPS.haar 1 =
      if i = j then 1 / 2 else 0 := by
  set φ : ℝ → ℝ := fun s => f (pt s) with hφdef
  have hφ : Function.Periodic φ 1 := by
    intro x
    simp only [hφdef]
    rw [Spikes.pt_add_one]
  have hφm : Measurable φ := hf.comp DGPS.Analysis.PeriodicMollification.measurable_pt
  have hUreal : ∀ x, UrealF L η f x = UrealGen φ L η x := fun x => rfl
  have hUtor : ∀ y, UfeatF L η f y = UtorGen φ L η y := fun y => rfl
  have hsix : ∀ x, UrealF L η f (x + 1 / 6) = rot120 (UrealF L η f x) := fun x =>
    UrealGen_add_sixth hL hφ η x
  have hhalf : ∀ x, UrealF L η f (x + 1 / 2) = UrealF L η f x := fun x =>
    UrealGen_add_half hL hφ η x
  have tor : ∀ (a : ℝ) (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      (∀ x, UrealF L η f (x + a) = G (UrealF L η f x)) →
      ∀ y, UfeatF L η f (y + pt a) = G (UfeatF L η f y) := by
    intro a G hG y
    conv_lhs => rw [← pt_secT y]
    rw [← spt_add, UfeatF_pt hL, hG, ← UfeatF_pt hL,
      pt_secT]
  have hsixT := tor (1 / 6) rot120 hsix
  have hhalfT := tor (1 / 2) id hhalf
  obtain ⟨m0, m2⟩ := moments_gen hL hφ hφm η
  refine ⟨⟨hsix, hhalf⟩, ⟨hsixT, hhalfT⟩, ?_, m0, m2⟩
  intro κ t
  unfold featurePotential
  rw [featureLogPartition_rot hsixT t, norm_rot120]
