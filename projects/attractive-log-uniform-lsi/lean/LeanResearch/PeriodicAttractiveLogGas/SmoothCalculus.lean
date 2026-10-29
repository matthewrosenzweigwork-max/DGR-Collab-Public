import LeanResearch.PeriodicAttractiveLogGas.SmoothRepresentation
import LeanResearch.PeriodicAttractiveLogGas.WeakGradient
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Ordinary directional derivatives and the coordinate Laplacian of SmoothPair.
The existing directionalDerivative is a ContinuousMap; directionalDerivativePair
equips exactly that value with its actual smooth gradient. The Laplacian is the
sum of repeated derivatives in the labelled Euclidean coordinate directions.
All integration identities use the unweighted reference Haar measure. -/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

theorem SmoothPair.contDiff_directionalDerivative_lift {N : ℕ} (f : SmoothPair N)
    (v : Gradient N) :
    ContDiff ℝ ∞ (fun y ↦ f.directionalDerivative v (configurationQuotient N y)) := by
  simp only [SmoothPair.directionalDerivative, ContinuousMap.coe_mk,
    SmoothPair.inner_gradient_configurationQuotient]
  exact (contDiff_infty_iff_fderiv.mp f.smooth).2.clm_apply contDiff_const

/-- The genuine smooth pair whose value is the existing directional derivative. -/
def SmoothPair.directionalDerivativePair {N : ℕ} (f : SmoothPair N)
    (v : Gradient N) : SmoothPair N :=
  SmoothPair.ofContDiffLift (f.directionalDerivative v)
    (f.contDiff_directionalDerivative_lift v)

@[simp]
theorem SmoothPair.directionalDerivativePair_value {N : ℕ} (f : SmoothPair N)
    (v : Gradient N) :
    (f.directionalDerivativePair v).value = f.directionalDerivative v := rfl

@[simp]
theorem SmoothPair.directionalDerivativePair_value_apply {N : ℕ} (f : SmoothPair N)
    (v : Gradient N) (x : Configuration N) :
    (f.directionalDerivativePair v).value x = inner ℝ (f.gradient x) v := rfl

theorem SmoothPair.directionalDerivativePair_lift {N : ℕ} (f : SmoothPair N)
    (v y : Gradient N) :
    (f.directionalDerivativePair v).value (configurationQuotient N y) =
      fderiv ℝ (fun w ↦ f.value (configurationQuotient N w)) y v :=
  f.inner_gradient_configurationQuotient y v

theorem SmoothPair.hasDerivAt_translate_directionalDerivativePair {N : ℕ}
    (f : SmoothPair N) (v : Gradient N) (x : Configuration N) (t : ℝ) :
    HasDerivAt (fun s ↦ f.value (configurationQuotient N (s • v) + x))
      ((f.directionalDerivativePair v).value (configurationQuotient N (t • v) + x)) t :=
  f.hasDerivAt_translate v x t

def SmoothPair.secondDirectionalDerivativePair {N : ℕ} (f : SmoothPair N)
    (v : Gradient N) : SmoothPair N :=
  (f.directionalDerivativePair v).directionalDerivativePair v

theorem SmoothPair.secondDirectionalDerivativePair_value_apply {N : ℕ}
    (f : SmoothPair N) (v : Gradient N) (x : Configuration N) :
    (f.secondDirectionalDerivativePair v).value x =
      inner ℝ ((f.directionalDerivativePair v).gradient x) v := rfl

theorem SmoothPair.secondDirectionalDerivativePair_lift {N : ℕ}
    (f : SmoothPair N) (v y : Gradient N) :
    (f.secondDirectionalDerivativePair v).value (configurationQuotient N y) =
      fderiv ℝ (fun z ↦ fderiv ℝ (fun w ↦ f.value (configurationQuotient N w)) z v) y v := by
  simp only [SmoothPair.secondDirectionalDerivativePair, SmoothPair.directionalDerivativePair_lift]

/-- The ordinary Laplacian, with no particle-number factor or Gibbs weight. -/
def SmoothPair.laplacianValue {N : ℕ} (f : SmoothPair N) : C(Configuration N, ℝ) :=
  ∑ i : Fin N, ∑ k : Fin 2,
    (f.secondDirectionalDerivativePair (EuclideanSpace.single (i, k) 1)).value

theorem SmoothPair.contDiff_laplacianValue_lift {N : ℕ} (f : SmoothPair N) :
    ContDiff ℝ ∞ (fun y ↦ f.laplacianValue (configurationQuotient N y)) := by
  simp only [SmoothPair.laplacianValue, ContinuousMap.sum_apply]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro k _
  exact (f.secondDirectionalDerivativePair (EuclideanSpace.single (i, k) 1)).smooth

def SmoothPair.laplacian {N : ℕ} (f : SmoothPair N) : SmoothPair N :=
  SmoothPair.ofContDiffLift f.laplacianValue f.contDiff_laplacianValue_lift

@[simp]
theorem SmoothPair.laplacian_value {N : ℕ} (f : SmoothPair N) :
    f.laplacian.value = f.laplacianValue := rfl

theorem SmoothPair.laplacian_value_apply {N : ℕ} (f : SmoothPair N)
    (x : Configuration N) :
    f.laplacian.value x = ∑ i : Fin N, ∑ k : Fin 2,
      (f.secondDirectionalDerivativePair (EuclideanSpace.single (i, k) 1)).value x := by
  simp only [SmoothPair.laplacian_value, SmoothPair.laplacianValue, ContinuousMap.sum_apply]

theorem SmoothPair.laplacian_value_eq_sum_inner {N : ℕ} (f : SmoothPair N)
    (x : Configuration N) :
    f.laplacian.value x = ∑ i : Fin N, ∑ k : Fin 2,
      inner ℝ ((f.directionalDerivativePair (EuclideanSpace.single (i, k) 1)).gradient x)
        (EuclideanSpace.single (i, k) 1) := by
  simp only [SmoothPair.laplacian_value_apply, SmoothPair.secondDirectionalDerivativePair_value_apply]

/-- On the Euclidean cover this is exactly the sum of ordinary coordinate
second derivatives of the scalar lift. -/
theorem SmoothPair.laplacian_lift_eq_sum_fderiv {N : ℕ} (f : SmoothPair N)
    (y : Gradient N) :
    f.laplacian.value (configurationQuotient N y) = ∑ i : Fin N, ∑ k : Fin 2,
      fderiv ℝ (fun z ↦ fderiv ℝ (fun w ↦ f.value (configurationQuotient N w)) z
        (EuclideanSpace.single (i, k) 1)) y (EuclideanSpace.single (i, k) 1) := by
  simp only [SmoothPair.laplacian_value_apply, SmoothPair.secondDirectionalDerivativePair_lift]

theorem SmoothPair.integration_by_parts_directionalDerivativePair {N : ℕ}
    (f g : SmoothPair N) (v : Gradient N) :
    ∫ x, g.value x * (f.directionalDerivativePair v).value x ∂referenceMeasure N =
      -(∫ x, f.value x * (g.directionalDerivativePair v).value x ∂referenceMeasure N) :=
  f.integration_by_parts g v

theorem SmoothPair.integral_secondDirectionalDerivativePair_selfAdjoint {N : ℕ}
    (f g : SmoothPair N) (v : Gradient N) :
    ∫ x, g.value x * (f.secondDirectionalDerivativePair v).value x ∂referenceMeasure N =
      ∫ x, f.value x * (g.secondDirectionalDerivativePair v).value x ∂referenceMeasure N := by
  calc
    _ = -(∫ x, (f.directionalDerivativePair v).value x *
        (g.directionalDerivativePair v).value x ∂referenceMeasure N) :=
      (f.directionalDerivativePair v).integration_by_parts_directionalDerivativePair g v
    _ = -(∫ x, (g.directionalDerivativePair v).value x *
        (f.directionalDerivativePair v).value x ∂referenceMeasure N) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ mul_comm _ _
    _ = _ :=
      ((g.directionalDerivativePair v).integration_by_parts_directionalDerivativePair f v).symm

/-- Self-adjointness of the ordinary smooth Laplacian in the reference Haar pairing. -/
theorem SmoothPair.integral_laplacian_selfAdjoint {N : ℕ} (f g : SmoothPair N) :
    ∫ x, g.value x * f.laplacian.value x ∂referenceMeasure N =
      ∫ x, f.value x * g.laplacian.value x ∂referenceMeasure N := by
  have hint (u w : SmoothPair N) :
      Integrable (fun x ↦ u.value x * w.value x) (referenceMeasure N) := by
    exact memLp_one_iff_integrable.mp
      (ContinuousMap.memLp (μ := referenceMeasure N) (p := 1) ℝ (u.value * w.value))
  have hexpand (u w : SmoothPair N) :
      (∫ x, u.value x * w.laplacian.value x ∂referenceMeasure N) =
        ∑ i : Fin N, ∑ k : Fin 2,
          ∫ x, u.value x * (w.secondDirectionalDerivativePair
            (EuclideanSpace.single (i, k) 1)).value x ∂referenceMeasure N := by
    simp only [SmoothPair.laplacian_value_apply, Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ ↦
      integrable_finsetSum Finset.univ (fun k _ ↦
        hint u (w.secondDirectionalDerivativePair (EuclideanSpace.single (i, k) 1))))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun k _ ↦
      hint u (w.secondDirectionalDerivativePair (EuclideanSpace.single (i, k) 1)))
  rw [hexpand g f, hexpand f g]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  exact f.integral_secondDirectionalDerivativePair_selfAdjoint g (EuclideanSpace.single (i, k) 1)

end PeriodicAttractiveLogGas
