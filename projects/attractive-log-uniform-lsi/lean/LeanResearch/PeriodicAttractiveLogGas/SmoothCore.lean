import LeanResearch.PeriodicAttractiveLogGas.Geometry
import LeanResearch.PeriodicAttractiveLogGas.EntropyL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The actual periodic smooth-gradient graph. Source: prop:ambient.
The Euclidean cover defines the differential; the gradient is its Riesz vector.
The closure below is constructed without asserting that it is single-valued.
Closability and agreement with all ambient smooth functions are separate proof
obligations; neither is assumed by defining this graph. -/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

instance (N : ℕ) : BorelSpace (Configuration N) :=
  @Pi.borelSpace (Fin N) (fun _ ↦ Torus) _ _ _ _ _

def configurationQuotient (N : ℕ) (y : Gradient N) : Configuration N :=
  fun i k ↦ (y (i, k) : UnitAddCircle)

theorem configurationQuotient_surjective (N : ℕ) :
    Function.Surjective (configurationQuotient N) := by
  intro x
  refine ⟨WithLp.toLp 2 (fun ik : Fin N × Fin 2 ↦
    ((AddCircle.equivIoc (1 : ℝ) 0) (x ik.1 ik.2) : ℝ)), ?_⟩
  funext i k
  exact AddCircle.coe_equivIoc

/-- Smooth scalar function together with its genuine continuous Euclidean
gradient, specified by the derivative of its lift to the Euclidean cover. -/
structure SmoothPair (N : ℕ) where
  value : C(Configuration N, ℝ)
  gradient : C(Configuration N, Gradient N)
  smooth : ContDiff ℝ ∞ (fun y ↦ value (configurationQuotient N y))
  differential : ∀ y, HasFDerivAt (fun z ↦ value (configurationQuotient N z))
    (innerSL ℝ (gradient (configurationQuotient N y))) y

theorem SmoothPair.gradient_unique {N : ℕ} (f g : SmoothPair N) (h : f.value = g.value) :
    f.gradient = g.gradient := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N x
  have hg := g.differential y
  rw [← h] at hg
  have hd := (f.differential y).unique hg
  apply ext_inner_right ℝ
  intro v
  exact congrArg (fun L : Gradient N →L[ℝ] ℝ ↦ L v) hd

def SmoothPair.const (N : ℕ) (c : ℝ) : SmoothPair N where
  value := ContinuousMap.const _ c
  gradient := 0
  smooth := contDiff_const
  differential := by
    intro y
    simpa using (hasFDerivAt_const c y : HasFDerivAt (fun _ : Gradient N ↦ c) 0 y)

def smoothGradientGraph (N : ℕ) (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    Set (Lp ℝ 2 μ × Lp (Gradient N) 2 μ) :=
  Set.range (fun f : SmoothPair N ↦
    (ContinuousMap.toLp 2 μ ℝ f.value, ContinuousMap.toLp 2 μ ℝ f.gradient))

/-- Closure in scalar/vector L2 of the specified periodic smooth gradient graph.
Single-valuedness is not built into this definition and must be proved. -/
def closedGradientGraph (N : ℕ) (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    Set (Lp ℝ 2 μ × Lp (Gradient N) 2 μ) := closure (smoothGradientGraph N μ)

theorem smoothPair_mem_closedGradientGraph (N : ℕ) (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (f : SmoothPair N) :
    (ContinuousMap.toLp 2 μ ℝ f.value, ContinuousMap.toLp 2 μ ℝ f.gradient) ∈
      closedGradientGraph N μ := subset_closure ⟨f, rfl⟩

theorem constant_mem_closedGradientGraph (N : ℕ) (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (c : ℝ) :
    (ContinuousMap.toLp 2 μ ℝ (ContinuousMap.const _ c), (0 : Lp (Gradient N) 2 μ)) ∈
      closedGradientGraph N μ := by
  simpa [SmoothPair.const] using smoothPair_mem_closedGradientGraph N μ (SmoothPair.const N c)

def labelledCosine (N : ℕ) (i : Fin N) (k : Fin 2) : C(Configuration N, ℝ) where
  toFun x := (fourier 1 (x i k)).re
  continuous_toFun := by fun_prop

def labelledCosineGradient (N : ℕ) (i : Fin N) (k : Fin 2) : C(Configuration N, Gradient N) where
  toFun x := (-2 * Real.pi * (fourier 1 (x i k)).im) • EuclideanSpace.single (i, k) 1
  continuous_toFun := by fun_prop

theorem labelledCosine_lift (N : ℕ) (i : Fin N) (k : Fin 2) (y : Gradient N) :
    labelledCosine N i k (configurationQuotient N y) = Real.cos (2 * Real.pi * y (i, k)) := by
  change (fourier 1 (y (i, k) : UnitAddCircle)).re = _
  rw [fourier_coe_apply]
  simp [
    Complex.exp_re, Complex.mul_re, Complex.mul_im]

theorem labelledCosineGradient_lift (N : ℕ) (i : Fin N) (k : Fin 2) (y : Gradient N) :
    labelledCosineGradient N i k (configurationQuotient N y) =
      (-2 * Real.pi * Real.sin (2 * Real.pi * y (i, k))) • EuclideanSpace.single (i, k) 1 := by
  change (-2 * Real.pi * (fourier 1 (y (i, k) : UnitAddCircle)).im) •
    (EuclideanSpace.single (i, k) 1 : Gradient N) = _
  rw [fourier_coe_apply]
  simp [
    Complex.exp_im, Complex.mul_re, Complex.mul_im]

def SmoothPair.cosine (N : ℕ) (i : Fin N) (k : Fin 2) : SmoothPair N where
  value := labelledCosine N i k
  gradient := labelledCosineGradient N i k
  smooth := by
    simp only [labelledCosine_lift]
    have hp : ContDiff ℝ ∞ (fun y : Gradient N ↦ y (i, k)) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (i, k)).contDiff
    exact (contDiff_const.mul hp).cos
  differential := by
    intro y
    simp only [labelledCosine_lift, labelledCosineGradient_lift]
    let L : Gradient N →L[ℝ] ℝ := EuclideanSpace.proj (i, k)
    have hp : HasFDerivAt (fun z : Gradient N ↦ z (i, k)) L y := L.hasFDerivAt
    have heq : innerSL ℝ ((-2 * Real.pi * Real.sin (2 * Real.pi * y (i, k))) •
        EuclideanSpace.single (i, k) 1) =
        -Real.sin (2 * Real.pi * y (i, k)) • ((2 * Real.pi) • L) := by
      ext v
      simp [innerSL_apply_apply, EuclideanSpace.inner_single_left, L]
      ring
    rw [heq]
    exact (hp.const_mul (2 * Real.pi)).cos

theorem labelledCosine_nonconstant (N : ℕ) (i : Fin N) (k : Fin 2) :
    ∃ x y, labelledCosine N i k x ≠ labelledCosine N i k y := by
  refine ⟨configurationQuotient N 0,
    configurationQuotient N (EuclideanSpace.single (i, k) (1 / 2)), ?_⟩
  rw [labelledCosine_lift, labelledCosine_lift]
  norm_num [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring]

theorem SmoothPair.value_memLp {N : ℕ} (f : SmoothPair N)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] : MemLp f.value 2 μ :=
  ContinuousMap.memLp (μ := μ) (p := 2) ℝ f.value

theorem SmoothPair.gradient_memLp {N : ℕ} (f : SmoothPair N)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] : MemLp f.gradient 2 μ :=
  ContinuousMap.memLp (μ := μ) (p := 2) ℝ f.gradient

theorem SmoothPair.finite_energy {N : ℕ} (f : SmoothPair N)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    Integrable (fun x ↦ ‖f.gradient x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (f.gradient_memLp μ).aestronglyMeasurable).mp
    (f.gradient_memLp μ)

theorem cosine_mem_closedGradientGraph (N : ℕ) (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (i : Fin N) (k : Fin 2) :
    (ContinuousMap.toLp 2 μ ℝ (labelledCosine N i k),
      ContinuousMap.toLp 2 μ ℝ (labelledCosineGradient N i k)) ∈ closedGradientGraph N μ :=
  smoothPair_mem_closedGradientGraph N μ (SmoothPair.cosine N i k)

end PeriodicAttractiveLogGas
