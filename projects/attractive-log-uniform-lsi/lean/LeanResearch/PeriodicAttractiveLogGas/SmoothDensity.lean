import LeanResearch.PeriodicAttractiveLogGas.CoreAlgebra
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Density of the actual smooth scalar core. Source: prop:ambient.
The sine and cosine coordinate functions separate points of the whole product
torus. The real algebra of values of genuine SmoothPairs is therefore uniformly
dense, and consequently dense in L2 for finite weakly regular Borel measures.
No closability or weighted derivative assumption is used. -/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

def labelledSine (N : ℕ) (i : Fin N) (k : Fin 2) : C(Configuration N, ℝ) where
  toFun x := (fourier 1 (x i k)).im
  continuous_toFun := by fun_prop

def labelledSineGradient (N : ℕ) (i : Fin N) (k : Fin 2) : C(Configuration N, Gradient N) where
  toFun x := (2 * Real.pi * (fourier 1 (x i k)).re) • EuclideanSpace.single (i, k) 1
  continuous_toFun := by fun_prop

theorem labelledSine_lift (N : ℕ) (i : Fin N) (k : Fin 2) (y : Gradient N) :
    labelledSine N i k (configurationQuotient N y) = Real.sin (2 * Real.pi * y (i, k)) := by
  change (fourier 1 (y (i, k) : UnitAddCircle)).im = _
  rw [fourier_coe_apply]
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]

theorem labelledSineGradient_lift (N : ℕ) (i : Fin N) (k : Fin 2) (y : Gradient N) :
    labelledSineGradient N i k (configurationQuotient N y) =
      (2 * Real.pi * Real.cos (2 * Real.pi * y (i, k))) • EuclideanSpace.single (i, k) 1 := by
  change (2 * Real.pi * (fourier 1 (y (i, k) : UnitAddCircle)).re) •
    (EuclideanSpace.single (i, k) 1 : Gradient N) = _
  rw [fourier_coe_apply]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

def SmoothPair.sine (N : ℕ) (i : Fin N) (k : Fin 2) : SmoothPair N where
  value := labelledSine N i k
  gradient := labelledSineGradient N i k
  smooth := by
    simp only [labelledSine_lift]
    have hp : ContDiff ℝ ∞ (fun y : Gradient N ↦ y (i, k)) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (i, k)).contDiff
    exact (contDiff_const.mul hp).sin
  differential := by
    intro y
    simp only [labelledSine_lift, labelledSineGradient_lift]
    let L : Gradient N →L[ℝ] ℝ := EuclideanSpace.proj (i, k)
    have hp : HasFDerivAt (fun z : Gradient N ↦ z (i, k)) L y := L.hasFDerivAt
    have heq : innerSL ℝ ((2 * Real.pi * Real.cos (2 * Real.pi * y (i, k))) •
        EuclideanSpace.single (i, k) 1) =
        Real.cos (2 * Real.pi * y (i, k)) • ((2 * Real.pi) • L) := by
      ext v
      simp [innerSL_apply_apply, EuclideanSpace.inner_single_left, L]
      ring
    rw [heq]
    exact (hp.const_mul (2 * Real.pi)).sin

/-- The real algebra of continuous scalar values of actual smooth-gradient pairs. -/
def smoothValueSubalgebra (N : ℕ) : Subalgebra ℝ C(Configuration N, ℝ) where
  carrier := Set.range (fun f : SmoothPair N ↦ f.value)
  algebraMap_mem' c := by
    refine ⟨SmoothPair.const N c, ?_⟩
    ext x
    simp [SmoothPair.const]
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.add g, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.mul g, rfl⟩

@[simp]
theorem mem_smoothValueSubalgebra {N : ℕ} {u : C(Configuration N, ℝ)} :
    u ∈ smoothValueSubalgebra N ↔ ∃ f : SmoothPair N, f.value = u := Iff.rfl

theorem smoothPair_value_mem_smoothValueSubalgebra {N : ℕ} (f : SmoothPair N) :
    f.value ∈ smoothValueSubalgebra N := ⟨f, rfl⟩

theorem smoothValueSubalgebra_separatesPoints (N : ℕ) :
    (smoothValueSubalgebra N).SeparatesPoints := by
  classical
  intro x y hxy
  have hcoord : ∃ i : Fin N, ∃ k : Fin 2, x i k ≠ y i k := by
    by_contra h
    apply hxy
    funext i k
    by_contra hik
    exact h ⟨i, k, hik⟩
  obtain ⟨i, k, hik⟩ := hcoord
  by_cases hc : labelledCosine N i k x = labelledCosine N i k y
  · have hs : labelledSine N i k x ≠ labelledSine N i k y := by
      intro hs
      have hfourier : fourier 1 (x i k) = fourier 1 (y i k) := by
        apply Complex.ext
        · exact hc
        · exact hs
      apply hik
      apply AddCircle.injective_toCircle one_ne_zero
      apply Subtype.ext
      simpa only [fourier_one] using hfourier
    refine ⟨_, ⟨labelledSine N i k, ?_, rfl⟩, hs⟩
    exact ⟨SmoothPair.sine N i k, rfl⟩
  · refine ⟨_, ⟨labelledCosine N i k, ?_, rfl⟩, hc⟩
    exact ⟨SmoothPair.cosine N i k, rfl⟩

theorem smoothValueSubalgebra_topologicalClosure_eq_top (N : ℕ) :
    (smoothValueSubalgebra N).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (smoothValueSubalgebra_separatesPoints N)

/-- Actual smooth scalar values are dense for the uniform topology on continuous maps. -/
theorem denseRange_smoothPair_value (N : ℕ) :
    DenseRange (fun f : SmoothPair N ↦ f.value) := by
  change Dense (smoothValueSubalgebra N : Set C(Configuration N, ℝ))
  rw [dense_iff_closure_eq]
  exact congrArg (fun A : Subalgebra ℝ C(Configuration N, ℝ) ↦
    (A : Set C(Configuration N, ℝ))) (smoothValueSubalgebra_topologicalClosure_eq_top N)

/-- The scalar values of the actual smooth core are dense in weighted L2. -/
theorem denseRange_smoothPair_toLp (N : ℕ) (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] [μ.WeaklyRegular] :
    DenseRange (fun f : SmoothPair N ↦ ContinuousMap.toLp 2 μ ℝ f.value) := by
  let T : C(Configuration N, ℝ) →L[ℝ] Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ
  have hT : DenseRange T := ContinuousMap.toLp_denseRange ℝ μ ℝ (by norm_num)
  have hd := hT.dense_image T.continuous (denseRange_smoothPair_value N)
  simpa only [DenseRange, T, ← Set.range_comp, Function.comp_def] using! hd

end PeriodicAttractiveLogGas
