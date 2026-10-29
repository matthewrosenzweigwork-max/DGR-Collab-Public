import LeanResearch.PeriodicAttractiveLogGas.PeriodicCalculus
import Mathlib.Analysis.Complex.RealDeriv

/-! Ordinary coordinate differentiation of Fourier coefficients on the
labelled configuration torus. No Gibbs density is differentiated. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PeriodicAttractiveLogGas

def configurationCharacter (N : ℕ) (k : Fin N × Fin 2 → ℤ) : C(Configuration N, ℂ) where
  toFun x := UnitAddTorus.mFourier k (fun j ↦ x j.1 j.2)
  continuous_toFun := by fun_prop

@[simp] theorem configurationCharacter_zero (N : ℕ) (k : Fin N × Fin 2 → ℤ) :
    configurationCharacter N k 0 = 1 := by
  simp [configurationCharacter, UnitAddTorus.mFourier]

theorem configurationCharacter_add (N : ℕ) (k : Fin N × Fin 2 → ℤ)
    (x y : Configuration N) :
    configurationCharacter N k (x + y) =
      configurationCharacter N k x * configurationCharacter N k y := by
  simp only [configurationCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Pi.add_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

theorem configurationCharacter_cancel (N : ℕ) (k : Fin N × Fin 2 → ℤ)
    (x : Configuration N) :
    configurationCharacter N k x * configurationCharacter N (-k) x = 1 := by
  change UnitAddTorus.mFourier k _ * UnitAddTorus.mFourier (-k) _ = _
  rw [← UnitAddTorus.mFourier_add, add_neg_cancel, UnitAddTorus.mFourier_zero]
  rfl

theorem configurationCharacter_coordinate_translate (N : ℕ)
    (k : Fin N × Fin 2 → ℤ) (j : Fin N × Fin 2) (t : ℝ) :
    configurationCharacter N k (configurationQuotient N (t • EuclideanSpace.single j 1)) =
      fourier (k j) (t : UnitAddCircle) := by
  classical
  change (∏ a, fourier (k a) ((t • (EuclideanSpace.single j 1 : Gradient N)) a : UnitAddCircle)) = _
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

theorem configurationCharacter_hasDerivAt_coordinate (N : ℕ)
    (k : Fin N × Fin 2 → ℤ) (j : Fin N × Fin 2) :
    HasDerivAt (fun t : ℝ ↦ configurationCharacter N k
      (configurationQuotient N (t • EuclideanSpace.single j 1)))
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) 0 := by
  simp only [configurationCharacter_coordinate_translate]
  simpa using hasDerivAt_fourier (1 : ℝ) (k j) 0

def configurationFourierCoeff {N : ℕ} (f : Configuration N → ℂ)
    (k : Fin N × Fin 2 → ℤ) : ℂ :=
  ∫ x, configurationCharacter N (-k) x * f x ∂referenceMeasure N

theorem configurationFourierCoeff_translate {N : ℕ} (f : C(Configuration N, ℂ))
    (k : Fin N × Fin 2 → ℤ) (a : Configuration N) :
    configurationFourierCoeff (fun x ↦ f (a + x)) k =
      configurationCharacter N k a * configurationFourierCoeff f k := by
  unfold configurationFourierCoeff
  have h (x : Configuration N) :
      configurationCharacter N (-k) x * f (a + x) =
        configurationCharacter N k a *
          (configurationCharacter N (-k) (a + x) * f (a + x)) := by
    rw [configurationCharacter_add]
    calc
      _ = 1 * (configurationCharacter N (-k) x * f (a + x)) := by ring
      _ = _ := by rw [← configurationCharacter_cancel N k a]; ring
  simp_rw [h]
  rw [integral_const_mul]
  congr 1
  exact integral_add_left_eq_self
    (fun x ↦ configurationCharacter N (-k) x * f x) a

theorem SmoothPair.configurationFourierCoeff_gradient {N : ℕ} (f : SmoothPair N)
    (k : Fin N × Fin 2 → ℤ) (j : Fin N × Fin 2) :
    configurationFourierCoeff (fun x ↦ (f.gradient x j : ℂ)) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
        configurationFourierCoeff (fun x ↦ (f.value x : ℂ)) k := by
  let v : Gradient N := EuclideanSpace.single j 1
  let g : C(Configuration N, ℂ) := ⟨fun x ↦ (f.value x : ℂ), by fun_prop⟩
  let b : C(Configuration N, ℂ) := ⟨fun x ↦ (f.gradient x j : ℂ), by fun_prop⟩
  let F (t : ℝ) (x : Configuration N) :=
    configurationCharacter N (-k) x * g (configurationQuotient N (t • v) + x)
  let D (t : ℝ) (x : Configuration N) :=
    configurationCharacter N (-k) x * b (configurationQuotient N (t • v) + x)
  have hFcont (t : ℝ) : Continuous (F t) := by dsimp [F]; fun_prop
  have hDcont (t : ℝ) : Continuous (D t) := by dsimp [D]; fun_prop
  have hFint : Integrable (F 0) (referenceMeasure N) :=
    memLp_one_iff_integrable.mp
      (ContinuousMap.memLp (μ := referenceMeasure N) (p := 1) ℂ ⟨F 0, hFcont 0⟩)
  have hbound : ∀ᵐ x ∂referenceMeasure N, ∀ t ∈ (Set.univ : Set ℝ),
      ‖D t x‖ ≤ ‖configurationCharacter N (-k)‖ * ‖b‖ := by
    apply Filter.Eventually.of_forall
    intro x t _
    dsimp [D]
    rw [norm_mul]
    exact mul_le_mul ((configurationCharacter N (-k)).norm_coe_le_norm x)
      (b.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  have hderiv (x : Configuration N) (t : ℝ) : HasDerivAt (fun s ↦ F s x) (D t x) t := by
    have hh := (f.hasDerivAt_translate v x t).ofReal_comp
    have hb : HasDerivAt (fun s ↦ g (configurationQuotient N (s • v) + x))
        (b (configurationQuotient N (t • v) + x)) t := by
      simpa [g, b, v, EuclideanSpace.inner_single_right] using hh
    exact hb.const_mul _
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := referenceMeasure N) (F := F) (F' := D) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ ↦ ‖configurationCharacter N (-k)‖ * ‖b‖)
    Filter.univ_mem (Filter.Eventually.of_forall fun t ↦ (hFcont t).aestronglyMeasurable)
    hFint (hDcont 0).aestronglyMeasurable hbound (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ ↦ hderiv x t)
  have htranslate : (fun t : ℝ ↦ ∫ x, F t x ∂referenceMeasure N) =
      fun t ↦ configurationCharacter N k (configurationQuotient N (t • v)) *
        configurationFourierCoeff g k := by
    funext t
    exact configurationFourierCoeff_translate g k _
  have hrhs := (configurationCharacter_hasDerivAt_coordinate N k j).mul_const
    (configurationFourierCoeff g k)
  rw [htranslate] at hdiff
  have heq := hdiff.2.unique hrhs
  simpa only [D, zero_smul, configurationQuotient_zero, zero_add, g, b,
    ContinuousMap.coe_mk, configurationFourierCoeff] using heq

end PeriodicAttractiveLogGas
