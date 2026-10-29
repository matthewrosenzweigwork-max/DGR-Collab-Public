import LeanResearch.PeriodicAttractiveLogGas.ConfigurationFourier
import LeanResearch.PeriodicAttractiveLogGas.GreenWeakFourier
import LeanResearch.PeriodicAttractiveLogGas.SmoothCalculus
import Mathlib.MeasureTheory.Integral.Pi

/-! Ordinary test-function calculus for the distributional Green equation.
The single-particle configuration is explicitly identified with the square
torus, including its probability measure and coordinate derivatives. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace PeriodicAttractiveLogGas

theorem torus_mFourierCoeff_neg (f : Torus → ℂ) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ -f x) k = -UnitAddTorus.mFourierCoeff f k := by
  simp only [torus_mFourierCoeff_eq_integral, mul_neg, integral_neg]

theorem torus_mFourierCoeff_sum {ι : Type*} [Fintype ι]
    (f : ι → C(Torus, ℂ)) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ ∑ i, f i x) k =
      ∑ i, UnitAddTorus.mFourierCoeff (f i) k := by
  classical
  simp only [torus_mFourierCoeff_eq_integral, Finset.mul_sum]
  apply integral_finsetSum
  intro i _
  exact memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℂ
    ((UnitAddTorus.mFourier (-k)) * f i))

def singleConfiguration (x : Torus) : Configuration 1 := fun _ ↦ x

@[simp] theorem singleConfiguration_eval (x : Configuration 1) :
    singleConfiguration (x 0) = x := by
  ext i j
  exact congrArg (fun a : Fin 1 ↦ x a j) (Subsingleton.elim 0 i)

def singleFrequency (k : Frequency) : Fin 1 × Fin 2 → ℤ := fun j ↦ k j.2

theorem configurationCharacter_one (k : Frequency) (x : Configuration 1) :
    configurationCharacter 1 (singleFrequency k) x = UnitAddTorus.mFourier k (x 0) := by
  simp only [configurationCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    singleFrequency, Fintype.prod_prod_type]
  simp

def singleTorusValue (f : C(Configuration 1, ℂ)) : C(Torus, ℂ) where
  toFun x := f (singleConfiguration x)
  continuous_toFun := by unfold singleConfiguration; fun_prop

theorem configurationFourierCoeff_one (f : C(Configuration 1, ℂ)) (k : Frequency) :
    configurationFourierCoeff f (singleFrequency k) =
      UnitAddTorus.mFourierCoeff (singleTorusValue f) k := by
  rw [torus_mFourierCoeff_eq_integral]
  unfold configurationFourierCoeff
  have hneg : -singleFrequency k = singleFrequency (-k) := rfl
  simp only [hneg, configurationCharacter_one]
  have hf (x : Configuration 1) : f x = singleTorusValue f (x 0) := by
    simp [singleTorusValue]
  simp_rw [hf]
  exact integral_comp_eval (μ := fun _ : Fin 1 ↦ torusMeasure)
    (i := (0 : Fin 1))
    (((UnitAddTorus.mFourier (-k)).continuous.mul (singleTorusValue f).continuous).aestronglyMeasurable)

def SmoothPair.torusValue (f : SmoothPair 1) : C(Torus, ℝ) where
  toFun x := f.value (singleConfiguration x)
  continuous_toFun := by unfold singleConfiguration; fun_prop

theorem SmoothPair.torus_fourierCoeff_gradient (f : SmoothPair 1)
    (k : Frequency) (j : Fin 2) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (f.gradient (singleConfiguration x) (0, j) : ℂ)) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f.torusValue x : ℂ)) k := by
  let g : C(Configuration 1, ℂ) := ⟨fun x ↦ (f.value x : ℂ), by fun_prop⟩
  let b : C(Configuration 1, ℂ) := ⟨fun x ↦ (f.gradient x (0, j) : ℂ), by fun_prop⟩
  have h := f.configurationFourierCoeff_gradient (singleFrequency k) (0, j)
  change configurationFourierCoeff b (singleFrequency k) =
    (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * configurationFourierCoeff g (singleFrequency k) at h
  rw [configurationFourierCoeff_one, configurationFourierCoeff_one] at h
  exact h

theorem SmoothPair.torus_fourierCoeff_directionalDerivative (f : SmoothPair 1)
    (k : Frequency) (j : Fin 2) :
    UnitAddTorus.mFourierCoeff (fun x ↦
      ((f.directionalDerivativePair (EuclideanSpace.single (0, j) 1)).torusValue x : ℂ)) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f.torusValue x : ℂ)) k := by
  simpa [SmoothPair.torusValue, SmoothPair.directionalDerivative,
    EuclideanSpace.inner_single_right] using
    f.torus_fourierCoeff_gradient k j

theorem SmoothPair.torus_fourierCoeff_secondDerivative (f : SmoothPair 1)
    (k : Frequency) (j : Fin 2) :
    UnitAddTorus.mFourierCoeff (fun x ↦
      ((f.secondDirectionalDerivativePair (EuclideanSpace.single (0, j) 1)).torusValue x : ℂ)) k =
      ((-(4 * Real.pi ^ 2 * (k j : ℝ) ^ 2) : ℝ) : ℂ) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f.torusValue x : ℂ)) k := by
  unfold SmoothPair.secondDirectionalDerivativePair
  rw [SmoothPair.torus_fourierCoeff_directionalDerivative,
    SmoothPair.torus_fourierCoeff_directionalDerivative]
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem SmoothPair.torus_fourierCoeff_laplacian (f : SmoothPair 1) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (f.laplacian.torusValue x : ℂ)) k =
      ((-(4 * Real.pi ^ 2 * frequencySq k) : ℝ) : ℂ) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f.torusValue x : ℂ)) k := by
  let d (j : Fin 2) : C(Torus, ℂ) :=
    ⟨fun x ↦ ((f.secondDirectionalDerivativePair (EuclideanSpace.single (0, j) 1)).torusValue x : ℂ),
      by fun_prop⟩
  have hd : (fun x ↦ (f.laplacian.torusValue x : ℂ)) = fun x ↦ ∑ j, d j x := by
    funext x
    simp [SmoothPair.torusValue, SmoothPair.laplacianValue, d]
  rw [hd, torus_mFourierCoeff_sum]
  have hcoeff (j : Fin 2) : UnitAddTorus.mFourierCoeff (d j) k =
      ((-(4 * Real.pi ^ 2 * (k j : ℝ) ^ 2) : ℝ) : ℂ) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f.torusValue x : ℂ)) k :=
    f.torus_fourierCoeff_secondDerivative k j
  simp only [hcoeff, frequencySq, Fin.sum_univ_two]
  push_cast
  ring

theorem SmoothPair.torus_fourierCoeff_negativeLaplacian (f : SmoothPair 1) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ ((-f.laplacian.torusValue x : ℝ) : ℂ)) k =
      ((4 * Real.pi ^ 2 * frequencySq k : ℝ) : ℂ) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f.torusValue x : ℂ)) k := by
  simp only [Complex.ofReal_neg, torus_mFourierCoeff_neg,
    SmoothPair.torus_fourierCoeff_laplacian]
  push_cast
  ring

/-- The distributional negative-Laplacian identity for every actual smooth
periodic test. The Laplacian is the proved ordinary coordinate derivative
operator, and the test is unrestricted at the origin. -/
theorem greenRealRepresentative_weak_laplacian (f : SmoothPair 1) :
    (∫ x, greenRealRepresentative x * (-f.laplacian.torusValue x) ∂torusMeasure) =
      (2 * Real.pi) * (f.torusValue 0 - ∫ x, f.torusValue x ∂torusMeasure) := by
  exact greenRealRepresentative_pairing_eq_of_fourier_laplacian
    f.torusValue (-f.laplacian.torusValue) f.torus_fourierCoeff_negativeLaplacian

theorem greenRealRepresentative_negativeLaplacian_integrable (f : SmoothPair 1) :
    Integrable (fun x ↦ greenRealRepresentative x * (-f.laplacian.torusValue x))
      torusMeasure := greenRealRepresentative_mul_integrable (-f.laplacian.torusValue)

def torusQuotient (y : EuclideanSpace ℝ (Fin 2)) : Torus := fun j ↦ (y j : UnitAddCircle)

def firstParticleCoordinates : Gradient 1 →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦ EuclideanSpace.proj (0, j))

@[simp] theorem firstParticleCoordinates_apply (y : Gradient 1) (j : Fin 2) :
    firstParticleCoordinates y j = y (0, j) := rfl

def singleParticleCoordinates (y : EuclideanSpace ℝ (Fin 2)) : Gradient 1 :=
  WithLp.toLp 2 (fun j ↦ y j.2)

@[simp] theorem firstParticleCoordinates_singleParticle (y : EuclideanSpace ℝ (Fin 2)) :
    firstParticleCoordinates (singleParticleCoordinates y) = y := by ext j; rfl

@[simp] theorem firstParticleCoordinates_single (j : Fin 2) :
    firstParticleCoordinates (EuclideanSpace.single (0, j) 1) = EuclideanSpace.single j 1 := by
  ext k
  simp [firstParticleCoordinates_apply]

theorem fderiv_comp_firstParticle_apply (F : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hF : Differentiable ℝ F) (y v : Gradient 1) :
    fderiv ℝ (fun z ↦ F (firstParticleCoordinates z)) y v =
      fderiv ℝ F (firstParticleCoordinates y) (firstParticleCoordinates v) := by
  have h := ((hF (firstParticleCoordinates y)).hasFDerivAt.comp y
    firstParticleCoordinates.hasFDerivAt).fderiv
  exact congrArg (fun L : Gradient 1 →L[ℝ] ℝ ↦ L v) h

theorem firstParticleCoordinates_norm (y : Gradient 1) :
    ‖firstParticleCoordinates y‖ = ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, gradient_norm_sq]
  simp

/-- Every smooth periodic test on the ordinary Euclidean two-dimensional
cover is represented; no support condition is imposed at the pole. -/
def SmoothPair.ofTorusContDiffLift (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) : SmoothPair 1 :=
  SmoothPair.ofContDiffLift ⟨fun x ↦ f (x 0), by fun_prop⟩
    (by exact hf.comp firstParticleCoordinates.contDiff)

@[simp] theorem SmoothPair.ofTorusContDiffLift_torusValue (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) :
    (SmoothPair.ofTorusContDiffLift f hf).torusValue = f := rfl

/-- The ordinary negative Laplacian of a smooth periodic torus test, computed
using the actual second coordinate derivatives above. -/
def torusNegativeLaplacian (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) : C(Torus, ℝ) :=
  -(SmoothPair.ofTorusContDiffLift f hf).laplacian.torusValue

/-- Identification with minus the usual sum of the two Euclidean second
coordinate derivatives; this fixes the differential operator's normalization. -/
theorem torusNegativeLaplacian_lift (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) (y : EuclideanSpace ℝ (Fin 2)) :
    torusNegativeLaplacian f hf (torusQuotient y) =
      -∑ j : Fin 2, fderiv ℝ
        (fun z ↦ fderiv ℝ (fun w ↦ f (torusQuotient w)) z (EuclideanSpace.single j 1))
        y (EuclideanSpace.single j 1) := by
  let F : EuclideanSpace ℝ (Fin 2) → ℝ := fun w ↦ f (torusQuotient w)
  have hF : Differentiable ℝ F := hf.differentiable (by simp)
  have hD (j : Fin 2) : Differentiable ℝ (fun z ↦ fderiv ℝ F z (EuclideanSpace.single j 1)) :=
    ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const).differentiable (by simp)
  have hfirst (j : Fin 2) :
      (fun z ↦ fderiv ℝ (fun w ↦ F (firstParticleCoordinates w)) z
        (EuclideanSpace.single (0, j) 1)) =
      (fun z ↦ fderiv ℝ F (firstParticleCoordinates z) (EuclideanSpace.single j 1)) := by
    funext z
    rw [fderiv_comp_firstParticle_apply F hF, firstParticleCoordinates_single]
  change -(SmoothPair.ofTorusContDiffLift f hf).laplacian.value
    (configurationQuotient 1 (singleParticleCoordinates y)) = _
  rw [SmoothPair.laplacian_lift_eq_sum_fderiv]
  simp only [Fin.sum_univ_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change fderiv ℝ (fun z ↦ fderiv ℝ (fun w ↦ F (firstParticleCoordinates w)) z
    (EuclideanSpace.single (0, j) 1)) (singleParticleCoordinates y)
      (EuclideanSpace.single (0, j) 1) = _
  rw [hfirst, fderiv_comp_firstParticle_apply _ (hD j),
    firstParticleCoordinates_single, firstParticleCoordinates_singleParticle]

theorem greenRealRepresentative_weak_equation (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) :
    (∫ x, greenRealRepresentative x * torusNegativeLaplacian f hf x ∂torusMeasure) =
      (2 * Real.pi) * (f 0 - ∫ x, f x ∂torusMeasure) := by
  exact greenRealRepresentative_weak_laplacian (SmoothPair.ofTorusContDiffLift f hf)

theorem greenRealRepresentative_test_integrable (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) :
    Integrable (fun x ↦ greenRealRepresentative x * torusNegativeLaplacian f hf x)
      torusMeasure := greenRealRepresentative_mul_integrable (torusNegativeLaplacian f hf)

end PeriodicAttractiveLogGas
