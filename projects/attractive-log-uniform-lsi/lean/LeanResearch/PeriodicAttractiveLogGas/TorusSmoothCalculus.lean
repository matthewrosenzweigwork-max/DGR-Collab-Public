import LeanResearch.PeriodicAttractiveLogGas.GreenEquation
import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierGradient

/-! Smooth translation and actual two-coordinate calculus for the Green
representation in source Lemma 3.1. All torus derivatives below come from the
already defined ordinary smooth pairs; the single-particle coordinate maps
preserve the Euclidean inner product and normalized Haar integrals exactly.
-/

noncomputable section
open MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace

namespace PeriodicAttractiveLogGas

instance referenceMeasure_isNegInvariant (N : ℕ) :
    Measure.IsNegInvariant (referenceMeasure N) :=
  Measure.pi.isNegInvariant (fun _ : Fin N ↦ torusMeasure)

@[simp] theorem configurationQuotient_singleParticleCoordinates (y : PlanarSpace) :
    configurationQuotient 1 (singleParticleCoordinates y) =
      singleConfiguration (torusQuotient y) := rfl

def singleParticleCoordinatesL : PlanarSpace →L[ℝ] Gradient 1 :=
  (EuclideanSpace.equiv (Fin 1 × Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ik ↦ EuclideanSpace.proj ik.2)

@[simp] theorem singleParticleCoordinatesL_apply (y : PlanarSpace) :
    singleParticleCoordinatesL y = singleParticleCoordinates y := rfl

@[simp] theorem singleParticleCoordinates_single (j : Fin 2) :
    singleParticleCoordinates (EuclideanSpace.single j 1) =
      EuclideanSpace.single (0, j) 1 := by
  ext ik
  obtain ⟨i, k⟩ := ik
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [singleParticleCoordinates]

theorem inner_firstParticleCoordinates (y : Gradient 1) (v : PlanarSpace) :
    inner ℝ (firstParticleCoordinates y) v = inner ℝ y (singleParticleCoordinates v) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    firstParticleCoordinates_apply, singleParticleCoordinates, Fintype.sum_prod_type]

def SmoothPair.torusGradient (f : SmoothPair 1) : C(Torus, PlanarSpace) where
  toFun x := firstParticleCoordinates (f.gradient (singleConfiguration x))
  continuous_toFun := by unfold singleConfiguration; fun_prop

theorem SmoothPair.torusGradient_norm (f : SmoothPair 1) (x : Torus) :
    ‖f.torusGradient x‖ = ‖f.gradient (singleConfiguration x)‖ :=
  firstParticleCoordinates_norm _

theorem SmoothPair.torus_directionalDerivative_value (f : SmoothPair 1)
    (x : Torus) (v : PlanarSpace) :
    (f.directionalDerivativePair (singleParticleCoordinates v)).torusValue x =
      inner ℝ (f.torusGradient x) v :=
  (inner_firstParticleCoordinates _ v).symm

theorem SmoothPair.torus_differential (f : SmoothPair 1) (y : PlanarSpace) :
    HasFDerivAt (fun z ↦ f.torusValue (torusQuotient z))
      (innerSL ℝ (f.torusGradient (torusQuotient y))) y := by
  have h := (f.differential (singleParticleCoordinates y)).comp y
    singleParticleCoordinatesL.hasFDerivAt
  convert h using 1
  · ext z
    simp only [SmoothPair.torusValue, ContinuousMap.coe_mk, Function.comp_apply,
      configurationQuotient_singleParticleCoordinates]
  · ext v
    simpa only [SmoothPair.torusGradient, ContinuousMap.coe_mk, ContinuousLinearMap.comp_apply, singleParticleCoordinatesL_apply,
      innerSL_apply_apply, configurationQuotient_singleParticleCoordinates] using
      inner_firstParticleCoordinates (f.gradient (singleConfiguration (torusQuotient y))) v

theorem SmoothPair.torusGradient_inner_lift (f : SmoothPair 1) (y v : PlanarSpace) :
    inner ℝ (f.torusGradient (torusQuotient y)) v =
      fderiv ℝ (fun z ↦ f.torusValue (torusQuotient z)) y v := by
  rw [(f.torus_differential y).fderiv]
  rfl

theorem integral_reference_one_eq_torus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Configuration 1 → E)
    (hF : AEStronglyMeasurable (fun x ↦ F (singleConfiguration x)) torusMeasure) :
    (∫ X, F X ∂referenceMeasure 1) = ∫ x, F (singleConfiguration x) ∂torusMeasure := by
  calc
    (∫ X, F X ∂referenceMeasure 1) =
        ∫ X, F (singleConfiguration (X 0)) ∂referenceMeasure 1 := by
      apply integral_congr_ae
      filter_upwards with X
      rw [singleConfiguration_eval]
    _ = _ := integral_comp_eval (μ := fun _ : Fin 1 ↦ torusMeasure) (i := (0 : Fin 1)) hF

theorem SmoothPair.torus_integration_by_parts (f g : SmoothPair 1) (v : PlanarSpace) :
    (∫ x, g.torusValue x * inner ℝ (f.torusGradient x) v ∂torusMeasure) =
      -(∫ x, f.torusValue x * inner ℝ (g.torusGradient x) v ∂torusMeasure) := by
  have h := f.integration_by_parts g (singleParticleCoordinates v)
  rw [integral_reference_one_eq_torus _ (by unfold singleConfiguration; fun_prop),
    integral_reference_one_eq_torus _ (by unfold singleConfiguration; fun_prop)] at h
  simpa only [SmoothPair.torusValue, SmoothPair.torusGradient, ContinuousMap.coe_mk,
    inner_firstParticleCoordinates] using h

/-- Pullback by the actual affine involution Y ↦ X-Y. -/
def SmoothPair.translateSub {N : ℕ} (f : SmoothPair N) (X : Configuration N) :
    SmoothPair N where
  value := ⟨fun Y ↦ f.value (X - Y), by fun_prop⟩
  gradient := ⟨fun Y ↦ -f.gradient (X - Y), by fun_prop⟩
  smooth := by
    obtain ⟨x, rfl⟩ := configurationQuotient_surjective N X
    change ContDiff ℝ ∞ (fun y ↦ f.value (configurationQuotient N x - configurationQuotient N y))
    simpa only [Function.comp_apply, id_eq, configurationQuotient_sub] using!
      f.smooth.comp (contDiff_const.sub contDiff_id)
  differential := by
    intro y
    obtain ⟨x, rfl⟩ := configurationQuotient_surjective N X
    have h := (f.differential (x - y)).comp y ((hasFDerivAt_id y).const_sub x)
    change HasFDerivAt (fun z ↦ f.value (configurationQuotient N x - configurationQuotient N z))
      (innerSL ℝ (-f.gradient (configurationQuotient N x - configurationQuotient N y))) y
    convert h using 1
    · ext z
      simp only [Function.comp_apply, configurationQuotient_sub]
    · ext v
      simp only [ContinuousLinearMap.comp_apply, neg_apply, configurationQuotient_sub,
        ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_neg_left, inner_neg_right]

@[simp] theorem SmoothPair.translateSub_value {N : ℕ} (f : SmoothPair N)
    (X Y : Configuration N) : (f.translateSub X).value Y = f.value (X - Y) := rfl

@[simp] theorem SmoothPair.translateSub_gradient {N : ℕ} (f : SmoothPair N)
    (X Y : Configuration N) : (f.translateSub X).gradient Y = -f.gradient (X - Y) := rfl

theorem SmoothPair.translateSub_secondDirectionalDerivative_value {N : ℕ}
    (f : SmoothPair N) (X Y : Configuration N) (v : Gradient N) :
    ((f.translateSub X).secondDirectionalDerivativePair v).value Y =
      (f.secondDirectionalDerivativePair v).value (X - Y) := by
  have heq : ((f.translateSub X).directionalDerivativePair v).value =
      (((f.directionalDerivativePair v).translateSub X).smul (-1)).value := by
    ext Z
    simp [SmoothPair.smul, SmoothPair.directionalDerivative,
      SmoothPair.directionalDerivativePair_value, SmoothPair.translateSub_gradient]
  have hg := SmoothPair.gradient_unique _ _ heq
  simp only [SmoothPair.secondDirectionalDerivativePair_value_apply]
  rw [congrArg (fun G : C(Configuration N, Gradient N) ↦ G Y) hg]
  simp [SmoothPair.smul]

theorem SmoothPair.translateSub_laplacian_value {N : ℕ} (f : SmoothPair N)
    (X Y : Configuration N) :
    (f.translateSub X).laplacian.value Y = f.laplacian.value (X - Y) := by
  simp only [SmoothPair.laplacian_value_apply,
    SmoothPair.translateSub_secondDirectionalDerivative_value]

theorem SmoothPair.translateSub_integral {N : ℕ} (f : SmoothPair N)
    (X : Configuration N) :
    (∫ Y, (f.translateSub X).value Y ∂referenceMeasure N) =
      ∫ Y, f.value Y ∂referenceMeasure N :=
  integral_sub_left_eq_self f.value (referenceMeasure N) X

@[simp] theorem SmoothPair.translateSub_torusValue (f : SmoothPair 1) (x y : Torus) :
    (f.translateSub (singleConfiguration x)).torusValue y = f.torusValue (x - y) := rfl

@[simp] theorem SmoothPair.translateSub_torusGradient (f : SmoothPair 1) (x y : Torus) :
    (f.translateSub (singleConfiguration x)).torusGradient y = -f.torusGradient (x - y) :=
  firstParticleCoordinates.map_neg _

/-- Identification of the regularized kernel's genuine smooth-pair gradient
with its separately defined ordinary Riesz gradient. -/
theorem torusGradient_regularizedGreen (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    (SmoothPair.ofTorusContDiffLift
      ⟨regularizedGreen ε hε, continuous_regularizedGreen ε hε⟩
      (contDiff_regularizedGreen_lift ε hε hs)).torusGradient z =
        regularizedGreenGradient ε hε z := by
  obtain ⟨y, rfl⟩ := torusQuotient_surjective z
  apply ext_inner_right ℝ
  intro v
  rw [SmoothPair.torusGradient_inner_lift,
    regularizedGreenGradient_inner, regularizedGreenDifferential_lift]
  rfl

end PeriodicAttractiveLogGas
