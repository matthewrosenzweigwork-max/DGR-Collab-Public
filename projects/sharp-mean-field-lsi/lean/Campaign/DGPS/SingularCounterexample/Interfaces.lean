import DGPS.Foundations.SobolevFourier
import SharpSymmetricLSI.Defs.D09_ParticleRates

/-!
# Shared interfaces for the singular circle counterexample

This module fixes the one-dimensional torus and Fourier conventions and aliases the legacy
particle constants at dimension one.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.SingularCounterexample

abbrev Circle := DGPS.Torus 1

/-- The circle point represented by the real number `t`. -/
abbrev torusPoint (t : ℝ) : Circle := DGPS.torusLift (fun _ : Fin 1 => t)

/-- The canonical additive difference on the circle. -/
abbrev circleDiff (x y : Circle) : Circle := x - y

@[simp] theorem circleDiff_self (x : Circle) : circleDiff x x = 0 := by
  change x - x = 0
  exact sub_self x

theorem circleDiff_swap (x y : Circle) : circleDiff x y = -circleDiff y x := by
  change x - y = -(y - x)
  abel

@[simp] theorem circleDiff_neg_neg (x y : Circle) : circleDiff (-x) (-y) = -circleDiff x y := by
  change -x - -y = -(x - y)
  abel

def freqZ (k : ℤ) : Fin 1 → ℤ := fun _ => k

/-- The existing complex Fourier coefficient restricted to the one-dimensional frequencies. -/
noncomputable abbrev coeff1 (f : Circle → ℝ) (k : ℤ) : ℂ :=
  DGPS.fourierCoeff f (freqZ k)

@[simp] theorem coeff1_eq_fourierCoeff (f : Circle → ℝ) (k : ℤ) :
    coeff1 f k = DGPS.fourierCoeff f (freqZ k) := rfl

def HasNonnegNonzeroFourier (k : Circle → ℝ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → (coeff1 k n).im = 0 ∧ 0 ≤ (coeff1 k n).re

def HasPosNonzeroFourier (k : Circle → ℝ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → (coeff1 k n).im = 0 ∧ 0 < (coeff1 k n).re

noncomputable def circleHsWeight (s : ℝ) (k : ℤ) : ℝ :=
  (1 + (2 * Real.pi * (k : ℝ)) ^ 2) ^ s

def MemCircleHs (s : ℝ) (f : Circle → ℝ) : Prop :=
  MemLp f 2 (DGPS.haar 1) ∧
    Summable (fun k : ℤ => circleHsWeight s k * ‖coeff1 f k‖ ^ 2)

/-- Minimal hypotheses for a real even circle kernel with nonnegative nonzero Fourier
coefficients. -/
def AdmissibleKernel (k : Circle → ℝ) : Prop :=
  Measurable k ∧ Integrable k (DGPS.haar 1) ∧
    (∃ C : ℝ, ∀ x, C ≤ k x) ∧
    (∀ x, k (-x) = k x) ∧ k 0 = 0 ∧ HasNonnegNonzeroFourier k

structure BaselineKernel where
  g : Circle → ℝ
  measurable_g : Measurable g
  bounded_g : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x| ≤ C
  even_g : ∀ x, g (-x) = g x
  zero_g : g 0 = 0
  fourier_nonneg : HasNonnegNonzeroFourier g

noncomputable abbrev circleGibbs (V : Circle → ℝ) (W : Circle → Circle → ℝ) (N : ℕ) :=
  SharpLSI.gibbs V W N

noncomputable abbrev circleEnergy (V : Circle → ℝ) (W : Circle → Circle → ℝ) (N : ℕ)
    (f : SharpLSI.Config N 1 → ℝ) :=
  SharpLSI.energy V W N f

noncomputable abbrev circleLamAll (V : Circle → ℝ) (W : Circle → Circle → ℝ) (N : ℕ) :=
  SharpLSI.lamAll V W N

noncomputable abbrev circleLamSym (V : Circle → ℝ) (W : Circle → Circle → ℝ) (N : ℕ) :=
  SharpLSI.lamSym V W N

noncomputable abbrev circleRAll (V : Circle → ℝ) (W : Circle → Circle → ℝ) (N : ℕ) :=
  SharpLSI.rAll V W N

noncomputable abbrev circleRSym (V : Circle → ℝ) (W : Circle → Circle → ℝ) (N : ℕ) :=
  SharpLSI.rSym V W N

theorem haar_singleton_zero (x : Circle) : DGPS.haar 1 {x} = 0 := by
  rw [DGPS.haar_eq_map_unitBox 1]
  rw [Measure.map_apply SharpLSI.measurable_liftT (measurableSet_singleton x)]
  have hx : SharpLSI.secT x ∈ SharpLSI.unitBox (Fin 1) := by
    rw [SharpLSI.unitBox, Set.mem_univ_pi]
    intro i
    simpa [SharpLSI.secT] using (AddCircle.measurableEquivIoc 1 0 (x i)).property
  have hpre :
      SharpLSI.liftT ⁻¹' ({x} : Set Circle) ∩ SharpLSI.unitBox (Fin 1) =
        {SharpLSI.secT x} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hyx, hyB⟩
      have hy := SharpLSI.secT_liftT hyB
      rw [hyx] at hy
      exact hy.symm
    · intro hy
      subst y
      exact ⟨SharpLSI.liftT_secT x, hx⟩
  rw [Measure.restrict_apply (SharpLSI.measurable_liftT (measurableSet_singleton x))]
  rw [hpre]
  exact MeasureTheory.NullSingletonClass.measure_singleton _

/-- Product Haar measure does not charge the collision diagonal. -/
theorem haar_pair_collision_zero :
    (DGPS.haar 1).prod (DGPS.haar 1)
      {p : Circle × Circle | p.1 = p.2} = 0 := by
  classical
  let s : Set (Circle × Circle) := {p | p.1 = p.2}
  have hs : MeasurableSet s := by
    exact (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hfiber (x : Circle) : (DGPS.haar 1) (Prod.mk x ⁻¹' s) = 0 := by
    have hset : Prod.mk x ⁻¹' s = {x} := by
      ext y
      simp [s]
    rw [hset]
    exact haar_singleton_zero x
  rw [Measure.prod_apply hs]
  simp_rw [hfiber]
  simp

/-- A change at the chosen circle representative of the collision point preserves the Haar-a.e.
class of the kernel. -/
theorem circle_ae_eq_of_eq_off_zero {f g : Circle → ℝ}
    (hfg : ∀ x, x ≠ 0 → f x = g x) : f =ᵐ[DGPS.haar 1] g := by
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
    (haar_singleton_zero (0 : Circle))] with x hx
  apply hfg x
  intro h
  apply hx
  simp [h]

/-- Circle Fourier coefficients are unchanged when the kernel is changed at zero. -/
theorem coeff1_eq_of_eq_off_zero {f g : Circle → ℝ}
    (hfg : ∀ x, x ≠ 0 → f x = g x) (k : ℤ) : coeff1 f k = coeff1 g k := by
  have hae := circle_ae_eq_of_eq_off_zero hfg
  change UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) _ =
    UnitAddTorus.mFourierCoeff (fun y => (g y : ℂ)) _
  rw [SharpLSI.mFourierCoeff_eq_integral, SharpLSI.mFourierCoeff_eq_integral]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  rw [hx]

/-- Pair interactions that agree away from zero agree almost everywhere under product Haar. -/
theorem pair_interaction_ae_eq_of_eq_off_zero {f g : Circle → ℝ}
    (hfg : ∀ x, x ≠ 0 → f x = g x) :
    (fun p : Circle × Circle => f (circleDiff p.1 p.2)) =ᵐ[(DGPS.haar 1).prod (DGPS.haar 1)]
      (fun p => g (circleDiff p.1 p.2)) := by
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp haar_pair_collision_zero]
    with p hp
  apply hfg (circleDiff p.1 p.2)
  intro hdiff
  apply hp
  change p.1 = p.2
  exact sub_eq_zero.mp (by simpa [circleDiff] using hdiff)

/-- Product-Haar pair integrals are unchanged when the interaction is changed at zero. -/
theorem pair_interaction_integral_eq_of_eq_off_zero {f g : Circle → ℝ}
    (hfg : ∀ x, x ≠ 0 → f x = g x) :
    ∫ p : Circle × Circle, f (circleDiff p.1 p.2) ∂(DGPS.haar 1).prod (DGPS.haar 1) =
      ∫ p, g (circleDiff p.1 p.2) ∂(DGPS.haar 1).prod (DGPS.haar 1) := by
  exact integral_congr_ae (pair_interaction_ae_eq_of_eq_off_zero hfg)

end DGPS.SingularCounterexample
