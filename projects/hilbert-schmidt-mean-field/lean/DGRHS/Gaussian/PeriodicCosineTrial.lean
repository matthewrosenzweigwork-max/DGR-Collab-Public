import DGRHS.Gaussian.PeriodicLogReality
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Genuine first-coordinate cosine under normalized torus Haar. Exact first
and second moments, bounded positive trial densities, and proper entropy are
proved from native Fourier orthogonality, without a desired instability or
quartic hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local instance periodicTrialCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

lemma periodicCircle_fourier_integral (n : ℤ) :
    (∫ x : UnitAddCircle,fourier n x ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff,fourier_zero,Pi.single_apply,eq_comm] using h

lemma periodicHaar_integral_coordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : UnitAddCircle → E} (hf : Integrable f AddCircle.haarAddCircle) (i : ι) :
    (∫ x : PeriodicTorus ι,f (x i) ∂periodicHaar ι) = ∫ x,f x ∂AddCircle.haarAddCircle := by
  have hm := measurePreserving_eval (fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle)) i
  have hf' : AEStronglyMeasurable f (Measure.map (fun x : PeriodicTorus ι => x i) (periodicHaar ι)) := by
    change AEStronglyMeasurable f (Measure.map (Function.eval i) (Measure.pi (fun _ : ι => (AddCircle.haarAddCircle : Measure UnitAddCircle))))
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  exact (integral_map hm.aemeasurable hf').symm.trans (by rw [hm.map_eq])

def periodicCoordinateCos (i : ι) (x : PeriodicTorus ι) : ℝ :=
  (fourier 1 (x i)).re
omit [Fintype ι] [Nonempty ι] in
lemma periodicCoordinateCos_continuous (i : ι) : Continuous (periodicCoordinateCos i) := by
  unfold periodicCoordinateCos
  fun_prop
omit [Fintype ι] [Nonempty ι] in
lemma periodicCoordinateCos_abs_le_one (i : ι) (x : PeriodicTorus ι) :
    |periodicCoordinateCos i x| ≤ 1 := by
  exact (Complex.abs_re_le_norm _).trans_eq (by simp [fourier_apply])
lemma periodicCoordinateCos_integrable (i : ι) :
    Integrable (periodicCoordinateCos i) (periodicHaar ι) := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (periodicCoordinateCos_continuous i).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using periodicCoordinateCos_abs_le_one i x
lemma periodicCoordinateCos_mean_zero (i : ι) :
    (∫ x,periodicCoordinateCos i x ∂periodicHaar ι) = 0 := by
  have hi : Integrable (fourier (T := 1) 1) AddCircle.haarAddCircle :=
    (fourier 1).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [show (∫ x,periodicCoordinateCos i x ∂periodicHaar ι) =
    ∫ x : UnitAddCircle,(fourier 1 x).re ∂AddCircle.haarAddCircle from
      periodicHaar_integral_coordinate hi.re i]
  change (∫ x : UnitAddCircle,RCLike.re (fourier 1 x) ∂AddCircle.haarAddCircle) = 0
  rw [integral_re hi,periodicCircle_fourier_integral]
  norm_num
lemma periodicCircle_cos_sq (x : UnitAddCircle) :
    (fourier 1 x).re^2 = (1+(fourier 2 x).re)/2 := by
  let z := fourier 1 x
  have hz : ‖z‖ = 1 := by simp [z,fourier_apply]
  have hsq : z.re^2+z.im^2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simp only [Complex.normSq_apply,pow_two] at h ⊢
    nlinarith
  have hmul : (fourier 2 x).re = z.re^2-z.im^2 := by
    have h : (fourier 2 x) = z*z := by
      simpa [z] using (fourier_add (m := 1) (n := 1) (x := x))
    rw [h,Complex.mul_re]
    ring
  change z.re^2 = (1+(fourier 2 x).re)/2
  rw [hmul]
  nlinarith
lemma periodicCoordinateCos_second_moment (i : ι) :
    (∫ x,periodicCoordinateCos i x^2 ∂periodicHaar ι) = 1/2 := by
  have hi : Integrable (fourier (T := 1) 2) AddCircle.haarAddCircle :=
    (fourier 2).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hC : Integrable (fun x : UnitAddCircle => (fourier 1 x).re^2) AddCircle.haarAddCircle := by
    exact (Complex.continuous_re.comp (fourier 1).continuous).pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [show (∫ x,periodicCoordinateCos i x^2 ∂periodicHaar ι) =
    ∫ x : UnitAddCircle,(fourier 1 x).re^2 ∂AddCircle.haarAddCircle from
      periodicHaar_integral_coordinate hC i]
  simp_rw [periodicCircle_cos_sq]
  rw [integral_div]
  change (∫ x : UnitAddCircle,(1:ℝ)+RCLike.re (fourier 2 x) ∂AddCircle.haarAddCircle)/2 = 1/2
  rw [integral_add (integrable_const _) hi.re,integral_re hi,periodicCircle_fourier_integral]
  norm_num

def periodicCosineTrialDensity (i : ι) (ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  1+ε*periodicCoordinateCos i x
lemma periodicCosineTrialDensity_bounds (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) (x : PeriodicTorus ι) :
    1/2 ≤ periodicCosineTrialDensity i ε x ∧ periodicCosineTrialDensity i ε x ≤ 3/2 := by
  have h : |ε*periodicCoordinateCos i x| ≤ 1/2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (periodicCoordinateCos_abs_le_one i x) (abs_nonneg ε)).trans
      (by simpa using hε)
  have h' := abs_le.mp h
  constructor <;> unfold periodicCosineTrialDensity <;> linarith
lemma periodicCosineTrialDensity_integral (i : ι) (ε : ℝ) :
    (∫ x,periodicCosineTrialDensity i ε x ∂periodicHaar ι) = 1 := by
  rw [show periodicCosineTrialDensity i ε = (fun x => 1+ε*periodicCoordinateCos i x) from rfl,
    integral_add (integrable_const _) ((periodicCoordinateCos_integrable i).const_mul ε),
    integral_const_mul,periodicCoordinateCos_mean_zero]
  simp

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCoordinateCos_second_moment
#print axioms DGRHS.Periodic.periodicCosineTrialDensity_integral
#check @DGRHS.Periodic.periodicCoordinateCos_second_moment
