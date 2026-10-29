import DGRHS.Gaussian.PeriodicHeatMassControl
import DGRHS.Gaussian.PeriodicLongHeatBound

/-! Exact matching of the actual torus heat parameter with the physical
Gaussian scale used by the checked logarithmic Frullani core. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatScaleFactor (ι : Type u) [Fintype ι] : ℝ :=
  (Real.sqrt (2*Real.pi))^(Fintype.card ι)

lemma periodicHeatScaleFactor_pos : 0<periodicHeatScaleFactor ι := by
  unfold periodicHeatScaleFactor
  positivity

lemma periodicHeat_physical_scale_sqrt (t : ℝ) (ht : 0<t) :
    Real.sqrt (1/(2*Real.pi*t^2)) = (Real.sqrt (2*Real.pi)*t)⁻¹ := by
  rw [one_div,Real.sqrt_inv,Real.sqrt_mul (by positivity : 0≤2*Real.pi),Real.sqrt_sq_eq_abs,
    abs_of_pos ht]

lemma periodicHeat_physical_scale_coefficient (t : ℝ) (ht : 0<t) :
    periodicHeatScaleFactor ι*t^(Fintype.card ι-1)*
      (Real.sqrt (1/(2*Real.pi*t^2)))^(Fintype.card ι) = t⁻¹ := by
  rw [periodicHeat_physical_scale_sqrt t ht,periodicHeatScaleFactor,inv_pow,mul_pow]
  have hs : Real.sqrt (2*Real.pi)≠0 := by positivity
  have hd : 1≤Fintype.card ι := Fintype.card_pos
  have hp : t^(Fintype.card ι-1)*t=t^(Fintype.card ι) := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  apply (mul_right_cancel₀ ht.ne')
  field_simp [ht.ne',hs]
  exact hp

lemma periodicHeat_physical_scale_parameter (t : ℝ) (ht : 0<t) :
    Real.pi/(1/(2*Real.pi*t^2)) = 2*Real.pi^2*t^2 := by
  field_simp

lemma periodicHeat_physical_scale_exponent (t r : ℝ) (ht : 0<t) :
    -Real.pi*(1/(2*Real.pi*t^2))*r^2 = -r^2/(2*t^2) := by
  field_simp [ht.ne',Real.pi_ne_zero]

/-- Genuine equality with the physical lattice integrand, at every positive
scale and every point; it supplies the coefficient-one logarithmic core. -/
theorem periodicHeat_physical_scale_identity (t : ℝ) (ht : 0<t) (x : EuclideanSpace ℝ ι) :
    periodicHeatScaleFactor ι*t^(Fintype.card ι-1)*
      (periodicGaussianHeat (2*Real.pi^2*t^2) (fun i => (x i : UnitAddCircle))).re =
      t⁻¹*∑' k : PeriodicFrequency ι,Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2)) := by
  have h := periodicGaussianHeat_physical_formula (1/(2*Real.pi*t^2)) (by positivity) x
  rw [periodicHeat_physical_scale_parameter t ht] at h
  rw [h,Complex.ofReal_re]
  simp only [periodicHeat_physical_scale_exponent t _ ht]
  rw [← mul_assoc,periodicHeat_physical_scale_coefficient t ht]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeat_physical_scale_sqrt
#print axioms DGRHS.Periodic.periodicHeat_physical_scale_coefficient
#print axioms DGRHS.Periodic.periodicHeat_physical_scale_identity
#check @DGRHS.Periodic.periodicHeat_physical_scale_identity
