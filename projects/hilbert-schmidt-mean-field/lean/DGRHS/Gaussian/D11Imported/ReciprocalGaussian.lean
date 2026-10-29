/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-! Reciprocal Gaussian integral underlying the half-integer Bessel identity.
This file establishes its reciprocal change of variables from the actual
improper integral, without assuming a Bessel transform formula. -/
noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian.D11Imported.ReciprocalGaussian

def kernel (a x : ℝ) : ℝ := Real.exp (-x^2-(a/x)^2)
def mass (a : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), kernel a x

lemma kernel_pos (a x : ℝ) : 0 < kernel a x := Real.exp_pos _

lemma kernel_le_gaussian (a x : ℝ) : kernel a x ≤ Real.exp (-x^2) := by
  unfold kernel
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (a/x)])

lemma kernel_measurable (a : ℝ) : Measurable (kernel a) := by
  unfold kernel
  fun_prop

lemma kernel_integrable (a : ℝ) : IntegrableOn (kernel a) (Ioi (0:ℝ)) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1)
  apply hg.integrableOn.mono' (kernel_measurable a).aestronglyMeasurable
  exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_pos (kernel_pos a x)]; exact kernel_le_gaussian a x)

lemma reciprocal_image {a : ℝ} (ha : 0 < a) :
    (fun x : ℝ => a/x) '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos ha hx
  · intro hy
    refine ⟨a/y, div_pos ha hy, ?_⟩
    field_simp

lemma reciprocal_injOn {a : ℝ} (ha : 0 < a) : InjOn (fun x : ℝ => a/x) (Ioi 0) := by
  intro x hx y hy he
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have h := (div_eq_div_iff hx0 hy0).mp he
  nlinarith

lemma kernel_reciprocal {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    kernel a (a/x) = kernel a x := by
  have he : a/(a/x)=x := by field_simp
  unfold kernel
  rw [he]
  congr 1
  ring

lemma weighted_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0:ℝ), (a/x^2)*kernel a x) = mass a := by
  have hd (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) :
      HasDerivWithinAt (fun x : ℝ => a/x) (-a/x^2) (Ioi 0) x := by
    have h := (hasDerivAt_const x a).div (hasDerivAt_id x) (ne_of_gt hx)
    convert h.hasDerivWithinAt using 1 <;> first | rfl | simp
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd (reciprocal_injOn ha) (kernel a)
  rw [reciprocal_image ha] at h
  change mass a = _ at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [kernel_reciprocal ha hx]
  simp only [smul_eq_mul, neg_div, abs_neg, abs_of_pos (div_pos ha (sq_pos_of_pos hx))]

lemma mass_pos (a : ℝ) : 0 < mass a := by
  unfold mass
  rw [integral_pos_iff_support_of_nonneg (fun x => (kernel_pos a x).le) (kernel_integrable a)]
  have hs : Function.support (kernel a) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (kernel_pos a x).ne'
  rw [hs, Measure.restrict_apply_univ]
  simp

lemma weighted_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (a/x^2)*kernel a x) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [weighted_integral ha]
  exact (mass_pos a).ne'

#print axioms weighted_integral
end DGRHS.Gaussian.D11Imported.ReciprocalGaussian
