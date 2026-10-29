import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
Concrete product-L2 estimate for the actual kernel operator bilinear form.
This constructs no assumed spectral sequence, eigenbasis, or kernel operator.
-/

open MeasureTheory
open scoped ENNReal

namespace DGRHS.Kernel

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

lemma memLp_separated_mul {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    MemLp (fun z : α × α => f z.1 * g z.2) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq
    ((hf.comp_fst μ).aestronglyMeasurable.mul (hg.comp_snd μ).aestronglyMeasurable)).2
  simpa only [Pi.mul_apply, mul_pow] using hf.integrable_sq.mul_prod hg.integrable_sq

lemma norm_toLp_sq {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {f : β → ℝ} (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx]

lemma norm_separated_mul {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖(memLp_separated_mul μ hf hg).toLp (fun z : α × α => f z.1 * g z.2)‖ =
      ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have hs : ‖(memLp_separated_mul μ hf hg).toLp (fun z : α × α => f z.1 * g z.2)‖ ^ 2 =
      (‖hf.toLp f‖ * ‖hg.toLp g‖) ^ 2 := by
    rw [norm_toLp_sq, mul_pow, norm_toLp_sq hf, norm_toLp_sq hg]
    simp_rw [mul_pow]
    exact integral_prod_mul (fun x => f x ^ 2) (fun y => g y ^ 2)
  have hp : 0 ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg ((memLp_separated_mul μ hf hg).toLp (fun z : α × α => f z.1 * g z.2))]

lemma integrable_kernel_bilinear {h : α × α → ℝ} {f g : α → ℝ}
    (hh : MemLp h 2 (μ.prod μ)) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => h z * (f z.1 * g z.2)) (μ.prod μ) := by
  exact hh.integrable_mul (memLp_separated_mul μ hf hg)

end DGRHS.Kernel

#print axioms DGRHS.Kernel.memLp_separated_mul
#print axioms DGRHS.Kernel.norm_toLp_sq
#print axioms DGRHS.Kernel.norm_separated_mul
#print axioms DGRHS.Kernel.integrable_kernel_bilinear
