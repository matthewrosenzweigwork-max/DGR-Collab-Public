/- Bounded scalar integration gives a weak Hilbert mean through the adjoint.
No Bochner integrability or separable-range premise for the feature is used. -/
import DGRHS.Kernel.ScalarRKHSMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Kernel

 theorem exists_scalarRKHS_weakMean {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [RKHS ℝ H Ω ℝ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hk : ∀ (x : Ω) (r : ℝ),Measurable (fun y=>(RKHS.kerFun H x r) y))
    (M : ℝ) (hcap : ∀ x,‖RKHS.kernel H x x‖≤M) :
    ∃ b : H,∀ f : H, Integrable (fun x=>f x) μ ∧
      (∫ x,f x ∂μ)=inner ℝ f b := by
  have hm (f : H) := measurable_scalarRKHS_function hk f
  have hb (f : H) (x : Ω) : ‖f x‖≤‖f‖*Real.sqrt M :=
    (RKHS.norm_apply_le f x).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hcap x)) (norm_nonneg f))
  have hi (f : H) : Integrable (fun x=>f x) μ :=
    Integrable.of_bound (hm f).aestronglyMeasurable (‖f‖*Real.sqrt M)
      (Filter.Eventually.of_forall (hb f))
  let l : H→ₗ[ℝ]ℝ := {
    toFun := fun f=>∫ x,f x ∂μ
    map_add' := fun f g=>by
      simpa only [RKHS.coe_add,Pi.add_apply] using integral_add (hi f) (hi g)
    map_smul' := fun r f=>by
      simpa only [RKHS.coe_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply] using
        (integral_const_mul r (fun x=>f x)) }
  let L : H→L[ℝ]ℝ := l.mkContinuous (Real.sqrt M) (fun f=>by
    simpa [l,mul_comm] using
      norm_integral_le_of_norm_le_const (μ:=μ) (f:=fun x=>f x)
        (Filter.Eventually.of_forall (hb f)))
  refine ⟨L.adjoint 1,fun f=>⟨hi f,?_⟩⟩
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [Real.inner_apply,mul_one]
  rfl
end DGRHS.Kernel
#check @DGRHS.Kernel.exists_scalarRKHS_weakMean
#print axioms DGRHS.Kernel.exists_scalarRKHS_weakMean
