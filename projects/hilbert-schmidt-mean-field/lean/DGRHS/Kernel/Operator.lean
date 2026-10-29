/- Supporting actual downstream instantiation of licensed row-operator.
Exact development receipts are in records/kernel-operator/RESULT.json.
No paper-result protected acceptance is claimed.
Source: DGR v1 centered-kernel operator in Section2. Requires centered kernel L2,
not an additional assumption that the uncentered interaction is L2. -/
import DGRHS.Kernel.Imported.KernelOperator
import DGRHS.Kernel.Separated
import DGRHS.Kernel.Centering
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Symmetric
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace DGRHS.Kernel
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

noncomputable def integralOperator (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := Operator.l2KernelOp (hk.toLp k)

theorem integralOperator_apply_ae (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (f : Lp ℝ 2 μ) :
    (integralOperator k hk f : α → ℝ) =ᵐ[μ] fun x ↦ ∫ y, k (x,y) * f y ∂μ := by
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ((hk.toLp k : Lp ℝ 2 (μ.prod μ)) : α × α → ℝ) (x,y) = k (x,y) :=
    Measure.ae_ae_of_ae_prod hk.coeFn_toLp
  filter_upwards [Operator.l2KernelOp_apply_ae (hk.toLp k) f, hae] with x hx hrow
  change (Operator.l2KernelOp (hk.toLp k) f : α → ℝ) x = _
  rw [hx]
  exact integral_congr_ae (by filter_upwards [hrow] with y hy using by rw [hy])

theorem norm_l2KernelOp_le (κ : Lp ℝ 2 (μ.prod μ)) : ‖Operator.l2KernelOp κ‖ ≤ ‖κ‖ := by
  have hmap : ‖(Operator.l2KernelOp : Lp ℝ 2 (μ.prod μ) →L[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))‖ ≤ 1 := by
    unfold Operator.l2KernelOp
    exact LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  calc
    ‖Operator.l2KernelOp κ‖ ≤ ‖(Operator.l2KernelOp : Lp ℝ 2 (μ.prod μ) →L[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))‖ * ‖κ‖ := Operator.l2KernelOp.le_opNorm κ
    _ ≤ 1 * ‖κ‖ := mul_le_mul_of_nonneg_right hmap (norm_nonneg κ)
    _ = ‖κ‖ := one_mul _

theorem norm_integralOperator_le (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ)) :
    ‖integralOperator k hk‖ ≤ ‖hk.toLp k‖ := norm_l2KernelOp_le _

/-- Bilinear integral is justified by product-space L2 times the separated L2 product. -/
theorem inner_integralOperator (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (f g : Lp ℝ 2 μ) :
    inner ℝ (integralOperator k hk f) g = ∫ p, k p * g p.1 * f p.2 ∂(μ.prod μ) := by
  have hint : Integrable (fun p : α × α ↦ k p * (g p.1 * f p.2)) (μ.prod μ) :=
    integrable_kernel_bilinear μ hk (Lp.memLp g) (Lp.memLp f)
  have hrepr := integralOperator_apply_ae k hk f
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℝ ((integralOperator k hk f) x) (g x) ∂μ)
        = ∫ x, (∫ y, k (x,y) * f y ∂μ) * g x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hrepr] with x hx
      rw [hx]
      simp only [RCLike.inner_apply', conj_trivial, mul_comm]
    _ = ∫ x, ∫ y, k (x,y) * (g x * f y) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ∫ p, k p * (g p.1 * f p.2) ∂(μ.prod μ) := (integral_prod _ hint).symm
    _ = ∫ p, k p * g p.1 * f p.2 ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [] with p
      ring

/-- Symmetry follows from the actual kernel equality a.e.; no spectral premise. -/
theorem integralOperator_isSymmetric (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (hsym : ∀ᵐ p ∂μ.prod μ, k p.swap = k p) :
    (integralOperator k hk).toLinearMap.IsSymmetric := by
  intro f g
  calc
    inner ℝ (integralOperator k hk f) g
        = ∫ p, k p * g p.1 * f p.2 ∂(μ.prod μ) := inner_integralOperator k hk f g
    _ = ∫ p, k p.swap * f p.2 * g p.1 ∂(μ.prod μ) := by
      refine integral_congr_ae ?_
      filter_upwards [hsym] with p hp
      rw [hp]
      ring
    _ = ∫ p, k p * f p.1 * g p.2 ∂(μ.prod μ) :=
      integral_prod_swap (fun p : α × α ↦ k p * f p.1 * g p.2)
    _ = inner ℝ (integralOperator k hk g) f := (inner_integralOperator k hk g f).symm
    _ = inner ℝ f (integralOperator k hk g) := real_inner_comm _ _


noncomputable def oneL2 : Lp ℝ 2 μ :=
  (memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ : α ↦ (1 : ℝ))

theorem oneL2_coeFn : (oneL2 (μ := μ) : α → ℝ) =ᵐ[μ] fun _ ↦ (1 : ℝ) :=
  (memLp_const (μ := μ) (p := 2) (1 : ℝ)).coeFn_toLp

/-- The canonical row mean kills the actual constant function in L2. -/
theorem integralOperator_one_eq_zero (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ))
    (hmean : ∀ᵐ x ∂μ, ∫ y, k (x,y) ∂μ = 0) :
    integralOperator k hk (oneL2 (μ := μ)) = 0 := by
  apply Lp.ext
  filter_upwards [integralOperator_apply_ae k hk (oneL2 (μ := μ)), hmean,
    Lp.coeFn_zero ℝ 2 μ] with x hx hrow hzero
  rw [hx, hzero]
  calc
    (∫ y, k (x,y) * (oneL2 (μ := μ) : Lp ℝ 2 μ) y ∂μ)
        = ∫ y, k (x,y) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [oneL2_coeFn (μ := μ)] with y hy
      rw [hy, mul_one]
    _ = 0 := hrow

/-- Symmetric canonical operator range is orthogonal to constants. -/
theorem inner_one_integralOperator_eq_zero (k : α × α → ℝ)
    (hk : MemLp k 2 (μ.prod μ)) (hsym : ∀ᵐ p ∂μ.prod μ, k p.swap = k p)
    (hmean : ∀ᵐ x ∂μ, ∫ y, k (x,y) ∂μ = 0) (f : Lp ℝ 2 μ) :
    inner ℝ (oneL2 (μ := μ)) (integralOperator k hk f) = 0 := by
  calc
    inner ℝ (oneL2 (μ := μ)) (integralOperator k hk f)
        = inner ℝ (integralOperator k hk (oneL2 (μ := μ))) f :=
      (integralOperator_isSymmetric k hk hsym (oneL2 (μ := μ)) f).symm
    _ = 0 := by rw [integralOperator_one_eq_zero k hk hmean, inner_zero_left]


theorem integralOperator_isCompact (k : α × α → ℝ) (hk : MemLp k 2 (μ.prod μ)) :
    IsCompactOperator (integralOperator k hk) := Operator.l2KernelOp_isCompact _

/-- Actual centered interaction operator; only the centered kernel needs L2. -/
noncomputable def centeredIntegralOperator (W : α → α → ℝ)
    (hk : MemLp (Function.uncurry (DGRHS.centeredKernel μ W)) 2 (μ.prod μ)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := integralOperator _ hk

theorem centeredIntegralOperator_isCompact (W : α → α → ℝ)
    (hk : MemLp (Function.uncurry (DGRHS.centeredKernel μ W)) 2 (μ.prod μ)) :
    IsCompactOperator (centeredIntegralOperator W hk) := integralOperator_isCompact _ hk

theorem centeredIntegralOperator_isSymmetric (W : α → α → ℝ)
    (hk : MemLp (Function.uncurry (DGRHS.centeredKernel μ W)) 2 (μ.prod μ))
    (hWsym : ∀ x y, W x y = W y x) :
    (centeredIntegralOperator W hk).toLinearMap.IsSymmetric := by
  apply integralOperator_isSymmetric
  exact Filter.Eventually.of_forall (fun p ↦ DGRHS.centeredKernel_symmetric μ W hWsym p.2 p.1)

theorem centeredIntegralOperator_one_eq_zero (W : α → α → ℝ)
    (hk : MemLp (Function.uncurry (DGRHS.centeredKernel μ W)) 2 (μ.prod μ))
    (hW : Integrable (Function.uncurry W) (μ.prod μ)) :
    centeredIntegralOperator W hk (oneL2 (μ := μ)) = 0 :=
  integralOperator_one_eq_zero _ hk (DGRHS.integral_centeredKernel_right μ W hW)

/-- Concrete typeclass bridge for Borel finite-dimensional spaces. -/
theorem separable_L2 [MeasurableSpace.CountablyGenerated α] :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

end DGRHS.Kernel

#print axioms DGRHS.Kernel.integralOperator_apply_ae
#check DGRHS.Kernel.integralOperator_apply_ae

#print axioms DGRHS.Kernel.norm_integralOperator_le
#check DGRHS.Kernel.norm_integralOperator_le

#print axioms DGRHS.Kernel.inner_integralOperator
#check DGRHS.Kernel.inner_integralOperator

#print axioms DGRHS.Kernel.integralOperator_isSymmetric
#check DGRHS.Kernel.integralOperator_isSymmetric

#print axioms DGRHS.Kernel.integralOperator_one_eq_zero
#check DGRHS.Kernel.integralOperator_one_eq_zero

#print axioms DGRHS.Kernel.inner_one_integralOperator_eq_zero
#check DGRHS.Kernel.inner_one_integralOperator_eq_zero

#print axioms DGRHS.Kernel.integralOperator_isCompact
#check DGRHS.Kernel.integralOperator_isCompact

#print axioms DGRHS.Kernel.centeredIntegralOperator_isCompact
#check DGRHS.Kernel.centeredIntegralOperator_isCompact

#print axioms DGRHS.Kernel.centeredIntegralOperator_isSymmetric
#check DGRHS.Kernel.centeredIntegralOperator_isSymmetric

#print axioms DGRHS.Kernel.centeredIntegralOperator_one_eq_zero
#check DGRHS.Kernel.centeredIntegralOperator_one_eq_zero

#print axioms DGRHS.Kernel.separable_L2
#check DGRHS.Kernel.separable_L2
