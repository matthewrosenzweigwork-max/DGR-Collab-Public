import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-! The ordinary Hessian and harmonicity of the local logarithmic singularity. -/

noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped RealInnerProductSpace Topology ContDiff Laplacian

namespace PeriodicAttractiveLogGas

theorem fderiv_fderiv_planarLogKernel_apply {x : PlanarSpace} (hx : x ≠ 0)
    (u v : PlanarSpace) :
    fderiv ℝ (fderiv ℝ planarLogKernel) x u v =
      2 * (‖x‖ ^ 2)⁻¹ ^ 2 * ⟪x, u⟫ * ⟪x, v⟫ - (‖x‖ ^ 2)⁻¹ * ⟪u, v⟫ := by
  have hs := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := ((hasDerivAt_inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).comp_hasFDerivAt x hs).neg
  have hd := hi.smul (innerSL ℝ (E := PlanarSpace)).hasFDerivAt
  change HasFDerivAt (fun y : PlanarSpace ↦ -(‖y‖ ^ 2)⁻¹ • innerSL ℝ y) _ x at hd
  have heq : fderiv ℝ planarLogKernel =ᶠ[𝓝 x]
      (fun y : PlanarSpace ↦ -(‖y‖ ^ 2)⁻¹ • innerSL ℝ y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact fderiv_planarLogKernel hy
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply,
    innerSL_apply_apply, smul_eq_mul, Function.comp_apply, Pi.neg_apply, inv_pow]
  change -(‖x‖ ^ 2)⁻¹ * ⟪u, v⟫ +
    -(-((‖x‖ ^ 2) ^ 2)⁻¹ * ((2 : ℕ) • ⟪x, u⟫)) * ⟪x, v⟫ = _
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem laplacian_planarLogKernel {x : PlanarSpace} (hx : x ≠ 0) :
    Δ planarLogKernel x = 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis planarLogKernel
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_planarLogKernel_apply hx]
  have hs : ∑ j : Fin 2, (x j) ^ 2 = ‖x‖ ^ 2 := EuclideanSpace.real_norm_sq_eq x |>.symm
  simp only [EuclideanSpace.inner_basisFun_real]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_true, mul_assoc, ← sq]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hs]
  field_simp
  norm_num

theorem harmonicAt_planarLogKernel {x : PlanarSpace} (hx : x ≠ 0) :
    HarmonicAt planarLogKernel x := by
  refine ⟨(contDiffAt_planarLogKernel hx).of_le (by simp), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact laplacian_planarLogKernel hy

end PeriodicAttractiveLogGas
