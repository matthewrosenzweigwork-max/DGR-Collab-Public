import DGPS.Lipschitz.HessianKernel
import DGPS.Equilibrium.Hessian
import SharpSymmetricLSI.Paper.Sec42Spectral1

/-!
# Coercivity after exclusion of the density-Hessian nullspace

The only additional structural input is triviality of the actual nullspace. Compactness,
self-adjointness and nonnegativity are already established at a free-energy minimizer.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

/-- A positive semidefinite identity plus compact symmetric operator is coercive if its
kernel vanishes. The bounded inverse is obtained from the compact-operator alternative. -/
theorem coercive_id_add_compact_of_kernel_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hsym : ∀ f g : H, inner ℝ (T f) g = inner ℝ f (T g))
    (hpos : ∀ f : H, 0 ≤ inner ℝ f (f + T f))
    (hker : ∀ f : H, f + T f = 0 → f = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : H, c * ‖f‖ ^ 2 ≤ inner ℝ f (f + T f) := by
  have hunit : IsUnit (1 + T : H →L[ℝ] H) := by
    rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (𝕜 := ℝ) (X := H)
      (T := T) hT (μ := (-1 : ℝ)) (by norm_num) with heig | hres
    · obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
      have hvT : T v = -v := by simpa using hv.apply_eq_smul
      exact False.elim (hv.2 (hker v (by rw [hvT]; simp)))
    · rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, neg_one_smul] at hres
      have he : (1 + T : H →L[ℝ] H) = -((-1 : H →L[ℝ] H) - T) := by abel
      rw [he]
      exact hres.neg
  obtain ⟨u, hu⟩ := hunit
  let B : H →L[ℝ] H := 1 + T
  let S : H →L[ℝ] H := ↑u⁻¹
  have hleft : ∀ f : H, S (B f) = f := by
    intro f
    have hSB : S * B = 1 := by
      change (↑u⁻¹ : H →L[ℝ] H) * (1 + T) = 1
      rw [← hu]
      exact u.inv_mul
    exact congrArg (fun C : H →L[ℝ] H => C f) hSB
  have hsymB : ∀ f g : H, inner ℝ g (B f) = inner ℝ f (B g) := by
    intro f g
    simp only [B, add_apply, one_apply_eq_self, inner_add_right]
    rw [← hsym f g, real_inner_comm g f, real_inner_comm g (T f)]
  have hnorm : ∀ f : H, ‖B f‖ ^ 2 ≤ ‖B‖ * inner ℝ f (B f) := by
    intro f
    exact SharpLSI.norm_sq_apply_le (P := fun _ : H => True)
      (fun _ _ _ _ _ => trivial) (fun _ _ => trivial)
      (fun f g _ _ => hsymB f g)
      (fun f _ => hpos f) (u := f) trivial
  let C : ℝ := ‖S‖ ^ 2 * ‖B‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1 / C, one_div_pos.mpr hC, fun f => ?_⟩
  have hnf : ‖f‖ ≤ ‖S‖ * ‖B f‖ := by
    calc ‖f‖ = ‖S (B f)‖ := congrArg norm (hleft f).symm
      _ ≤ _ := S.le_opNorm _
  have hsquare : ‖f‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖B f‖ ^ 2 := by
    calc ‖f‖ ^ 2 ≤ (‖S‖ * ‖B f‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnf 2
      _ = _ := mul_pow _ _ _
  have hbound : ‖f‖ ^ 2 ≤ (‖S‖ ^ 2 * ‖B‖) * inner ℝ f (B f) := by
    calc ‖f‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖B f‖ ^ 2 := hsquare
      _ ≤ ‖S‖ ^ 2 * (‖B‖ * inner ℝ f (B f)) :=
        mul_le_mul_of_nonneg_left (hnorm f) (sq_nonneg _)
      _ = _ := by ring
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC]
  change ‖f‖ ^ 2 ≤ inner ℝ f (B f) * C
  have hp : 0 ≤ inner ℝ f (B f) := hpos f
  dsimp only [C]
  nlinarith [hp]

variable {d : ℕ}

/-- The two production kernel operators represent the same actual centered kernel. -/
theorem centeredOperator_eq_kernelOp (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    centeredOperator A (μ : Measure (Torus d)) = DGPS.kernelOp A μ := by
  ext f
  filter_upwards [centeredOperator_apply_ae A (μ : Measure (Torus d)) f,
    DGPS.kernelOp_ae A μ f] with x hx hy
  exact hx.trans hy.symm

/-- Excluding the actual minimizer nullspace supplies the canonical coercive Hessian used by
the Gaussian covariance layer. No positivity-to-nullspace implication is assumed implicitly. -/
theorem isCoerciveDensityHessian_of_nullspace_eq_bot (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (hker : nullspace A μ = ⊥) : IsCoerciveDensityHessian A μ := by
  have hzero : ∀ f : meanZeroL2 μ, f + centeredOperator0 A μ f = 0 → f = 0 := by
    intro f hf
    have hmem := (mem_nullspace A μ f).2 hf
    rw [hker, Submodule.mem_bot] at hmem
    exact hmem
  obtain ⟨c, hc, hbound⟩ := coercive_id_add_compact_of_kernel_zero
    (centeredOperator0 A μ) (isCompactOperator_centeredOperator0 A μ)
    (centeredOperator0_symm A μ)
    (fun f => by rw [real_inner_comm]; exact centeredOperator0_psd A μ hmin f) hzero
  refine ⟨c, hc, fun f => ?_⟩
  let g : meanZeroL2 μ := ⟨f.1, (mem_meanZeroL2 μ f.1).2 f.2⟩
  have hg := hbound g
  change c * ‖f.1‖ ^ 2 ≤ inner ℝ f.1
    (f.1 + centeredOperator A (μ : Measure (Torus d)) f.1) at hg
  change c * ‖f.1‖ ^ 2 ≤ inner ℝ f.1 (f.1 + DGPS.kernelOp A μ f.1)
  rwa [centeredOperator_eq_kernelOp A μ] at hg

end DGPS.Lipschitz
