import SharpSymmetricLSI.Paper.NBody2
import SharpSymmetricLSI.Paper.Tensorize
import SharpSymmetricLSI.Defs.D18_GaussianForm

/-!
# R33 groundwork: the particle gradient of a cylinder test

For `C¹` periodic `e_j` and a cylinder `φ ∈ C_c^∞(ℝ^J)`, the test
`φ_N = φ(Z_{N,1},…,Z_{N,J})`, `Z_{N,i} = N^{-1/2} ∑_l e_i(X_l)`, is `C¹` on the lift and
`∇_{l} φ_N = N^{-1/2} ∑_i ∂_iφ(Z_N) ∇e_i(X_l)` (manuscript Section 8.3).
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

variable {d : ℕ}

/-- The fluctuation vector `(Z_{N,1},…,Z_{N,J})` built from `eC`. -/
noncomputable def zC (eC : ℕ → Torus d → ℝ) (N J : ℕ) (X : Config N d) : Fin J → ℝ :=
  fun i => (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, eC (i + 1) (X l)

/-- `zC` on the lift. -/
noncomputable def zL (eC : ℕ → Torus d → ℝ) (N J : ℕ) (x : Fin N × Fin d → ℝ) : Fin J → ℝ :=
  fun i => (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, (eC (i + 1) ∘ liftT) (projBlockL l x)

theorem zC_unflat_liftT (eC : ℕ → Torus d → ℝ) (N J : ℕ) (x : Fin N × Fin d → ℝ) :
    zC eC N J (unflat (liftT x)) = zL eC N J x := by
  funext i; simp only [zC, zL, Function.comp_apply, projBlockL_apply]; rfl

theorem clm_apply_eq_sum {J : ℕ} (L : (Fin J → ℝ) →L[ℝ] ℝ) (w : Fin J → ℝ) :
    L w = ∑ i, L (Pi.single i 1) * w i := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Pi.single i (w i) = w i • (Pi.single i (1 : ℝ) : Fin J → ℝ) := by
    ext j; simp [Pi.single_apply]
  rw [this, map_smul, smul_eq_mul, mul_comm]

section
variable {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (N : ℕ) (c : Cyl)
include hφ

theorem hasFDerivAt_zL_i (i : ℕ) (x : Fin N × Fin d → ℝ) :
    HasFDerivAt (fun x : Fin N × Fin d → ℝ => (N : ℝ) ^ (-(1 / 2 : ℝ)) *
        ∑ l, (eC (i + 1) ∘ liftT) (projBlockL l x))
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) • ∑ l, (fderiv ℝ (eC (i + 1) ∘ liftT) (projBlockL l x)).comp
        (projBlockL l)) x := by
  have h : ∀ l : Fin N, HasFDerivAt (fun x => (eC (i + 1) ∘ liftT) (projBlockL l x))
      ((fderiv ℝ (eC (i + 1) ∘ liftT) (projBlockL l x)).comp (projBlockL l)) x := fun l =>
    (((hφ (i + 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp x
      (projBlockL l).hasFDerivAt
  exact (HasFDerivAt.fun_sum fun l _ => h l).const_mul _

theorem contDiff_compZ {J : ℕ} {φ : (Fin J → ℝ) → ℝ} (hφ1 : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 (((fun X => φ (zC eC N J X)) ∘ unflat) ∘ liftT) := by
  have hcomp : ((fun X => φ (zC eC N J X)) ∘ unflat) ∘ liftT = φ ∘ zL eC N J := by
    funext x; simp only [Function.comp_apply]; rw [zC_unflat_liftT]
  rw [hcomp]
  refine hφ1.comp ?_
  refine contDiff_pi.2 fun i => contDiff_const.mul (ContDiff.sum fun l _ => ?_)
  exact (hφ (i + 1)).comp (projBlockL l).contDiff

/-- **The weak gradient of `φ(Z_N)` for a `C¹` function `φ`.** -/
theorem isWeakGrad_compZ {J : ℕ} (φ : (Fin J → ℝ) → ℝ) (hφ1 : ContDiff ℝ 1 φ) :
    IsWeakGrad ((fun X => φ (zC eC N J X)) ∘ unflat)
      (fun y p => ∑ i : Fin J, fderiv ℝ φ (zC eC N J (unflat y)) (Pi.single i 1) *
        ((N : ℝ) ^ (-(1 / 2 : ℝ)) * cgrad (eC (i + 1)) (projBlock p.1 y) p.2)) := by
  have hcomp : ((fun X => φ (zC eC N J X)) ∘ unflat) ∘ liftT = φ ∘ zL eC N J := by
    funext x; simp only [Function.comp_apply]; rw [zC_unflat_liftT]
  have hzd : ∀ x, HasFDerivAt (zL eC N J) (ContinuousLinearMap.pi fun i : Fin J =>
      (N : ℝ) ^ (-(1 / 2 : ℝ)) • ∑ l, (fderiv ℝ (eC (i + 1) ∘ liftT) (projBlockL l x)).comp
        (projBlockL l)) x := fun x => hasFDerivAt_pi.2 fun i => hasFDerivAt_zL_i hφ N i x
  have hφd : ∀ z, HasFDerivAt φ (fderiv ℝ φ z) z := fun z =>
    (hφ1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hC1 : ContDiff ℝ 1 (((fun X => φ (zC eC N J X)) ∘ unflat) ∘ liftT) := by
    rw [hcomp]
    refine hφ1.comp ?_
    refine contDiff_pi.2 fun i => contDiff_const.mul (ContDiff.sum fun l _ => ?_)
    exact (hφ (i + 1)).comp (projBlockL l).contDiff
  convert isWeakGrad_of_contDiff hC1 using 1
  funext y p
  rw [hcomp, ((hφd _).comp (secT y) (hzd (secT y))).fderiv]
  have hz : zL eC N J (secT y) = zC eC N J (unflat y) := by
    rw [← zC_unflat_liftT, liftT_secT]
  obtain ⟨l0, k⟩ := p
  rw [ContinuousLinearMap.comp_apply, hz, clm_apply_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.sum_apply]
  congr 1
  rw [Finset.sum_eq_single l0]
  · rw [ContinuousLinearMap.comp_apply, projBlockL_single, if_pos rfl]
    rfl
  · intro l _ hl
    rw [ContinuousLinearMap.comp_apply, projBlockL_single, if_neg (Ne.symm hl), map_zero]
  · intro h; exact absurd (Finset.mem_univ l0) h

/-- **The weak gradient of a cylinder test.** -/
theorem isWeakGrad_cyl :
    IsWeakGrad ((fun X => c.φ (zC eC N c.J X)) ∘ unflat)
      (fun y p => ∑ i : Fin c.J, fderiv ℝ c.φ (zC eC N c.J (unflat y)) (Pi.single i 1) *
        ((N : ℝ) ^ (-(1 / 2 : ℝ)) * cgrad (eC (i + 1)) (projBlock p.1 y) p.2)) :=
  isWeakGrad_compZ hφ N c.φ (c.smooth.of_le (by simp))

end

end SharpLSI
