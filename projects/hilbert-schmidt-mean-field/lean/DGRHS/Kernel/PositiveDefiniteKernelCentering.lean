/- Original bounded finite-Gram kernel positivity survives probability centering.
Uses native RKHS construction and a proper scalar weak mean; no separability,
strong feature measurability or feature-representation premise is introduced. -/
import DGRHS.Kernel.ScalarRKHSWeakMean
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Kernel

 theorem positiveDefiniteKernel_centering {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω→Ω→ℝ)
    (hq : IsPositiveDefiniteKernel q) (hmeas : Measurable (Function.uncurry q))
    (M : ℝ) (hcap : ∀ x,q x x≤M) :
    IsPositiveDefiniteKernel (DGRHS.centeredKernel μ q) := by
  letI : Fact (scalarKernelMatrix q).PosSemidef := ⟨hq.scalarKernel_posSemidef⟩
  let H := RKHS.OfKernel (scalarKernelMatrix q)
  have hK : RKHS.kernel H=scalarKernelMatrix q := RKHS.OfKernel.kernel_ofKernel
  have hkm (x : Ω) (r : ℝ) : Measurable (fun y=>(RKHS.kerFun H x r) y) := by
    have he : (fun y=>(RKHS.kerFun H x r) y)=(fun y=>q y x*r) := by
      funext y
      rw [RKHS.kerFun_apply,hK]
      simp only [scalarKernelMatrix,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
        smul_eq_mul]
    rw [he]
    exact (hmeas.comp (measurable_id.prodMk measurable_const)).mul_const r
  have hkc (x : Ω) : ‖RKHS.kernel H x x‖≤M := by
    rw [hK]
    simpa [scalarKernelMatrix,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (hq.diagonal_nonneg x)] using hcap x
  obtain ⟨b,hb⟩ := exists_scalarRKHS_weakMean μ hkm M hkc
  let k : Ω→H := fun x=>RKHS.kerFun H x 1
  have hgram (x y : Ω) : inner ℝ (k x) (k y)=q x y := by
    have h := RKHS.kernel_inner (H:=H) y x (1:ℝ) (1:ℝ)
    rw [hK] at h
    have he : inner ℝ (k x) (k y)=q y x := by
      simpa only [scalarKernelMatrix,k,Real.inner_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul,mul_one,one_mul] using h.symm
    exact he.trans (hq.symmetric y x)
  have hrep (x y : Ω) : (k x) y=q x y := by
    dsimp only [k]
    rw [RKHS.kerFun_apply,hK]
    simpa [scalarKernelMatrix,hq.symmetric] using (rfl : q y x=q y x)
  have hrow (x : Ω) : (∫ y,q x y ∂μ)=inner ℝ (k x) b := by
    simpa only [hrep] using (hb (k x)).2
  have hcol (y : Ω) : (∫ x,q x y ∂μ)=inner ℝ (k y) b := by
    have he : (fun x=>q x y)=(fun x=>q y x) := funext (fun x=>hq.symmetric x y)
    rw [he]
    exact hrow y
  have hbfun (x : Ω) : inner ℝ (k x) b=b x := by
    dsimp only [k]
    simp only [RKHS.kerFun_inner,Real.inner_apply,one_mul]
  have hpair : (∫ z,q z.1 z.2 ∂μ.prod μ)=inner ℝ b b := by
    have hi := (positiveDefiniteKernel_centered_cap μ q hq hmeas M hcap).1
    change (∫ z,Function.uncurry q z ∂μ.prod μ)=inner ℝ b b
    rw [integral_prod _ hi]
    change (∫ x,∫ y,q x y ∂μ ∂μ)=inner ℝ b b
    simp_rw [hrow,hbfun]
    exact (hb b).2
  have hc (x y : Ω) : DGRHS.centeredKernel μ q x y=inner ℝ (k x-b) (k y-b) := by
    unfold DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
    rw [hrow,hcol,hpair]
    rw [inner_sub_left,inner_sub_right,inner_sub_right,hgram]
    rw [real_inner_comm b (k y)]
    ring
  refine ⟨DGRHS.centeredKernel_symmetric μ q hq.symmetric,?_⟩
  intro n x c
  have hs : 0 ≤ inner ℝ (∑ i,c i • (k (x i)-b)) (∑ i,c i • (k (x i)-b)) :=
    real_inner_self_nonneg
  rw [_root_.sum_inner] at hs
  simp only [real_inner_smul_left] at hs
  have he (i : Fin n) : inner ℝ (k (x i)-b) (∑ j,c j • (k (x j)-b))=
      ∑ j,c j*inner ℝ (k (x i)-b) (k (x j)-b) := by
    rw [_root_.inner_sum]
    simp only [real_inner_smul_right]
  simp_rw [he,Finset.mul_sum] at hs
  simpa only [mul_assoc,hc] using hs
end DGRHS.Kernel
#check @DGRHS.Kernel.positiveDefiniteKernel_centering
#print axioms DGRHS.Kernel.positiveDefiniteKernel_centering
