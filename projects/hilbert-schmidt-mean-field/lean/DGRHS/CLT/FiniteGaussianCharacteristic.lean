/- Actual finite Gaussian CF from zero means and proper covariances, followed
by the native characteristic-function consequence of weak convergence.
Correlations are retained; no independent-coordinate assumption is made. -/
import DGRHS.CLT.SourceObservableFluctuation
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Moments.Variance
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace DGRHS.CLT
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma finiteGaussian_scalar_law {m : ℕ} (Z : Ω → (Fin m → ℝ))
    (hG : HasGaussianLaw Z P) (hmean : ∀ k, (∫ ω,Z ω k ∂P) = 0)
    (covMat : Fin m → Fin m → ℝ)
    (hcov : ∀ k l, (∫ ω,Z ω k*Z ω l ∂P) = covMat k l) (θ : Fin m → ℝ) :
    HasLaw (fun ω => ∑ k : Fin m,θ k*Z ω k)
      (gaussianReal 0 (Real.toNNReal (∑ k : Fin m,∑ l : Fin m,θ k*θ l*covMat k l))) P := by
  let L : (Fin m → ℝ) →L[ℝ] ℝ := ∑ k : Fin m, θ k • ContinuousLinearMap.proj k
  have hL : ∀ z : Fin m → ℝ, L z = ∑ k : Fin m,θ k*z k := by
    intro z
    simp [L]
  have hScalar : HasGaussianLaw (fun ω => ∑ k : Fin m,θ k*Z ω k) P := by
    simpa only [hL] using hG.map_fun L
  have hk : ∀ k, MemLp (fun ω => Z ω k) 2 P := fun k => (hG.map_fun (ContinuousLinearMap.proj k)).memLp_two
  have hsmean : (∫ ω,∑ k : Fin m,θ k*Z ω k ∂P) = 0 := by
    rw [integral_finsetSum _ (fun k _ => ((hk k).integrable (by norm_num)).const_mul (θ k))]
    simp_rw [integral_const_mul,hmean,mul_zero]
    simp
  have hsvar : variance (fun ω => ∑ k : Fin m,θ k*Z ω k) P =
      ∑ k : Fin m,∑ l : Fin m,θ k*θ l*covMat k l := by
    rw [variance_fun_sum (fun k => (hk k).const_mul (θ k))]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [covariance_const_mul_left,covariance_const_mul_right,covariance_eq_sub (hk k) (hk l)]
    simp only [Pi.mul_apply,hmean,mul_zero,sub_zero,hcov]
    ring
  refine ⟨hScalar.aemeasurable,?_⟩
  rw [hScalar.map_eq_gaussianReal,hsmean,hsvar]

lemma finiteGaussian_characteristic {m : ℕ} (Z : Ω → (Fin m → ℝ))
    (hG : HasGaussianLaw Z P) (hmean : ∀ k, (∫ ω,Z ω k ∂P) = 0)
    (covMat : Fin m → Fin m → ℝ)
    (hcov : ∀ k l, (∫ ω,Z ω k*Z ω l ∂P) = covMat k l) (θ : Fin m → ℝ) :
    (∫ ω,Complex.exp ((∑ k : Fin m,θ k*Z ω k : ℝ)*Complex.I) ∂P) =
      Complex.exp (-(∑ k : Fin m,∑ l : Fin m,θ k*θ l*covMat k l : ℝ)/2) := by
  have hl := finiteGaussian_scalar_law Z hG hmean covMat hcov θ
  have hnonneg : 0 ≤ ∑ k : Fin m,∑ l : Fin m,θ k*θ l*covMat k l := by
    have hv := variance_nonneg (fun ω => ∑ k : Fin m,θ k*Z ω k) P
    -- The proper Gaussian scalar variance is also obtained directly from the
    -- actual finite covariance computation, without assuming covMat is positive.
    have hk : ∀ k, MemLp (fun ω => Z ω k) 2 P := fun k => (hG.map_fun (ContinuousLinearMap.proj k)).memLp_two
    have he' : variance (fun ω => ∑ k : Fin m,θ k*Z ω k) P =
        ∑ k : Fin m,∑ l : Fin m,θ k*θ l*covMat k l := by
      rw [variance_fun_sum (fun k => (hk k).const_mul (θ k))]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [covariance_const_mul_left,covariance_const_mul_right,covariance_eq_sub (hk k) (hk l)]
      simp only [Pi.mul_apply,hmean,mul_zero,sub_zero,hcov]
      ring
    rw [he'] at hv
    exact hv
  calc
    _ = charFun (P.map (fun ω => ∑ k : Fin m,θ k*Z ω k)) 1 := by
      rw [charFun_apply_real,integral_map hl.aemeasurable (by fun_prop)]
      simp only [Function.comp_def,one_mul,Complex.ofReal_one,one_mul]
    _ = _ := by
      rw [hl.map_eq,charFun_gaussianReal]
      simp [Real.coe_toNNReal _ hnonneg]
      congr 1
      ring

variable {ΩN : ℕ → Type*} [∀ N, MeasurableSpace (ΩN N)]
    {PN : ∀ N, Measure (ΩN N)} [∀ N, IsProbabilityMeasure (PN N)]

theorem finiteGaussian_characteristic_tendsto {m : ℕ}
    (X : ∀ N,ΩN N → (Fin m → ℝ)) (Z : Ω → (Fin m → ℝ))
    (hw : TendstoInDistribution X atTop Z PN P)
    (hG : HasGaussianLaw Z P) (hmean : ∀ k, (∫ ω,Z ω k ∂P) = 0)
    (covMat : Fin m → Fin m → ℝ)
    (hcov : ∀ k l, (∫ ω,Z ω k*Z ω l ∂P) = covMat k l) (θ : Fin m → ℝ) :
    Tendsto (fun N => ∫ ω,Complex.exp ((∑ k : Fin m,θ k*X N ω k : ℝ)*Complex.I) ∂PN N)
      atTop (𝓝 (Complex.exp (-(∑ k : Fin m,∑ l : Fin m,θ k*θ l*covMat k l : ℝ)/2))) := by
  let L : (Fin m → ℝ) →L[ℝ] ℝ := ∑ k : Fin m, θ k • ContinuousLinearMap.proj k
  have hL : ∀ z : Fin m → ℝ, L z = ∑ k : Fin m,θ k*z k := by
    intro z; simp [L]
  have hscalar := hw.continuous_comp L.continuous
  have ht := hscalar.tendsto_charFun 1
  have heN : ∀ N, charFun ((PN N).map (L ∘ X N)) 1 =
      ∫ ω,Complex.exp ((∑ k : Fin m,θ k*X N ω k : ℝ)*Complex.I) ∂PN N := by
    intro N
    rw [charFun_apply_real,integral_map (hscalar.forall_aemeasurable N) (by fun_prop)]
    simp [Function.comp_def,hL]
  have heZ : charFun (P.map (L ∘ Z)) 1 =
      Complex.exp (-(∑ k : Fin m,∑ l : Fin m,θ k*θ l*covMat k l : ℝ)/2) := by
    rw [charFun_apply_real,integral_map hscalar.aemeasurable_limit (by fun_prop)]
    simpa [Function.comp_def,hL] using finiteGaussian_characteristic Z hG hmean covMat hcov θ
  simpa only [heN,heZ] using ht
end DGRHS.CLT
#print axioms DGRHS.CLT.finiteGaussian_scalar_law
#print axioms DGRHS.CLT.finiteGaussian_characteristic
#print axioms DGRHS.CLT.finiteGaussian_characteristic_tendsto
#check @DGRHS.CLT.finiteGaussian_characteristic_tendsto
