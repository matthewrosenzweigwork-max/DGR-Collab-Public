import DGRHS.Gaussian.PeriodicConvolutionMultiplier

/-! Native Fourier Parseval gives actual
bounded-test positivity from actual nonnegative Fourier coefficients. The
physical residual coefficients must be separately derived, never premises
at the final partition endpoint. -/
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Convolution
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local instance periodicFormCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

lemma periodic_bounded_fourier_form_hasSum (G F : PeriodicTorus ι → ℝ)
    (hG : Integrable G (periodicHaar ι)) (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x,‖F x‖ ≤ B) (a : PeriodicFrequency ι → ℝ)
    (hcoeff : ∀ k,UnitAddTorus.mFourierCoeff (fun x => (G x:ℂ)) k = (a k:ℂ)) :
    HasSum (fun k => a k*((UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).re^2+
      (UnitAddTorus.mFourierCoeff (fun x => (F x:ℂ)) k).im^2))
      (∫ x,F x*(∫ y,F y*G (x-y) ∂periodicHaar ι) ∂periodicHaar ι) := by
  let Fc : PeriodicTorus ι → ℂ := fun x => (F x:ℂ)
  let Gc : PeriodicTorus ι → ℂ := fun x => (G x:ℂ)
  let Tc := Fc ⋆[ContinuousLinearMap.mul ℂ ℂ,periodicHaar ι] Gc
  have hB : 0 ≤ B := (norm_nonneg (F 0)).trans (hb 0)
  have hFcAES : AEStronglyMeasurable Fc (periodicHaar ι) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hF
  have hFcB : ∀ x,‖Fc x‖ ≤ B := fun x => by simpa only [Fc,Complex.norm_real,Real.norm_eq_abs] using hb x
  have hFc2 : MemLp Fc 2 (periodicHaar ι) := by
    apply (memLp_const (B:ℂ)).of_le hFcAES
    exact Eventually.of_forall fun x => by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB] using hFcB x
  have hGcI : Integrable Gc (periodicHaar ι) := hG.ofReal
  have hTc2 : MemLp Tc 2 (periodicHaar ι) := periodic_bounded_convolution_memLp hFcAES B hFcB hGcI
  let fL := hFc2.toLp Fc
  let tL := hTc2.toLp Tc
  have hfcoe : (fL : PeriodicTorus ι → ℂ) =ᵐ[periodicHaar ι] Fc := hFc2.coeFn_toLp
  have htcoe : (tL : PeriodicTorus ι → ℂ) =ᵐ[periodicHaar ι] Tc := hTc2.coeFn_toLp
  have hmult (k : PeriodicFrequency ι) : UnitAddTorus.mFourierCoeff Tc k =
      UnitAddTorus.mFourierCoeff Fc k*(a k:ℂ) := by
    rw [periodic_mFourierCoeff_convolution (hFc2.integrable (by norm_num)) hGcI,hcoeff]
  have hp := UnitAddTorus.hasSum_prod_mFourierCoeff fL tL
  have he (k : PeriodicFrequency ι) :
      (conj (UnitAddTorus.mFourierCoeff fL k)*UnitAddTorus.mFourierCoeff tL k).re =
        a k*((UnitAddTorus.mFourierCoeff Fc k).re^2+(UnitAddTorus.mFourierCoeff Fc k).im^2) := by
    rw [periodic_mFourierCoeff_congr hfcoe,periodic_mFourierCoeff_congr htcoe,hmult]
    simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_add]
    ring
  have hs := (RCLike.hasSum_re ℂ hp).congr_fun (fun k => (he k).symm)
  have hreal (x : PeriodicTorus ι) : Tc x = ((∫ y,F y*G (x-y) ∂periodicHaar ι : ℝ):ℂ) := by
    change (∫ y,Fc y*Gc (x-y) ∂periodicHaar ι) = _
    calc
      _ = ∫ y,((F y*G (x-y):ℝ):ℂ) ∂periodicHaar ι := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by simp only [Fc,Gc,Complex.ofReal_mul]
      _ = _ := (@RCLike.ofRealLI ℂ _).integral_comp_comm (fun y => F y*G (x-y))
  have hconj : MemLp (fun x => conj (fL x)) 2 (periodicHaar ι) :=
    (memLp_congr_ae (Lp.coeFn_star fL)).mp (Lp.memLp (star fL))
  have hi : Integrable (fun x => conj (fL x)*tL x) (periodicHaar ι) :=
    hconj.integrable_mul (Lp.memLp tL)
  have hi' : Integrable (fun x => conj (Fc x)*Tc x) (periodicHaar ι) :=
    hi.congr (by filter_upwards [hfcoe,htcoe] with x hx hy; rw [hx,hy])
  have hj : RCLike.re (∫ x,conj (fL x)*tL x ∂periodicHaar ι) =
      ∫ x,F x*(∫ y,F y*G (x-y) ∂periodicHaar ι) ∂periodicHaar ι := by
    rw [integral_congr_ae (by filter_upwards [hfcoe,htcoe] with x hx hy; rw [hx,hy]),←integral_re hi']
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change RCLike.re (conj (Fc x)*Tc x) = F x*(∫ y,F y*G (x-y) ∂periodicHaar ι)
      rw [hreal]; simp [Fc]
  convert hs using 1
  exact hj.symm

lemma periodic_bounded_fourier_form_nonneg (G F : PeriodicTorus ι → ℝ)
    (hG : Integrable G (periodicHaar ι)) (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x,‖F x‖ ≤ B) (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k,0 ≤ a k)
    (hcoeff : ∀ k,UnitAddTorus.mFourierCoeff (fun x => (G x:ℂ)) k = (a k:ℂ)) :
    0 ≤ ∫ x,F x*(∫ y,F y*G (x-y) ∂periodicHaar ι) ∂periodicHaar ι := by
  have hs := periodic_bounded_fourier_form_hasSum G F hG hF B hb a hcoeff
  rw [←hs.tsum_eq]
  exact tsum_nonneg fun k => mul_nonneg (ha k) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Actual original periodic logarithmic Fourier kernel is positive on all
bounded measurable real tests; no positivity conclusion is supplied. -/
lemma periodicLog_bounded_form_nonneg (F : PeriodicTorus ι → ℝ)
    (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x,‖F x‖ ≤ B) :
    0 ≤ ∫ x,F x*(∫ y,F y*periodicLogKernel (x-y) ∂periodicHaar ι) ∂periodicHaar ι := by
  let a : PeriodicFrequency ι → ℝ := fun k =>
    if k=0 then 0 else periodicLogConstant ι/(2*Real.pi)^(Fintype.card ι)*
      ‖periodicFrequencyVector k‖⁻¹^(Fintype.card ι)
  apply periodic_bounded_fourier_form_nonneg periodicLogKernel F
    periodicLogKernel_integrable hF B hb a
  · intro k
    dsimp [a]
    split_ifs
    · exact le_rfl
    · have hC := periodicLogConstant_pos (ι := ι)
      positivity
  · intro k
    rw [periodicLogKernel_fourierCoeff]
    simp only [a,periodicLogFourierCoeff]
    split_ifs <;> simp

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_bounded_fourier_form_hasSum
#print axioms DGRHS.Periodic.periodic_bounded_fourier_form_nonneg
#print axioms DGRHS.Periodic.periodicLog_bounded_form_nonneg
#check @DGRHS.Periodic.periodic_bounded_fourier_form_hasSum
#check @DGRHS.Periodic.periodicLog_bounded_form_nonneg
