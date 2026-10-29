/- Original logarithmic source tail supplies the unbounded feature-rate
moment through the actual diagonal estimate. No upper bound on attractive
potential or desired weighted moment is assumed. -/
import DGRHS.Gaussian.FeatureRateDiagonalMoment
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X} [IsProbabilityMeasure μ]

lemma featureRateMoment_of_source_diagonal (β A : ℝ) (hβ : 0<β)
    (k : X→H) (hk : StronglyMeasurable k) (F : X→ℝ)
    (hdiag : ∀ᵐ x ∂μ,‖k x‖^2≤A+2*F x)
    (htail : Integrable (fun x=>Real.exp (4*β*F x)) μ) :
    Integrable (featureExponentialMomentWeight β k) μ ∧
      (∫ x,featureExponentialMomentWeight β k x ∂μ)≤
        featureDiagonalMomentConstant β*Real.exp (2*β*A)*
          (∫ x,Real.exp (4*β*F x) ∂μ) := by
  have he (x : X) (hx : ‖k x‖^2≤A+2*F x) :
      Real.exp (2*β*‖k x‖^2)≤Real.exp (2*β*A)*Real.exp (4*β*F x) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hx (show 0≤2*β by positivity)]
  have hi : Integrable (fun x=>Real.exp (2*β*‖k x‖^2)) μ :=
    (htail.const_mul (Real.exp (2*β*A))).mono'
      (Real.continuous_exp.comp_stronglyMeasurable
        ((hk.norm.pow 2).const_mul (2*β))).aestronglyMeasurable
      (hdiag.mono fun x hx=>by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)];exact he x hx)
  obtain ⟨hw,hb⟩ := integrable_featureRateWeight_of_diagonal_exponential β (2*β) hβ
    (by linarith) k hk hi
  have hupper : (∫ x,Real.exp (2*β*‖k x‖^2) ∂μ)≤
      Real.exp (2*β*A)*(∫ x,Real.exp (4*β*F x) ∂μ) := by
    calc
      _ ≤ ∫ x,Real.exp (2*β*A)*Real.exp (4*β*F x) ∂μ :=
        integral_mono_ae hi (htail.const_mul _) (hdiag.mono he)
      _ = _ := integral_const_mul _ _
  refine ⟨hw,hb.trans ?_⟩
  have hc : 0≤featureDiagonalMomentConstant β := by unfold featureDiagonalMomentConstant;positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hupper hc
end DGRHS.Gaussian
#check @DGRHS.Gaussian.featureRateMoment_of_source_diagonal
#print axioms DGRHS.Gaussian.featureRateMoment_of_source_diagonal
