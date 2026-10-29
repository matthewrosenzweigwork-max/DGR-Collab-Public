import DGRHS.Gaussian.HoeffdingL2
import DGRHS.Kernel.Operator

/-! Product-AE congruence and actual linearity of source Hoeffding centering
and its SAME L2 integral operator. Proper section subtraction is justified. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def hoeffdingCentered (W : X × X → ℝ) (p : X × X) : ℝ :=
  DGRHS.centeredKernel μ (fun x y => W (x,y)) p.1 p.2

lemma stronglyMeasurable_hoeffdingCentered (W : X × X → ℝ) (hWm : StronglyMeasurable W) :
    StronglyMeasurable (hoeffdingCentered μ W) := by
  exact ((hWm.sub (hWm.integral_prod_right'.comp_measurable measurable_fst)).sub
    (hWm.integral_prod_left'.comp_measurable measurable_snd)).add stronglyMeasurable_const

lemma ae_hoeffdingCentered_congr (W V : X × X → ℝ) (he : W =ᵐ[μ.prod μ] V) :
    hoeffdingCentered μ W =ᵐ[μ.prod μ] hoeffdingCentered μ V := by
  have h1 := Measure.ae_ae_eq_curry_of_prod he
  have hswap : (fun p : X × X => W p.swap) =ᵐ[μ.prod μ] (fun p => V p.swap) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae he
  have h2 := Measure.ae_ae_eq_curry_of_prod hswap
  filter_upwards [he,
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae h1,
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae h2] with p hp hp1 hp2
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change (fun y => W (p.1,y)) =ᵐ[μ] (fun y => V (p.1,y)) at hp1
  change (fun x => W (x,p.2)) =ᵐ[μ] (fun x => V (x,p.2)) at hp2
  change W p - (∫ y, W (p.1,y) ∂μ) - (∫ x, W (x,p.2) ∂μ) + (∫ z, W z ∂μ.prod μ) =
    V p - (∫ y, V (p.1,y) ∂μ) - (∫ x, V (x,p.2) ∂μ) + (∫ z, V z ∂μ.prod μ)
  rw [hp, integral_congr_ae hp1, integral_congr_ae hp2, integral_congr_ae he]

lemma ae_hoeffdingCentered_sub (W V : X × X → ℝ)
    (hW : Integrable W (μ.prod μ)) (hV : Integrable V (μ.prod μ)) :
    hoeffdingCentered μ (W - V) =ᵐ[μ.prod μ] hoeffdingCentered μ W - hoeffdingCentered μ V := by
  filter_upwards [
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hW.prod_right_ae,
    (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hV.prod_right_ae,
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hW.prod_left_ae,
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hV.prod_left_ae] with p hWx hVx hWy hVy
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  simp only [Pi.sub_apply]
  rw [integral_sub hWx hVx, integral_sub hWy hVy, integral_sub hW hV]
  ring

lemma gaussian_integralOperator_congr (W V : X × X → ℝ)
    (hW : MemLp W 2 (μ.prod μ)) (hV : MemLp V 2 (μ.prod μ)) (he : W =ᵐ[μ.prod μ] V) :
    DGRHS.Kernel.integralOperator W hW = DGRHS.Kernel.integralOperator V hV := by
  unfold DGRHS.Kernel.integralOperator
  congr 1
  apply Lp.ext
  filter_upwards [hW.coeFn_toLp, hV.coeFn_toLp, he] with p hpW hpV hp
  rw [hpW, hpV, hp]

lemma gaussian_integralOperator_sub (W V : X × X → ℝ)
    (hW : MemLp W 2 (μ.prod μ)) (hV : MemLp V 2 (μ.prod μ)) :
    DGRHS.Kernel.integralOperator (W - V) (hW.sub hV) =
      DGRHS.Kernel.integralOperator W hW - DGRHS.Kernel.integralOperator V hV := by
  unfold DGRHS.Kernel.integralOperator
  rw [MemLp.toLp_sub, map_sub]

end DGRHS.Gaussian

#check DGRHS.Gaussian.hoeffdingCentered
#print axioms DGRHS.Gaussian.hoeffdingCentered
#check DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered
#print axioms DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered
#check DGRHS.Gaussian.ae_hoeffdingCentered_congr
#print axioms DGRHS.Gaussian.ae_hoeffdingCentered_congr
#check DGRHS.Gaussian.ae_hoeffdingCentered_sub
#print axioms DGRHS.Gaussian.ae_hoeffdingCentered_sub
#check DGRHS.Gaussian.gaussian_integralOperator_congr
#print axioms DGRHS.Gaussian.gaussian_integralOperator_congr
#check DGRHS.Gaussian.gaussian_integralOperator_sub
#print axioms DGRHS.Gaussian.gaussian_integralOperator_sub
