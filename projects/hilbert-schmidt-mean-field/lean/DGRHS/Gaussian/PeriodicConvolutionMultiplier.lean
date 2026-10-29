import DGRHS.Gaussian.PeriodicCosineConvolution
import Mathlib.Analysis.Convolution

/-! Bounded-test convolution multiplier for the actual normalized torus Haar.
Generalizes the read-only licensed local GreenL2Coercivity convolution
multiplier proof to the actual arbitrary finite torus. Attribution and exact
predecessor SHA are in FINITE_COMPRESSION_ROUTE_20261002.md. No local Young
inequality body or old campaign verdict is imported. -/
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Convolution
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local instance periodicMultiplierCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

lemma periodic_mFourierCoeff_convolution {F G : PeriodicTorus ι → ℂ}
    (hF : Integrable F (periodicHaar ι)) (hG : Integrable G (periodicHaar ι))
    (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff
      (F ⋆[ContinuousLinearMap.mul ℂ ℂ,periodicHaar ι] G) k =
      UnitAddTorus.mFourierCoeff F k * UnitAddTorus.mFourierCoeff G k := by
  let χ : PeriodicTorus ι → ℂ := UnitAddTorus.mFourier (-k)
  have hχ : Continuous χ := (UnitAddTorus.mFourier (-k)).continuous
  have hj : Integrable (fun z : PeriodicTorus ι × PeriodicTorus ι => F z.2*G (z.1-z.2))
      ((periodicHaar ι).prod (periodicHaar ι)) :=
    hF.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hG
  have hw : Integrable (fun z : PeriodicTorus ι × PeriodicTorus ι => χ z.1*(F z.2*G (z.1-z.2)))
      ((periodicHaar ι).prod (periodicHaar ι)) :=
    hj.bdd_mul (hχ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun z => (periodic_mFourier_norm_apply (-k) z.1).le)
  have harg (x y : PeriodicTorus ι) : χ x=χ (x-y)*χ y := by
    dsimp only [χ]
    rw [←periodic_mFourier_argument_add,sub_add_cancel]
  rw [periodic_mFourierCoeff_eq_integral]
  change (∫ x,χ x*(∫ y,F y*G (x-y) ∂periodicHaar ι) ∂periodicHaar ι) = _
  calc
    _ = ∫ x,∫ y,χ x*(F y*G (x-y)) ∂periodicHaar ι ∂periodicHaar ι := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (integral_const_mul (χ x) _).symm
    _ = ∫ y,∫ x,χ x*(F y*G (x-y)) ∂periodicHaar ι ∂periodicHaar ι :=
      integral_integral_swap hw
    _ = ∫ y,(χ y*F y)*UnitAddTorus.mFourierCoeff G k ∂periodicHaar ι := by
      apply integral_congr_ae
      filter_upwards [] with y
      calc
        _ = ∫ x,(χ y*F y)*(χ (x-y)*G (x-y)) ∂periodicHaar ι := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp only; rw [harg x y]; ring
        _ = (χ y*F y)*(∫ x,χ (x-y)*G (x-y) ∂periodicHaar ι) := integral_const_mul _ _
        _ = (χ y*F y)*(∫ x,χ x*G x ∂periodicHaar ι) := by
          congr 1
          exact integral_sub_right_eq_self (fun x => χ x*G x) y
        _ = _ := by rw [periodic_mFourierCoeff_eq_integral]
    _ = _ := by rw [integral_mul_const,periodic_mFourierCoeff_eq_integral F k]

/-- Bounded tests give genuine L2 convolution directly; no Young inequality
conclusion or L2 output premise is supplied. -/
lemma periodic_bounded_convolution_memLp {F G : PeriodicTorus ι → ℂ}
    (hF : AEStronglyMeasurable F (periodicHaar ι)) (B : ℝ)
    (hb : ∀ x,‖F x‖ ≤ B) (hG : Integrable G (periodicHaar ι)) :
    MemLp (F ⋆[ContinuousLinearMap.mul ℂ ℂ,periodicHaar ι] G) 2 (periodicHaar ι) := by
  have hB : 0 ≤ B := (norm_nonneg (F 0)).trans (hb 0)
  have hiF : Integrable F (periodicHaar ι) :=
    (integrable_const B).mono' hF (Eventually.of_forall hb)
  have hj : Integrable (fun z : PeriodicTorus ι × PeriodicTorus ι => F z.2*G (z.1-z.2))
      ((periodicHaar ι).prod (periodicHaar ι)) :=
    hiF.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hG
  have hAES : AEStronglyMeasurable
      (F ⋆[ContinuousLinearMap.mul ℂ ℂ,periodicHaar ι] G) (periodicHaar ι) :=
    hj.integral_prod_left.aestronglyMeasurable
  apply (memLp_const (B*(∫ z,‖G z‖ ∂periodicHaar ι))).of_le hAES
  apply Eventually.of_forall
  intro x
  have hp := periodicHaar_preserving_sub_left (ι := ι) x
  have hiG : Integrable (fun y => G (x-y)) (periodicHaar ι) :=
    hp.integrable_comp_of_integrable hG
  have hrow : Integrable (fun y => F y*G (x-y)) (periodicHaar ι) :=
    hiG.bdd_mul hF (Eventually.of_forall hb)
  have hn : (∫ y,‖G (x-y)‖ ∂periodicHaar ι) = ∫ z,‖G z‖ ∂periodicHaar ι :=
    integral_sub_left_eq_self (fun z => ‖G z‖) (periodicHaar ι) x
  have hnonneg : 0 ≤ B*(∫ z,‖G z‖ ∂periodicHaar ι) := mul_nonneg hB (integral_nonneg fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
  change ‖∫ y,F y*G (x-y) ∂periodicHaar ι‖ ≤ _
  calc
    _ ≤ ∫ y,‖F y*G (x-y)‖ ∂periodicHaar ι := norm_integral_le_integral_norm _
    _ ≤ ∫ y,B*‖G (x-y)‖ ∂periodicHaar ι :=
      integral_mono hrow.norm (hiG.norm.const_mul B) (fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul,hn]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_mFourierCoeff_convolution
#print axioms DGRHS.Periodic.periodic_bounded_convolution_memLp

#check @DGRHS.Periodic.periodic_mFourierCoeff_convolution
#check @DGRHS.Periodic.periodic_bounded_convolution_memLp
