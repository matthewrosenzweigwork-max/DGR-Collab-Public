import DGRHS.Gaussian.PeriodicPhysicalGreenPowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Genuine one-point Green exponential integrability up to the sharp power
threshold gamma<d, using the actual fundamental-cube Haar formula and native
finite-dimensional local integrability of norm^(-gamma). -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local instance periodicExpCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def periodicFundamentalCube (ι : Type u) [Fintype ι] : Set (ι → ℝ) :=
  {x | ∀ i,x i∈Ioc (-1/2:ℝ) (-1/2+1)}

lemma periodicFundamentalCube_measurable : MeasurableSet (periodicFundamentalCube ι) :=
  MeasurableSet.univ_pi' (fun i => measurableSet_Ioc)

lemma periodicFundamentalCube_abs {x : ι → ℝ} (hx : x∈periodicFundamentalCube ι) :
    ∀ i,|x i|≤1/2 := by
  intro i
  have h := hx i
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

lemma periodicFundamentalCube_ball : periodicFundamentalCube ι ⊆ ball 0 1 := by
  intro x hx
  rw [mem_ball_zero_iff]
  have h : ‖x‖≤1/2 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
    (fun i => by simpa only [Real.norm_eq_abs] using periodicFundamentalCube_abs hx i)
  linarith

lemma periodicPhysicalGreen_exp_chart_measurable (γ : ℝ) :
    Measurable (fun x : ι → ℝ => Real.exp (γ*periodicPhysicalGreen (fun i => (x i:UnitAddCircle)))) := by
  apply Real.continuous_exp.measurable.comp
  apply measurable_const.mul
  apply periodicPhysicalGreen_measurable.comp
  exact Measurable.of_eval (fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i))

lemma periodicPhysicalGreen_exp_chart_integrable (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ)) :
    IntegrableOn (fun x : ι → ℝ => Real.exp (γ*periodicPhysicalGreen (fun i => (x i:UnitAddCircle))))
      (periodicFundamentalCube ι) := by
  let f := fun x : ι → ℝ => Real.exp (γ*periodicPhysicalGreen (fun i => (x i:UnitAddCircle)))
  let F := (periodicFundamentalCube ι).indicator f
  have hd : Module.finrank ℝ (ι → ℝ)=Fintype.card ι := by simp
  have hm : Measurable F := (periodicPhysicalGreen_exp_chart_measurable γ).indicator periodicFundamentalCube_measurable
  have hb : IntegrableOn F (ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by rw [hd]; exact Fintype.card_pos) (α := γ)
      (C := Real.exp (γ*periodicPhysicalGreenUpperConstant ι)) (by simpa only [hd] using hγd)
      _ hm.aestronglyMeasurable
    have haez : ∀ᵐ x : ι → ℝ ∂volume,x≠0 := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_of_ae haez] with x hx0
    by_cases hx : x∈periodicFundamentalCube ι
    · rw [show F x=f x from indicator_of_mem hx f,show ‖f x‖=f x from Real.norm_of_nonneg (Real.exp_pos _).le]
      exact periodicPhysicalGreen_exp_cube_bound γ hγ0 x (periodicFundamentalCube_abs hx) hx0
    · rw [show F x=0 from indicator_of_notMem hx f,norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
  apply (hb.mono_set periodicFundamentalCube_ball).congr_fun _ periodicFundamentalCube_measurable
  intro x hx
  exact indicator_of_mem hx f

/-- The actual physical Green exponential is Haar-integrable for gamma<d. -/
theorem periodicPhysicalGreen_exp_integrable (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ)) :
    Integrable (fun x : PeriodicTorus ι => Real.exp (γ*periodicPhysicalGreen x)) (periodicHaar ι) := by
  refine ⟨(Real.continuous_exp.measurable.comp (measurable_const.mul periodicPhysicalGreen_measurable)).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => (Real.exp_pos _).le))).mpr
  have he := UnitAddTorus.lintegral_preimage
    (fun x : PeriodicTorus ι => ENNReal.ofReal (Real.exp (γ*periodicPhysicalGreen x))) (fun _ => (-1/2:ℝ))
  change (∫⁻ x,ENNReal.ofReal (Real.exp (γ*periodicPhysicalGreen x)) ∂periodicHaar ι)=_ at he
  rw [he]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => (Real.exp_pos _).le))).mp
    (periodicPhysicalGreen_exp_chart_integrable γ hγ0 hγd).hasFiniteIntegral

/-- Actual source kernel integrability, obtained through proved physical identification. -/
theorem periodicLogKernel_exp_integrable (γ : ℝ) (hγ0 : 0≤γ) (hγd : γ<(Fintype.card ι:ℝ)) :
    Integrable (fun x : PeriodicTorus ι => Real.exp (γ*periodicLogKernel x)) (periodicHaar ι) :=
  (periodicPhysicalGreen_exp_integrable γ hγ0 hγd).congr
    (periodicPhysicalGreen_eq_kernel_ae.fun_comp (fun r : ℝ => Real.exp (γ*r)))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicPhysicalGreen_exp_chart_integrable
#print axioms DGRHS.Periodic.periodicPhysicalGreen_exp_integrable
#print axioms DGRHS.Periodic.periodicLogKernel_exp_integrable
#check @DGRHS.Periodic.periodicLogKernel_exp_integrable
