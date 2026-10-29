import DGRHS.Gaussian.GaussianLogFrullani
import DGRHS.Gaussian.GaussianLogInfraredScalar

/-! The genuine zero-image heat integral has coefficient-one logarithmic
singularity, with an explicit uniform remainder. The proper scalar integral
identity is reused from the checked Frullani development. -/
noncomputable section
open MeasureTheory Set Filter
namespace DGRHS.Periodic
open DGRHS.Gaussian

def periodicLocalLogCore (r : ℝ) : ℝ :=
  ∫ t : ℝ in Ioc 0 1,t⁻¹*Real.exp (-r^2/(2*t^2))

lemma periodicLocalLogCore_integrable (r : ℝ) (hr : 0<r) :
    IntegrableOn (fun t : ℝ => t⁻¹*Real.exp (-r^2/(2*t^2))) (Ioc 0 1) :=
  integrableOn_gaussianLog_profile_short 1 r (by norm_num) hr

lemma periodicLocalLogCore_split (r : ℝ) (hr : 0<r) :
    periodicLocalLogCore r-gaussianLogCounterterm 1+
      (∫ t : ℝ in Ioi 1,t⁻¹*(Real.exp (-r^2/(2*t^2))-Real.exp (-1/(2*t^2)))) =
      -Real.log r := by
  let D := fun t : ℝ => t⁻¹*(Real.exp (-r^2/(2*t^2))-Real.exp (-1/(2*t^2)))
  have hi := integrableOn_gaussianLog_profile_difference r hr
  have he := integral_add_compl (s := Iic (1:ℝ)) measurableSet_Iic hi
  rw [compl_Iic,Measure.restrict_restrict measurableSet_Iic,Measure.restrict_restrict measurableSet_Ioi] at he
  have hA : Iic (1:ℝ)∩Ioi 0=Ioc 0 1 := by ext t;simp [and_comm]
  have hB : Ioi (1:ℝ)∩Ioi 0=Ioi 1 := by
    ext t
    simp only [mem_inter_iff,mem_Ioi]
    constructor
    · exact And.left
    · intro h;exact ⟨h,lt_trans zero_lt_one h⟩
  rw [hA,hB,integral_gaussianLog_profile_difference r hr] at he
  rw [←he]
  congr 1
  have hx : D=fun t : ℝ => t⁻¹*Real.exp (-r^2/(2*t^2))-t⁻¹*Real.exp (-1/(2*t^2)) := by funext t;dsimp [D];ring
  change periodicLocalLogCore r-gaussianLogCounterterm 1=∫ t in Ioc 0 1,D t
  rw [hx,integral_sub (periodicLocalLogCore_integrable r hr) (integrableOn_gaussianLogCounterterm 1 (by norm_num))]
  rfl

lemma periodicLocalLogCore_tail_bounds (r : ℝ) (hr : 0<r) (hr1 : r≤1) :
    0≤(∫ t : ℝ in Ioi 1,t⁻¹*(Real.exp (-r^2/(2*t^2))-Real.exp (-1/(2*t^2)))) ∧
      (∫ t : ℝ in Ioi 1,t⁻¹*(Real.exp (-r^2/(2*t^2))-Real.exp (-1/(2*t^2))))≤1/4 := by
  let D := fun t : ℝ => t⁻¹*(Real.exp (-r^2/(2*t^2))-Real.exp (-1/(2*t^2)))
  have hd : IntegrableOn D (Ioi 1) := (integrableOn_gaussianLog_profile_difference r hr).mono_set
    (by intro t ht;change 1<t at ht;change 0<t;linarith)
  have hpos : ∀ᵐ t ∂volume.restrict (Ioi (1:ℝ)),0≤D t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0<t := lt_trans zero_lt_one ht
    dsimp only [D]
    apply mul_nonneg (by positivity)
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hb : ∀ᵐ t ∂volume.restrict (Ioi (1:ℝ)),D t≤rieszGaussianScaleWeight (1/2) 2 t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 1<t := ht
    have he : Real.exp (-r^2/(2*t^2))≤1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg r)) (by positivity))
    have hle : D t≤t⁻¹*(1-Real.exp (-1/(2*t^2))) := by
      dsimp [D]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact hle.trans (gaussianLog_profile_deficit_tail_le t ht')
  refine ⟨integral_nonneg_of_ae hpos,?_⟩
  have h := integral_mono_ae hd (integrable_rieszGaussianScaleWeight (1/2) 2 1 (by norm_num) (by norm_num)) hb
  rw [integral_rieszGaussianScaleWeight (1/2) 2 1 (by norm_num) (by norm_num)] at h
  norm_num at h
  exact h

/-- Exact leading coefficient one; the remainder interval is independent of r. -/
theorem periodicLocalLogCore_log_bounds (r : ℝ) (hr : 0<r) (hr1 : r≤1) :
    -Real.log r+gaussianLogCounterterm 1-1/4≤periodicLocalLogCore r ∧
      periodicLocalLogCore r≤-Real.log r+gaussianLogCounterterm 1 := by
  have hs := periodicLocalLogCore_split r hr
  have hb := periodicLocalLogCore_tail_bounds r hr hr1
  constructor <;> linarith [hb.1,hb.2]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLocalLogCore_integrable
#print axioms DGRHS.Periodic.periodicLocalLogCore_split
#print axioms DGRHS.Periodic.periodicLocalLogCore_tail_bounds
#print axioms DGRHS.Periodic.periodicLocalLogCore_log_bounds
#check @DGRHS.Periodic.periodicLocalLogCore_log_bounds
