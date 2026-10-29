import DGRHS.Gaussian.PeriodicCosineTrial
import DGRHS.Concentration.EntropyBasic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodic_trial_entropy_pointwise (y : ℝ) (hy : |y| ≤ 1/2) :
    |(1+y)*Real.log (1+y)-y-y^2/2| ≤ 4*|y|^3 := by
  have hy1 : |-y| < 1 := by simpa only [abs_neg] using hy.trans_lt (by norm_num : (1/2:ℝ)<1)
  have hr := Real.abs_log_sub_add_sum_range_le hy1 2
  have hr' : |Real.log (1+y)-y+y^2/2| ≤ |y|^3/(1-|y|) := by
    norm_num [Finset.sum_range_succ] at hr
    simpa [sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hr
  have hd : 0 < 1-|y| := by linarith
  have hb : |Real.log (1+y)-y+y^2/2| ≤ 2*|y|^3 :=
    hr'.trans ((div_le_iff₀ hd).mpr (by nlinarith [pow_nonneg (abs_nonneg y) 3]))
  have hab : |1+y| ≤ 3/2 := by
    have h := abs_le.mp hy
    apply abs_le.mpr
    constructor <;> linarith
  have hp : 0 ≤ |y|^3 := pow_nonneg (abs_nonneg y) _
  calc
    |(1+y)*Real.log (1+y)-y-y^2/2| =
        |(1+y)*(Real.log (1+y)-y+y^2/2)-y^3/2| := by congr 1; ring
    _ ≤ |(1+y)*(Real.log (1+y)-y+y^2/2)|+|y^3/2| := abs_sub _ _
    _ = |1+y| * |Real.log (1+y)-y+y^2/2|+|y|^3/2 := by rw [abs_mul,abs_div,abs_pow]; norm_num
    _ ≤ (3/2)*(2*|y|^3)+|y|^3/2 := by gcongr
    _ ≤ 4*|y|^3 := by nlinarith

lemma periodicCosineTrial_positiveBounded (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    DGRHS.Concentration.PositiveBounded (periodicHaar ι) (periodicCosineTrialDensity i ε) (1/2) (3/2) := by
  refine ⟨?_,by norm_num,by norm_num,Filter.Eventually.of_forall (periodicCosineTrialDensity_bounds i ε hε)⟩
  have hm : Continuous (periodicCosineTrialDensity i ε) := by
    unfold periodicCosineTrialDensity
    exact continuous_const.add (continuous_const.mul (periodicCoordinateCos_continuous i))
  exact hm.aestronglyMeasurable

/-- Exact leading entropy coefficient from the actual Haar cosine trial,
with a concrete cubic remainder sufficient for strict supercriticality. -/
lemma periodicCosineTrial_entropy_bound (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    (∫ x,periodicCosineTrialDensity i ε x * Real.log (periodicCosineTrialDensity i ε x) ∂periodicHaar ι)
      ≤ ε^2/4+4*|ε|^3 := by
  have hf := periodicCosineTrial_positiveBounded i ε hε
  have hLp : MemLp (periodicCoordinateCos i) 2 (periodicHaar ι) :=
    (memLp_const (1:ℝ)).of_le (periodicCoordinateCos_continuous i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_one] using periodicCoordinateCos_abs_le_one i x)
  have hsq : Integrable (fun x => periodicCoordinateCos i x^2) (periodicHaar ι) := by
    simpa only [pow_two,Pi.mul_def] using hLp.integrable_mul hLp
  have hlin := (periodicCoordinateCos_integrable i).const_mul ε
  have hquad := hsq.const_mul (ε^2/2)
  have hp : Integrable (fun x => ε*periodicCoordinateCos i x+(ε^2/2)*periodicCoordinateCos i x^2) (periodicHaar ι) := hlin.add hquad
  have hc := integrable_const (4*|ε|^3) (μ := periodicHaar ι)
  have hb : (∫ x,periodicCosineTrialDensity i ε x * Real.log (periodicCosineTrialDensity i ε x) ∂periodicHaar ι)
      ≤ ∫ x,ε*periodicCoordinateCos i x+(ε^2/2)*periodicCoordinateCos i x^2+4*|ε|^3 ∂periodicHaar ι := by
    apply integral_mono hf.mul_log_integrable (hp.add hc)
    intro x
    have hy : |ε*periodicCoordinateCos i x| ≤ |ε| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (periodicCoordinateCos_abs_le_one i x) (abs_nonneg ε)
    have ht := (abs_le.mp (periodic_trial_entropy_pointwise (ε*periodicCoordinateCos i x) (hy.trans hε))).2
    have ht' : |ε*periodicCoordinateCos i x|^3 ≤ |ε|^3 := pow_le_pow_left₀ (abs_nonneg _) hy 3
    change (1+ε*periodicCoordinateCos i x)*Real.log (1+ε*periodicCoordinateCos i x) ≤
      ε*periodicCoordinateCos i x+(ε^2/2)*periodicCoordinateCos i x^2+4*|ε|^3
    nlinarith
  rw [integral_add hp hc,integral_add hlin hquad,integral_const_mul,integral_const_mul,
    periodicCoordinateCos_mean_zero,periodicCoordinateCos_second_moment,integral_const] at hb
  simp only [probReal_univ,one_smul,mul_zero,zero_add] at hb
  convert hb using 1 <;> ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCosineTrial_entropy_bound
#check @DGRHS.Periodic.periodicCosineTrial_entropy_bound
