import DGRHS.Gaussian.PeriodicShortGreenFourier
import DGRHS.Gaussian.PeriodicLongGreenFourier
import DGRHS.Gaussian.PeriodicHeatMellinCoefficient

/-! Actual physical heat Green candidate, proper Haar integrability, exact
source Fourier coefficients, and coefficient-one local logarithmic bounds. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicPhysicalGreen (x : PeriodicTorus ι) : ℝ :=
  periodicShortGreen x+periodicHeatScaleFactor ι*periodicLongHeatRemainder (Real.pi^2) x

lemma periodicPhysicalGreen_measurable : Measurable (periodicPhysicalGreen (ι := ι)) :=
  periodicShortGreen_measurable.add (measurable_const.mul
    (periodicLongHeatRemainder_continuous (Real.pi^2) (by positivity)).measurable)

lemma periodicPhysicalGreen_integrable : Integrable (periodicPhysicalGreen (ι := ι)) (periodicHaar ι) :=
  periodicShortGreen_integrable.add ((periodicLongHeatRemainder_integrable (Real.pi^2) (by positivity)).const_mul _)

lemma periodicHeat_full_scale_split (k : PeriodicFrequency ι) (hk : k≠0) :
    (∫ t : ℝ in Ioc 0 1,t^(Fintype.card ι-1)*Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2)) +
      periodicLongHeatCoefficient (Real.pi^2) k =
    ∫ t : ℝ in Ioi 0,t^(Fintype.card ι-1)*Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2) := by
  have hn := periodicFrequency_norm_pos hk
  have hi : IntegrableOn (fun t : ℝ => t^(Fintype.card ι-1)*
      Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2)) (Ioi 0) := by
    convert periodicHeat_full_scale_integrable (ι := ι) (2*Real.pi^2*‖periodicFrequencyVector k‖^2) (by positivity) using 1
    ext t
    congr 2
    ring
  have he := integral_add_compl (s := Iic (1:ℝ)) measurableSet_Iic hi
  rw [compl_Iic,Measure.restrict_restrict measurableSet_Iic,Measure.restrict_restrict measurableSet_Ioi] at he
  have hA : Iic (1:ℝ)∩Ioi 0=Ioc 0 1 := by ext t;simp [and_comm]
  have hB : Ioi (1:ℝ)∩Ioi 0=Ioi 1 := by
    ext t
    simp only [mem_inter_iff,mem_Ioi]
    constructor
    · exact And.left
    · intro h;exact ⟨h,lt_trans zero_lt_one h⟩
  simpa only [hA,hB,periodicLongHeatCoefficient,if_neg hk] using he

lemma periodic_integrable_character_mul {f : PeriodicTorus ι → ℂ}
    (hf : Integrable f (periodicHaar ι)) (k : PeriodicFrequency ι) :
    Integrable (fun x => UnitAddTorus.mFourier k x*f x) (periodicHaar ι) := by
  apply hf.norm.mono' ((UnitAddTorus.mFourier k).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by simp [periodic_mFourier_norm_apply])

/-- Actual source coefficients, with no coefficient or comparison premise. -/
theorem periodicPhysicalGreen_fourierCoeff (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicPhysicalGreen x:ℂ)) k =
      periodicLogFourierCoeff k := by
  have hs := periodic_integrable_character_mul (periodicShortGreen_integrable (ι := ι)).ofReal (-k)
  have hl := periodic_integrable_character_mul
    ((periodicLongHeatRemainder_integrable (ι := ι) (Real.pi^2) (by positivity)).ofReal.const_mul
      (periodicHeatScaleFactor ι:ℂ)) (-k)
  have hsum : UnitAddTorus.mFourierCoeff (fun x => (periodicPhysicalGreen x:ℂ)) k =
      UnitAddTorus.mFourierCoeff (fun x => (periodicShortGreen x:ℂ)) k+
        (periodicHeatScaleFactor ι:ℂ)*UnitAddTorus.mFourierCoeff
          (fun x => (periodicLongHeatRemainder (Real.pi^2) x:ℂ)) k := by
    simp only [periodic_mFourierCoeff_eq_integral,periodicPhysicalGreen,Complex.ofReal_add,Complex.ofReal_mul,mul_add]
    calc
      _ = (∫ x,UnitAddTorus.mFourier (-k) x*(periodicShortGreen x:ℂ) ∂periodicHaar ι)+
          ∫ x,UnitAddTorus.mFourier (-k) x*((periodicHeatScaleFactor ι:ℂ)*(periodicLongHeatRemainder (Real.pi^2) x:ℂ)) ∂periodicHaar ι := integral_add hs hl
      _ = _ := by
        congr 1
        simp only [mul_left_comm (UnitAddTorus.mFourier (-k) _) (periodicHeatScaleFactor ι:ℂ),integral_const_mul]
  rw [hsum,periodicShortGreen_fourierCoeff,periodicLongHeatRemainder_fourierCoeff _ (by positivity)]
  by_cases hk : k=0
  · subst k
    simp [periodicFrequencyVector_zero,periodicLongHeatCoefficient,periodicLogFourierCoeff]
  · simp only [if_neg hk,sub_zero]
    have he : (∫ t : ℝ in Ioc 0 1,(periodicHeatScaleFactor ι*t^(Fintype.card ι-1):ℝ)*
        (Real.exp (-(2*Real.pi^2*t^2)*‖periodicFrequencyVector k‖^2):ℂ)) =
        (periodicHeatScaleFactor ι:ℂ)*((∫ t : ℝ in Ioc 0 1,t^(Fintype.card ι-1)*
          Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2):ℝ):ℂ) := by
      calc
        _ = ∫ t : ℝ in Ioc 0 1,((periodicHeatScaleFactor ι*(t^(Fintype.card ι-1)*
          Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2)):ℝ):ℂ) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun t => by simp only [Complex.ofReal_mul,mul_assoc,neg_mul])
        _ = ((∫ t : ℝ in Ioc 0 1,periodicHeatScaleFactor ι*(t^(Fintype.card ι-1)*
          Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2)):ℝ):ℂ) :=
            (@RCLike.ofRealLI ℂ _).integral_comp_comm _
        _ = _ := by rw [integral_const_mul,Complex.ofReal_mul]
    rw [he,← mul_add,← Complex.ofReal_add,periodicHeat_full_scale_split k hk,← Complex.ofReal_mul]
    exact periodicHeat_full_coefficient k hk

def periodicLongGreenBound (ι : Type u) [Fintype ι] : ℝ :=
  periodicHeatScaleFactor ι*periodicLongHeatMass ι (Real.pi^2)*
    ∑' k : PeriodicFrequency ι,Real.exp (-(Real.pi^2)*‖periodicFrequencyVector k‖^2)

lemma periodicPhysicalGreen_short_difference_bound (x : PeriodicTorus ι) :
    |periodicPhysicalGreen x-periodicShortGreen x|≤periodicLongGreenBound ι := by
  have hc := (periodicHeatScaleFactor_pos (ι := ι)).le
  have hb := mul_le_mul_of_nonneg_left (periodicLongHeatRemainder_norm_bound (Real.pi^2) (by positivity) x) hc
  simpa only [periodicPhysicalGreen,add_sub_cancel_left,abs_mul,abs_of_nonneg hc,
    Real.norm_eq_abs,mul_assoc,periodicLongGreenBound] using hb

/-- The actual physical candidate has exactly the source logarithmic singularity. -/
theorem periodicPhysicalGreen_log_bounds (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) (hx1 : ‖x‖≤1) :
    -Real.log ‖x‖+DGRHS.Gaussian.gaussianLogCounterterm 1-1/4-periodicShortHeatMean ι-periodicLongGreenBound ι ≤
      periodicPhysicalGreen (fun i => (x i:UnitAddCircle)) ∧
    periodicPhysicalGreen (fun i => (x i:UnitAddCircle)) ≤
      -Real.log ‖x‖+DGRHS.Gaussian.gaussianLogCounterterm 1+periodicImageRemainderBound ι-
        periodicShortHeatMean ι+periodicLongGreenBound ι := by
  have hs := periodicShortGreen_log_bounds x hx hx0 hx1
  have hl := abs_le.mp (periodicPhysicalGreen_short_difference_bound (fun i => (x i:UnitAddCircle)))
  constructor <;> linarith [hs.1,hs.2,hl.1,hl.2]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicPhysicalGreen_integrable
#print axioms DGRHS.Periodic.periodicPhysicalGreen_fourierCoeff
#print axioms DGRHS.Periodic.periodicPhysicalGreen_log_bounds
#check @DGRHS.Periodic.periodicPhysicalGreen_fourierCoeff
