import DGRHS.Gaussian.PeriodicHeatTimeTail

/-! A genuine heat-time envelope. It controls both the spatial L1 mass and
 the negative part of the centered positive heat kernel at every positive time. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatTimeEnvelopeConstant (ι : Type u) [Fintype ι] : ℝ :=
  2*Real.exp (1/2)+periodicHeatTailMass ι

def periodicHeatTimeEnvelope (ι : Type u) [Fintype ι] (s : ℝ) : ℝ :=
  periodicHeatTimeEnvelopeConstant ι*Real.exp (-s/2)

lemma periodicHeatTimeEnvelope_nonneg (s : ℝ) : 0≤periodicHeatTimeEnvelope ι s := by
  unfold periodicHeatTimeEnvelope periodicHeatTimeEnvelopeConstant
  exact mul_nonneg (add_nonneg (by positivity) periodicHeatTailMass_nonneg) (Real.exp_pos _).le

lemma periodicHeatTimeEnvelope_small (s : ℝ) (hs : s≤1) :
    2≤periodicHeatTimeEnvelope ι s := by
  have he : 1≤Real.exp (1/2)*Real.exp (-s/2) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hn := mul_nonneg (periodicHeatTailMass_nonneg (ι := ι)) (Real.exp_pos (-s/2)).le
  unfold periodicHeatTimeEnvelope periodicHeatTimeEnvelopeConstant
  nlinarith

lemma periodicHeatTimeEnvelope_large (s : ℝ) :
    Real.exp (-s/2)*periodicHeatTailMass ι≤periodicHeatTimeEnvelope ι s := by
  unfold periodicHeatTimeEnvelope periodicHeatTimeEnvelopeConstant
  nlinarith [mul_nonneg (by positivity : 0≤2*Real.exp (1/2)) (Real.exp_pos (-s/2)).le]

lemma periodicGaussianHeat_centered_envelope_mass (s : ℝ) (hs : 0<s) :
    (∫ x,‖periodicGaussianHeat s x-1‖ ∂periodicHaar ι)≤periodicHeatTimeEnvelope ι s := by
  by_cases hs1 : s≤1
  · exact (periodicGaussianHeat_centered_mass_bound s hs).trans (periodicHeatTimeEnvelope_small s hs1)
  · have hi := ((periodicGaussianHeat_integrable (ι := ι) s hs).sub (integrable_const 1)).norm
    calc
      _ ≤ ∫ _x : PeriodicTorus ι,Real.exp (-s/2)*periodicHeatTailMass ι ∂periodicHaar ι :=
        integral_mono hi (integrable_const _) (periodicGaussianHeat_centered_time_bound s (le_of_not_ge hs1))
      _ = Real.exp (-s/2)*periodicHeatTailMass ι := by simp
      _ ≤ _ := periodicHeatTimeEnvelope_large s

lemma periodicGaussianHeat_centered_envelope_lower (s : ℝ) (hs : 0<s) (x : PeriodicTorus ι) :
    -periodicHeatTimeEnvelope ι s≤(periodicGaussianHeat s x).re-1 := by
  by_cases hs1 : s≤1
  · have he := periodicHeatTimeEnvelope_small (ι := ι) s hs1
    have hp := (periodicGaussianHeat_real_nonneg s hs x).1
    linarith
  · have hb := (abs_le.mp (periodicGaussianHeat_real_centered_time_bound s (le_of_not_ge hs1) x)).1
    have he := periodicHeatTimeEnvelope_large (ι := ι) s
    linarith

lemma periodicHeatTimeEnvelope_measurable : Measurable (periodicHeatTimeEnvelope ι) := by
  unfold periodicHeatTimeEnvelope
  fun_prop

lemma periodicHeatTimeEnvelope_weight_integrable (p : ℝ) (hp : -1<p) :
    IntegrableOn (fun s : ℝ => s^p*periodicHeatTimeEnvelope ι s) (Ioi 0) := by
  have hi := (periodicHeatTime_rpow_exp_integrable p (1/2) hp (by norm_num)).const_mul
    (periodicHeatTimeEnvelopeConstant ι)
  apply hi.congr
  exact Eventually.of_forall (fun s => by
    dsimp only [periodicHeatTimeEnvelope]
    rw [show -(1/2:ℝ)*s=-s/2 by ring]
    ring)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicGaussianHeat_centered_envelope_mass
#print axioms DGRHS.Periodic.periodicGaussianHeat_centered_envelope_lower
#print axioms DGRHS.Periodic.periodicHeatTimeEnvelope_weight_integrable
