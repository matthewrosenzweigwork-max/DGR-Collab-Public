import DGRHS.Gaussian.PeriodicHeatMellinFourier
import DGRHS.Gaussian.PeriodicHeatMellinLimit

/-! The source-normalized genuine heat regularization. Its coefficients
are the exact Green coefficients times the heat multiplier, proved from
proper Mellin integrals, and its zero-time member is the actual Green kernel. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatMellinExponent (ι : Type u) [Fintype ι] : ℝ := (Fintype.card ι:ℝ)/2-1

def periodicHeatMellinFactor (ι : Type u) [Fintype ι] : ℝ :=
  (4*Real.pi)^((Fintype.card ι:ℝ)/2)/(2*(2*Real.pi)^(Fintype.card ι))

def periodicHeatRegularizedGreen (τ : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicHeatMellinFactor ι*periodicMellinHeatGreen (periodicHeatMellinExponent ι) τ x

lemma periodicHeatMellinExponent_nonneg (hd : 2≤Fintype.card ι) : 0≤periodicHeatMellinExponent ι := by
  have h : (2:ℝ)≤Fintype.card ι := by exact_mod_cast hd
  unfold periodicHeatMellinExponent
  linarith

lemma periodicHeatMellinFactor_pos : 0<periodicHeatMellinFactor ι := by
  unfold periodicHeatMellinFactor
  positivity

lemma periodicHeatMellinFactor_coefficient (r : ℝ) (hr : 0<r) :
    periodicHeatMellinFactor ι*((1/r^2)^(periodicHeatMellinExponent ι+1)*
      Real.Gamma (periodicHeatMellinExponent ι+1)) =
    periodicLogConstant ι/(2*Real.pi)^(Fintype.card ι)*(r⁻¹)^(Fintype.card ι) := by
  have he : periodicHeatMellinExponent ι+1=(Fintype.card ι:ℝ)/2 := by
    unfold periodicHeatMellinExponent;ring
  rw [he,periodic_rpow_half_nat _ (by positivity)]
  have hs : Real.sqrt (1/r^2)=r⁻¹ := by
    rw [Real.sqrt_div zero_le_one,Real.sqrt_one,Real.sqrt_sq_eq_abs,abs_of_pos hr,one_div]
  rw [hs]
  unfold periodicHeatMellinFactor periodicLogConstant
  ring

lemma periodicHeatRegularizedGreen_integrable (hd : 2≤Fintype.card ι) (τ : ℝ) (hτ : 0≤τ) :
    Integrable (periodicHeatRegularizedGreen (ι := ι) τ) (periodicHaar ι) :=
  (periodicMellinHeatGreen_integrable _ τ (periodicHeatMellinExponent_nonneg hd) hτ).const_mul _

lemma periodicHeatRegularizedGreen_measurable (τ : ℝ) :
    Measurable (periodicHeatRegularizedGreen (ι := ι) τ) := by
  have hm : Measurable (fun q : PeriodicTorus ι × ℝ =>
      periodicHeatMellinWeight (periodicHeatMellinExponent ι) τ q.2*((periodicGaussianHeat q.2 q.1).re-1)) := by
    exact ((periodicHeatMellinWeight_measurable _ τ).comp measurable_snd).mul
      ((Complex.continuous_re.measurable.comp
        (periodicGaussianHeat_joint_measurable.comp measurable_swap)).sub measurable_const)
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Exact source heat multiplier; physical heat time is τ/(4*pi^2). -/
theorem periodicHeatRegularizedGreen_fourierCoeff (hd : 2≤Fintype.card ι) (τ : ℝ) (hτ : 0≤τ)
    (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicHeatRegularizedGreen τ x:ℂ)) k =
      (Real.exp (-τ*‖periodicFrequencyVector k‖^2):ℂ)*periodicLogFourierCoeff k := by
  have he : UnitAddTorus.mFourierCoeff (fun x => (periodicHeatRegularizedGreen τ x:ℂ)) k =
      (periodicHeatMellinFactor ι:ℂ)*
        UnitAddTorus.mFourierCoeff (fun x => (periodicMellinHeatGreen (periodicHeatMellinExponent ι) τ x:ℂ)) k := by
    simp only [periodic_mFourierCoeff_eq_integral,periodicHeatRegularizedGreen,Complex.ofReal_mul]
    simp only [mul_left_comm (UnitAddTorus.mFourier (-k) _) (periodicHeatMellinFactor ι:ℂ),integral_const_mul]
  rw [he]
  by_cases hk : k=0
  · subst k
    rw [periodicMellinHeatGreen_fourier_zero _ τ (periodicHeatMellinExponent_nonneg hd) hτ]
    simp
  · rw [periodicMellinHeatGreen_fourier_nonzero _ τ (periodicHeatMellinExponent_nonneg hd) hτ k hk,
      periodicLogFourierCoeff,if_neg hk,← Complex.ofReal_mul,← Complex.ofReal_mul]
    congr 1
    rw [show -τ*‖periodicFrequencyVector k‖^2=-(‖periodicFrequencyVector k‖^2*τ) by ring,
      mul_left_comm,periodicHeatMellinFactor_coefficient _ (periodicFrequency_norm_pos hk)]

/-- The actual zero-time representative is the original spectral Green kernel. -/
theorem periodicHeatRegularizedGreen_zero_eq_ae (hd : 2≤Fintype.card ι) :
    periodicHeatRegularizedGreen (ι := ι) 0=ᵐ[periodicHaar ι]periodicLogKernel := by
  have h := periodicL1_fourier_unique (fun x : PeriodicTorus ι => (periodicHeatRegularizedGreen 0 x:ℂ))
    (fun x => (periodicLogKernel x:ℂ)) (periodicHeatRegularizedGreen_integrable hd 0 le_rfl).ofReal
    periodicLogKernel_integrable.ofReal (fun k => by
      rw [periodicHeatRegularizedGreen_fourierCoeff hd 0 le_rfl,periodicLogKernel_fourierCoeff]
      simp)
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatRegularizedGreen_fourierCoeff
#print axioms DGRHS.Periodic.periodicHeatRegularizedGreen_zero_eq_ae
#check @DGRHS.Periodic.periodicHeatRegularizedGreen_fourierCoeff
