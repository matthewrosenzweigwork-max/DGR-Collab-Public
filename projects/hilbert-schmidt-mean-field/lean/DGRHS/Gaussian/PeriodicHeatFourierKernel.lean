import DGRHS.Gaussian.PeriodicHeatFourierCoefficients

/-! The actual continuous Fourier representative at positive heat time,
identified with the Mellin representative used for the partition limit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ComplexConjugate
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatFourierKernel (τ : ℝ) (x : PeriodicTorus ι) : ℝ :=
  (∑' k : PeriodicFrequency ι,(periodicHeatCoefficient τ k:ℂ)*UnitAddTorus.mFourier k x).re

lemma periodicHeatFourierSeries_summable (τ : ℝ) (hτ : 0<τ) (x : PeriodicTorus ι) :
    Summable (fun k : PeriodicFrequency ι => (periodicHeatCoefficient τ k:ℂ)*UnitAddTorus.mFourier k x) := by
  apply Summable.of_norm
  simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (periodicHeatCoefficient_nonneg τ _),
    periodic_mFourier_norm_apply,mul_one] using periodicHeatCoefficient_summable (ι := ι) τ hτ

lemma periodicHeatFourierKernel_coe (τ : ℝ) (x : PeriodicTorus ι) :
    (periodicHeatFourierKernel τ x:ℂ)=
      ∑' k : PeriodicFrequency ι,(periodicHeatCoefficient τ k:ℂ)*UnitAddTorus.mFourier k x := by
  apply RCLike.conj_eq_iff_re.mp
  rw [Complex.conj_tsum]
  simp only [map_mul,Complex.conj_ofReal,← UnitAddTorus.mFourier_neg]
  have he := (Equiv.neg (PeriodicFrequency ι)).tsum_eq
    (fun k : PeriodicFrequency ι => (periodicHeatCoefficient τ k:ℂ)*UnitAddTorus.mFourier k x)
  simpa only [Equiv.neg_apply,periodicHeatCoefficient_neg] using he

lemma periodicHeatFourierKernel_continuous (τ : ℝ) (hτ : 0<τ) :
    Continuous (periodicHeatFourierKernel (ι := ι) τ) := by
  apply Complex.continuous_re.comp
  apply periodicFourierSeries_continuous
  simpa only [Complex.norm_real,Real.norm_of_nonneg (periodicHeatCoefficient_nonneg τ _)] using
    periodicHeatCoefficient_summable (ι := ι) τ hτ

lemma periodicHeatFourierKernel_integrable (τ : ℝ) (hτ : 0<τ) :
    Integrable (periodicHeatFourierKernel (ι := ι) τ) (periodicHaar ι) :=
  (periodicHeatFourierKernel_continuous τ hτ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma periodicHeatFourierKernel_fourierCoeff (τ : ℝ) (hτ : 0<τ) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicHeatFourierKernel τ x:ℂ)) k=(periodicHeatCoefficient τ k:ℂ) := by
  simp only [periodicHeatFourierKernel_coe]
  apply periodicFourierSeries_coefficient
  simpa only [Complex.norm_real,Real.norm_of_nonneg (periodicHeatCoefficient_nonneg τ _)] using
    periodicHeatCoefficient_summable (ι := ι) τ hτ

/-- The continuous covariance representative is the same actual regularization. -/
theorem periodicHeatFourierKernel_eq_mellin_ae (hd : 2≤Fintype.card ι) (τ : ℝ) (hτ : 0<τ) :
    periodicHeatFourierKernel (ι := ι) τ=ᵐ[periodicHaar ι]periodicHeatRegularizedGreen τ := by
  have h := periodicL1_fourier_unique (fun x : PeriodicTorus ι => (periodicHeatFourierKernel τ x:ℂ))
    (fun x => (periodicHeatRegularizedGreen τ x:ℂ)) (periodicHeatFourierKernel_integrable τ hτ).ofReal
    (periodicHeatRegularizedGreen_integrable hd τ hτ.le).ofReal (fun k => by
      rw [periodicHeatFourierKernel_fourierCoeff τ hτ,periodicHeatRegularizedGreen_fourierCoeff hd τ hτ.le,
        periodicHeatCoefficient_coe])
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

lemma periodicHeatFourierKernel_zero (τ : ℝ) (hτ : 0<τ) :
    periodicHeatFourierKernel (ι := ι) τ 0=∑' k : PeriodicFrequency ι,periodicHeatCoefficient τ k := by
  unfold periodicHeatFourierKernel
  have he (k : PeriodicFrequency ι) : UnitAddTorus.mFourier k (0 : PeriodicTorus ι)=1 := by
    simp [UnitAddTorus.mFourier,fourier_apply]
  simp only [he,mul_one]
  rw [Complex.re_tsum]
  · simp only [Complex.ofReal_re]
  · apply Summable.of_norm
    simpa only [Complex.norm_real,Real.norm_of_nonneg (periodicHeatCoefficient_nonneg τ _)] using
      periodicHeatCoefficient_summable (ι := ι) τ hτ

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatFourierKernel_continuous
#print axioms DGRHS.Periodic.periodicHeatFourierKernel_eq_mellin_ae
#print axioms DGRHS.Periodic.periodicHeatFourierKernel_zero
