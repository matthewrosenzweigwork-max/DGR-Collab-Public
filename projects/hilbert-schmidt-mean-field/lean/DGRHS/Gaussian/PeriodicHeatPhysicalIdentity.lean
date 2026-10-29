import DGRHS.Gaussian.PeriodicGaussianHeatFourier

/-! The actual Gaussian heat series is the positive physical lattice sum,
with the exact real square-root normalization. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicCenteredRepresentative (x : PeriodicTorus ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (UnitAddTorus.measurableEquivPiIoc (fun _ : ι => -(1/2:ℝ)) x).val

lemma periodicCenteredRepresentative_bounds (x : PeriodicTorus ι) :
    ∀ i, |periodicCenteredRepresentative x i|≤1/2 := by
  intro i
  have h := (UnitAddTorus.measurableEquivPiIoc (fun _ : ι => -(1/2:ℝ)) x).property i
  change -(1/2:ℝ)<periodicCenteredRepresentative x i ∧
    periodicCenteredRepresentative x i≤-(1/2:ℝ)+1 at h
  exact abs_le.mpr ⟨h.1.le,by linarith [h.2]⟩

lemma periodicCenteredRepresentative_coe (x : PeriodicTorus ι) :
    (fun i => (periodicCenteredRepresentative x i : UnitAddCircle)) = x := by
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : ι => -(1/2:ℝ))).symm_apply_apply x

lemma periodicCenteredRepresentative_measurable :
    Measurable (periodicCenteredRepresentative (ι := ι)) := by
  exact (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp
    (measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (fun _ : ι => -(1/2:ℝ))).measurable)

lemma periodic_complex_half_power (a : ℝ) (ha : 0≤a) :
    (a:ℂ)^(1/2:ℂ) = (Real.sqrt a : ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
    (Complex.ofReal_cpow ha (1/2:ℝ)).symm

lemma periodicGaussianHeat_physical_identity (a : ℝ) (ha : 0<a) (x : EuclideanSpace ℝ ι) :
    ((∑' k : PeriodicFrequency ι,Real.exp (-Real.pi*a*‖x+periodicFrequencyVector k‖^2) : ℝ):ℂ) =
      (((1/Real.sqrt a)^(Fintype.card ι):ℝ):ℂ)*
        periodicGaussianHeat (Real.pi/a) (fun i => (x i : UnitAddCircle)) := by
  have h := periodicMultidimensionalGaussian_poisson a ha x
  rw [periodic_complex_half_power a ha.le] at h
  have hf : (fun k : PeriodicFrequency ι =>
      Complex.exp (-(Real.pi:ℂ)*a*(‖x+periodicFrequencyVector k‖:ℂ)^2)) =
      fun k => (Real.exp (-Real.pi*a*‖x+periodicFrequencyVector k‖^2):ℂ) := by
    funext k
    simp only [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow]
  rw [hf,← Complex.ofReal_tsum] at h
  convert h using 1
  simp only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
  congr 1
  unfold periodicGaussianHeat
  apply tsum_congr
  intro k
  congr 1
  simp only [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div,
    Complex.ofReal_pow,neg_div]

lemma periodicGaussianHeat_physical_formula (a : ℝ) (ha : 0<a) (x : EuclideanSpace ℝ ι) :
    periodicGaussianHeat (Real.pi/a) (fun i => (x i : UnitAddCircle)) =
      ((Real.sqrt a)^(Fintype.card ι)*
        ∑' k : PeriodicFrequency ι,Real.exp (-Real.pi*a*‖x+periodicFrequencyVector k‖^2):ℝ) := by
  have h := periodicGaussianHeat_physical_identity a ha x
  have hs : Real.sqrt a≠0 := (Real.sqrt_pos.mpr ha).ne'
  have hh := congrArg (fun z : ℂ => ((Real.sqrt a : ℝ):ℂ)^(Fintype.card ι)*z) h
  simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,← mul_assoc,
    ← mul_pow,mul_one_div_cancel (Complex.ofReal_ne_zero.mpr hs),one_pow,one_mul,
    Complex.ofReal_mul] using hh.symm

lemma periodicGaussianHeat_real_nonneg (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    0≤(periodicGaussianHeat a x).re ∧ (periodicGaussianHeat a x).im=0 := by
  have hp : 0<Real.pi/a := div_pos Real.pi_pos ha
  have h := periodicGaussianHeat_physical_formula (Real.pi/a) hp (periodicCenteredRepresentative x)
  rw [periodicCenteredRepresentative_coe] at h
  have he : Real.pi/(Real.pi/a)=a := by field_simp
  rw [he] at h
  rw [h]
  simp only [Complex.ofReal_re,Complex.ofReal_im,and_true]
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (tsum_nonneg (fun k => (Real.exp_pos _).le))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCenteredRepresentative_coe
#print axioms DGRHS.Periodic.periodicGaussianHeat_physical_identity
#print axioms DGRHS.Periodic.periodicGaussianHeat_physical_formula
#print axioms DGRHS.Periodic.periodicGaussianHeat_real_nonneg
#check @DGRHS.Periodic.periodicGaussianHeat_physical_formula
