import DGRHS.Gaussian.PeriodicLogReality

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Source-normalized positive-Riesz coefficients
and the actual Haar L2 element. Native real-exponent lattice summability is
used at Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (Apache-2.0,
Andrew Yang); the checked logarithmic Fourier-basis construction is adapted.
No L2 kernel or desired Fourier identity is a premise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal lp ComplexConjugate
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma summable_periodicFrequency_rpow (r : ℝ)
    (hr : r < -(Fintype.card ι : ℝ)) :
    Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖ ^ r) := by
  have hdim : Module.finrank ℤ (periodicFrequencyLattice (ι := ι)) = Fintype.card ι := by
    rw [ZLattice.rank ℝ (periodicFrequencyLattice (ι := ι))]
    exact finrank_euclideanSpace
  have hs := ZLattice.summable_norm_rpow (periodicFrequencyLattice (ι := ι)) r
    (by simpa only [hdim] using hr)
  have hp := hs.comp_injective periodicFrequencyLatticePoint_injective
  change Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖ ^ r) at hp
  exact hp

lemma summable_periodicFrequency_riesz_square_power (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Summable (fun k : PeriodicFrequency ι =>
      ‖periodicFrequencyVector k‖ ^ (2 * (s - (Fintype.card ι : ℝ)))) :=
  summable_periodicFrequency_rpow _ (by linarith)

/-- Project heat has multiplier exp(-u|k|²); its time is 4π² times physical
heat time. This is the proposed source prefactor, not a periodization theorem. -/
def periodicRieszMellinFactor (ι : Type u) [Fintype ι] (s : ℝ) : ℝ :=
  Real.pi ^ (s - (Fintype.card ι : ℝ) / 2) / (s * Real.Gamma (s / 2))

def periodicRieszFourierAmplitude (ι : Type u) [Fintype ι] (s : ℝ) : ℝ :=
  periodicRieszMellinFactor ι s * Real.Gamma (((Fintype.card ι : ℝ) - s) / 2)

lemma periodicRieszMellinFactor_pos (s : ℝ) (hs : 0 < s) :
    0 < periodicRieszMellinFactor ι s := by
  exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (mul_pos hs (Real.Gamma_pos_of_pos (by positivity)))

lemma periodicRieszFourierAmplitude_pos (s : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) :
    0 < periodicRieszFourierAmplitude ι s := by
  exact mul_pos (periodicRieszMellinFactor_pos s hs)
    (Real.Gamma_pos_of_pos (by linarith))

def periodicRieszFourierCoeff (s : ℝ) (k : PeriodicFrequency ι) : ℂ :=
  if k = 0 then 0 else
    ((periodicRieszFourierAmplitude ι s *
      ‖periodicFrequencyVector k‖ ^ (s - (Fintype.card ι : ℝ)) : ℝ) : ℂ)

@[simp] lemma periodicRieszFourierCoeff_zero (s : ℝ) :
    periodicRieszFourierCoeff s (0 : PeriodicFrequency ι) = 0 := by
  simp [periodicRieszFourierCoeff]

lemma periodicRieszFourierCoeff_neg (s : ℝ) (k : PeriodicFrequency ι) :
    periodicRieszFourierCoeff s (-k) = periodicRieszFourierCoeff s k := by
  simp [periodicRieszFourierCoeff, periodicFrequencyVector_neg]

@[simp] lemma conj_periodicRieszFourierCoeff (s : ℝ) (k : PeriodicFrequency ι) :
    conj (periodicRieszFourierCoeff s k) = periodicRieszFourierCoeff s k := by
  unfold periodicRieszFourierCoeff
  split_ifs <;> simp only [map_zero, Complex.conj_ofReal]

lemma norm_periodicRieszFourierCoeff_sq (s : ℝ)
    (hsd : s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    ‖periodicRieszFourierCoeff s k‖ ^ 2 =
      (periodicRieszFourierAmplitude ι s) ^ 2 *
        ‖periodicFrequencyVector k‖ ^ (2 * (s - (Fintype.card ι : ℝ))) := by
  by_cases hk : k = 0
  · subst k
    have he : 2 * (s - (Fintype.card ι : ℝ)) ≠ 0 := by linarith
    simp [Real.zero_rpow he]
  · simp only [periodicRieszFourierCoeff, if_neg hk, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, mul_pow]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring

lemma summable_periodicRieszFourierCoeff_sq (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Summable (fun k : PeriodicFrequency ι => ‖periodicRieszFourierCoeff s k‖ ^ 2) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  exact ((summable_periodicFrequency_riesz_square_power s hs).mul_left
    ((periodicRieszFourierAmplitude ι s) ^ 2)).congr
      (fun k => (norm_periodicRieszFourierCoeff_sq s hsd k).symm)

lemma periodicRieszFourierCoeff_memℓp (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) : Memℓp (periodicRieszFourierCoeff (ι := ι) s) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  simpa using summable_periodicRieszFourierCoeff_sq s hs

def periodicRieszCoefficientVector (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    ℓ²(PeriodicFrequency ι, ℂ) :=
  ⟨periodicRieszFourierCoeff s, periodicRieszFourierCoeff_memℓp s hs⟩

def periodicRieszL2 (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Lp ℂ 2 (periodicHaar ι) :=
  (periodicFourierBasis (ι := ι)).repr.symm (periodicRieszCoefficientVector s hs)

lemma periodicRieszL2_fourierCoeff (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (periodicRieszL2 s hs) k = periodicRieszFourierCoeff s k := by
  rw [← periodicFourierBasis_repr]
  simp [periodicRieszL2, periodicRieszCoefficientVector]

lemma periodicRieszL2_unique (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (f : Lp ℂ 2 (periodicHaar ι))
    (hf : ∀ k : PeriodicFrequency ι,
      UnitAddTorus.mFourierCoeff f k = periodicRieszFourierCoeff s k) :
    f = periodicRieszL2 s hs := by
  apply (periodicFourierBasis (ι := ι)).repr.injective
  apply lp.ext
  funext k
  simpa only [periodicFourierBasis_repr, periodicRieszL2_fourierCoeff] using hf k

lemma periodicRieszL2_integrable (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Integrable (periodicRieszL2 s hs : PeriodicTorus ι → ℂ) (periodicHaar ι) :=
  MemLp.integrable (by norm_num) (Lp.memLp _)

lemma periodicRieszL2_integral_zero (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (∫ x, periodicRieszL2 s hs x ∂periodicHaar ι) = 0 := by
  simpa only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul, periodicRieszFourierCoeff_zero] using!
      periodicRieszL2_fourierCoeff s hs (0 : PeriodicFrequency ι)

lemma periodicRieszL2_star (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    star (periodicRieszL2 s hs) = periodicRieszL2 s hs := by
  apply periodicRieszL2_unique
  intro k
  rw [periodic_mFourierCoeff_star, periodicRieszL2_fourierCoeff,
    periodicRieszFourierCoeff_neg, conj_periodicRieszFourierCoeff]

lemma periodicRieszL2_conj_ae (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (fun x => conj (periodicRieszL2 s hs x)) =ᵐ[periodicHaar ι] periodicRieszL2 s hs := by
  have h := Lp.coeFn_star (periodicRieszL2 s hs)
  rw [periodicRieszL2_star] at h
  exact h.symm

lemma periodicRieszL2_reflect (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    periodicReflectL2 (periodicRieszL2 s hs) = periodicRieszL2 s hs := by
  apply periodicRieszL2_unique
  intro k
  rw [periodic_mFourierCoeff_reflectL2, periodicRieszL2_fourierCoeff,
    periodicRieszFourierCoeff_neg]

lemma periodicRieszL2_even_ae (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (fun x => periodicRieszL2 s hs (-x)) =ᵐ[periodicHaar ι] periodicRieszL2 s hs := by
  have h := periodicReflectL2_coeFn (periodicRieszL2 s hs)
  rw [periodicRieszL2_reflect] at h
  exact h.symm

/-- An everywhere even, strongly measurable real representative. -/
def periodicRieszKernel (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (x : PeriodicTorus ι) : ℝ :=
  ((periodicRieszL2 s hs x).re + (periodicRieszL2 s hs (-x)).re) / 2

lemma periodicRieszKernel_measurable (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Measurable (periodicRieszKernel s hs) := by
  have h : Measurable (fun x : PeriodicTorus ι => (periodicRieszL2 s hs x).re) :=
    Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (periodicRieszL2 s hs)).measurable
  exact (h.add (h.comp measurable_neg)).div_const 2

lemma periodicRieszKernel_even (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (x : PeriodicTorus ι) : periodicRieszKernel s hs (-x) = periodicRieszKernel s hs x := by
  simp only [periodicRieszKernel, neg_neg]
  ring

lemma periodicRieszKernel_ae_re (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    periodicRieszKernel s hs =ᵐ[periodicHaar ι] (fun x => (periodicRieszL2 s hs x).re) := by
  filter_upwards [periodicRieszL2_even_ae s hs] with x hx
  simp only [periodicRieszKernel, hx]
  ring

lemma periodicRieszKernel_coe_ae (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (fun x => (periodicRieszKernel s hs x : ℂ)) =ᵐ[periodicHaar ι] periodicRieszL2 s hs := by
  filter_upwards [periodicRieszKernel_ae_re s hs, periodicRieszL2_conj_ae s hs] with x hx hc
  rw [hx]
  exact RCLike.conj_eq_iff_re.mp hc

lemma periodicRieszKernel_memLp (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    MemLp (periodicRieszKernel s hs) 2 (periodicHaar ι) :=
  (memLp_congr_ae (periodicRieszKernel_ae_re s hs)).2 (Lp.memLp (periodicRieszL2 s hs)).re

lemma periodicRieszKernel_stronglyMeasurable (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    StronglyMeasurable (periodicRieszKernel s hs) :=
  (periodicRieszKernel_measurable s hs).stronglyMeasurable

lemma periodicRieszKernel_integrable (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Integrable (periodicRieszKernel s hs) (periodicHaar ι) :=
  (periodicRieszKernel_memLp s hs).integrable (by norm_num)

lemma periodicRieszKernel_integral_zero (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (∫ x, periodicRieszKernel s hs x ∂periodicHaar ι) = 0 := by
  calc
    _ = ∫ x, (periodicRieszL2 s hs x).re ∂periodicHaar ι :=
      integral_congr_ae (periodicRieszKernel_ae_re s hs)
    _ = (∫ x, periodicRieszL2 s hs x ∂periodicHaar ι).re :=
      integral_re (periodicRieszL2_integrable s hs)
    _ = 0 := by rw [periodicRieszL2_integral_zero]; rfl

lemma periodicRieszFourierCoeff_re_pos (s : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) (hk : k ≠ 0) :
    0 < (periodicRieszFourierCoeff s k).re := by
  have hk0 : periodicFrequencyVector k ≠ 0 := by
    intro h
    apply hk
    exact periodicFrequencyVector_injective (by simpa using h)
  simp only [periodicRieszFourierCoeff, if_neg hk, Complex.ofReal_re]
  exact mul_pos (periodicRieszFourierAmplitude_pos s hs hsd)
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hk0) _)

end DGRHS.Periodic
