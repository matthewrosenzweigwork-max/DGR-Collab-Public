import DGRHS.Gaussian.PeriodicPositiveMellinBandParticleCap
import DGRHS.Concentration.MasterExponential

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Actual time-band master prerequisites.
The full positive heat is retained before centering. Pointwise symmetry is
derived from the real Fourier Gram identity, whereas positivity and mass in
the upstream band bounds come from Poisson periodization. The proper finite
band never invokes an AE identity on a particle diagonal. This adapts the
checked Euclidean master-band interface; it does not certify the separate
supplied Fourier-cutoff lemmas. No master datum or exponential bound is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicGaussianHeat_real_sub_symmetric (t : ℝ) (ht : 0 < t)
    (x y : PeriodicTorus ι) :
    (periodicGaussianHeat t (x-y)).re = (periodicGaussianHeat t (y-x)).re := by
  have hxy := periodicCenteredHeatCoefficient_gram t ht x y
  have hyx := periodicCenteredHeatCoefficient_gram t ht y x
  rw [real_inner_comm] at hxy
  linarith

lemma periodicRieszPositiveBand_pair_symmetric (s τ δ a : ℝ)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (x y : PeriodicTorus ι) :
    periodicRieszPositiveBand s τ δ a (x-y) =
      periodicRieszPositiveBand s τ δ a (y-x) := by
  unfold periodicRieszPositiveBand periodicPositiveMellinBand
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  unfold periodicPositiveMellinIntegrand
  rw [periodicGaussianHeat_real_sub_symmetric (t+τ)
    (add_pos_of_pos_of_nonneg (hδ.trans_lt ht.1) hτ) x y]

lemma periodicHeatDiagonalSmallConstant_le_global :
    periodicHeatDiagonalSmallConstant ι ≤ periodicHeatDiagonalGlobalConstant ι := by
  have hD := periodicHeatTailMass_nonneg (ι := ι)
  unfold periodicHeatDiagonalGlobalConstant
  have hlast : 0 ≤ periodicHeatTailMass ι * ((Fintype.card ι).factorial : ℝ) *
      (2 : ℝ)^Fintype.card ι := by positivity
  linarith

/-- Common lower-time envelope coefficient, with the source 1/s normalization. -/
def periodicRieszMasterEnvelope (s : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι / (s/2)

lemma periodicRieszMasterEnvelope_nonneg (s : ℝ) (hs : 0 < s) :
    0 ≤ periodicRieszMasterEnvelope s ι := by
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  have hC := periodicHeatDiagonalGlobalConstant_nonneg (ι := ι)
  unfold periodicRieszMasterEnvelope
  positivity

def periodicRieszMasterBand (s τ δ a c : ℝ) (ρ : PeriodicTorus ι → ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  c • hoeffdingCentered (periodicCappedDensityMeasure ρ)
    (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszPositiveBand s τ δ a (q.1-q.2))

lemma measurable_periodicRieszMasterBand (s τ δ a c : ℝ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    Measurable (periodicRieszMasterBand s τ δ a c ρ) :=
  ((stronglyMeasurable_hoeffdingCentered _ _
    ((periodicRieszPositiveBand_measurable s τ δ a).stronglyMeasurable.comp_measurable
      (measurable_fst.sub measurable_snd))).const_smul c).measurable

lemma memLp_infty_periodicRieszMasterBand (s τ δ a c : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    MemLp (periodicRieszMasterBand s τ δ a c ρ) ∞
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  (periodicRieszPositiveBand_centered_memLp_infty s τ δ a hs hτ hδ ha1
    (periodicCappedDensityMeasure ρ)).const_smul c

lemma periodicRieszMasterBand_symmetric (s τ δ a c : ℝ)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (x y : PeriodicTorus ι) :
    periodicRieszMasterBand s τ δ a c ρ (x,y) =
      periodicRieszMasterBand s τ δ a c ρ (y,x) := by
  have h := DGRHS.centeredKernel_symmetric (periodicCappedDensityMeasure ρ)
    (fun x y => periodicRieszPositiveBand s τ δ a (x-y))
    (periodicRieszPositiveBand_pair_symmetric s τ δ a hτ hδ) x y
  exact congrArg (fun z : ℝ => c*z) h

lemma periodicRieszMasterBand_canonical (s τ δ a c : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    ∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      ∫ y, periodicRieszMasterBand s τ δ a c ρ (x,y) ∂periodicCappedDensityMeasure ρ = 0 := by
  have h := DGRHS.integral_centeredKernel_right (periodicCappedDensityMeasure ρ)
    (fun x y => periodicRieszPositiveBand s τ δ a (x-y))
    (periodicRieszPositiveBand_pair_proper s τ δ a hs hτ hδ ha1
      (periodicCappedDensityMeasure ρ)).2.2
  filter_upwards [h] with x hx
  unfold periodicRieszMasterBand
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  change c * (∫ y, DGRHS.centeredKernel (periodicCappedDensityMeasure ρ)
    (fun x y => periodicRieszPositiveBand s τ δ a (x-y)) x y
    ∂periodicCappedDensityMeasure ρ) = 0
  rw [hx, mul_zero]

lemma norm_periodicRieszMasterBand_le (s τ δ a c : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (q : PeriodicTorus ι × PeriodicTorus ι) :
    ‖periodicRieszMasterBand s τ δ a c ρ q‖ ≤
      4*|c| *(periodicRieszMasterEnvelope s ι * δ^(-s/2)) := by
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  have he : periodicRieszMellinFactor ι s * periodicHeatDiagonalSmallConstant ι *
      (δ^(-s/2)/(s/2)) ≤ periodicRieszMasterEnvelope s ι * δ^(-s/2) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (periodicHeatDiagonalSmallConstant_le_global (ι := ι)) hF)
      (by positivity : 0 ≤ δ^(-s/2)/(s/2))
    simpa only [periodicRieszMasterEnvelope, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  exact (periodicRieszPositiveBand_scaled_centered_norm_bound s τ δ a c hs hτ hδ ha1
    (periodicCappedDensityMeasure ρ) q).trans
      (mul_le_mul_of_nonneg_left he (by positivity))

lemma essential_periodicRieszMasterBand_le (s τ δ a c : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    (eLpNormEssSup (periodicRieszMasterBand s τ δ a c ρ)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))).toReal ≤
      4*|c| *(periodicRieszMasterEnvelope s ι * δ^(-s/2)) := by
  have hD := periodicRieszMasterEnvelope_nonneg (ι := ι) s hs
  have hC : 0 ≤ 4*|c| *(periodicRieszMasterEnvelope s ι * δ^(-s/2)) := by positivity
  have h := eLpNormEssSup_le_of_ae_bound
    (μ := (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))
    (Eventually.of_forall (norm_periodicRieszMasterBand_le s τ δ a c hs hτ hδ ha1 ρ))
  simpa only [ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

lemma periodicRieszMasterBand_particle_cap (s τ δ a c : ℝ) (hs : 0 < s)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1) (hc : 0 ≤ c)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (periodicRieszMasterBand s τ δ a c ρ) x ≤
      2*c*(periodicRieszMasterEnvelope s ι * δ^(-s/2)) := by
  unfold periodicRieszMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  convert mul_le_mul_of_nonneg_left
    (periodicRieszPositiveBand_particle_cap s τ δ a hs hτ hδ ha1
      (periodicCappedDensityMeasure ρ) N hN x) hc using 1 <;>
    simp only [periodicRieszMasterEnvelope, div_eq_mul_inv] <;> ring

lemma exists_periodicRieszMaster_scale (s β M : ℝ)
    (hs : 2*s < (Fintype.card ι : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      16*(2*β)^2*periodicRieszBandRowControl s a M ι < 1/glzUniversalTailConstant ∧
      4*|2*β| *Real.sqrt (periodicRieszBandRowControl s a M ι) < 1/glzUniversalTailConstant :=
  exists_periodicRieszBand_small_scale s (2*β) M (1/glzUniversalTailConstant) hs
    (by positivity [glzUniversalTailConstant_pos])

lemma periodicRieszMasterBand_norm_fields (s τ δ a β : ℝ) (hs : 0 < s)
    (hsd : 2*s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (ha : 0 < a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hrow : 16*(2*β)^2*periodicRieszBandRowControl s a M ι ≤ 1/glzUniversalTailConstant)
    (hop : 4*|2*β| *Real.sqrt (periodicRieszBandRowControl s a M ι) ≤ 1/glzUniversalTailConstant) :
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, (periodicRieszMasterBand s τ δ a (2*β) ρ (x,y))^2
        ∂periodicCappedDensityMeasure ρ) ≤ 1/glzUniversalTailConstant) ∧
    ((∫ q, (periodicRieszMasterBand s τ δ a (2*β) ρ q)^2
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤ 1/glzUniversalTailConstant) ∧
    ‖DGRHS.Kernel.integralOperator (periodicRieszMasterBand s τ δ a (2*β) ρ)
      ((memLp_infty_periodicRieszMasterBand s τ δ a (2*β) hs hτ hδ ha1 ρ).mono_exponent
        (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ ≤ 1/glzUniversalTailConstant := by
  obtain ⟨hr,hj⟩ := periodicRieszPositiveBand_scaled_square_controls s τ δ a (2*β)
    hsd hτ hδ.le ha ha1 ρ M hM hρ
  refine ⟨?_, hj.trans hrow, ?_⟩
  · filter_upwards [hr] with x hx
    exact hx.trans hrow
  · exact (periodicRieszPositiveBand_scaled_operator_bound s τ δ a (2*β)
      hsd hτ hδ.le ha ha1 ρ M hM hρ).trans hop

end DGRHS.Periodic
