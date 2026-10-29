/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ElevenEuclideanFourier
import DGRHS.Gaussian.D11Imported.ElevenPeriodizedMass
import DGRHS.Gaussian.D11Imported.PeriodizationCharacter
import DGRHS.Gaussian.D11Imported.PeriodizationComplexIntegral

/-! Fourier coefficients of the actual periodized competitor, obtained by
unfolding the lattice sum on the normalized Haar fundamental cube. -/
noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven
set_option backward.isDefEq.respectTransparency false

lemma profile_character_integrable (k : Frequency 11) :
    Integrable (fun x : Fin 11 → ℝ => liftedCharacter k x * (euclideanProfile x:ℂ)) := by
  apply euclideanProfile_integrable.norm.mono'
    ((liftedCharacter_measurable k).mul
      (Complex.measurable_ofReal.comp euclideanProfile_continuous.measurable)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖liftedCharacter k x * (euclideanProfile x:ℂ)‖ ≤ ‖euclideanProfile x‖
    rw [norm_mul, liftedCharacter_norm, one_mul, Complex.norm_real])

lemma periodizedProfile_fourier_unfold (k : Frequency 11) :
    fourierCoeff periodizedProfile k =
      ∫ x : Fin 11 → ℝ, liftedCharacter k x * (euclideanProfile x:ℂ) := by
  have hm := PeriodizationCube.quotient_measurePreserving 11
  have hme : Measurable (fun x : Torus 11 => UnitAddTorus.mFourier (-k) x * (periodizedProfile x:ℂ)) :=
    (UnitAddTorus.mFourier (-k)).continuous.measurable.mul
      (Complex.measurable_ofReal.comp periodizedProfile_measurable)
  have h := integral_map (μ := volume.restrict (PeriodizationCube.cube 11))
    hm.measurable.aemeasurable hme.aestronglyMeasurable
  rw [hm.map_eq] at h
  change fourierCoeff periodizedProfile k = _ at h
  rw [h]
  calc
    _ = ∫ x in PeriodizationCube.cube 11, ∑' n : Frequency 11,
        liftedCharacter k (fun i => x i+(n i:ℝ)) *
          (euclideanProfile (fun i => x i+(n i:ℝ)):ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (PeriodizationCube.cube_measurable 11)] with x hx
      rw [periodizedProfile_on_cube hx, Complex.ofReal_tsum, ← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [liftedCharacter_periodic]
      rfl
    _ = _ := PeriodizationCube.unfold_integral_complex 11 _
      ((liftedCharacter_measurable k).mul
        (Complex.measurable_ofReal.comp euclideanProfile_continuous.measurable))
      (profile_character_integrable k)

lemma periodizedProfile_fourier (k : Frequency 11) :
    fourierCoeff periodizedProfile k = (fourierProfile (2*Real.pi*frequencyLength k/5):ℂ) := by
  rw [periodizedProfile_fourier_unfold]
  have h := (PiLp.volume_preserving_toLp (Fin 11)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin 11) =>
      StudentIntegral.phase (WithLp.toLp 2 (fun i => (k i:ℝ))) x *
        (euclideanProfile (fun i => x i):ℂ))
  have he : (∫ x : Fin 11 → ℝ, liftedCharacter k x * (euclideanProfile x:ℂ)) =
      ∫ x : EuclideanSpace ℝ (Fin 11),
        StudentIntegral.phase (WithLp.toLp 2 (fun i => (k i:ℝ))) x *
          (euclideanProfile (fun i => x i):ℂ) := by
    rw [← h]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [liftedCharacter_eq_phase])
  rw [he, euclideanProfile_fourier]
  congr 2
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

lemma periodizedProfile_fourier_pos (k : Frequency 11) :
    0 < (fourierCoeff periodizedProfile k).re := by
  rw [periodizedProfile_fourier, Complex.ofReal_re]
  have hk : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  unfold fourierProfile fourierPolynomial
  positivity

#print axioms periodizedProfile_fourier
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
