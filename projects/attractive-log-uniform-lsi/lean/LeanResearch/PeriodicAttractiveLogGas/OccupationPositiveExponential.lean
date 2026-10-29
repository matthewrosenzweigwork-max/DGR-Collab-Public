import LeanResearch.PeriodicAttractiveLogGas.GreenGradientMoments
import LeanResearch.PeriodicAttractiveLogGas.CoordinateConditionalKernels

/-! The positive-field exponential estimate in the proof of the source
occupation-rates proposition. The singular one-site moment is established
before repeated conditioning under the original, fixed specified-label law.
The development record distinguishes checked boundaries from pending work. -/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.OccupationPositiveExponential

open MeshCells MeshAdjacentCells LabelOccupations OneCoordinateConditionals
  ConditionalLawEstimates GreenConditionalInfluence GreenGradientMoments
  GreenPointWeights CellRestrictions

/-- The positive part of the manuscript's totalized Green representative. -/
def positiveGreen (z : Torus) : ℝ := max (greenRealRepresentative z) 0

/-- The exact envelope appearing in the source one-site Holder estimate. -/
def positiveEnvelope (z : Torus) : ℝ :=
  positiveGreen z * Real.exp (positiveGreen z / 4)

theorem positiveGreen_nonneg (z : Torus) : 0 ≤ positiveGreen z := le_max_right _ _

theorem positiveGreen_measurable : Measurable positiveGreen :=
  greenRealRepresentative_measurable.max measurable_const

theorem positiveEnvelope_nonneg (z : Torus) : 0 ≤ positiveEnvelope z :=
  mul_nonneg (positiveGreen_nonneg z) (Real.exp_pos _).le

theorem positiveEnvelope_measurable : Measurable positiveEnvelope :=
  positiveGreen_measurable.mul (positiveGreen_measurable.div_const 4).exp

theorem positive_envelope_scalar_bound (t : ℝ) :
    t * Real.exp (t / 4) ≤ 4 * Real.exp (t / 2) := by
  have h := Real.add_one_le_exp (t / 4)
  have ht' : t ≤ 4 * Real.exp (t / 4) := by linarith
  calc
    _ ≤ 4 * Real.exp (t / 4) * Real.exp (t / 4) :=
      mul_le_mul_of_nonneg_right ht' (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem regular_positive_exp_half_bound {z : Torus} (hz : z ≠ 0) :
    Real.exp (max (regularGreenRepresentative z) 0 / 2) ≤
      Real.exp (kernelConstant / 2) * torusEuclideanNorm z ^ (- (1 / 2 : ℝ)) := by
  have hr : 0 < torusEuclideanNorm z :=
    lt_of_le_of_ne (torusEuclideanNorm_nonneg z)
      (fun h ↦ hz ((torusEuclideanNorm_eq_zero_iff z).mp h.symm))
  have hl : Real.log (torusEuclideanNorm z) ≤ 0 :=
    Real.log_nonpos hr.le (torusEuclideanNorm_le_one z)
  have hg : regularGreenRepresentative z ≤
      kernelConstant - Real.log (torusEuclideanNorm z) := by
    have hu := (le_abs_self
      (regularGreenRepresentative z + Real.log (torusEuclideanNorm z))).trans
        (kernel_log_bound z hz)
    linarith
  have hm : max (regularGreenRepresentative z) 0 ≤
      kernelConstant - Real.log (torusEuclideanNorm z) :=
    max_le hg (by linarith [kernelConstant_pos])
  calc
    _ ≤ Real.exp ((kernelConstant - Real.log (torusEuclideanNorm z)) / 2) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hm (by norm_num))
    _ = _ := by
      rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
      congr 1
      ring

/-- A slightly stronger power majorant proves finiteness of the exact
source envelope. Only the Haar-null representative discrepancy and pole
are discarded. -/
theorem positiveEnvelope_power_ae_bound :
    ∀ᵐ z ∂torusMeasure, ‖positiveEnvelope z‖ ^ (4 / 3 : ℝ) ≤
      (4 * Real.exp (kernelConstant / 2)) ^ (4 / 3 : ℝ) *
        torusEuclideanNorm z ^ (- (2 / 3 : ℝ)) := by
  filter_upwards [torusMeasure.ae_ne (0 : Torus), regularGreenRepresentative_ae]
    with z hz he
  have hp : positiveGreen z = max (regularGreenRepresentative z) 0 := by
    simp only [positiveGreen, he]
  have hb : positiveEnvelope z ≤
      (4 * Real.exp (kernelConstant / 2)) *
        torusEuclideanNorm z ^ (- (1 / 2 : ℝ)) := by
    calc
      _ ≤ 4 * Real.exp (positiveGreen z / 2) :=
        positive_envelope_scalar_bound (positiveGreen z)
      _ ≤ 4 * (Real.exp (kernelConstant / 2) *
          torusEuclideanNorm z ^ (- (1 / 2 : ℝ))) := by
        rw [hp]
        exact mul_le_mul_of_nonneg_left (regular_positive_exp_half_bound hz) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ((4 * Real.exp (kernelConstant / 2)) *
        torusEuclideanNorm z ^ (- (1 / 2 : ℝ))) ^ (4 / 3 : ℝ) := by
      rw [Real.norm_of_nonneg (positiveEnvelope_nonneg z)]
      exact Real.rpow_le_rpow (positiveEnvelope_nonneg z) hb (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (torusEuclideanNorm_nonneg z) _),
        ← Real.rpow_mul (torusEuclideanNorm_nonneg z)]
      norm_num

theorem positiveEnvelope_power_integrable :
    Integrable (fun z ↦ ‖positiveEnvelope z‖ ^ (4 / 3 : ℝ)) torusMeasure := by
  have hi := (integrable_torusEuclideanNorm_rpow_neg (2 / 3 : ℝ) (by norm_num)).const_mul
    ((4 * Real.exp (kernelConstant / 2)) ^ (4 / 3 : ℝ))
  apply hi.mono' (positiveEnvelope_measurable.norm.pow_const _).aestronglyMeasurable
  filter_upwards [positiveEnvelope_power_ae_bound] with z hz
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hz

theorem positiveEnvelope_memLp : MemLp positiveEnvelope conjugateExponent torusMeasure := by
  apply (integrable_norm_rpow_iff positiveEnvelope_measurable.aestronglyMeasurable
    (by norm_num [conjugateExponent]) (by simp [conjugateExponent])).mp
  simpa only [conjugateExponent, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    using positiveEnvelope_power_integrable

/-- One fixed-resolution constant, independent of particle number, labels,
pole, and inverse temperature. The exact source envelope defines it. -/
def envelopeBound (J : ℕ) : ℝ :=
  ((J : ℝ) ^ 2 * ∫ z, ‖positiveEnvelope z‖ ^ (4 / 3 : ℝ) ∂torusMeasure) ^ (3 / 4 : ℝ)

theorem envelopeBound_nonneg (J : ℕ) : 0 ≤ envelopeBound J :=
  Real.rpow_nonneg (mul_nonneg (sq_nonneg _)
    (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)) _

theorem cell_positiveEnvelope_moment {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (z : Torus) :
    MemLp (fun y ↦ positiveEnvelope (z - y)) conjugateExponent (meshCellMeasure J hJ a) ∧
      lpNorm (fun y ↦ positiveEnvelope (z - y)) conjugateExponent (meshCellMeasure J hJ a) ≤
        envelopeBound J := by
  have hmp := torusMeasure.measurePreserving_sub_left z
  have hm : MemLp (fun y ↦ positiveEnvelope (z - y)) conjugateExponent torusMeasure :=
    positiveEnvelope_memLp.comp_measurePreserving hmp
  have hi : Integrable (fun y ↦ ‖positiveEnvelope (z - y)‖ ^ (4 / 3 : ℝ)) torusMeasure :=
    hmp.integrable_comp_of_integrable positiveEnvelope_power_integrable
  have hmcell : MemLp (fun y ↦ positiveEnvelope (z - y)) conjugateExponent
      (meshCellMeasure J hJ a) := by
    rw [meshCellMeasure]
    exact (hm.restrict _).smul_measure (by simp)
  refine ⟨hmcell, ?_⟩
  rw [conjugateExponent, DensityMoments.lpNorm_ofReal_eq
    (by norm_num : (0 : ℝ) < 4 / 3) hmcell.aestronglyMeasurable]
  have hb : (∫ y, ‖positiveEnvelope (z - y)‖ ^ (4 / 3 : ℝ)
      ∂meshCellMeasure J hJ a) ≤
      (J : ℝ) ^ 2 * ∫ y, ‖positiveEnvelope y‖ ^ (4 / 3 : ℝ) ∂torusMeasure := by
    rw [meshCellMeasure, integral_smul_measure]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul]
    have hr := integral_mono_measure (Measure.restrict_le_self :
      torusMeasure.restrict (meshCell J hJ a) ≤ torusMeasure)
        (Eventually.of_forall fun y ↦ Real.rpow_nonneg (norm_nonneg _) (4 / 3 : ℝ)) hi
    have he : (∫ y, ‖positiveEnvelope (z - y)‖ ^ (4 / 3 : ℝ) ∂torusMeasure) =
        ∫ y, ‖positiveEnvelope y‖ ^ (4 / 3 : ℝ) ∂torusMeasure := by
      have hmmap : AEStronglyMeasurable (fun y ↦ ‖positiveEnvelope y‖ ^ (4 / 3 : ℝ))
          (Measure.map (fun y ↦ z - y) torusMeasure) := by
        rw [hmp.map_eq]
        exact positiveEnvelope_power_integrable.aestronglyMeasurable
      have he' := integral_map hmp.aemeasurable hmmap
      rw [hmp.map_eq] at he'
      exact he'.symm
    exact mul_le_mul_of_nonneg_left (hr.trans_eq he) (sq_nonneg _)
  unfold envelopeBound
  convert Real.rpow_le_rpow
    (integral_nonneg (μ := meshCellMeasure J hJ a) fun y : Torus ↦
      Real.rpow_nonneg (norm_nonneg (positiveEnvelope (z - y))) (4 / 3 : ℝ)) hb
    (by norm_num : (0 : ℝ) ≤ 3 / 4) using 1
  norm_num

/-- The source elementary exponential inequality, followed by the exact
envelope at coefficient one quarter. -/
theorem exp_le_one_add_envelope {u a : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 1 / 4)
    (ha : 0 ≤ a) :
    Real.exp (u * a) ≤ 1 + u * (a * Real.exp (a / 4)) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(u * a)))
    (Real.exp_pos (u * a)).le
  have he : Real.exp (u * a) * Real.exp (-(u * a)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [he] at h
  have hsmall : u * a ≤ a / 4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsmall) (mul_nonneg hu ha)
  nlinarith

section Density

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

/-- Real Holder transfer with integrability proved before the integral
comparison. No moment of the density-weighted law is an input. -/
theorem density_envelope_bound {p f : A → ℝ} {K B : ℝ}
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp4 : MemLp p 4 μ)
    (hK : lpNorm p 4 μ ≤ K) (hf0 : ∀ x, 0 ≤ f x)
    (hf4 : MemLp f conjugateExponent μ) (hB : lpNorm f conjugateExponent μ ≤ B) :
    Integrable f (μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) ∧
      (∫ x, f x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) ≤ K * B := by
  have hi : Integrable f (μ.withDensity (fun x ↦ ENNReal.ofReal (p x))) := by
    rw [integrable_nonnegative_density_iff hp hp0]
    simpa only [smul_eq_mul] using integrable_four_mul_conjugate hp4 hf4
  refine ⟨hi, ?_⟩
  rw [DensityMoments.integral_density rfl hp (Eventually.of_forall hp0)]
  have hh := integral_norm_mul_le hp4 hf4
  simp only [abs_of_nonneg (hp0 _), abs_of_nonneg (hf0 _)] at hh
  exact hh.trans (mul_le_mul hK hB lpNorm_nonneg (lpNorm_nonneg.trans hK))

end Density

/-- The actual one-site kernel inherits the exact envelope bound from its
proved L4 density estimate; the representative change is only AE. -/
theorem conditional_envelope_bound {n J : ℕ} (hJ : 0 < J) {β₀ β : ℝ}
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J)
    (hb : LawBounds hJ β₀ β i Y a .cell) (z : Torus) :
    Integrable (fun y ↦ positiveEnvelope (z - y))
      (conditionalKernel (meshCellMeasure J hJ a) i β Y) ∧
      (∫ y, positiveEnvelope (z - y)
        ∂conditionalKernel (meshCellMeasure J hJ a) i β Y) ≤
          densityNormBound β₀ * envelopeBound J := by
  let w : Fin n → ℝ := fun _ ↦ β / (n + 1 : ℕ)
  let p := pointDensity (meshCellMeasure J hJ a) Y w
  have hden := pointDensity_ae_rawDensity hJ (mesh_two_le hmesh) a .cell β Y
  change p =ᵐ[meshCellMeasure J hJ a] rawDensity (meshCellMeasure J hJ a) β Y at hden
  have hp4 : MemLp p 4 (meshCellMeasure J hJ a) :=
    (memLp_congr_ae hden).mpr hb.density_memLp
  have hpB : lpNorm p 4 (meshCellMeasure J hJ a) ≤ densityNormBound β₀ := by
    change (eLpNorm p 4 (meshCellMeasure J hJ a)).toReal ≤ _
    rw [eLpNorm_congr_ae hden]
    exact hb.density_norm
  have hp0 (y : Torus) : 0 ≤ p y :=
    div_nonneg (torusWeight_pos Y w y).le hb.regular_normalizer_pos.le
  have hf := cell_positiveEnvelope_moment hJ a z
  have hh := density_envelope_bound (measurable_pointDensity _ Y w) hp0 hp4 hpB
    (fun y ↦ positiveEnvelope_nonneg (z - y)) hf.1 hf.2
  change Integrable _ (pointLaw (meshCellMeasure J hJ a) Y w) ∧
    (∫ y, positiveEnvelope (z - y) ∂pointLaw (meshCellMeasure J hJ a) Y w) ≤ _ at hh
  have hk : conditionalKernel (meshCellMeasure J hJ a) i β Y =
      pointLaw (meshCellMeasure J hJ a) Y w := by
    simpa only [patchMeasure] using! hb.kernel_eq_pointLaw
  rw [hk]
  exact hh

/-- The single-factor source inequality for every admitted fixed outside
placement, including coincident source positions. -/
theorem conditional_exponential_bound {n J : ℕ} (hJ : 0 < J) {β₀ β u : ℝ}
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J)
    (hb : LawBounds hJ β₀ β i Y a .cell) (z : Torus)
    (hu : 0 ≤ u) (hu4 : u ≤ 1 / 4) :
    Integrable (fun y ↦ Real.exp (u * positiveGreen (z - y)))
      (conditionalKernel (meshCellMeasure J hJ a) i β Y) ∧
      (∫ y, Real.exp (u * positiveGreen (z - y))
        ∂conditionalKernel (meshCellMeasure J hJ a) i β Y) ≤
          1 + u * (densityNormBound β₀ * envelopeBound J) := by
  let ν := conditionalKernel (meshCellMeasure J hJ a) i β Y
  let : IsProbabilityMeasure ν := hb.probability
  obtain ⟨hEi, hEb⟩ := conditional_envelope_bound hJ hmesh i Y a hb z
  change Integrable (fun y ↦ positiveEnvelope (z - y)) ν at hEi
  change (∫ y, positiveEnvelope (z - y) ∂ν) ≤ densityNormBound β₀ * envelopeBound J at hEb
  have hmaj : Integrable (fun y ↦ 1 + u * positiveEnvelope (z - y)) ν := by
    simpa only [Pi.add_apply] using! (integrable_const (1 : ℝ)).add (hEi.const_mul u)
  have hpoint (y : Torus) : Real.exp (u * positiveGreen (z - y)) ≤
      1 + u * positiveEnvelope (z - y) :=
    exp_le_one_add_envelope hu hu4 (positiveGreen_nonneg (z - y))
  have hm : Measurable (fun y ↦ Real.exp (u * positiveGreen (z - y))) :=
    ((positiveGreen_measurable.comp (measurable_const.sub measurable_id)).const_mul u).exp
  have hi : Integrable (fun y ↦ Real.exp (u * positiveGreen (z - y))) ν := by
    apply hmaj.mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun y ↦ by
      simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hpoint y
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y, 1 + u * positiveEnvelope (z - y) ∂ν :=
      integral_mono_ae hi hmaj (Eventually.of_forall hpoint)
    _ = 1 + u * ∫ y, positiveEnvelope (z - y) ∂ν := by
      rw [integral_add (integrable_const _) (hEi.const_mul u), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hEb hu)

theorem capped_conditional_exponential_bound {n J : ℕ} (hJ : 0 < J)
    {β₀ β δ u : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (z : Torus) (hu : 0 ≤ u) (hu4 : u ≤ 1 / 4) :
    Integrable (fun y ↦ Real.exp (u * positiveGreen (z - y)))
      (conditionalKernel (meshCellMeasure J hJ a) i β Y) ∧
      (∫ y, Real.exp (u * positiveGreen (z - y))
        ∂conditionalKernel (meshCellMeasure J hJ a) i β Y) ≤
          1 + u * (densityNormBound β₀ * envelopeBound J) :=
  conditional_exponential_bound hJ hmesh i Y a
    (capped_patch_law hJ hβ hβ₀ hδ hmesh η hη i Y hY a .cell) z hu hu4

section FixedJointLaw

variable {N : ℕ}

/-- Repeated conditioning of nonnegative factors, always under the same
joint probability law. No product integrability is assumed. The conclusion
is extended-valued, so it also establishes finiteness when the bound is finite. -/
theorem lintegral_product_le
    (κ : Fin N → Kernel (Configuration N) Torus) [∀ i, IsMarkovKernel (κ i)]
    (μ : Measure (Configuration N)) [IsProbabilityMeasure μ]
    (hstat : ConditionalKernelL2.PreservesLaw κ μ)
    (f : Fin N → Torus → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (C : ℝ≥0∞)
    (hC : ∀ i, ∀ᵐ X ∂μ, (∫⁻ y, f i y ∂κ i X) ≤ C)
    (A : Finset (Fin N)) :
    (∫⁻ X, ∏ j ∈ A, f j (X j) ∂μ) ≤ C ^ A.card := by
  classical
  have hm (S : Finset (Fin N)) : Measurable (fun X : Configuration N ↦ ∏ j ∈ S, f j (X j)) :=
    Finset.measurable_prod S (fun j _ ↦ (hf j).comp (measurable_pi_apply j))
  induction A using Finset.induction with
  | empty => simp
  | insert i A hi ih =>
    have he (X : Configuration N) (y : Torus) :
        (∏ j ∈ insert i A, f j ((Function.update X i y) j)) =
          f i y * ∏ j ∈ A, f j (X j) := by
      rw [Finset.prod_insert hi, Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hi hj
      rw [Function.update_of_ne hji]
    calc
      _ = ∫⁻ X, ∫⁻ y, ∏ j ∈ insert i A, f j ((Function.update X i y) j)
          ∂κ i X ∂μ := (CoordinateConditionalKernels.lintegral_resample κ μ hstat i
            (hm (insert i A))).symm
      _ = ∫⁻ X, (∫⁻ y, f i y ∂κ i X) * ∏ j ∈ A, f j (X j) ∂μ := by
        simp_rw [he]
        apply lintegral_congr
        intro X
        exact lintegral_mul_const _ (hf i)
      _ ≤ ∫⁻ X, C * ∏ j ∈ A, f j (X j) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hC i] with X hX
        exact mul_le_mul hX le_rfl zero_le zero_le
      _ = C * ∫⁻ X, ∏ j ∈ A, f j (X j) ∂μ := lintegral_const_mul C (hm A)
      _ ≤ C * C ^ A.card := mul_le_mul le_rfl ih zero_le zero_le
      _ = C ^ (insert i A).card := by rw [Finset.card_insert_of_notMem hi, pow_succ]; ac_rfl

end FixedJointLaw

/-- The extended product estimate for the original specified-label Gibbs
law. Its actual outside marginal supplies admissible placements almost
everywhere. Every kernel still has the original denominator n+1. -/
theorem label_positive_product_lintegral {n J : ℕ} (hJ : 0 < J)
    (hN : 2 ≤ n + 1) {β₀ β δ u : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (z : Torus) (hu : 0 ≤ u) (hu4 : u ≤ 1 / 4) (A : Finset (Fin (n + 1))) :
    (∫⁻ X, ∏ j ∈ A, ENNReal.ofReal (Real.exp (u * positiveGreen (z - X j)))
      ∂labelGibbsMeasure hJ η β) ≤
        ENNReal.ofReal (1 + u * (densityNormBound β₀ * envelopeBound J)) ^ A.card := by
  classical
  let μ := labelGibbsMeasure hJ η β
  let : IsProbabilityMeasure μ := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ
    (hβ₀.trans_lt hsub)
  let q : Fin (n + 1) → Kernel (Configuration n) Torus :=
    fun i ↦ conditionalKernel (meshCellMeasure J hJ (η i)) i β
  let κ := CoordinateConditionalKernels.finLift q
  have hstat : ConditionalKernelL2.PreservesLaw κ μ := by
    apply CoordinateConditionalKernels.preservesLaw_finLift q μ
    intro i F hF
    exact lintegral_label_conditionals hJ (mesh_two_le hmesh) hN η i hβ
      (hβ₀.trans_lt hsub) hF
  have hout (i : Fin (n + 1)) : ∀ᵐ Y ∂Measure.map (removeSite i) μ,
      PrescribedOutside hJ η i Y := by
    change ∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β),
      PrescribedOutside hJ η i Y
    rw [labelGibbsMeasure_eq_cond hJ hN η hβ (hβ₀.trans_lt hsub)]
    exact ae_cond_patchOutside hJ (mesh_two_le hmesh) hN η (fun _ ↦ .cell) i
      hβ (hβ₀.trans_lt hsub)
  have hfm : Measurable (fun y ↦ ENNReal.ofReal (Real.exp (u * positiveGreen (z - y)))) :=
    (((positiveGreen_measurable.comp (measurable_const.sub measurable_id)).const_mul u).exp).ennreal_ofReal
  have hcond (i : Fin (n + 1)) : ∀ᵐ X ∂μ,
      (∫⁻ y, ENNReal.ofReal (Real.exp (u * positiveGreen (z - y))) ∂κ i X) ≤
        ENNReal.ofReal (1 + u * (densityNormBound β₀ * envelopeBound J)) := by
    have hx := ae_of_ae_map (measurable_removeSite i).aemeasurable (hout i)
    filter_upwards [hx] with X hX
    have hh := capped_conditional_exponential_bound hJ hβ hβ₀ hδ hmesh η hη i
      (removeSite i X) hX (η i) z hu hu4
    change (∫⁻ y, ENNReal.ofReal (Real.exp (u * positiveGreen (z - y)))
      ∂conditionalKernel (meshCellMeasure J hJ (η i)) i β (removeSite i X)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hh.1
      (Eventually.of_forall fun y ↦ (Real.exp_pos (u * positiveGreen (z - y))).le)]
    exact ENNReal.ofReal_le_ofReal hh.2
  exact lintegral_product_le κ μ hstat
    (fun _ y ↦ ENNReal.ofReal (Real.exp (u * positiveGreen (z - y))))
    (fun _ ↦ hfm) _ hcond A

/-- Finiteness of the preceding extended integral is used before the
ordinary exponential integral is formed. -/
theorem label_positive_sum_moment {n J : ℕ} (hJ : 0 < J)
    (hN : 2 ≤ n + 1) {β₀ β δ u : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (z : Torus) (hu : 0 ≤ u) (hu4 : u ≤ 1 / 4) (A : Finset (Fin (n + 1))) :
    Integrable (fun X ↦ Real.exp (u * ∑ j ∈ A, positiveGreen (z - X j)))
      (labelGibbsMeasure hJ η β) ∧
      (∫ X, Real.exp (u * ∑ j ∈ A, positiveGreen (z - X j))
        ∂labelGibbsMeasure hJ η β) ≤
          (1 + u * (densityNormBound β₀ * envelopeBound J)) ^ A.card := by
  have hm : Measurable (fun X : Configuration (n + 1) ↦
      Real.exp (u * ∑ j ∈ A, positiveGreen (z - X j))) :=
    ((Finset.measurable_sum A fun j _ ↦ positiveGreen_measurable.comp
      (measurable_const.sub (measurable_pi_apply j))).const_mul u).exp
  have hC : 0 ≤ 1 + u * (densityNormBound β₀ * envelopeBound J) := by
    have hK := (densityNormBound_pos β₀).le
    have hB := envelopeBound_nonneg J
    positivity
  have he (X : Configuration (n + 1)) :
      ENNReal.ofReal (Real.exp (u * ∑ j ∈ A, positiveGreen (z - X j))) =
        ∏ j ∈ A, ENNReal.ofReal (Real.exp (u * positiveGreen (z - X j))) := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg fun j _ ↦ (Real.exp_pos _).le
  have hl : (∫⁻ X, ENNReal.ofReal (Real.exp (u * ∑ j ∈ A, positiveGreen (z - X j)))
      ∂labelGibbsMeasure hJ η β) ≤
        ENNReal.ofReal ((1 + u * (densityNormBound β₀ * envelopeBound J)) ^ A.card) := by
    simp_rw [he]
    rw [ENNReal.ofReal_pow hC]
    exact label_positive_product_lintegral hJ hN hβ hβ₀ hsub hδ hmesh η hη z hu hu4 A
  have hi : Integrable (fun X ↦ Real.exp (u * ∑ j ∈ A, positiveGreen (z - X j)))
      (labelGibbsMeasure hJ η β) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Eventually.of_forall fun X ↦ (Real.exp_pos _).le)).mp
        (hl.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hC A.card)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun X ↦ (Real.exp_pos _).le)]
  exact hl

/-- The random field of the manuscript, with the original particle number
and the distinguished particle omitted. This definition is shared by the
subsequent occupation-field estimates. -/
def psi {N : ℕ} (i : Fin N) (z : Torus) (X : Configuration N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, greenRealRepresentative (z - X j)

theorem psi_measurable {N : ℕ} (i : Fin N) (z : Torus) : Measurable (psi i z) :=
  (Finset.measurable_sum _ fun j _ ↦ greenRealRepresentative_measurable.comp
    (measurable_const.sub (measurable_pi_apply j))).const_mul _

theorem exp_psi_le_positive_sum {N : ℕ} (i : Fin N) (z : Torus) (X : Configuration N)
    {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (s * psi i z X) ≤
      Real.exp ((s / N) * ∑ j : Fin N, positiveGreen (z - X j)) := by
  have hsum : (∑ j ∈ Finset.univ.erase i, greenRealRepresentative (z - X j)) ≤
      ∑ j : Fin N, positiveGreen (z - X j) := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, positiveGreen (z - X j) :=
        Finset.sum_le_sum fun j _ ↦ le_max_left _ _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun j _ _ ↦ positiveGreen_nonneg (z - X j))
  apply Real.exp_le_exp.mpr
  simpa only [psi, div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left hsum (div_nonneg hs (Nat.cast_nonneg N))

theorem power_one_add_div_le_exp {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 0 < N) :
    (1 + C / N) ^ N ≤ Real.exp C := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (Real.exp (C / N)) ^ N := pow_le_pow_left₀ (by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp (C / N)) N
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp

/-- The exact positive-exponential chain in the source. All mesh, cap,
subcritical normalization and one-site hypotheses are discharged, and the
same original Gibbs law appears throughout. The zero-coupling endpoint is
included, and no collision or symmetry restriction is imposed. -/
theorem label_field_exponential_moment {N J : ℕ} (hN : 2 ≤ N)
    {β₀ β δ s : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap δ η)
    (hs : 0 ≤ s) (hNs : 4 * s ≤ N) (i : Fin N) (z : Torus) :
    Integrable (fun X ↦ Real.exp (s * psi i z X)) (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, Real.exp (s * psi i z X) ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
        (1 + s * densityNormBound β₀ * envelopeBound J / N) ^ N ∧
      (1 + s * densityNormBound β₀ * envelopeBound J / N) ^ N ≤
        Real.exp (s * densityNormBound β₀ * envelopeBound J) := by
  cases N with
  | zero => omega
  | succ n =>
    have hNr : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hu : 0 ≤ s / (n + 1 : ℕ) := div_nonneg hs hNr.le
    have hu4 : s / (n + 1 : ℕ) ≤ 1 / 4 := (div_le_iff₀ hNr).mpr (by linarith)
    obtain ⟨hPi, hPb⟩ := label_positive_sum_moment (mesh_pos hmesh) hN
      hβ hβ₀ hsub hδ hmesh η hη z hu hu4 Finset.univ
    have hm : Measurable (fun X ↦ Real.exp (s * psi i z X)) :=
      ((psi_measurable i z).const_mul s).exp
    have hi : Integrable (fun X ↦ Real.exp (s * psi i z X))
        (labelGibbsMeasure (mesh_pos hmesh) η β) := by
      apply hPi.mono' hm.aestronglyMeasurable
      exact Eventually.of_forall fun X ↦ by
        simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using exp_psi_le_positive_sum i z X hs
    have hbase : 1 + (s / (n + 1 : ℕ)) * (densityNormBound β₀ * envelopeBound J) =
        1 + s * densityNormBound β₀ * envelopeBound J / (n + 1 : ℕ) := by ring
    refine ⟨hi, ?_, power_one_add_div_le_exp
      (mul_nonneg (mul_nonneg hs (densityNormBound_pos β₀).le) (envelopeBound_nonneg J))
      (by omega)⟩
    calc
      _ ≤ ∫ X, Real.exp ((s / (n + 1 : ℕ)) * ∑ j : Fin (n + 1), positiveGreen (z - X j))
          ∂labelGibbsMeasure (mesh_pos hmesh) η β :=
        integral_mono_ae hi hPi (Eventually.of_forall fun X ↦ exp_psi_le_positive_sum i z X hs)
      _ ≤ _ := by simpa only [Finset.card_univ, Fintype.card_fin, hbase] using hPb

theorem label_field_exponential_bound {N J : ℕ} (hN : 2 ≤ N)
    {β₀ β δ s : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap δ η)
    (hs : 0 ≤ s) (hNs : 4 * s ≤ N) (i : Fin N) (z : Torus) :
    Integrable (fun X ↦ Real.exp (s * psi i z X)) (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, Real.exp (s * psi i z X) ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤
        Real.exp (s * densityNormBound β₀ * envelopeBound J) := by
  obtain ⟨hi, hp, hb⟩ := label_field_exponential_moment hN hβ hβ₀ hsub hδ hmesh η hη hs hNs i z
  exact ⟨hi, hp.trans hb⟩

end PeriodicAttractiveLogGas.OccupationPositiveExponential
