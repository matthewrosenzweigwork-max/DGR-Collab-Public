import LeanResearch.PeriodicAttractiveLogGas.OccupationPositiveExponential
import LeanResearch.PeriodicAttractiveLogGas.ResidualDoubleCentering
import LeanResearch.PeriodicAttractiveLogGas.DeletedConditionalVariance

/-! Actual marginal densities and square-integrable conditional fields in
the first part of the occupation-rates proof. All outside distributions are
marginals of the original specified-label Gibbs law. The development record
records the current checked boundary and the remaining source obligations. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.OccupationFieldL2

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions
  OneCoordinateConditionals ConditionalLawEstimates GreenConditionalInfluence
  OccupationPositiveExponential CoordinateConditionalKernels

section Mixtures

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  (τ : Measure A) (ρ : Measure B) [IsProbabilityMeasure τ] [IsProbabilityMeasure ρ]
  (p : A → B → ℝ)

/-- An actual average of conditional densities, including their random
normalizers. It is never a density of a smaller Gibbs system. -/
def densityAverage (x : A) : ℝ := ∫ y, p x y ∂ρ

theorem measurable_densityAverage (hp : Measurable (Function.uncurry p)) :
    Measurable (densityAverage ρ p) :=
  hp.stronglyMeasurable.integral_prod_right.measurable

omit [MeasurableSpace A] [IsProbabilityMeasure ρ] in
theorem densityAverage_nonneg (hp0 : ∀ x y, 0 ≤ p x y) (x : A) :
    0 ≤ densityAverage ρ p x := integral_nonneg (hp0 x)

theorem natural_power_eLpNorm {C : Type*} [MeasurableSpace C]
    {ν : Measure C} {f : C → ℝ} (hf : AEStronglyMeasurable f ν)
    {q : ℕ} (hq : q ≠ 0) :
    eLpNorm f (q : ℝ≥0∞) ν ^ q = ∫⁻ x, ‖f x‖ₑ ^ q ∂ν := by
  have hqn : (q : ℝ≥0) ≠ 0 := by exact_mod_cast hq
  simpa only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := ν) hqn hf)

theorem fourth_power_eLpNorm {C : Type*} [MeasurableSpace C]
    {ν : Measure C} {f : C → ℝ} (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 4 ν ^ 4 = ∫⁻ x, ‖f x‖ₑ ^ 4 ∂ν :=
  natural_power_eLpNorm hf (by norm_num)

/-- Jensen and Tonelli preserve the one-site L4 constant under the actual
outside averaging. Joint integrability is a conclusion, before it is used
to identify the density measure. -/
theorem densityAverage_L4 (hp : Measurable (Function.uncurry p))
    {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ y ∂ρ, MemLp (fun x ↦ p x y) 4 τ ∧
      lpNorm (fun x ↦ p x y) 4 τ ≤ K) :
    Integrable (Function.uncurry p) (τ.prod ρ) ∧
      MemLp (densityAverage ρ p) 4 τ ∧ lpNorm (densityAverage ρ p) 4 τ ≤ K := by
  have hmoment : ∀ᵐ y ∂ρ, (∫⁻ x, ‖p x y‖ₑ ^ 4 ∂τ) ≤ ENNReal.ofReal K ^ 4 := by
    filter_upwards [hb] with y hy
    rw [← fourth_power_eLpNorm hy.1.aestronglyMeasurable, ← ofReal_lpNorm hy.1]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hy.2) 4
  have hpair : MemLp (Function.uncurry p) 4 (τ.prod ρ) :=
    CanonicalRowHolder.memLp_of_ae_leftMoment_le τ ρ p 4 (by norm_num) hp
      (by finiteness) hmoment
  have hbar := measurable_densityAverage ρ p hp
  have hb4 : (∫⁻ x, ‖densityAverage ρ p x‖ₑ ^ 4 ∂τ) ≤ ENNReal.ofReal K ^ 4 := by
    calc
      _ ≤ ∫⁻ x, ∫⁻ y, ‖p x y‖ₑ ^ 4 ∂ρ ∂τ :=
        lintegral_mono fun x ↦ ResidualDoubleCentering.enorm_integral_pow_le
          (hp.comp (measurable_const.prodMk measurable_id)) (by norm_num)
      _ = ∫⁻ y, ∫⁻ x, ‖p x y‖ₑ ^ 4 ∂τ ∂ρ :=
        lintegral_lintegral_swap (hp.enorm.pow_const 4).aemeasurable
      _ ≤ ∫⁻ _y : B, ENNReal.ofReal K ^ 4 ∂ρ := lintegral_mono_ae hmoment
      _ = _ := by simp
  have he : eLpNorm (densityAverage ρ p) 4 τ ≤ ENNReal.ofReal K := by
    have hpow : eLpNorm (densityAverage ρ p) 4 τ ^ 4 ≤ ENNReal.ofReal K ^ 4 := by
      rw [fourth_power_eLpNorm hbar.aestronglyMeasurable]
      exact hb4
    have hr := ENNReal.rpow_le_rpow hpow (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat,
      show (4 : ℝ) * (1 / 4) = 1 by norm_num, ENNReal.rpow_one] using hr
  have hm : MemLp (densityAverage ρ p) 4 τ := by
    rw [memLp_iff]
    exact he.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hpair.integrable (by norm_num), hm, ?_⟩
  simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal hK] using
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top he)

/-- The averaged density has the expected measure, proved with Tonelli
after joint integrability has supplied the necessary section integrability. -/
theorem lintegral_densityAverage (hp : Measurable (Function.uncurry p))
    (hp0 : ∀ x y, 0 ≤ p x y) (hi : Integrable (Function.uncurry p) (τ.prod ρ))
    {F : A → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x ∂τ.withDensity (fun x ↦ ENNReal.ofReal (densityAverage ρ p x))) =
      ∫⁻ y, ∫⁻ x, F x ∂τ.withDensity (fun x ↦ ENNReal.ofReal (p x y)) ∂ρ := by
  rw [lintegral_withDensity_eq_lintegral_mul τ
    (measurable_densityAverage ρ p hp).ennreal_ofReal hF]
  calc
    _ = ∫⁻ x, (∫⁻ y, ENNReal.ofReal (p x y) ∂ρ) * F x ∂τ := by
      apply lintegral_congr_ae
      filter_upwards [hi.prod_right_ae] with x hx
      change Integrable (fun y ↦ p x y) ρ at hx
      change ENNReal.ofReal (∫ y, p x y ∂ρ) * F x = _
      rw [ofReal_integral_eq_lintegral_ofReal hx
        (Eventually.of_forall (hp0 x))]
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (p x y) * F x ∂ρ ∂τ := by
      apply lintegral_congr
      intro x
      exact (lintegral_mul_const _
        (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal).symm
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (p x y) * F x ∂τ ∂ρ :=
      lintegral_lintegral_swap
        (hp.ennreal_ofReal.mul (hF.comp measurable_fst)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      exact (lintegral_withDensity_eq_lintegral_mul τ
        (hp.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal hF).symm

end Mixtures

section ActualMarginals

theorem measurable_rawDensity {n : ℕ} (τ : Measure Torus) [SFinite τ] (β : ℝ) :
    Measurable (fun p : Torus × Configuration n ↦ rawDensity τ β p.2 p.1) := by
  have hw : Measurable (fun p : Torus × Configuration n ↦ rawSourceWeight β p.2 p.1) := by
    apply Real.continuous_exp.measurable.comp
    exact Finset.measurable_sum _ fun j _ ↦
      (greenRealRepresentative_measurable.comp
        (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))).const_mul _
  have hn : Measurable (fun Y : Configuration n ↦ ∫ z, rawSourceWeight β Y z ∂τ) :=
    hw.stronglyMeasurable.integral_prod_left.measurable
  exact hw.div (hn.comp measurable_snd)

theorem rawDensity_nonneg {n : ℕ} (τ : Measure Torus) (β : ℝ)
    (Y : Configuration n) (z : Torus) : 0 ≤ rawDensity τ β Y z :=
  div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ ↦ (Real.exp_pos _).le)

/-- The original coordinate marginal, prior to choosing its density. -/
def marginalLaw {N J : ℕ} (hJ : 0 < J) (η : LabelVector J N) (β : ℝ) (i : Fin N) :
    Measure Torus := Measure.map (fun X : Configuration N ↦ X i) (labelGibbsMeasure hJ η β)

/-- Density of the original marginal relative to its own normalized cell
measure. The original N remains in every conditional density. -/
def cellMarginalDensity {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (i : Fin (n + 1)) (z : Torus) : ℝ :=
  densityAverage (Measure.map (removeSite i) (labelGibbsMeasure hJ η β))
    (fun z Y ↦ rawDensity (meshCellMeasure J hJ (η i)) β Y z) z

theorem measurable_cellMarginalDensity {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1))
    [IsFiniteMeasure (labelGibbsMeasure hJ η β)] :
    Measurable (cellMarginalDensity hJ η β i) :=
  (measurable_rawDensity (meshCellMeasure J hJ (η i)) β).stronglyMeasurable.integral_prod_right.measurable

theorem cellMarginalDensity_nonneg {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) (z : Torus) :
    0 ≤ cellMarginalDensity hJ η β i z :=
  integral_nonneg fun Y ↦ rawDensity_nonneg _ β Y z

/-- The true marginal inherits the proved one-site L4 estimate. Its density
identity and its L4 bound are both conclusions. -/
theorem cellMarginalDensity_law_and_L4 {n J : ℕ} (hN : 2 ≤ n + 1)
    {β₀ β δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) (i : Fin (n + 1)) :
    marginalLaw (mesh_pos hmesh) η β i =
      (meshCellMeasure J (mesh_pos hmesh) (η i)).withDensity
        (fun z ↦ ENNReal.ofReal (cellMarginalDensity (mesh_pos hmesh) η β i z)) ∧
      MemLp (cellMarginalDensity (mesh_pos hmesh) η β i) 4
        (meshCellMeasure J (mesh_pos hmesh) (η i)) ∧
      lpNorm (cellMarginalDensity (mesh_pos hmesh) η β i) 4
        (meshCellMeasure J (mesh_pos hmesh) (η i)) ≤ densityNormBound β₀ := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let τ := meshCellMeasure J (mesh_pos hmesh) (η i)
  let ρ := Measure.map (removeSite i) μ
  let p : Torus → Configuration n → ℝ := fun z Y ↦ rawDensity τ β Y z
  let : IsProbabilityMeasure μ := isProbabilityMeasure_labelGibbsMeasure
    (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  let : IsProbabilityMeasure ρ := by
    constructor
    change Measure.map (removeSite i) μ univ = 1
    rw [Measure.map_apply (measurable_removeSite i) MeasurableSet.univ]
    simp
  have hp : Measurable (Function.uncurry p) := measurable_rawDensity τ β
  have hout : ∀ᵐ Y ∂ρ, PrescribedOutside (mesh_pos hmesh) η i Y := by
    change ∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β), _
    rw [labelGibbsMeasure_eq_cond (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)]
    exact ae_cond_patchOutside (mesh_pos hmesh) (mesh_two_le hmesh) hN η
      (fun _ ↦ .cell) i hβ (hβ₀.trans_lt hsub)
  have hb : ∀ᵐ Y ∂ρ, MemLp (fun z ↦ p z Y) 4 τ ∧
      lpNorm (fun z ↦ p z Y) 4 τ ≤ densityNormBound β₀ := by
    filter_upwards [hout] with Y hY
    have h := capped_patch_law (mesh_pos hmesh) hβ hβ₀ hδ hmesh η hη i Y hY (η i) .cell
    exact ⟨h.density_memLp, h.density_norm⟩
  obtain ⟨hi, hm, hn⟩ := densityAverage_L4 τ ρ p hp (densityNormBound_pos β₀).le hb
  refine ⟨?_, hm, hn⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [marginalLaw, lintegral_map hF (measurable_pi_apply i)]
  rw [(label_conditionals hN hβ hβ₀ hsub hδ hmesh η hη i).2
    (fun X ↦ F (X i)) (hF.comp (measurable_pi_apply i))]
  simp only [insertSite_self]
  exact (lintegral_densityAverage τ ρ p hp (fun z Y ↦ rawDensity_nonneg τ β Y z) hi hF).symm

end ActualMarginals

section GreenMoments

/-- The totalized manuscript representative has the same finite Haar
moments as the regular representative, by their proved AE equality. -/
theorem green_memLp (r : ℝ) (hr : 1 ≤ r) :
    MemLp greenRealRepresentative (ENNReal.ofReal r) torusMeasure :=
  (memLp_congr_ae regularGreenRepresentative_ae).mp
    (memLp_regularGreenRepresentative r hr)

/-- An explicit fixed-mesh bound, valid for any specified Haar Lp function.
There is no particle, pole, label or temperature parameter in this constant. -/
def cellMomentBound (J : ℕ) (f : Torus → ℝ) (r : ℝ) : ℝ :=
  ((J : ℝ) ^ 2 * ∫ y, ‖f y‖ ^ r ∂torusMeasure) ^ (1 / r)

theorem cellMomentBound_nonneg (J : ℕ) (f : Torus → ℝ) (r : ℝ) :
    0 ≤ cellMomentBound J f r :=
  Real.rpow_nonneg (mul_nonneg (sq_nonneg _)
    (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)) _

theorem cell_translation_moment {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {f : Torus → ℝ} (hf : Measurable f) {r : ℝ} (hr : 0 < r)
    (hfr : MemLp f (ENNReal.ofReal r) torusMeasure) (z : Torus) :
    MemLp (fun y ↦ f (z - y)) (ENNReal.ofReal r) (meshCellMeasure J hJ a) ∧
      lpNorm (fun y ↦ f (z - y)) (ENNReal.ofReal r) (meshCellMeasure J hJ a) ≤
        cellMomentBound J f r := by
  have hmp := torusMeasure.measurePreserving_sub_left z
  have hm := hfr.comp_measurePreserving hmp
  have hpower : Integrable (fun y ↦ ‖f y‖ ^ r) torusMeasure := by
    simpa only [ENNReal.toReal_ofReal hr.le] using! hfr.integrable_norm_rpow'
  have hi : Integrable (fun y ↦ ‖f (z - y)‖ ^ r) torusMeasure :=
    hmp.integrable_comp_of_integrable hpower
  have hmcell : MemLp (fun y ↦ f (z - y)) (ENNReal.ofReal r)
      (meshCellMeasure J hJ a) := by
    rw [meshCellMeasure]
    exact (hm.restrict _).smul_measure (by simp)
  refine ⟨hmcell, ?_⟩
  rw [DensityMoments.lpNorm_ofReal_eq hr hmcell.aestronglyMeasurable]
  have hb : (∫ y, ‖f (z - y)‖ ^ r ∂meshCellMeasure J hJ a) ≤
      (J : ℝ) ^ 2 * ∫ y, ‖f y‖ ^ r ∂torusMeasure := by
    rw [meshCellMeasure, integral_smul_measure]
    simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul]
    have hrest := integral_mono_measure (Measure.restrict_le_self :
      torusMeasure.restrict (meshCell J hJ a) ≤ torusMeasure)
        (Eventually.of_forall fun y ↦ Real.rpow_nonneg (norm_nonneg _) r) hi
    have he : (∫ y, ‖f (z - y)‖ ^ r ∂torusMeasure) =
        ∫ y, ‖f y‖ ^ r ∂torusMeasure := by
      have he' := integral_map_of_stronglyMeasurable (μ := torusMeasure) hmp.measurable
        (hf.norm.pow_const r).stronglyMeasurable
      rw [hmp.map_eq] at he'
      exact he'.symm
    exact mul_le_mul_of_nonneg_left (hrest.trans_eq he) (sq_nonneg _)
  exact Real.rpow_le_rpow
    (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) r) hb
    (one_div_nonneg.mpr hr.le)

theorem cell_green_moment {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (r : ℝ) (hr : 1 ≤ r) (z : Torus) :
    MemLp (fun y ↦ greenRealRepresentative (z - y)) (ENNReal.ofReal r)
      (meshCellMeasure J hJ a) ∧
      lpNorm (fun y ↦ greenRealRepresentative (z - y)) (ENNReal.ofReal r)
        (meshCellMeasure J hJ a) ≤ cellMomentBound J greenRealRepresentative r :=
  cell_translation_moment hJ a greenRealRepresentative_measurable
    (zero_lt_one.trans_le hr) (green_memLp r hr) z

theorem green_square_memLp :
    MemLp (fun y ↦ greenRealRepresentative y ^ 2)
      conjugateExponent torusMeasure := by
  have h4 : MemLp greenRealRepresentative 4 torusMeasure := by
    simpa only [ENNReal.ofReal_ofNat] using green_memLp 4 (by norm_num)
  have h2 : MemLp (fun y ↦ greenRealRepresentative y ^ 2) 2 torusMeasure := by
    apply (memLp_two_iff_integrable_sq
      (greenRealRepresentative_measurable.pow_const 2).aestronglyMeasurable).mpr
    have hi : Integrable (fun y ↦ ‖greenRealRepresentative y‖ ^ 4) torusMeasure := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using! h4.integrable_norm_rpow'
    simpa only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] using! hi
  exact h2.mono_exponent (by norm_num [conjugateExponent])

/-- The common uniform conditional and marginal second-moment constant. -/
def greenSecondMomentBound (J : ℕ) (β₀ : ℝ) : ℝ :=
  densityNormBound β₀ * cellMomentBound J (fun y ↦ greenRealRepresentative y ^ 2) (4 / 3)

theorem greenSecondMomentBound_nonneg (J : ℕ) (β₀ : ℝ) :
    0 ≤ greenSecondMomentBound J β₀ :=
  mul_nonneg (densityNormBound_pos β₀).le (cellMomentBound_nonneg _ _ _)

theorem conditional_green_second_moment {n J : ℕ} (hJ : 0 < J)
    {β₀ β : ℝ} (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J)
    (hb : LawBounds hJ β₀ β i Y a .cell) (z : Torus) :
    Integrable (fun y ↦ greenRealRepresentative (z - y) ^ 2)
      (conditionalKernel (meshCellMeasure J hJ a) i β Y) ∧
      (∫ y, greenRealRepresentative (z - y) ^ 2
        ∂conditionalKernel (meshCellMeasure J hJ a) i β Y) ≤ greenSecondMomentBound J β₀ := by
  have hcell := cell_translation_moment hJ a
    (greenRealRepresentative_measurable.pow_const 2) (by norm_num : (0 : ℝ) < 4 / 3)
    green_square_memLp z
  have hp : Measurable (rawDensity (meshCellMeasure J hJ a) β Y) := by
    have hinc : Measurable (fun z : Torus ↦ (z, Y)) := measurable_id.prodMk measurable_const
    simpa only [Function.comp_def] using!
      (measurable_rawDensity (n := n) (meshCellMeasure J hJ a) β).comp hinc
  have hk : conditionalKernel (meshCellMeasure J hJ a) i β Y =
      (meshCellMeasure J hJ a).withDensity
        (fun y ↦ ENNReal.ofReal (rawDensity (meshCellMeasure J hJ a) β Y y)) :=
    hb.kernel_eq_raw
  rw [hk]
  exact density_envelope_bound hp (rawDensity_nonneg _ β Y) hb.density_memLp hb.density_norm
    (fun _ ↦ sq_nonneg _) hcell.1 hcell.2

theorem capped_conditional_green_second_moment {n J : ℕ} (hJ : 0 < J)
    {β₀ β δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (z : Torus) :
    Integrable (fun y ↦ greenRealRepresentative (z - y) ^ 2)
      (conditionalKernel (meshCellMeasure J hJ a) i β Y) ∧
      (∫ y, greenRealRepresentative (z - y) ^ 2
        ∂conditionalKernel (meshCellMeasure J hJ a) i β Y) ≤ greenSecondMomentBound J β₀ :=
  conditional_green_second_moment hJ i Y a
    (capped_patch_law hJ hβ hβ₀ hδ hmesh η hη i Y hY a .cell) z

/-- Uniform Green second moments for the actual coordinate of the original
specified-label Gibbs system, with square integrability proved first. -/
theorem coordinate_green_second_moment {n J : ℕ} (hN : 2 ≤ n + 1)
    {β₀ β δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (z : Torus) :
    MemLp (fun X ↦ greenRealRepresentative (z - X i)) 2
      (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, greenRealRepresentative (z - X i) ^ 2
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤ greenSecondMomentBound J β₀ := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let : IsProbabilityMeasure μ := isProbabilityMeasure_labelGibbsMeasure
    (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  obtain ⟨hlaw, hp4, hpB⟩ := cellMarginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i
  have hcell := cell_translation_moment (mesh_pos hmesh) (η i)
    (greenRealRepresentative_measurable.pow_const 2) (by norm_num : (0 : ℝ) < 4 / 3)
    green_square_memLp z
  have hh := density_envelope_bound
    (measurable_cellMarginalDensity (mesh_pos hmesh) η β i)
    (cellMarginalDensity_nonneg (mesh_pos hmesh) η β i) hp4 hpB
    (fun y ↦ sq_nonneg (greenRealRepresentative (z - y))) hcell.1 hcell.2
  rw [← hlaw] at hh
  have hgm : Measurable (fun y : Torus ↦ greenRealRepresentative (z - y)) :=
    greenRealRepresentative_measurable.comp (measurable_const.sub measurable_id)
  have hmarg : MemLp (fun y ↦ greenRealRepresentative (z - y)) 2
      (marginalLaw (mesh_pos hmesh) η β i) :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hh.1
  have hmp : MeasurePreserving (fun X : Configuration (n + 1) ↦ X i) μ
      (marginalLaw (mesh_pos hmesh) η β i) := ⟨measurable_pi_apply i, rfl⟩
  refine ⟨hmarg.comp_measurePreserving hmp, ?_⟩
  have he : (∫ y, greenRealRepresentative (z - y) ^ 2
      ∂marginalLaw (mesh_pos hmesh) η β i) =
      ∫ X, greenRealRepresentative (z - X i) ^ 2 ∂μ :=
    integral_map_of_stronglyMeasurable (μ := μ) (measurable_pi_apply i)
      (hgm.pow_const 2).stronglyMeasurable
  have hb : (∫ y, greenRealRepresentative (z - y) ^ 2
      ∂marginalLaw (mesh_pos hmesh) η β i) ≤ greenSecondMomentBound J β₀ := hh.2
  rw [he] at hb
  exact hb

end GreenMoments

section HaarDensities

def haarCellDensity {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (p : Torus → ℝ)
    (z : Torus) : ℝ := (J : ℝ) ^ 2 * (meshCell J hJ a).indicator p z

theorem measurable_haarCellDensity {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {p : Torus → ℝ} (hp : Measurable p) : Measurable (haarCellDensity hJ a p) :=
  (hp.indicator (measurableSet_meshCell J hJ a)).const_mul _

theorem haarCellDensity_nonneg {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {p : Torus → ℝ} (hp0 : ∀ z, 0 ≤ p z) (z : Torus) :
    0 ≤ haarCellDensity hJ a p z := by
  classical
  by_cases hz : z ∈ meshCell J hJ a
  · simpa only [haarCellDensity, indicator_of_mem hz] using mul_nonneg (sq_nonneg _) (hp0 z)
  · simp only [haarCellDensity, indicator_of_notMem hz, mul_zero, le_refl]

theorem haarCellDensity_law {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {p : Torus → ℝ} (hp : Measurable p) :
    torusMeasure.withDensity (fun z ↦ ENNReal.ofReal (haarCellDensity hJ a p z)) =
      (meshCellMeasure J hJ a).withDensity (fun z ↦ ENNReal.ofReal (p z)) := by
  classical
  have he : (fun z ↦ ENNReal.ofReal (haarCellDensity hJ a p z)) =
      (meshCell J hJ a).indicator (fun z ↦ (J : ℝ≥0∞) ^ 2 * ENNReal.ofReal (p z)) := by
    funext z
    by_cases hz : z ∈ meshCell J hJ a
    · simp only [haarCellDensity, indicator_of_mem hz, ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_pow (Nat.cast_nonneg J), ENNReal.ofReal_natCast]
    · simp only [haarCellDensity, indicator_of_notMem hz, mul_zero, ENNReal.ofReal_zero]
  rw [he, withDensity_indicator (measurableSet_meshCell J hJ a)]
  change (torusMeasure.restrict (meshCell J hJ a)).withDensity
    ((J : ℝ≥0∞) ^ 2 • fun z ↦ ENNReal.ofReal (p z)) = _
  rw [withDensity_smul _ hp.ennreal_ofReal, meshCellMeasure, withDensity_smul_measure]

theorem haarCellDensity_norm_four {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) :
    (fun z ↦ ‖haarCellDensity hJ a p z‖ ^ 4) =
      fun z ↦ (J : ℝ) ^ 8 * (meshCell J hJ a).indicator (fun z ↦ ‖p z‖ ^ 4) z := by
  classical
  funext z
  by_cases hz : z ∈ meshCell J hJ a
  · simp only [haarCellDensity, indicator_of_mem hz, norm_mul,
      Real.norm_of_nonneg (sq_nonneg _), mul_pow]
    ring
  · simp only [haarCellDensity, indicator_of_notMem hz, mul_zero, norm_zero, zero_pow
      (by norm_num : 4 ≠ 0)]

theorem integral_haarCellDensity_norm_four {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (p : Torus → ℝ) :
    (∫ z, ‖haarCellDensity hJ a p z‖ ^ 4 ∂torusMeasure) =
      (J : ℝ) ^ 6 * ∫ z, ‖p z‖ ^ 4 ∂meshCellMeasure J hJ a := by
  rw [haarCellDensity_norm_four, integral_const_mul,
    integral_indicator (measurableSet_meshCell J hJ a), meshCellMeasure, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul]
  ring

theorem fourth_power_lpNorm {A : Type*} [MeasurableSpace A]
    {ν : Measure A} {f : A → ℝ} (hf : AEStronglyMeasurable f ν) :
    lpNorm f 4 ν ^ 4 = ∫ x, ‖f x‖ ^ 4 ∂ν := by
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_ofNat] using
    DensityMoments.lpNorm_rpow_eq_integral (by norm_num : (0 : ℝ) < 4) hf

theorem fourth_lpNorm {A : Type*} [MeasurableSpace A]
    {ν : Measure A} {f : A → ℝ} (hf : AEStronglyMeasurable f ν) :
    lpNorm f 4 ν = (∫ x, ‖f x‖ ^ 4 ∂ν) ^ (1 / 4 : ℝ) := by
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_ofNat] using
    DensityMoments.lpNorm_ofReal_eq (by norm_num : (0 : ℝ) < 4) hf

theorem haarCellDensity_L4 {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {p : Torus → ℝ} (hp : Measurable p) (hp4 : MemLp p 4 (meshCellMeasure J hJ a))
    {K : ℝ} (hpK : lpNorm p 4 (meshCellMeasure J hJ a) ≤ K) :
    MemLp (haarCellDensity hJ a p) 4 torusMeasure ∧
      (∫ z, ‖haarCellDensity hJ a p z‖ ^ 4 ∂torusMeasure) ≤ K ^ 4 * (J : ℝ) ^ 6 := by
  have hJ0 : (J : ℝ≥0∞) ^ 2 ≠ 0 := by positivity
  have hi : Integrable (fun z ↦ ‖p z‖ ^ 4) (meshCellMeasure J hJ a) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using! hp4.integrable_norm_rpow'
  have hir : Integrable (fun z ↦ ‖p z‖ ^ 4) (torusMeasure.restrict (meshCell J hJ a)) :=
    (integrable_smul_measure hJ0 (by simp)).mp hi
  have him : Integrable (fun z ↦ ‖haarCellDensity hJ a p z‖ ^ 4) torusMeasure := by
    rw [haarCellDensity_norm_four]
    exact ((integrable_indicator_iff (measurableSet_meshCell J hJ a)).mpr hir).const_mul _
  have hm : MemLp (haarCellDensity hJ a p) 4 torusMeasure := by
    apply (integrable_norm_rpow_iff (measurable_haarCellDensity hJ a hp).aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).mp
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using! him
  refine ⟨hm, ?_⟩
  rw [integral_haarCellDensity_norm_four, ← fourth_power_lpNorm hp4.aestronglyMeasurable]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lpNorm_nonneg hpK 4) (by positivity : (0 : ℝ) ≤ J ^ 6)

/-- Literal Haar marginal density from the source, with its cell support. -/
def marginalDensity {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (i : Fin (n + 1)) : Torus → ℝ :=
  haarCellDensity hJ (η i) (cellMarginalDensity hJ η β i)

def averageDensity {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (z : Torus) : ℝ :=
  (n + 1 : ℝ)⁻¹ * ∑ i, marginalDensity hJ η β i z

def particlePotential {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (i : Fin (n + 1)) (z : Torus) : ℝ :=
  ∫ y, greenRealRepresentative (z - y) * marginalDensity hJ η β i y ∂torusMeasure

def meanPotential {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (z : Torus) : ℝ :=
  ∫ y, greenRealRepresentative (z - y) * averageDensity hJ η β y ∂torusMeasure

theorem measurable_marginalDensity {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1))
    [IsFiniteMeasure (labelGibbsMeasure hJ η β)] :
    Measurable (marginalDensity hJ η β i) :=
  measurable_haarCellDensity hJ (η i) (measurable_cellMarginalDensity hJ η β i)

theorem marginalDensity_nonneg {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) (z : Torus) :
    0 ≤ marginalDensity hJ η β i z :=
  haarCellDensity_nonneg hJ (η i) (cellMarginalDensity_nonneg hJ η β i) z

theorem measurable_averageDensity {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ)
    [IsFiniteMeasure (labelGibbsMeasure hJ η β)] :
    Measurable (averageDensity hJ η β) :=
  (Finset.measurable_sum _ (fun i _ ↦ measurable_marginalDensity hJ η β i)).const_mul _

theorem averageDensity_nonneg {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (z : Torus) :
    0 ≤ averageDensity hJ η β z :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ marginalDensity_nonneg hJ η β i z)

theorem marginalDensity_eq_zero_of_not_mem {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) {z : Torus}
    (hz : z ∉ meshCell J hJ (η i)) : marginalDensity hJ η β i z = 0 := by
  simp only [marginalDensity, haarCellDensity, indicator_of_notMem hz, mul_zero]

theorem indicator_marginalDensity {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J) :
    (meshCell J hJ a).indicator (marginalDensity hJ η β i) =
      fun z ↦ if η i = a then marginalDensity hJ η β i z else 0 := by
  classical
  funext z
  by_cases he : η i = a
  · rw [ite_eq_left he]
    by_cases hz : z ∈ meshCell J hJ a
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz]
      exact (marginalDensity_eq_zero_of_not_mem hJ η β i (by simpa only [he] using hz)).symm
  · rw [ite_eq_right he]
    by_cases hz : z ∈ meshCell J hJ a
    · rw [indicator_of_mem hz]
      exact marginalDensity_eq_zero_of_not_mem hJ η β i (fun hi ↦ he (hi.symm.trans hz))
    · exact indicator_of_notMem hz _

/-- The restriction of the actual average to one half-open cell. -/
def cellAverageDensity {n J : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (β : ℝ) (a : MeshIndex J) : Torus → ℝ :=
  (meshCell J hJ a).indicator (averageDensity hJ η β)

theorem cellAverageDensity_eq_sum {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (a : MeshIndex J) :
    cellAverageDensity hJ η β a = fun z ↦ (n + 1 : ℝ)⁻¹ *
      ∑ i ∈ Finset.univ.filter (fun i ↦ η i = a), marginalDensity hJ η β i z := by
  classical
  funext z
  by_cases hz : z ∈ meshCell J hJ a
  · rw [cellAverageDensity, indicator_of_mem hz, averageDensity]
    congr 1
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have he : η i ≠ a := fun h ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact marginalDensity_eq_zero_of_not_mem hJ η β i (fun hzi ↦ he (hzi.symm.trans hz))
  · rw [cellAverageDensity, indicator_of_notMem hz]
    symm
    rw [Finset.sum_eq_zero (fun i hi ↦ marginalDensity_eq_zero_of_not_mem hJ η β i
      (by simpa only [(Finset.mem_filter.mp hi).2] using hz)), mul_zero]

theorem averageDensity_norm_four_eq_sum {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (z : Torus) :
    ‖averageDensity hJ η β z‖ ^ 4 = ∑ a, ‖cellAverageDensity hJ η β a z‖ ^ 4 := by
  classical
  symm
  rw [Finset.sum_eq_single (meshLabel J hJ z)]
  · simp only [cellAverageDensity, indicator_of_mem (show z ∈ meshCell J hJ (meshLabel J hJ z) from rfl)]
  · intro a _ ha
    rw [cellAverageDensity, indicator_of_notMem (show z ∉ meshCell J hJ a from fun hz ↦ ha hz.symm)]
    norm_num
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem occupation_fraction_four_sum_le_one {n J : ℕ} (η : LabelVector J (n + 1)) :
    (∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) ^ 4) ≤ 1 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have ha (a : MeshIndex J) : (occupation η a : ℝ) / (n + 1 : ℝ) ≤ 1 := by
    apply (div_le_one hn).mpr
    have hc : occupation η a ≤ n + 1 := by
      simpa only [occupation, Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.filter_subset (fun i ↦ η i = a) Finset.univ)
    exact_mod_cast hc
  calc
    _ ≤ ∑ a, (occupation η a : ℝ) / (n + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have h0 : 0 ≤ (occupation η a : ℝ) / (n + 1 : ℝ) := by positivity
      have h3 : ((occupation η a : ℝ) / (n + 1 : ℝ)) ^ 3 ≤ 1 := pow_le_one₀ h0 (ha a)
      calc
        _ = ((occupation η a : ℝ) / (n + 1 : ℝ)) *
            ((occupation η a : ℝ) / (n + 1 : ℝ)) ^ 3 := by ring
        _ ≤ ((occupation η a : ℝ) / (n + 1 : ℝ)) * 1 := mul_le_mul_of_nonneg_left h3 h0
        _ = _ := mul_one _
    _ = 1 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, sum_occupation]
      simp only [Nat.cast_add, Nat.cast_one, div_self hn.ne']

variable {n J : ℕ} (hN : 2 ≤ n + 1) {β₀ β δ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)

include hN hβ hβ₀ hsub hδ hη

theorem marginalDensity_law_and_L4 (i : Fin (n + 1)) :
    marginalLaw (mesh_pos hmesh) η β i =
      torusMeasure.withDensity (fun z ↦ ENNReal.ofReal (marginalDensity (mesh_pos hmesh) η β i z)) ∧
      MemLp (marginalDensity (mesh_pos hmesh) η β i) 4 torusMeasure ∧
      lpNorm (marginalDensity (mesh_pos hmesh) η β i) 4 torusMeasure ≤
        (densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) ^ (1 / 4 : ℝ) := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  obtain ⟨hlaw, hp, hpB⟩ := cellMarginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i
  have hpmeas := measurable_cellMarginalDensity (mesh_pos hmesh) η β i
  obtain ⟨hm, hb⟩ := haarCellDensity_L4 (mesh_pos hmesh) (η i) hpmeas hp hpB
  refine ⟨hlaw.trans (haarCellDensity_law (mesh_pos hmesh) (η i) hpmeas).symm, hm, ?_⟩
  change lpNorm (haarCellDensity (mesh_pos hmesh) (η i)
    (cellMarginalDensity (mesh_pos hmesh) η β i)) 4 torusMeasure ≤ _
  rw [fourth_lpNorm hm.aestronglyMeasurable]
  exact Real.rpow_le_rpow (integral_nonneg fun _ ↦ by positivity) hb (by norm_num)

theorem marginalDensity_integral_one (i : Fin (n + 1)) :
    (∫ z, marginalDensity (mesh_pos hmesh) η β i z ∂torusMeasure) = 1 := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  let : IsProbabilityMeasure (marginalLaw (mesh_pos hmesh) η β i) := by
    constructor
    rw [marginalLaw, Measure.map_apply (measurable_pi_apply i) MeasurableSet.univ]
    simp
  exact DensityMoments.integral_density_one
    (marginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i).1
    (measurable_marginalDensity (mesh_pos hmesh) η β i)
    (Eventually.of_forall (marginalDensity_nonneg (mesh_pos hmesh) η β i))

theorem averageDensity_L4 :
    MemLp (averageDensity (mesh_pos hmesh) η β) 4 torusMeasure ∧
      lpNorm (averageDensity (mesh_pos hmesh) η β) 4 torusMeasure ≤
        (densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) ^ (1 / 4 : ℝ) ∧
      (∫ z, averageDensity (mesh_pos hmesh) η β z ∂torusMeasure) = 1 := by
  have hm (i : Fin (n + 1)) := marginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i
  have hs : MemLp (fun z ↦ ∑ i, marginalDensity (mesh_pos hmesh) η β i z) 4 torusMeasure :=
    memLp_finsetSum _ (fun i _ ↦ (hm i).2.1)
  have hnn : (0 : ℝ) < n + 1 := by positivity
  refine ⟨hs.const_mul _, ?_, ?_⟩
  · change lpNorm (fun z ↦ (n + 1 : ℝ)⁻¹ * ∑ i, marginalDensity (mesh_pos hmesh) η β i z)
      4 torusMeasure ≤ _
    rw [DensityEntropy.lpNorm_const_mul, abs_of_pos (inv_pos.mpr hnn)]
    have hsum : lpNorm (fun z ↦ ∑ i, marginalDensity (mesh_pos hmesh) η β i z) 4 torusMeasure ≤
        ∑ i, lpNorm (marginalDensity (mesh_pos hmesh) η β i) 4 torusMeasure := by
      have he : (fun z ↦ ∑ i, marginalDensity (mesh_pos hmesh) η β i z) =
          ∑ i, marginalDensity (mesh_pos hmesh) η β i := by
        funext z
        simp only [Finset.sum_apply]
      rw [he]
      exact lpNorm_sum_le
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) ↦ (hm i).2.1)
        (by norm_num : (1 : ℝ≥0∞) ≤ 4)
    calc
      _ ≤ (n + 1 : ℝ)⁻¹ * ∑ i, lpNorm (marginalDensity (mesh_pos hmesh) η β i) 4 torusMeasure :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnn.le)
      _ ≤ (n + 1 : ℝ)⁻¹ * ∑ _i : Fin (n + 1),
          (densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ (hm i).2.2) (inv_nonneg.mpr hnn.le)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one, ← mul_assoc, inv_mul_cancel₀ hnn.ne', one_mul]
  · change (∫ z, (n + 1 : ℝ)⁻¹ * ∑ i, marginalDensity (mesh_pos hmesh) η β i z ∂torusMeasure) = 1
    rw [integral_const_mul, integral_finsetSum Finset.univ]
    · simp only [marginalDensity_integral_one hN hβ hβ₀ hsub hδ hmesh η hη,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ hnn.ne']
    · intro i _
      exact (hm i).2.1.integrable (by norm_num)

/-- The literal cell mass of the actual averaged Haar density is the
prescribed occupation fraction. -/
theorem averageDensity_cell_mass (a : MeshIndex J) :
    (∫ z in meshCell J (mesh_pos hmesh) a,
      averageDensity (mesh_pos hmesh) η β z ∂torusMeasure) =
      (occupation η a : ℝ) / (n + 1 : ℝ) := by
  classical
  rw [← integral_indicator (measurableSet_meshCell J (mesh_pos hmesh) a)]
  change (∫ z, cellAverageDensity (mesh_pos hmesh) η β a z ∂torusMeasure) = _
  rw [cellAverageDensity_eq_sum, integral_const_mul,
    integral_finsetSum _ (fun i _ ↦
      (marginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i).2.1.integrable (by norm_num))]
  simp only [marginalDensity_integral_one hN hβ hβ₀ hsub hδ hmesh η hη,
    Finset.sum_const, nsmul_eq_mul, one_mul, occupation, div_eq_mul_inv, mul_comm]

theorem cellAverageDensity_L4 (a : MeshIndex J) :
    MemLp (cellAverageDensity (mesh_pos hmesh) η β a) 4 torusMeasure ∧
      lpNorm (cellAverageDensity (mesh_pos hmesh) η β a) 4 torusMeasure ≤
        ((occupation η a : ℝ) / (n + 1 : ℝ)) *
          (densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) ^ (1 / 4 : ℝ) := by
  classical
  let A := Finset.univ.filter (fun i ↦ η i = a)
  have hm (i : Fin (n + 1)) := marginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i
  rw [cellAverageDensity_eq_sum]
  refine ⟨(memLp_finsetSum A (fun i _ ↦ (hm i).2.1)).const_mul _, ?_⟩
  rw [DensityEntropy.lpNorm_const_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < n + 1))]
  have he : (fun z ↦ ∑ i ∈ A, marginalDensity (mesh_pos hmesh) η β i z) =
      ∑ i ∈ A, marginalDensity (mesh_pos hmesh) η β i := by
    funext z
    simp only [Finset.sum_apply]
  have hs : lpNorm (fun z ↦ ∑ i ∈ A, marginalDensity (mesh_pos hmesh) η β i z) 4 torusMeasure ≤
      ∑ i ∈ A, lpNorm (marginalDensity (mesh_pos hmesh) η β i) 4 torusMeasure := by
    rw [he]
    exact lpNorm_sum_le (fun i (_ : i ∈ A) ↦ (hm i).2.1) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  calc
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ i ∈ A, lpNorm (marginalDensity (mesh_pos hmesh) η β i) 4 torusMeasure :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ _i ∈ A,
        (densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ (hm i).2.2) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, A, occupation, div_eq_mul_inv]
      ring

/-- Cellwise Minkowski and disjoint support give the source's exact
occupation-weighted fourth moment. No equality of same-label marginals is
needed: the actual individual marginal bound suffices. -/
theorem averageDensity_L4_refined :
    lpNorm (averageDensity (mesh_pos hmesh) η β) 4 torusMeasure ^ 4 ≤
      densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6 *
        ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) ^ 4 := by
  have hm := (averageDensity_L4 hN hβ hβ₀ hsub hδ hmesh η hη).1
  have hc (a : MeshIndex J) := cellAverageDensity_L4 hN hβ hβ₀ hsub hδ hmesh η hη a
  have hi (a : MeshIndex J) : Integrable
      (fun z ↦ ‖cellAverageDensity (mesh_pos hmesh) η β a z‖ ^ 4) torusMeasure := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using! (hc a).1.integrable_norm_rpow'
  have hr : ((densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) ^ (1 / 4 : ℝ)) ^ 4 =
      densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6 := by
    rw [← Real.rpow_ofNat, one_div,
      Real.rpow_inv_rpow (by positivity : 0 ≤ densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6)
        (by norm_num : (4 : ℝ) ≠ 0)]
  rw [fourth_power_lpNorm hm.aestronglyMeasurable]
  simp_rw [averageDensity_norm_four_eq_sum]
  rw [integral_finsetSum Finset.univ (fun a _ ↦ hi a)]
  calc
    _ ≤ ∑ a, ((occupation η a : ℝ) / (n + 1 : ℝ)) ^ 4 *
        (densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6) := by
      apply Finset.sum_le_sum
      intro a _
      rw [← fourth_power_lpNorm (hc a).1.aestronglyMeasurable]
      have hb := pow_le_pow_left₀ lpNorm_nonneg (hc a).2 4
      simpa only [mul_pow, hr] using hb
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem averageDensity_fourth_bound :
    lpNorm (averageDensity (mesh_pos hmesh) η β) 4 torusMeasure ^ 4 ≤
      densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6 := by
  have hh := mul_le_mul_of_nonneg_left (occupation_fraction_four_sum_le_one η)
    (by positivity : 0 ≤ densityNormBound β₀ ^ 4 * (J : ℝ) ^ 6)
  exact (averageDensity_L4_refined hN hβ hβ₀ hsub hδ hmesh η hη).trans (by simpa only [mul_one] using hh)

end HaarDensities

section CoordinateSums

theorem sum_coordinate_update {ι : Type*} {E : ι → Type*} [DecidableEq ι]
    (A : Finset ι) (g : ∀ j, E j → ℝ) (X : ∀ j, E j) (k : ι) (z : E k)
    (hk : k ∈ A) :
    (∑ j ∈ A, g j (Function.update X k z j)) =
      (∑ j ∈ A.erase k, g j (X j)) + g k z := by
  rw [← Finset.sum_erase_add A _ hk, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem sum_coordinate_update_of_notMem {ι : Type*} {E : ι → Type*} [DecidableEq ι]
    (A : Finset ι) (g : ∀ j, E j → ℝ) (X : ∀ j, E j) (k : ι) (z : E k)
    (hk : k ∉ A) :
    (∑ j ∈ A, g j (Function.update X k z j)) = ∑ j ∈ A, g j (X j) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (show j ≠ k from fun he ↦ hk (he ▸ hj))]

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
  [∀ i, MeasurableSpace (E i)]
  (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]
  (μ : Measure (∀ k, E k)) [IsProbabilityMeasure μ]

/-- Exact coordinate-sum specialization of the established L2 fine variance
theorem. The unchanged summands determine the center of each section.
All section-variance integrals are genuine integrable functions. -/
theorem coordinate_sum_variance
    (hind : CoordinateOscillation.IndependentSite κ)
    (hstat : ConditionalKernelL2.PreservesLaw κ μ)
    (hα : CoordinateOscillation.maxColumnSum κ ≤ 1 / 2)
    (g : ∀ j, E j → ℝ) (hg : ∀ j, Measurable (g j))
    (hg2 : ∀ j, MemLp (fun X : ∀ k, E k ↦ g j (X j)) 2 μ)
    (A : Finset ι) (c : ℝ) :
    variance (fun X ↦ c * ∑ j ∈ A, g j (X j)) μ ≤
      2 * c ^ 2 * ∑ j ∈ A, ∫ X, g j (X j) ^ 2 ∂μ := by
  classical
  let F : (∀ k, E k) → ℝ := fun X ↦ c * ∑ j ∈ A, g j (X j)
  have hFm : Measurable F :=
    (Finset.measurable_sum _ fun j _ ↦ (hg j).comp (measurable_pi_apply j)).const_mul c
  have hF2 : MemLp F 2 μ :=
    (memLp_finsetSum _ fun j _ ↦ hg2 j).const_mul c
  have hpoint (k : ι) (X : ∀ j, E j) :
      ConditionalVarianceIntegral.kernelVariance κ F k X ≤
        if k ∈ A then c ^ 2 * CoordinateOscillation.siteAverage κ
          (fun X ↦ g k (X k) ^ 2) k X else 0 := by
    by_cases hk : k ∈ A
    · rw [ite_eq_left hk]
      have he (z : E k) : F (Function.update X k z) -
          c * ∑ j ∈ A.erase k, g j (X j) = c * g k z := by
        dsimp only [F]
        rw [sum_coordinate_update A g X k z hk]
        ring
      calc
        _ ≤ ∫ z, (F (Function.update X k z) - c * ∑ j ∈ A.erase k, g j (X j)) ^ 2 ∂κ k X :=
          DensityMoments.variance_le_integral_sub_sq
            (hFm.comp (measurable_update X)) _
        _ = c ^ 2 * ∫ z, g k z ^ 2 ∂κ k X := by
          simp_rw [he, mul_pow]
          rw [integral_const_mul]
        _ = _ := by simp only [CoordinateOscillation.siteAverage, Function.update_self]
    · rw [ite_eq_right hk]
      have he : (fun z : E k ↦ F (Function.update X k z)) = fun _ ↦ F X := by
        funext z
        dsimp only [F]
        rw [sum_coordinate_update_of_notMem A g X k z hk]
      rw [ConditionalVarianceIntegral.kernelVariance, he,
        variance_eq_sub (memLp_const (F X))]
      simp only [Pi.pow_apply, integral_const, probReal_univ, one_smul, sub_self, le_refl]
  have hint (k : ι) :
      (∫ X, ConditionalVarianceIntegral.kernelVariance κ F k X ∂μ) ≤
        if k ∈ A then c ^ 2 * (∫ X, g k (X k) ^ 2 ∂μ) else 0 := by
    have hVi := ConditionalVarianceIntegral.integrable_kernelVariance κ μ hind hstat hF2 k
    have hgm : Measurable (fun X : ∀ j, E j ↦ g k (X k) ^ 2) :=
      ((hg k).comp (measurable_pi_apply k)).pow_const 2
    have hSi := ConditionalVarianceIntegral.integrable_siteAverage κ μ hstat hgm
      (hg2 k).integrable_sq k
    by_cases hk : k ∈ A
    · rw [ite_eq_left hk]
      have hh := integral_mono_ae hVi (hSi.const_mul (c ^ 2))
        (Eventually.of_forall fun X ↦ by simpa only [ite_eq_left hk] using hpoint k X)
      rw [integral_const_mul, ConditionalVarianceIntegral.integral_siteAverage κ μ hstat
        hgm (hg2 k).integrable_sq k] at hh
      exact hh
    · rw [ite_eq_right hk]
      have hh := integral_mono_ae hVi (integrable_const (0 : ℝ))
        (Eventually.of_forall fun X ↦ by simpa only [ite_eq_right hk] using hpoint k X)
      simpa only [integral_zero] using hh
  have hsum : (∑ k, if k ∈ A then c ^ 2 * (∫ X, g k (X k) ^ 2 ∂μ) else 0) =
      c ^ 2 * ∑ k ∈ A, ∫ X, g k (X k) ^ 2 ∂μ := by
    calc
      _ = ∑ k ∈ A, if k ∈ A then c ^ 2 * (∫ X, g k (X k) ^ 2 ∂μ) else 0 :=
        (Finset.sum_subset (Finset.subset_univ A) (fun k _ hk ↦ by simp only [ite_eq_right hk])).symm
      _ = ∑ k ∈ A, c ^ 2 * (∫ X, g k (X k) ^ 2 ∂μ) :=
        Finset.sum_congr rfl fun k hk ↦ ite_eq_left hk
      _ = _ := (Finset.mul_sum _ _ _).symm
  calc
    _ ≤ 2 * ∑ k, ∫ X, ConditionalVarianceIntegral.kernelVariance κ F k X ∂μ :=
      ConditionalVarianceIntegral.variance_le_twice_kernel_variances κ μ hind hstat hα hF2
    _ ≤ 2 * ∑ k, if k ∈ A then c ^ 2 * (∫ X, g k (X k) ^ 2 ∂μ) else 0 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hint k) (by norm_num)
    _ = _ := by rw [hsum]; ring

end CoordinateSums

section FineFieldVariance

/-- The exact source fine-variance bound for the singular field under the
original specified-label law. The subtype influence supremum has already
been bounded on the actual cell product, and the proven all-L2 extension
performs the passage from bounded functions. -/
theorem psi_variance_le {n J : ℕ} (hN : 2 ≤ n + 1)
    {β₀ β δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (z : Torus) :
    variance (psi i z) (labelGibbsMeasure (mesh_pos hmesh) η β) ≤
      2 / (n + 1 : ℝ) ^ 2 * ∑ j ∈ Finset.univ.erase i,
        ∫ X, greenRealRepresentative (z - X j) ^ 2 ∂labelGibbsMeasure (mesh_pos hmesh) η β := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let ν := DeletedPairConditionals.patchLaw (mesh_pos hmesh) (mesh_two_le hmesh)
    η (fun _ ↦ .cell) none β
  let κ := DeletedPairConditionals.patchKernels (mesh_pos hmesh) (mesh_two_le hmesh)
    η (fun _ ↦ .cell) none β
  let φ := patchInclusion (mesh_pos hmesh) η (fun _ ↦ .cell)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_labelGibbsMeasure
    (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  let : IsProbabilityMeasure ν := DeletedPairConditionals.patchLaw_probability
    (mesh_pos hmesh) (mesh_two_le hmesh) hN η (fun _ ↦ .cell) none hβ (hβ₀.trans_lt hsub)
  have hφ : MeasurePreserving φ ν μ := ⟨measurable_patchInclusion _ _ _,
    DeletedPairConditionals.map_patchLaw_none_cells (mesh_pos hmesh) (mesh_two_le hmesh)
      hN η hβ (hβ₀.trans_lt hsub)⟩
  let g (j : Fin (n + 1))
      (y : OneCoordinateConditionals.patchDomain J (mesh_pos hmesh) (η j) .cell) : ℝ :=
    greenRealRepresentative (z - (y : Torus))
  have hgm (j : Fin (n + 1)) : Measurable (g j) :=
    greenRealRepresentative_measurable.comp (measurable_const.sub measurable_subtype_coe)
  have hg2 (j : Fin (n + 1)) : MemLp (fun X ↦ g j (X j)) 2 ν := by
    simpa only [Function.comp_def, φ, patchInclusion, domainInclusion, g] using!
      (coordinate_green_second_moment hN hβ hβ₀ hsub hδ hmesh η hη j z).1.comp_measurePreserving hφ
  have hδ₀ : 0 ≤ δ := by
    have hh := one_le_cap_mass (Nat.zero_lt_succ n) hη
    by_contra hn
    have : δ * (n + 1 : ℕ) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hn) (by positivity)
    linarith
  have hv := coordinate_sum_variance κ ν
    (DeletedPairConditionals.independentSite_patchKernels
      (mesh_pos hmesh) (mesh_two_le hmesh) η (fun _ ↦ .cell) none β)
    (DeletedPairConditionals.preservesLaw_patchKernels
      (mesh_pos hmesh) (mesh_two_le hmesh) hN η (fun _ ↦ .cell) none hβ (hβ₀.trans_lt hsub))
    (DeletedConditionalVariance.maxColumnSum_cells_le_half none hβ hβ₀ hδ₀ hδ hmesh η hη)
    g hgm hg2 (Finset.univ.erase i) (n + 1 : ℝ)⁻¹
  have hevar : variance (psi i z) μ = variance (fun X ↦ psi i z (φ X)) ν := by
    rw [← hφ.map_eq]
    exact variance_map (psi_measurable i z).aemeasurable hφ.aemeasurable
  have hemoment (j : Fin (n + 1)) : (∫ X, g j (X j) ^ 2 ∂ν) =
      ∫ X, greenRealRepresentative (z - X j) ^ 2 ∂μ := by
    have hm : Measurable (fun X : Configuration (n + 1) ↦
        greenRealRepresentative (z - X j) ^ 2) :=
      (greenRealRepresentative_measurable.comp (measurable_const.sub (measurable_pi_apply j))).pow_const 2
    have he := integral_map_of_stronglyMeasurable (μ := ν) hφ.measurable hm.stronglyMeasurable
    rw [hφ.map_eq] at he
    exact he.symm
  have hepsi : (fun X ↦ (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, g j (X j)) =
      fun X ↦ psi i z (φ X) := by
    funext X
    simp only [psi, Nat.cast_add, Nat.cast_one, φ, patchInclusion, domainInclusion, g]
  rw [hepsi] at hv
  rw [← hevar] at hv
  simp_rw [hemoment] at hv
  simpa only [div_eq_mul_inv, inv_pow] using! hv

end FineFieldVariance

section FieldMeans

variable {n J : ℕ} (hN : 2 ≤ n + 1) {β₀ β δ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)

include hN hβ hβ₀ hsub hδ hη

theorem particlePotential_integrable (i : Fin (n + 1)) (z : Torus) :
    Integrable (fun y ↦ greenRealRepresentative (z - y) *
      marginalDensity (mesh_pos hmesh) η β i y) torusMeasure := by
  have hm := (marginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i).2.1
  have hg : MemLp (fun y ↦ greenRealRepresentative (z - y)) conjugateExponent torusMeasure :=
    (green_memLp (4 / 3) (by norm_num)).comp_measurePreserving
      (torusMeasure.measurePreserving_sub_left z)
  simpa only [mul_comm] using! integrable_four_mul_conjugate hm hg

theorem meanPotential_integrable (z : Torus) :
    Integrable (fun y ↦ greenRealRepresentative (z - y) *
      averageDensity (mesh_pos hmesh) η β y) torusMeasure := by
  have hm := (averageDensity_L4 hN hβ hβ₀ hsub hδ hmesh η hη).1
  have hg : MemLp (fun y ↦ greenRealRepresentative (z - y)) conjugateExponent torusMeasure :=
    (green_memLp (4 / 3) (by norm_num)).comp_measurePreserving
      (torusMeasure.measurePreserving_sub_left z)
  simpa only [mul_comm] using! integrable_four_mul_conjugate hm hg

/-- The convolution with the actual Haar marginal equals the expectation
of that coordinate under the original joint law. -/
theorem particlePotential_eq_integral (i : Fin (n + 1)) (z : Torus) :
    particlePotential (mesh_pos hmesh) η β i z =
      ∫ X, greenRealRepresentative (z - X i) ∂labelGibbsMeasure (mesh_pos hmesh) η β := by
  let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hgm : Measurable (fun y : Torus ↦ greenRealRepresentative (z - y)) :=
    greenRealRepresentative_measurable.comp (measurable_const.sub measurable_id)
  have hd := DensityMoments.integral_density
    (marginalDensity_law_and_L4 hN hβ hβ₀ hsub hδ hmesh η hη i).1
    (measurable_marginalDensity (mesh_pos hmesh) η β i)
    (Eventually.of_forall (marginalDensity_nonneg (mesh_pos hmesh) η β i))
    (fun y ↦ greenRealRepresentative (z - y))
  calc
    _ = ∫ y, greenRealRepresentative (z - y) ∂marginalLaw (mesh_pos hmesh) η β i := by
      simpa only [particlePotential, mul_comm] using! hd.symm
    _ = _ := integral_map_of_stronglyMeasurable (μ := labelGibbsMeasure (mesh_pos hmesh) η β)
      (measurable_pi_apply i) hgm.stronglyMeasurable

theorem meanPotential_eq_average (z : Torus) :
    meanPotential (mesh_pos hmesh) η β z =
      (n + 1 : ℝ)⁻¹ * ∑ i, particlePotential (mesh_pos hmesh) η β i z := by
  have he : (fun y ↦ greenRealRepresentative (z - y) * averageDensity (mesh_pos hmesh) η β y) =
      fun y ↦ (n + 1 : ℝ)⁻¹ * ∑ i, greenRealRepresentative (z - y) *
        marginalDensity (mesh_pos hmesh) η β i y := by
    funext y
    simp only [PeriodicAttractiveLogGas.OccupationFieldL2.averageDensity]
    rw [← Finset.mul_sum]
    ring
  change (∫ y, greenRealRepresentative (z - y) * averageDensity (mesh_pos hmesh) η β y
    ∂torusMeasure) = _
  rw [he, integral_const_mul, integral_finsetSum Finset.univ
    (fun i _ ↦ particlePotential_integrable hN hβ hβ₀ hsub hδ hmesh η hη i z)]
  rfl

theorem particlePotential_sq_le (i : Fin (n + 1)) (z : Torus) :
    particlePotential (mesh_pos hmesh) η β i z ^ 2 ≤ greenSecondMomentBound J β₀ := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let : IsProbabilityMeasure μ := isProbabilityMeasure_labelGibbsMeasure
    (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  obtain ⟨hm, hb⟩ := coordinate_green_second_moment hN hβ hβ₀ hsub hδ hmesh η hη i z
  rw [particlePotential_eq_integral hN hβ hβ₀ hsub hδ hmesh η hη]
  have hv := variance_eq_sub hm
  simp only [Pi.pow_apply] at hv
  have hzero := variance_nonneg (fun X ↦ greenRealRepresentative (z - X i)) μ
  change 0 ≤ variance (fun X ↦ greenRealRepresentative (z - X i))
    (labelGibbsMeasure (mesh_pos hmesh) η β) at hzero
  linarith

theorem particlePotential_abs_le (i : Fin (n + 1)) (z : Torus) :
    |particlePotential (mesh_pos hmesh) η β i z| ≤ greenSecondMomentBound J β₀ + 1 := by
  have hb := particlePotential_sq_le hN hβ hβ₀ hsub hδ hmesh η hη i z
  have hB := greenSecondMomentBound_nonneg J β₀
  nlinarith [sq_abs (particlePotential (mesh_pos hmesh) η β i z),
    sq_nonneg (|particlePotential (mesh_pos hmesh) η β i z| - 1)]

/-- A pointwise uniform bound, including every pole, follows from the
actual marginal moments. Its constant is independent of N and the labels. -/
theorem meanPotential_abs_le (z : Torus) :
    |meanPotential (mesh_pos hmesh) η β z| ≤ greenSecondMomentBound J β₀ + 1 := by
  rw [meanPotential_eq_average hN hβ hβ₀ hsub hδ hmesh η hη, abs_mul,
    abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < n + 1))]
  calc
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ i, |particlePotential (mesh_pos hmesh) η β i z| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ _i : Fin (n + 1), (greenSecondMomentBound J β₀ + 1) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦
        particlePotential_abs_le hN hβ hβ₀ hsub hδ hmesh η hη i z) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, ← mul_assoc, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_mul]

theorem psi_memLp (i : Fin (n + 1)) (z : Torus) :
    MemLp (psi i z) 2 (labelGibbsMeasure (mesh_pos hmesh) η β) :=
  (memLp_finsetSum _ fun j _ ↦
    (coordinate_green_second_moment hN hβ hβ₀ hsub hδ hmesh η hη j z).1).const_mul _

/-- The exact field mean retains the missing self-particle term and the
original particle denominator. -/
theorem psi_integral_eq (i : Fin (n + 1)) (z : Torus) :
    (∫ X, psi i z X ∂labelGibbsMeasure (mesh_pos hmesh) η β) =
      meanPotential (mesh_pos hmesh) η β z -
        (n + 1 : ℝ)⁻¹ * particlePotential (mesh_pos hmesh) η β i z := by
  classical
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let : IsProbabilityMeasure μ := isProbabilityMeasure_labelGibbsMeasure
    (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hi (j : Fin (n + 1)) : Integrable (fun X ↦ greenRealRepresentative (z - X j)) μ :=
    (coordinate_green_second_moment hN hβ hβ₀ hsub hδ hmesh η hη j z).1.integrable (by norm_num)
  calc
    _ = (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
        ∫ X, greenRealRepresentative (z - X j) ∂μ := by
      change (∫ X, psi i z X ∂μ) = _
      simp only [psi, Nat.cast_add, Nat.cast_one]
      rw [integral_const_mul, integral_finsetSum (Finset.univ.erase i) (fun j _ ↦ hi j)]
    _ = (n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
        particlePotential (mesh_pos hmesh) η β j z := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact (particlePotential_eq_integral hN hβ hβ₀ hsub hδ hmesh η hη j z).symm
    _ = _ := by
      rw [meanPotential_eq_average hN hβ hβ₀ hsub hδ hmesh η hη]
      rw [← Finset.sum_erase_add Finset.univ
        (fun j ↦ particlePotential (mesh_pos hmesh) η β j z) (Finset.mem_univ i)]
      ring

end FieldMeans

/-- Explicit fixed-resolution constant for the source field L2 estimate. -/
def fieldL2Constant (J : ℕ) (β₀ : ℝ) : ℝ := 2 * greenSecondMomentBound J β₀

theorem fieldL2Constant_nonneg (J : ℕ) (β₀ : ℝ) : 0 ≤ fieldL2Constant J β₀ :=
  mul_nonneg (by norm_num) (greenSecondMomentBound_nonneg J β₀)

/-- The first occupation-rates estimate, for every particle and every pole,
under the original capped-label Gibbs law. All moment, density, fine-variance
and mean identities used here have been proved for that law above. -/
theorem field_L2_bound {n J : ℕ} (hN : 2 ≤ n + 1)
    {β₀ β δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (z : Torus) :
    MemLp (fun X ↦ psi i z X - meanPotential (mesh_pos hmesh) η β z) 2
      (labelGibbsMeasure (mesh_pos hmesh) η β) ∧
      (∫ X, |psi i z X - meanPotential (mesh_pos hmesh) η β z| ^ 2
        ∂labelGibbsMeasure (mesh_pos hmesh) η β) ≤ fieldL2Constant J β₀ / (n + 1 : ℝ) := by
  classical
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let U := meanPotential (mesh_pos hmesh) η β z
  let P := particlePotential (mesh_pos hmesh) η β i z
  let B := greenSecondMomentBound J β₀
  let : IsProbabilityMeasure μ := isProbabilityMeasure_labelGibbsMeasure
    (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hNpos : (0 : ℝ) < n + 1 := by positivity
  have hB : 0 ≤ B := greenSecondMomentBound_nonneg J β₀
  have hψ : MemLp (psi i z) 2 μ := psi_memLp hN hβ hβ₀ hsub hδ hmesh η hη i z
  have herr : MemLp (fun X ↦ psi i z X - U) 2 μ := by
    simpa only [Pi.sub_apply] using! hψ.sub (memLp_const U)
  refine ⟨herr, ?_⟩
  have hmean : (∫ X, psi i z X - U ∂μ) = -((n + 1 : ℝ)⁻¹ * P) := by
    rw [integral_sub (hψ.integrable (by norm_num)) (integrable_const U)]
    simp only [integral_const, probReal_univ, one_smul]
    change (∫ X, psi i z X ∂labelGibbsMeasure (mesh_pos hmesh) η β) - U = _
    rw [psi_integral_eq hN hβ hβ₀ hsub hδ hmesh η hη]
    dsimp only [U, P]
    ring
  have he : (∫ X, (psi i z X - U) ^ 2 ∂μ) =
      variance (psi i z) μ + (n + 1 : ℝ)⁻¹ ^ 2 * P ^ 2 := by
    have hv := variance_eq_sub herr
    rw [variance_sub_const hψ.aestronglyMeasurable U, hmean, neg_sq, mul_pow] at hv
    simp only [Pi.pow_apply] at hv
    linarith
  have hsum : (∑ j ∈ Finset.univ.erase i,
      ∫ X, greenRealRepresentative (z - X j) ^ 2 ∂μ) ≤ (n : ℝ) * B := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, B := Finset.sum_le_sum fun j _ ↦
        (coordinate_green_second_moment hN hβ hβ₀ hsub hδ hmesh η hη j z).2
      _ = _ := by simp
  have hv : variance (psi i z) μ ≤ 2 / (n + 1 : ℝ) ^ 2 * ((n : ℝ) * B) :=
    (psi_variance_le hN hβ hβ₀ hsub hδ hmesh η hη i z).trans
      (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hp : P ^ 2 ≤ B := particlePotential_sq_le hN hβ hβ₀ hsub hδ hmesh η hη i z
  change (∫ X, |psi i z X - U| ^ 2 ∂μ) ≤ 2 * B / (n + 1 : ℝ)
  simp only [sq_abs]
  rw [he]
  calc
    _ ≤ 2 / (n + 1 : ℝ) ^ 2 * ((n : ℝ) * B) + (n + 1 : ℝ)⁻¹ ^ 2 * B :=
      add_le_add hv (mul_le_mul_of_nonneg_left hp (sq_nonneg _))
    _ = ((2 * (n : ℝ) + 1) * B) / (n + 1 : ℝ) ^ 2 := by
      field_simp [hNpos.ne']
    _ ≤ (2 * (n + 1 : ℝ) * B) / (n + 1 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
    _ = 2 * B / (n + 1 : ℝ) := by
      field_simp [hNpos.ne']

end PeriodicAttractiveLogGas.OccupationFieldL2
