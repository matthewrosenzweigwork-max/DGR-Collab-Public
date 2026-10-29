import LeanResearch.PeriodicAttractiveLogGas.ReferencePotentialBounds
import LeanResearch.PeriodicAttractiveLogGas.ReferenceDensityChange
import LeanResearch.PeriodicAttractiveLogGas.BoundaryCovarianceSplitting

/-! Continuity of the concrete reference-density map in the finite product
L1 topology, source lines 2350--2391. Fixed-point existence is separate. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ReferenceConvolutionContinuity

open MeshCells ReferenceResidual ReferencePotentialBounds

/-- The actual bounded-density L1-to-L2 estimate. -/
theorem bounded_difference_square {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f g : α → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hb : ∀ᵐ x ∂ν, |f x| ≤ M ∧ |g x| ≤ M) :
    MemLp (fun x => f x - g x) 2 ν ∧
    (∫ x, (f x - g x)^2 ∂ν) ≤ 2 * M * (∫ x, |f x - g x| ∂ν) := by
  have hf2 : MemLp f 2 ν := MemLp.of_bound hf M (hb.mono fun x hx => by
    simpa only [Real.norm_eq_abs] using hx.1)
  have hg2 : MemLp g 2 ν := MemLp.of_bound hg M (hb.mono fun x hx => by
    simpa only [Real.norm_eq_abs] using hx.2)
  have hd : MemLp (fun x => f x - g x) 2 ν := hf2.sub hg2
  refine ⟨hd, ?_⟩
  have hi := hd.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ ≤ ∫ x, (2 * M) * |f x - g x| ∂ν := by
      apply integral_mono_ae hd.integrable_sq (hi.abs.const_mul _)
      filter_upwards [hb] with x hx
      have ha : |f x - g x| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
      nlinarith [sq_abs (f x - g x), abs_nonneg (f x - g x)]
    _ = _ := integral_const_mul _ _

theorem cell_le_haar {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) :
    meshCellMeasure J hJ a ≤ ENNReal.ofReal ((J : ℝ)^2) • torusMeasure := by
  rw [meshCellMeasure, ENNReal.ofReal_pow (Nat.cast_nonneg J), ENNReal.ofReal_natCast]
  exact smul_le_smul_left _ Measure.restrict_le_self

theorem green_translate_memLp (x : Torus) : MemLp (greenKernel x) 2 torusMeasure :=
  regularGreenRepresentative_memLp.comp_measurePreserving
    (torusMeasure.measurePreserving_sub_left x)

theorem green_cell_memLp {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (x : Torus) :
    MemLp (greenKernel x) 2 (meshCellMeasure J hJ a) :=
  ((green_translate_memLp x).smul_measure (c := ENNReal.ofReal ((J : ℝ)^2))
    ENNReal.ofReal_ne_top).mono_measure (cell_le_haar hJ a)

theorem green_cell_square_le {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (x : Torus) :
    (∫ y, (greenKernel x y)^2 ∂meshCellMeasure J hJ a) ≤
      (J : ℝ)^2 * (∫ y, regularGreenRepresentative y ^ 2 ∂torusMeasure) := by
  have hi := (green_translate_memLp x).integrable_sq.smul_measure
    (c := ENNReal.ofReal ((J : ℝ)^2)) ENNReal.ofReal_ne_top
  calc
    _ ≤ ∫ y, (greenKernel x y)^2 ∂(ENNReal.ofReal ((J : ℝ)^2) • torusMeasure) :=
      integral_mono_measure (cell_le_haar hJ a) (Eventually.of_forall fun y => sq_nonneg _) hi
    _ = _ := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
      congr 1
      have hmp := torusMeasure.measurePreserving_sub_left x
      have hh := integral_map_of_stronglyMeasurable (μ := torusMeasure) hmp.measurable
        (regularGreenRepresentative_measurable.pow_const 2).stronglyMeasurable
      rw [hmp.map_eq] at hh
      simpa only [greenKernel] using hh.symm

/-- Uniform Cauchy--Schwarz bound for the actual cell Green integrals. -/
theorem cell_convolution_difference_square {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    {f g : Torus → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (meshCellMeasure J hJ a))
    (hg : AEStronglyMeasurable g (meshCellMeasure J hJ a))
    (hb : ∀ᵐ y ∂meshCellMeasure J hJ a, |f y| ≤ M ∧ |g y| ≤ M) (x : Torus) :
    (∫ y, greenKernel x y * (f y - g y) ∂meshCellMeasure J hJ a)^2 ≤
      ((J : ℝ)^2 * (∫ y, regularGreenRepresentative y ^ 2 ∂torusMeasure)) *
        (2 * M * ∫ y, |f y - g y| ∂meshCellMeasure J hJ a) := by
  obtain ⟨hd, hb'⟩ := bounded_difference_square hf hg hb
  have hc := BoundaryCovarianceSplitting.integral_mul_squared_le (green_cell_memLp hJ a x) hd
  exact hc.trans (mul_le_mul (green_cell_square_le hJ a x) hb'
    (integral_nonneg fun y => sq_nonneg _) (by positivity))

/-- Actual L1 density classes with the source AE bounds and normalization. -/
abbrev AdmissibleDensity (ν : Measure Torus) :=
  {f : Lp ℝ 1 ν // (∀ᵐ x ∂ν, Real.exp (-1) ≤ f x ∧ f x ≤ Real.exp 1) ∧
    (∫ x, f x ∂ν) = 1}

namespace AdmissibleDensity

variable {ν : Measure Torus} (f : AdmissibleDensity ν)

theorem measurable : Measurable (f.val : Torus → ℝ) := (Lp.stronglyMeasurable f.val).measurable

theorem nonneg : ∀ᵐ x ∂ν, 0 ≤ f.val x :=
  f.property.1.mono fun _ hx => (Real.exp_pos (-1)).le.trans hx.1

theorem abs_le : ∀ᵐ x ∂ν, |f.val x| ≤ Real.exp 1 := by
  filter_upwards [f.property.1, f.nonneg] with x hx hn
  simpa only [abs_of_nonneg hn] using hx.2

def law : Measure Torus := ν.withDensity (fun x => ENNReal.ofReal (f.val x))

instance probability [IsFiniteMeasure ν] : IsProbabilityMeasure f.law := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((Lp.memLp f.val).integrable le_rfl) f.nonneg,
    f.property.2, ENNReal.ofReal_one]

theorem law_le : f.law ≤ ENNReal.ofReal (Real.exp 1) • ν := by
  rw [law, ← withDensity_const]
  exact withDensity_mono (f.property.1.mono fun x hx => ENNReal.ofReal_le_ofReal hx.2)

end AdmissibleDensity

/-- The subtype/product topology here is literally the finite product L1 topology. -/
abbrev DensityFamily {J : ℕ} (hJ : 0 < J) :=
  (a : MeshIndex J) → AdmissibleDensity (meshCellMeasure J hJ a)

def familyMeasures {J : ℕ} {hJ : 0 < J} (φ : DensityFamily hJ) : MeshIndex J → Measure Torus :=
  fun a => (φ a).law

instance familyMeasures_probability {J : ℕ} {hJ : 0 < J} (φ : DensityFamily hJ) (a : MeshIndex J) :
    IsProbabilityMeasure (familyMeasures φ a) := (φ a).probability

theorem density_L1_distance {ν : Measure Torus} (f g : Lp ℝ 1 ν) :
    (∫ x, |f x - g x| ∂ν) = ‖f - g‖ := by
  rw [Lp.norm_def, toReal_eLpNorm, lpNorm_one_eq_integral_norm (Lp.memLp (f - g)).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  simp only [hx, Pi.sub_apply, Real.norm_eq_abs]

theorem potential_density_formula {J : ℕ} {hJ : 0 < J} (φ : DensityFamily hJ)
    (a : MeshIndex J) (x : Torus) :
    potential (familyMeasures φ a) x =
      ∫ y, (φ a).val y * greenKernel x y ∂meshCellMeasure J hJ a :=
  DensityMoments.integral_density rfl (φ a).measurable (φ a).nonneg _

theorem potential_difference_square {J : ℕ} {hJ : 0 < J} (φ ψ : DensityFamily hJ)
    (a : MeshIndex J) (x : Torus) :
    (potential (familyMeasures φ a) x - potential (familyMeasures ψ a) x)^2 ≤
      ((J : ℝ)^2 * (∫ y, regularGreenRepresentative y ^ 2 ∂torusMeasure)) *
        (2 * Real.exp 1 * ‖(φ a).val - (ψ a).val‖) := by
  have hfm : Integrable (fun y => (φ a).val y * greenKernel x y) (meshCellMeasure J hJ a) :=
    RelativeEntropyVariational.integrable_bounded_density_mul (φ a).measurable
      ((measurable_greenKernel.comp (measurable_const.prodMk measurable_id)))
      ((φ a).nonneg.and (φ a).property.1 |>.mono fun y hy => ⟨hy.1, hy.2.2⟩)
      ((green_cell_memLp hJ a x).integrable (by norm_num))
  have hgm : Integrable (fun y => (ψ a).val y * greenKernel x y) (meshCellMeasure J hJ a) :=
    RelativeEntropyVariational.integrable_bounded_density_mul (ψ a).measurable
      ((measurable_greenKernel.comp (measurable_const.prodMk measurable_id)))
      ((ψ a).nonneg.and (ψ a).property.1 |>.mono fun y hy => ⟨hy.1, hy.2.2⟩)
      ((green_cell_memLp hJ a x).integrable (by norm_num))
  have he : potential (familyMeasures φ a) x - potential (familyMeasures ψ a) x =
      ∫ y, greenKernel x y * ((φ a).val y - (ψ a).val y) ∂meshCellMeasure J hJ a := by
    rw [potential_density_formula, potential_density_formula, ← integral_sub hfm hgm]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring
  rw [he]
  have hb := cell_convolution_difference_square hJ a
    (Lp.memLp (φ a).val).aestronglyMeasurable (Lp.memLp (ψ a).val).aestronglyMeasurable
    ((φ a).abs_le.and (ψ a).abs_le) x
  simpa only [density_L1_distance] using hb

def continuityConstant (J : ℕ) : ℝ :=
  ((J : ℝ)^2 * (∫ y, regularGreenRepresentative y ^ 2 ∂torusMeasure)) * (2 * Real.exp 1)

theorem continuityConstant_nonneg (J : ℕ) : 0 ≤ continuityConstant J := by
  unfold continuityConstant
  positivity

theorem potential_difference_le {J : ℕ} {hJ : 0 < J} (φ ψ : DensityFamily hJ)
    (a : MeshIndex J) (x : Torus) :
    |potential (familyMeasures φ a) x - potential (familyMeasures ψ a) x| ≤
      Real.sqrt (continuityConstant J * ‖(φ a).val - (ψ a).val‖) := by
  have hh := potential_difference_square φ ψ a x
  have hn : 0 ≤ continuityConstant J * ‖(φ a).val - (ψ a).val‖ :=
    mul_nonneg (continuityConstant_nonneg J) (norm_nonneg _)
  have hs := Real.sq_sqrt hn
  have ha := Real.sqrt_nonneg (continuityConstant J * ‖(φ a).val - (ψ a).val‖)
  have hq : (potential (familyMeasures φ a) x - potential (familyMeasures ψ a) x)^2 ≤
      continuityConstant J * ‖(φ a).val - (ψ a).val‖ := by
    simpa only [continuityConstant, mul_assoc] using hh
  nlinarith [sq_abs (potential (familyMeasures φ a) x - potential (familyMeasures ψ a) x)]

theorem continuous_potential {J : ℕ} {hJ : 0 < J} (a : MeshIndex J) (x : Torus) :
    Continuous (fun φ : DensityFamily hJ => potential (familyMeasures φ a) x) := by
  apply continuous_iff_continuousAt.mpr
  intro ψ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hm : Continuous (fun φ : DensityFamily hJ =>
      Real.sqrt (continuityConstant J * ‖(φ a).val - (ψ a).val‖)) := by fun_prop
  have ht : Tendsto (fun φ : DensityFamily hJ =>
      Real.sqrt (continuityConstant J * ‖(φ a).val - (ψ a).val‖)) (𝓝 ψ) (𝓝 0) := by
    simpa only [ContinuousAt, sub_self, norm_zero, mul_zero, Real.sqrt_zero] using
      (hm.continuousAt (x := ψ))
  exact squeeze_zero (fun φ => norm_nonneg _)
    (fun φ => by simpa only [Real.norm_eq_abs] using potential_difference_le φ ψ a x) ht

open LabelOccupations ReferenceSelfTerms ReferenceDensityChange

/-- One explicit bound valid simultaneously at every torus point. -/
theorem averagePotential_difference_le {J N : ℕ} {hJ : 0 < J}
    (η : LabelVector J N) (φ ψ : DensityFamily hJ) (x : Torus) :
    |averagePotential (familyMeasures φ) η x - averagePotential (familyMeasures ψ) η x| ≤
      (∑ i, Real.sqrt (continuityConstant J * ‖(φ (η i)).val - (ψ (η i)).val‖)) / (N : ℝ) := by
  rw [averagePotential, averagePotential, ← sub_div, ← Finset.sum_sub_distrib,
    abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    potential_difference_le φ ψ (η i) x)

theorem continuous_averagePotential {J N : ℕ} {hJ : 0 < J}
    (η : LabelVector J N) (x : Torus) :
    Continuous (fun φ : DensityFamily hJ => averagePotential (familyMeasures φ) η x) :=
  (continuous_finsetSum _ fun i _ => continuous_potential (η i) x).div_const _

theorem family_averagePotential_bound {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) (φ : DensityFamily hJ) (x : Torus) :
    |averagePotential (familyMeasures φ) η x| ≤ globalPotentialBound J :=
  global_averagePotential_bound hJ hN (familyMeasures φ) (fun a => (φ a).law_le) η x

theorem continuous_cellNormalizer {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (a : MeshIndex J) :
    Continuous (fun φ : DensityFamily hJ => cellNormalizer hJ (familyMeasures φ) η β a) := by
  apply continuous_iff_continuousAt.mpr
  intro ψ
  apply continuousAt_of_dominated (bound := fun _ => Real.exp (β * globalPotentialBound J))
  · exact Eventually.of_forall fun φ =>
      ((ReferenceDensityChange.measurable_averagePotential (familyMeasures φ) η).const_mul β).exp.aestronglyMeasurable
  · exact Eventually.of_forall fun φ => Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (abs_le.mp (family_averagePotential_bound hN η φ x)).2 hβ)
  · exact integrable_const _
  · exact Eventually.of_forall fun x => (Real.continuous_exp.comp ((continuous_averagePotential η x).const_mul β)).continuousAt

/-- Literal density of the source normalized exponential on every cell,
including cells carrying no particle label. -/
def referenceMapValue {J N : ℕ} {hJ : 0 < J} (η : LabelVector J N) (β : ℝ)
    (φ : DensityFamily hJ) (a : MeshIndex J) (x : Torus) : ℝ :=
  Real.exp (β * averagePotential (familyMeasures φ) η x) /
    cellNormalizer hJ (familyMeasures φ) η β a

theorem measurable_referenceMapValue {J N : ℕ} {hJ : 0 < J}
    (η : LabelVector J N) (β : ℝ) (φ : DensityFamily hJ) (a : MeshIndex J) :
    Measurable (referenceMapValue η β φ a) :=
  ((ReferenceDensityChange.measurable_averagePotential (familyMeasures φ) η).const_mul β).exp.div_const _

theorem referenceMapValue_bound {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) (x : Torus) :
    0 < referenceMapValue η β φ a x ∧
    |referenceMapValue η β φ a x| ≤
      Real.exp (β * globalPotentialBound J) / Real.exp (-β * globalPotentialBound J) := by
  have hh := reference_exponential_normalizer hJ hN (familyMeasures φ)
    (fun a => (φ a).law_le) η hβ (meshCellMeasure J hJ a)
  have hz : 0 < cellNormalizer hJ (familyMeasures φ) η β a := hh.2.2.1
  have he : Real.exp (β * averagePotential (familyMeasures φ) η x) ≤
      Real.exp (β * globalPotentialBound J) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (abs_le.mp (family_averagePotential_bound hN η φ x)).2 hβ)
  have hp : 0 < referenceMapValue η β φ a x := div_pos (Real.exp_pos _) hz
  refine ⟨hp, ?_⟩
  rw [abs_of_pos hp]
  exact div_le_div₀ (Real.exp_pos _).le he (Real.exp_pos _) hh.2.2.2.1

theorem referenceMapValue_memLp {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) : MemLp (referenceMapValue η β φ a) 1 (meshCellMeasure J hJ a) :=
  MemLp.of_bound (measurable_referenceMapValue η β φ a).aestronglyMeasurable _
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (referenceMapValue_bound hN η hβ φ a x).2)

def referenceMap {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) : Lp ℝ 1 (meshCellMeasure J hJ a) :=
  (referenceMapValue_memLp hN η hβ φ a).toLp (referenceMapValue η β φ a)

theorem continuous_referenceMapValue {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (a : MeshIndex J) (x : Torus) :
    Continuous (fun φ : DensityFamily hJ => referenceMapValue η β φ a x) := by
  apply (Real.continuous_exp.comp ((continuous_averagePotential η x).const_mul β)).div
    (continuous_cellNormalizer hN η hβ a)
  intro φ
  exact (cell_exponential_normalizer hJ hN (familyMeasures φ)
    (fun a => (φ a).law_le) η hβ a).2.1.ne'

theorem norm_referenceMap_sub {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ ψ : DensityFamily hJ)
    (a : MeshIndex J) :
    ‖referenceMap hN η hβ φ a - referenceMap hN η hβ ψ a‖ =
      ∫ x, |referenceMapValue η β φ a x - referenceMapValue η β ψ a x|
        ∂meshCellMeasure J hJ a := by
  rw [← density_L1_distance]
  apply integral_congr_ae
  filter_upwards [(referenceMapValue_memLp hN η hβ φ a).coeFn_toLp,
    (referenceMapValue_memLp hN η hβ ψ a).coeFn_toLp] with x hx hy
  simp only [referenceMap, hx, hy]

/-- The concrete normalized-exponential map is continuous in the finite
product of actual cell L1 spaces. No fixed-point conclusion is assumed. -/
theorem continuous_referenceMap {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (referenceMap hN η hβ : DensityFamily hJ →
      ((a : MeshIndex J) → Lp ℝ 1 (meshCellMeasure J hJ a))) := by
  apply continuous_pi
  intro a
  apply continuous_iff_continuousAt.mpr
  intro ψ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [norm_referenceMap_sub]
  have hh : ContinuousAt (fun φ : DensityFamily hJ =>
      ∫ x, |referenceMapValue η β φ a x - referenceMapValue η β ψ a x|
        ∂meshCellMeasure J hJ a) ψ := by
    apply continuousAt_of_dominated (bound := fun _ =>
      2 * (Real.exp (β * globalPotentialBound J) / Real.exp (-β * globalPotentialBound J)))
    · exact Eventually.of_forall fun φ =>
        ((measurable_referenceMapValue η β φ a).sub
          (measurable_referenceMapValue η β ψ a)).norm.aestronglyMeasurable
    · exact Eventually.of_forall fun φ => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]
        exact (abs_sub _ _).trans (by linarith [(referenceMapValue_bound hN η hβ φ a x).2,
          (referenceMapValue_bound hN η hβ ψ a x).2])
    · exact integrable_const _
    · exact Eventually.of_forall fun x =>
        ((continuous_referenceMapValue hN η hβ a x).sub continuous_const).abs.continuousAt
  simpa only [ContinuousAt, sub_self, abs_zero, integral_zero] using hh

/-- The admissible domain is nonempty; this is only the uniform input
family, not a fixed-point assertion. -/
theorem admissibleDensity_nonempty (ν : Measure Torus) [IsProbabilityMeasure ν] :
    Nonempty (AdmissibleDensity ν) := by
  refine ⟨⟨Lp.const 1 ν (1 : ℝ), ?_, ?_⟩⟩
  · filter_upwards [Lp.coeFn_const 1 ν (1 : ℝ)] with x hx
    rw [hx]
    constructor
    · change Real.exp (-1) ≤ 1
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
    · change (1 : ℝ) ≤ Real.exp 1
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1)
  · rw [integral_congr_ae (Lp.coeFn_const 1 ν (1 : ℝ))]
    simp

theorem referenceMapValue_integral {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) :
    (∫ x, referenceMapValue η β φ a x ∂meshCellMeasure J hJ a) = 1 := by
  have hz := (cell_exponential_normalizer hJ hN (familyMeasures φ)
    (fun a => (φ a).law_le) η hβ a).2.1
  simp only [referenceMapValue, integral_div]
  exact div_self hz.ne'

/-- The original and regular Green representatives give the same true
potential at every pole for these absolutely continuous reference laws. -/
theorem potential_eq_original_green {J : ℕ} {hJ : 0 < J} (φ : DensityFamily hJ)
    (a : MeshIndex J) (x : Torus) :
    potential (familyMeasures φ a) x =
      ∫ y, greenRealRepresentative (x - y) ∂familyMeasures φ a := by
  have hac : familyMeasures φ a ≪ torusMeasure := Measure.absolutelyContinuous_of_le_smul
    (reference_le_haar hJ a (familyMeasures φ a) (φ a).law_le)
  apply integral_congr_ae
  exact hac.ae_le ((torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
    regularGreenRepresentative_ae)

@[simp] theorem referenceMapValue_zero {J N : ℕ} {hJ : 0 < J}
    (η : LabelVector J N) (φ : DensityFamily hJ) (a : MeshIndex J) (x : Torus) :
    referenceMapValue η 0 φ a x = 1 := by
  simp [referenceMapValue, cellNormalizer]

end PeriodicAttractiveLogGas.ReferenceConvolutionContinuity
