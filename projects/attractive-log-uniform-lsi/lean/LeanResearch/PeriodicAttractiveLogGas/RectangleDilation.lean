import LeanResearch.PeriodicAttractiveLogGas.RectangleSobolev
import LeanResearch.PeriodicAttractiveLogGas.Entropy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.Variance

/-! Affine transport for the last sentence of source Lemma 3.2.
The map is Z ↦ a + J⁻¹ • Z in the genuine Euclidean plane. The reference
rectangles, their normalized Lebesgue measures, and their Riesz gradients are
the checked objects of RectangleReflection/RectangleSobolev. Current central
development evidence and semantic/protected statuses are recorded separately.
The final transport lemmas take an already established reference inequality;
they do not establish the density inequalities or identify torus mesh charts.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.RectangleDilation

inductive Kind where
  | square
  | double

def closed : Kind → Set PlanarSpace
  | .square => closedUnitSquare
  | .double => closedDoubleRectangle

def openInterior : Kind → Set PlanarSpace
  | .square => openUnitSquare
  | .double => openDoubleRectangle

def width : Kind → Fin 2 → ℝ
  | .square => fun _ => 1
  | .double => doubleRectangleWidth

def halfOpen (b : Kind) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j => Set.Ico 0 (width b j))

theorem mem_closed_iff (b : Kind) (Z : PlanarSpace) :
    Z ∈ closed b ↔ ∀ j, 0 ≤ Z j ∧ Z j ≤ width b j := by
  cases b <;>
    simp only [closed, closedUnitSquare, closedDoubleRectangle, width,
      Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc]

def referenceMeasure : Kind → Measure PlanarSpace
  | .square => squareLebesgue
  | .double => rectangleLebesgue

def referenceWeight (b : Kind) : ℝ≥0∞ := (volume (closed b))⁻¹

theorem measurableSet_closed (b : Kind) : MeasurableSet (closed b) := by
  cases b
  · exact measurableSet_closedUnitSquare
  · exact measurableSet_closedDoubleRectangle

theorem isCompact_closed (b : Kind) : IsCompact (closed b) := by
  cases b
  · exact isCompact_closedUnitSquare
  · exact isCompact_closedDoubleRectangle

theorem volume_closed_ne_zero (b : Kind) : volume (closed b) ≠ 0 := by
  cases b <;> simp [closed, volume_closedUnitSquare, volume_closedDoubleRectangle]

theorem volume_closed_ne_top (b : Kind) : volume (closed b) ≠ ∞ := by
  cases b <;> simp [closed, volume_closedUnitSquare, volume_closedDoubleRectangle]

theorem referenceWeight_ne_zero (b : Kind) : referenceWeight b ≠ 0 := by
  simp [referenceWeight, volume_closed_ne_top b]

theorem referenceWeight_ne_top (b : Kind) : referenceWeight b ≠ ∞ := by
  simp [referenceWeight, volume_closed_ne_zero b]

theorem referenceMeasure_eq (b : Kind) :
    referenceMeasure b = referenceWeight b • volume.restrict (closed b) := by
  cases b
  · simp [referenceMeasure, referenceWeight, closed, squareLebesgue, volume_closedUnitSquare]
  · simp only [referenceMeasure, referenceWeight, closed, rectangleLebesgue,
      volume_closedDoubleRectangle]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num

instance referenceMeasure_probability (b : Kind) : IsProbabilityMeasure (referenceMeasure b) := by
  cases b
  · exact isProbabilityMeasure_squareLebesgue
  · exact isProbabilityMeasure_rectangleLebesgue

theorem restrict_halfOpen_eq_closed (b : Kind) :
    volume.restrict (halfOpen b) = volume.restrict (closed b) := by
  cases b <;> exact volume_restrict_halfOpenRectangle_eq_closed _

theorem ae_closed_mem_nhds (b : Kind) :
    ∀ᵐ Z ∂referenceMeasure b, closed b ∈ 𝓝 Z := by
  cases b
  · exact ae_mem_openUnitSquare.mono fun Z hZ => closedUnitSquare_mem_nhds hZ
  · exact ae_mem_openDoubleRectangle.mono fun Z hZ => closedDoubleRectangle_mem_nhds hZ

theorem ae_mem_closed (b : Kind) : ∀ᵐ Z ∂referenceMeasure b, Z ∈ closed b := by
  exact (ae_closed_mem_nhds b).mono fun _ h => mem_of_mem_nhds h

def affine (a : PlanarSpace) (J : ℝ) (Z : PlanarSpace) : PlanarSpace := a + J⁻¹ • Z
def inverseAffine (a : PlanarSpace) (J : ℝ) (x : PlanarSpace) : PlanarSpace := J • (x - a)

theorem continuous_affine (a : PlanarSpace) (J : ℝ) : Continuous (affine a J) := by
  unfold affine
  fun_prop

theorem continuous_inverseAffine (a : PlanarSpace) (J : ℝ) :
    Continuous (inverseAffine a J) := by
  unfold inverseAffine
  fun_prop

@[simp] theorem inverseAffine_affine (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0) (Z : PlanarSpace) :
    inverseAffine a J (affine a J Z) = Z := by
  simp [inverseAffine, affine, smul_smul, hJ]

@[simp] theorem affine_inverseAffine (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0) (x : PlanarSpace) :
    affine a J (inverseAffine a J x) = x := by
  simp [inverseAffine, affine, smul_smul, hJ]

def affineHomeomorph (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0) : PlanarSpace ≃ₜ PlanarSpace where
  toFun := affine a J
  invFun := inverseAffine a J
  left_inv := inverseAffine_affine a hJ
  right_inv := affine_inverseAffine a hJ
  continuous_toFun := continuous_affine a J
  continuous_invFun := continuous_inverseAffine a J

theorem measurableEmbedding_affine (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0) :
    MeasurableEmbedding (affine a J) := (affineHomeomorph a hJ).measurableEmbedding

def scaledClosed (b : Kind) (a : PlanarSpace) (J : ℝ) : Set PlanarSpace := affine a J '' closed b
def scaledHalfOpen (b : Kind) (a : PlanarSpace) (J : ℝ) : Set PlanarSpace := affine a J '' halfOpen b

theorem mem_scaledClosed_iff_inverse (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0)
    (x : PlanarSpace) : x ∈ scaledClosed b a J ↔ inverseAffine a J x ∈ closed b := by
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    simpa only [inverseAffine_affine a hJ] using hZ
  · intro hx
    exact ⟨inverseAffine a J x, hx, affine_inverseAffine a hJ x⟩

theorem mem_scaledClosed_iff_coordinates (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (x : PlanarSpace) : x ∈ scaledClosed b a J ↔
      ∀ j, a j ≤ x j ∧ x j ≤ a j + width b j / J := by
  rw [mem_scaledClosed_iff_inverse b a hJ.ne' x, mem_closed_iff]
  apply forall_congr'
  intro j
  change (0 ≤ J * (x j - a j) ∧ J * (x j - a j) ≤ width b j) ↔ _
  rw [mul_nonneg_iff_of_pos_left hJ, ← le_div_iff₀' hJ]
  constructor
  · rintro ⟨hl, hr⟩
    constructor <;> linarith
  · rintro ⟨hl, hr⟩
    constructor <;> linarith

theorem isCompact_scaledClosed (b : Kind) (a : PlanarSpace) (J : ℝ) :
    IsCompact (scaledClosed b a J) := (isCompact_closed b).image (continuous_affine a J)

theorem measurableSet_scaledClosed (b : Kind) (a : PlanarSpace) (J : ℝ) :
    MeasurableSet (scaledClosed b a J) := (isCompact_scaledClosed b a J).measurableSet

/-- The Lebesgue Jacobian is J², since the underlying Euclidean dimension is two. -/
theorem map_volume_affine (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    volume.map (affine a J) = ENNReal.ofReal (J ^ 2) • volume := by
  have hs := Measure.map_addHaar_smul (volume : Measure PlanarSpace) (inv_ne_zero hJ.ne')
  have hdim : Module.finrank ℝ PlanarSpace = 2 := by simp [PlanarSpace]
  rw [hdim] at hs
  have hcoeff : |((J⁻¹) ^ (2 : ℕ))⁻¹| = J ^ 2 := by
    simp [inv_pow, abs_of_nonneg (sq_nonneg J)]
  rw [hcoeff] at hs
  calc
    volume.map (affine a J) =
        (volume.map (fun Z : PlanarSpace => J⁻¹ • Z)).map (fun x => a + x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (ENNReal.ofReal (J ^ 2) • volume).map (fun x : PlanarSpace => a + x) := by rw [hs]
    _ = ENNReal.ofReal (J ^ 2) • volume := by
      rw [Measure.map_smul _ (by fun_prop), Measure.IsAddLeftInvariant.map_add_left_eq_self]

theorem map_restrict_volume_affine (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (s : Set PlanarSpace) :
    (volume.restrict s).map (affine a J) =
      ENNReal.ofReal (J ^ 2) • volume.restrict (affine a J '' s) := by
  have he := (measurableEmbedding_affine a hJ.ne').restrict_map volume (affine a J '' s)
  rw [(measurableEmbedding_affine a hJ.ne').injective.preimage_image,
    map_volume_affine a hJ, Measure.restrict_smul] at he
  exact he.symm

/-- This is an actual Lebesgue restriction with its explicit normalizing coefficient. -/
def scaledLebesgue (b : Kind) (a : PlanarSpace) (J : ℝ) : Measure PlanarSpace :=
  (ENNReal.ofReal (J ^ 2) * referenceWeight b) • volume.restrict (scaledClosed b a J)

theorem map_referenceMeasure (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    (referenceMeasure b).map (affine a J) = scaledLebesgue b a J := by
  rw [referenceMeasure_eq, Measure.map_smul _ (continuous_affine a J).measurable.aemeasurable,
    map_restrict_volume_affine a hJ, smul_smul]
  simp only [scaledLebesgue, scaledClosed, mul_comm]

theorem measurePreserving_affine_reference (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    MeasurePreserving (affine a J) (referenceMeasure b) (scaledLebesgue b a J) :=
  ⟨(continuous_affine a J).measurable, map_referenceMeasure b a hJ⟩

theorem scaledLebesgue_probability (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    IsProbabilityMeasure (scaledLebesgue b a J) := by
  rw [← map_referenceMeasure b a hJ]
  infer_instance

theorem volume_scaledClosed (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    volume (scaledClosed b a J) = (ENNReal.ofReal (J ^ 2) * referenceWeight b)⁻¹ := by
  let c : ℝ≥0∞ := ENNReal.ofReal (J ^ 2) * referenceWeight b
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hJ))
    (referenceWeight_ne_zero b)
  have hct : c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (referenceWeight_ne_top b)
  let := scaledLebesgue_probability b a hJ
  have hm : c * volume (scaledClosed b a J) = 1 := by
    simpa [scaledLebesgue, c, Measure.smul_apply] using
      (measure_univ (μ := scaledLebesgue b a J))
  calc
    volume (scaledClosed b a J) = c⁻¹ * (c * volume (scaledClosed b a J)) :=
      (ENNReal.inv_mul_cancel_left hc0 hct).symm
    _ = c⁻¹ := by rw [hm, mul_one]

theorem scaledLebesgue_eq_normalized (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    scaledLebesgue b a J = (volume (scaledClosed b a J))⁻¹ •
      volume.restrict (scaledClosed b a J) := by
  rw [volume_scaledClosed b a hJ, inv_inv]
  rfl

theorem volume_restrict_scaledHalfOpen_eq_closed (b : Kind) (a : PlanarSpace) {J : ℝ}
    (hJ : 0 < J) : volume.restrict (scaledHalfOpen b a J) =
      volume.restrict (scaledClosed b a J) := by
  have he := congrArg (fun μ : Measure PlanarSpace => μ.map (affine a J))
    (restrict_halfOpen_eq_closed b)
  rw [map_restrict_volume_affine a hJ, map_restrict_volume_affine a hJ] at he
  have hc0 : ENNReal.ofReal (J ^ 2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hJ)
  have he' := congrArg (fun μ : Measure PlanarSpace => (ENNReal.ofReal (J ^ 2))⁻¹ • μ) he
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using! he'

theorem scaledLebesgue_eq_normalized_halfOpen (b : Kind) (a : PlanarSpace) {J : ℝ}
    (hJ : 0 < J) : scaledLebesgue b a J = (volume (scaledHalfOpen b a J))⁻¹ •
      volume.restrict (scaledHalfOpen b a J) := by
  have hv := congrArg (fun μ : Measure PlanarSpace => μ Set.univ)
    (volume_restrict_scaledHalfOpen_eq_closed b a hJ)
  simp only [Measure.restrict_apply_univ] at hv
  rw [hv, volume_restrict_scaledHalfOpen_eq_closed b a hJ]
  exact scaledLebesgue_eq_normalized b a hJ

def transport (a : PlanarSpace) (J : ℝ) (μ : Measure PlanarSpace) : Measure PlanarSpace :=
  μ.map (affine a J)

theorem measurePreserving_transport (a : PlanarSpace) (J : ℝ) (μ : Measure PlanarSpace) :
    MeasurePreserving (affine a J) μ (transport a J μ) :=
  ⟨(continuous_affine a J).measurable, rfl⟩

instance transport_probability (a : PlanarSpace) (J : ℝ) (μ : Measure PlanarSpace)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (transport a J μ) := by
  constructor
  simp [transport, Measure.map_apply (continuous_affine a J).measurable]

theorem integral_transport (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0)
    (μ : Measure PlanarSpace) (f : PlanarSpace → ℝ) :
    (∫ Z, f (affine a J Z) ∂μ) = ∫ x, f x ∂transport a J μ :=
  (measurePreserving_transport a J μ).integral_comp (measurableEmbedding_affine a hJ) f

theorem eLpNorm_transport {E : Type*} [NormedAddCommGroup E]
    (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0) (μ : Measure PlanarSpace)
    (f : PlanarSpace → E) (p : ℝ≥0∞) :
    eLpNorm (fun Z => f (affine a J Z)) p μ = eLpNorm f p (transport a J μ) :=
  ((measurableEmbedding_affine a hJ).eLpNorm_map_measure (μ := μ) (g := f) (p := p)).symm

theorem lpNorm_transport {E : Type*} [NormedAddCommGroup E]
    (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0) (μ : Measure PlanarSpace)
    (f : PlanarSpace → E) (p : ℝ≥0∞) :
    lpNorm (fun Z => f (affine a J Z)) p μ = lpNorm f p (transport a J μ) :=
  congrArg ENNReal.toReal (eLpNorm_transport a hJ μ f p)

theorem memLp_transport_iff {E : Type*} [NormedAddCommGroup E]
    (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0) (μ : Measure PlanarSpace)
    (f : PlanarSpace → E) (p : ℝ≥0∞) :
    MemLp (fun Z => f (affine a J Z)) p μ ↔ MemLp f p (transport a J μ) :=
  (measurableEmbedding_affine a hJ).memLp_map_measure_iff.symm

/-- Entropy transport is exact even if its value is positive infinity. -/
theorem entropy_transport (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0)
    (μ : Measure PlanarSpace) (F : PlanarSpace → ℝ) :
    entropy μ (fun Z => F (affine a J Z)) = entropy (transport a J μ) F := by
  have hm : (transport a J μ).real Set.univ = μ.real Set.univ := by
    simp [transport, measureReal_def, Measure.map_apply (continuous_affine a J).measurable]
  unfold entropy
  rw [(measurePreserving_transport a J μ).lintegral_comp_emb
    (measurableEmbedding_affine a hJ) (fun x => ENNReal.ofReal (entropyDensity (F x))),
    integral_transport a hJ μ F, hm]

theorem variance_transport (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0)
    (μ : Measure PlanarSpace) (f : PlanarSpace → ℝ) :
    ProbabilityTheory.variance (fun Z => f (affine a J Z)) μ =
      ProbabilityTheory.variance f (transport a J μ) := by
  exact (ProbabilityTheory.variance_map_equiv f (affineHomeomorph a hJ).toMeasurableEquiv).symm

theorem centered_lpNorm_transport (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0)
    (μ : Measure PlanarSpace) (f : PlanarSpace → ℝ) (p : ℝ≥0∞) :
    lpNorm (fun Z => f (affine a J Z) - ∫ W, f (affine a J W) ∂μ) p μ =
      lpNorm (fun x => f x - ∫ y, f y ∂transport a J μ) p (transport a J μ) := by
  rw [integral_transport a hJ μ f]
  exact lpNorm_transport a hJ μ (fun x ↦ f x - ∫ y, f y ∂transport a J μ) p

def referenceLaw (b : Kind) (p : PlanarSpace → ℝ) : Measure PlanarSpace :=
  (referenceMeasure b).withDensity (fun Z => ENNReal.ofReal (p Z))

def scaledDensity (a : PlanarSpace) (J : ℝ) (p : PlanarSpace → ℝ) : PlanarSpace → ℝ :=
  fun x => p (inverseAffine a J x)

theorem scaledDensity_pullback (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0)
    (p : PlanarSpace → ℝ) : scaledDensity a J (fun Z => p (affine a J Z)) = p := by
  funext x
  simp only [scaledDensity, affine_inverseAffine a hJ]

def scaledLaw (b : Kind) (a : PlanarSpace) (J : ℝ) (p : PlanarSpace → ℝ) : Measure PlanarSpace :=
  (scaledLebesgue b a J).withDensity (fun x => ENNReal.ofReal (scaledDensity a J p x))

theorem transport_referenceLaw (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) : transport a J (referenceLaw b p) = scaledLaw b a J p := by
  apply Measure.ext
  intro s hs
  rw [transport, Measure.map_apply (continuous_affine a J).measurable hs,
    referenceLaw, withDensity_apply _ ((continuous_affine a J).measurable hs),
    scaledLaw, withDensity_apply _ hs]
  simpa only [scaledDensity, inverseAffine_affine a hJ.ne'] using
    (measurePreserving_affine_reference b a hJ).setLIntegral_comp_preimage_emb
      (measurableEmbedding_affine a hJ.ne')
      (fun x => ENNReal.ofReal (scaledDensity a J p x)) s

theorem scaledLaw_probability (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)] :
    IsProbabilityMeasure (scaledLaw b a J p) := by
  rw [← transport_referenceLaw b a hJ p]
  infer_instance

theorem scaledDensity_lower_iff (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) (c : ℝ) :
    (∀ᵐ x ∂scaledLebesgue b a J, c ≤ scaledDensity a J p x) ↔
      ∀ᵐ Z ∂referenceMeasure b, c ≤ p Z := by
  rw [← map_referenceMeasure b a hJ, (measurableEmbedding_affine a hJ.ne').ae_map_iff]
  simp only [scaledDensity, inverseAffine_affine a hJ.ne']

theorem scaledDensity_memLp_iff (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) (q : ℝ≥0∞) :
    MemLp (scaledDensity a J p) q (scaledLebesgue b a J) ↔ MemLp p q (referenceMeasure b) := by
  rw [← map_referenceMeasure b a hJ, (measurableEmbedding_affine a hJ.ne').memLp_map_measure_iff]
  simp only [Function.comp_def, scaledDensity, inverseAffine_affine a hJ.ne']

theorem scaledDensity_lpNorm (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) (q : ℝ≥0∞) :
    lpNorm (scaledDensity a J p) q (scaledLebesgue b a J) = lpNorm p q (referenceMeasure b) := by
  have he := lpNorm_transport a hJ.ne' (referenceMeasure b) (scaledDensity a J p) q
  simpa only [transport, map_referenceMeasure b a hJ, scaledDensity,
    inverseAffine_affine a hJ.ne'] using he.symm

theorem lipschitzWith_affine (a : PlanarSpace) (J : ℝ) :
    LipschitzWith ‖J⁻¹‖₊ (affine a J) := by
  apply LipschitzWith.of_dist_le_mul
  intro Z W
  simp only [affine, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    coe_nnnorm, le_refl]

theorem lipschitzOnWith_pullback (b : Kind) (a : PlanarSpace) (J : ℝ)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    LipschitzOnWith (K * ‖J⁻¹‖₊) (fun Z => f (affine a J Z)) (closed b) :=
  hf.comp (lipschitzWith_affine a J).lipschitzOnWith (fun Z hZ => ⟨Z, hZ, rfl⟩)

theorem ae_scaledClosed_mem_nhds (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    ∀ᵐ x ∂scaledLebesgue b a J, scaledClosed b a J ∈ 𝓝 x := by
  rw [← map_referenceMeasure b a hJ, (measurableEmbedding_affine a hJ.ne').ae_map_iff]
  filter_upwards [ae_closed_mem_nhds b] with Z hZ
  exact (affineHomeomorph a hJ.ne').isOpenMap.image_mem_nhds hZ

theorem ae_mem_scaledClosed (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J) :
    ∀ᵐ x ∂scaledLebesgue b a J, x ∈ scaledClosed b a J :=
  (ae_scaledClosed_mem_nhds b a hJ).mono fun _ h => mem_of_mem_nhds h

theorem transport_absolutelyContinuous {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {μ : Measure PlanarSpace} (hμ : μ ≪ referenceMeasure b) :
    transport a J μ ≪ scaledLebesgue b a J := by
  simpa only [transport, map_referenceMeasure b a hJ] using
    (measurableEmbedding_affine a hJ.ne').absolutelyContinuous_map hμ

/-- Rademacher is applied on the actual closed scaled rectangle. Boundary nullity
comes from the reference interior under the explicit affine pushforward. -/
theorem ae_differentiableAt_scaled {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    ∀ᵐ x ∂scaledLebesgue b a J, DifferentiableAt ℝ f x := by
  have hd : ∀ᵐ x ∂scaledLebesgue b a J,
      DifferentiableWithinAt ℝ f (scaledClosed b a J) x :=
    Measure.ae_smul_measure
      (hf.ae_differentiableWithinAt (μ := volume) (measurableSet_scaledClosed b a J)) _
  filter_upwards [hd, ae_scaledClosed_mem_nhds b a hJ] with x hx hi
  exact hx.differentiableAt hi

theorem ae_norm_gradient_scaled_le {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    ∀ᵐ x ∂scaledLebesgue b a J, ‖rectangleOrdinaryGradient f x‖ ≤ K := by
  filter_upwards [ae_scaledClosed_mem_nhds b a hJ] with x hx
  rw [norm_rectangleOrdinaryGradient]
  exact norm_fderiv_le_of_lipschitzOn ℝ hx hf

theorem aestronglyMeasurable_scaled {b : Kind} {a : PlanarSpace} {J : ℝ}
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    AEStronglyMeasurable f (scaledLebesgue b a J) :=
  (hf.continuousOn.aestronglyMeasurable (measurableSet_scaledClosed b a J)).smul_measure _

theorem memLp_scaled_of_absolutelyContinuous {b : Kind} {a : PlanarSpace} {J : ℝ}
    (hJ : 0 < J) {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ scaledLebesgue b a J) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (scaledClosed b a J)) (p : ℝ≥0∞) : MemLp f p ν := by
  obtain ⟨C, hC⟩ := (isCompact_scaledClosed b a J).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound ((aestronglyMeasurable_scaled hf).mono_ac hν) C
  filter_upwards [hν.ae_le (ae_mem_scaledClosed b a hJ)] with x hx
  exact hC x hx

theorem memLp_gradient_scaled_of_absolutelyContinuous {b : Kind} {a : PlanarSpace} {J : ℝ}
    (hJ : 0 < J) {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ scaledLebesgue b a J) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (scaledClosed b a J)) (p : ℝ≥0∞) :
    MemLp (rectangleOrdinaryGradient f) p ν :=
  MemLp.of_bound (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable K
    (hν.ae_le (ae_norm_gradient_scaled_le hJ hf))

theorem hasFDerivAt_affine (a : PlanarSpace) (J : ℝ) (Z : PlanarSpace) :
    HasFDerivAt (affine a J) (J⁻¹ • ContinuousLinearMap.id ℝ PlanarSpace) Z := by
  exact ((hasFDerivAt_id Z).const_smul J⁻¹).const_add a

theorem fderiv_pullback {a : PlanarSpace} {J : ℝ} {f : PlanarSpace → ℝ} {Z : PlanarSpace}
    (hf : DifferentiableAt ℝ f (affine a J Z)) :
    fderiv ℝ (fun W => f (affine a J W)) Z = J⁻¹ • fderiv ℝ f (affine a J Z) := by
  change fderiv ℝ (f ∘ affine a J) Z = _
  rw [(hf.hasFDerivAt.comp Z (hasFDerivAt_affine a J Z)).fderiv]
  ext v
  simp

/-- Riesz duality is linear and isometric for the genuine Euclidean norm. -/
theorem gradient_pullback {a : PlanarSpace} {J : ℝ} {f : PlanarSpace → ℝ} {Z : PlanarSpace}
    (hf : DifferentiableAt ℝ f (affine a J Z)) :
    rectangleOrdinaryGradient (fun W => f (affine a J W)) Z =
      J⁻¹ • rectangleOrdinaryGradient f (affine a J Z) := by
  unfold rectangleOrdinaryGradient
  rw [fderiv_pullback hf, map_smul]

theorem ae_gradient_pullback {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {μ : Measure PlanarSpace} (hμ : μ ≪ referenceMeasure b)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    rectangleOrdinaryGradient (fun W => f (affine a J W)) =ᵐ[μ]
      fun Z => J⁻¹ • rectangleOrdinaryGradient f (affine a J Z) := by
  have hd := (transport_absolutelyContinuous hJ hμ).ae_le (ae_differentiableAt_scaled hJ hf)
  have hd' := (measurableEmbedding_affine a hJ.ne').ae_map_iff.mp hd
  exact hd'.mono fun Z hZ => gradient_pullback hZ

theorem integrable_energy_scaled {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≪ referenceMeasure b)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    Integrable (fun x => ‖rectangleOrdinaryGradient f x‖ ^ 2) (transport a J μ) := by
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable).mp
      (memLp_gradient_scaled_of_absolutelyContinuous hJ
        (transport_absolutelyContinuous hJ hμ) hf 2)

theorem memLp_gradient_pullback {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≪ referenceMeasure b)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    MemLp (rectangleOrdinaryGradient (fun W => f (affine a J W))) 2 μ := by
  have hm := memLp_gradient_scaled_of_absolutelyContinuous hJ
    (transport_absolutelyContinuous hJ hμ) hf 2
  have hc := (memLp_transport_iff a hJ.ne' μ _ 2).mpr hm
  exact (memLp_congr_ae (ae_gradient_pullback hJ hμ hf)).mpr (hc.const_smul J⁻¹)

/-- Exact energy transport, including zero energy. Integrability is established above. -/
theorem integral_energy_pullback {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {μ : Measure PlanarSpace} [IsProbabilityMeasure μ] (hμ : μ ≪ referenceMeasure b)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    (∫ Z, ‖rectangleOrdinaryGradient (fun W => f (affine a J W)) Z‖ ^ 2 ∂μ) =
      (J ^ 2)⁻¹ * ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂transport a J μ := by
  calc
    _ = ∫ Z, ‖J⁻¹ • rectangleOrdinaryGradient f (affine a J Z)‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact (ae_gradient_pullback hJ hμ hf).mono fun Z hZ => congrArg (fun v => ‖v‖ ^ 2) hZ
    _ = (J ^ 2)⁻¹ * ∫ Z, ‖rectangleOrdinaryGradient f (affine a J Z)‖ ^ 2 ∂μ := by
      simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJ), mul_pow, inv_pow]
      exact integral_const_mul _ _
    _ = _ := by rw [integral_transport a hJ.ne' μ (fun x ↦ ‖rectangleOrdinaryGradient f x‖ ^ 2)]

theorem lpNorm_gradient_pullback {b : Kind} {a : PlanarSpace} {J : ℝ} (hJ : 0 < J)
    {μ : Measure PlanarSpace} (hμ : μ ≪ referenceMeasure b)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J))
    (p : ℝ≥0∞) :
    lpNorm (rectangleOrdinaryGradient (fun W => f (affine a J W))) p μ =
      J⁻¹ * lpNorm (rectangleOrdinaryGradient f) p (transport a J μ) := by
  have he := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := p) (ae_gradient_pullback hJ hμ hf))
  change lpNorm (rectangleOrdinaryGradient (fun W => f (affine a J W))) p μ =
    lpNorm (J⁻¹ • (fun Z => rectangleOrdinaryGradient f (affine a J Z))) p μ at he
  rw [he, lpNorm_const_smul, lpNorm_transport a hJ.ne' μ]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJ)]

theorem integrable_continuous_comp_scaled {b : Kind} {a : PlanarSpace} {J : ℝ}
    (hJ : 0 < J) {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ scaledLebesgue b a J) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (scaledClosed b a J)) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Integrable (fun x => Φ (f x)) ν := by
  have hc := hΦ.comp_continuousOn hf.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_scaledClosed b a J).exists_bound_of_continuousOn hc
  have hm : AEStronglyMeasurable (fun x => Φ (f x)) ν :=
    ((hc.aestronglyMeasurable (measurableSet_scaledClosed b a J)).smul_measure
      (ENNReal.ofReal (J ^ 2) * referenceWeight b)).mono_ac hν
  have hl : MemLp (fun x => Φ (f x)) 1 ν := by
    apply MemLp.of_bound hm C
    filter_upwards [hν.ae_le (ae_mem_scaledClosed b a hJ)] with x hx
    exact hC x hx
  exact hl.integrable le_rfl

theorem entropy_sq_eq_integral_scaled {b : Kind} {a : PlanarSpace} {J : ℝ}
    (hJ : 0 < J) {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ scaledLebesgue b a J) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    entropy ν (fun x => f x ^ 2) =
      ((∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂ν) -
        (∫ x, f x ^ 2 ∂ν) * Real.log (∫ x, f x ^ 2 ∂ν) : ℝ) := by
  apply entropy_eq_integral (Eventually.of_forall fun x => sq_nonneg (f x))
  exact integrable_continuous_comp_scaled hJ hν hf
    (Real.continuous_mul_log.comp (continuous_id.pow 2))

theorem measurable_scaledDensity {a : PlanarSpace} {J : ℝ} {p : PlanarSpace → ℝ}
    (hp : Measurable p) : Measurable (scaledDensity a J p) :=
  hp.comp (continuous_inverseAffine a J).measurable

/-- These are the finite-integrability gates for the actual probability law.
No condition on values of f off the scaled closure is imposed. -/
theorem density_dilation_finite (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)]
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    (∀ r : ℝ≥0∞, MemLp f r (scaledLaw b a J p)) ∧
    (∀ r : ℝ≥0∞, MemLp (fun Z => f (affine a J Z)) r (referenceLaw b p)) ∧
    MemLp (rectangleOrdinaryGradient f) 2 (scaledLaw b a J p) ∧
    MemLp (rectangleOrdinaryGradient (fun Z => f (affine a J Z))) 2 (referenceLaw b p) ∧
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (scaledLaw b a J p) := by
  let := scaledLaw_probability b a hJ p
  have hac : scaledLaw b a J p ≪ scaledLebesgue b a J := withDensity_absolutelyContinuous _ _
  have hac₀ : referenceLaw b p ≪ referenceMeasure b := withDensity_absolutelyContinuous _ _
  have hmem (r : ℝ≥0∞) : MemLp f r (scaledLaw b a J p) :=
    memLp_scaled_of_absolutelyContinuous hJ hac hf r
  refine ⟨hmem, ?_, memLp_gradient_scaled_of_absolutelyContinuous hJ hac hf 2,
    memLp_gradient_pullback hJ hac₀ hf, ?_⟩
  · intro r
    apply (memLp_transport_iff a hJ.ne' (referenceLaw b p) f r).mpr
    simpa only [transport_referenceLaw b a hJ p] using hmem r
  · exact integrable_continuous_comp_scaled (ν := scaledLaw b a J p)
      (f := f) (Φ := fun t : ℝ ↦ t ^ 2 * Real.log (t ^ 2)) hJ hac hf
      (Real.continuous_mul_log.comp (continuous_id.pow 2))

theorem density_dilation_mean (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p f : PlanarSpace → ℝ) :
    (∫ Z, f (affine a J Z) ∂referenceLaw b p) = ∫ x, f x ∂scaledLaw b a J p := by
  rw [← transport_referenceLaw b a hJ p]
  exact integral_transport a hJ.ne' _ f

theorem density_dilation_entropy (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p f : PlanarSpace → ℝ) :
    entropy (referenceLaw b p) (fun Z => f (affine a J Z) ^ 2) =
      entropy (scaledLaw b a J p) (fun x => f x ^ 2) := by
  rw [← transport_referenceLaw b a hJ p]
  exact entropy_transport a hJ.ne' (referenceLaw b p) (fun x ↦ f x ^ 2)

theorem density_dilation_energy (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)]
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    (∫ Z, ‖rectangleOrdinaryGradient (fun W => f (affine a J W)) Z‖ ^ 2 ∂referenceLaw b p) =
      (J ^ 2)⁻¹ * ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂scaledLaw b a J p := by
  rw [← transport_referenceLaw b a hJ p]
  exact integral_energy_pullback (μ := referenceLaw b p) hJ
    (withDensity_absolutelyContinuous _ _) hf

theorem density_dilation_gradient_norm (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    lpNorm (rectangleOrdinaryGradient (fun W => f (affine a J W))) 2 (referenceLaw b p) =
      J⁻¹ * lpNorm (rectangleOrdinaryGradient f) 2 (scaledLaw b a J p) := by
  rw [← transport_referenceLaw b a hJ p]
  exact lpNorm_gradient_pullback hJ (withDensity_absolutelyContinuous _ _) hf 2

/-- Generic transport of an already proved reference Poincaré inequality.
The inequality hypothesis is the input being transported, not a density theorem. -/
theorem transport_poincare (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)] (C : ℝ)
    (hPI : ∀ (u : PlanarSpace → ℝ) (L : ℝ≥0), LipschitzOnWith L u (closed b) →
      ProbabilityTheory.variance u (referenceLaw b p) ≤
        C * ∫ Z, ‖rectangleOrdinaryGradient u Z‖ ^ 2 ∂referenceLaw b p)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    ProbabilityTheory.variance f (scaledLaw b a J p) ≤
      (C / J ^ 2) * ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂scaledLaw b a J p := by
  have h := hPI (fun Z => f (affine a J Z)) (K * ‖J⁻¹‖₊)
    (lipschitzOnWith_pullback b a J hf)
  rw [variance_transport a hJ.ne' (referenceLaw b p) f,
    transport_referenceLaw b a hJ p, density_dilation_energy b a hJ p hf] at h
  simpa only [div_eq_mul_inv, mul_assoc] using h

/-- Generic transport of an already proved reference entropy inequality,
using the actual extended entropy and the actual Riesz energy. -/
theorem transport_logSobolev (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)] (C : ℝ)
    (hLSI : ∀ (u : PlanarSpace → ℝ) (L : ℝ≥0), LipschitzOnWith L u (closed b) →
      entropy (referenceLaw b p) (fun Z => u Z ^ 2) ≤
        ((C * ∫ Z, ‖rectangleOrdinaryGradient u Z‖ ^ 2 ∂referenceLaw b p : ℝ) : EReal))
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    entropy (scaledLaw b a J p) (fun x => f x ^ 2) ≤
      (((C / J ^ 2) * ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂scaledLaw b a J p : ℝ) : EReal) := by
  have h := hLSI (fun Z => f (affine a J Z)) (K * ‖J⁻¹‖₊)
    (lipschitzOnWith_pullback b a J hf)
  rw [density_dilation_entropy b a hJ p f, density_dilation_energy b a hJ p hf] at h
  simpa only [div_eq_mul_inv, mul_assoc] using h

/-- Generic transport of an already proved finite moment inequality.
The exponent remains an arbitrary finite real s≥2; there is no integer restriction. -/
theorem transport_moment (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)] (C : ℝ)
    {s : ℝ} (_hs : 2 ≤ s)
    (hMoment : ∀ (u : PlanarSpace → ℝ) (L : ℝ≥0), LipschitzOnWith L u (closed b) →
      lpNorm (fun Z => u Z - ∫ W, u W ∂referenceLaw b p) (ENNReal.ofReal s) (referenceLaw b p) ≤
        C * lpNorm (rectangleOrdinaryGradient u) 2 (referenceLaw b p))
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (scaledClosed b a J)) :
    lpNorm (fun x => f x - ∫ y, f y ∂scaledLaw b a J p) (ENNReal.ofReal s) (scaledLaw b a J p) ≤
      (C / J) * lpNorm (rectangleOrdinaryGradient f) 2 (scaledLaw b a J p) := by
  have h := hMoment (fun Z => f (affine a J Z)) (K * ‖J⁻¹‖₊)
    (lipschitzOnWith_pullback b a J hf)
  rw [centered_lpNorm_transport a hJ.ne' (referenceLaw b p) f,
    transport_referenceLaw b a hJ p, density_dilation_gradient_norm b a hJ p hf] at h
  simpa only [div_eq_mul_inv, mul_assoc] using h

end PeriodicAttractiveLogGas.RectangleDilation
