import LeanResearch.PeriodicAttractiveLogGas.RectangleSobolev
import LeanResearch.PeriodicAttractiveLogGas.Entropy
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.Variance

/-! The rectangle orientation step in source
lines 372–386 and the last sentence of Lemma 3.2. The actual map here is the
coordinate swap, an orientation-reversing linear isometry. It maps the
horizontal double rectangle exactly to the vertical one, even for the
half-open boundary convention. It is not called a literal quarter-turn.
No dilation or mesh-cell file is imported. Independent source review and
protected acceptance have separate records. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace PeriodicAttractiveLogGas.RectangleRotation

def swapIndex : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

@[simp] theorem swapIndex_zero : swapIndex 0 = 1 := by simp [swapIndex]
@[simp] theorem swapIndex_one : swapIndex 1 = 0 := by simp [swapIndex]
@[simp] theorem swapIndex_swapIndex (j : Fin 2) : swapIndex (swapIndex j) = j := by
  simp [swapIndex]
@[simp] theorem swapIndex_symm : swapIndex.symm = swapIndex := by
  simp [swapIndex]

/-- A genuine linear isometry of Euclidean two-space, not the maximum-norm plane. -/
def coordinateSwap : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ swapIndex

@[simp] theorem coordinateSwap_apply (x : PlanarSpace) (j : Fin 2) :
    coordinateSwap x j = x (swapIndex j) := by
  simp [coordinateSwap, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', swapIndex_symm]

@[simp] theorem coordinateSwap_symm : coordinateSwap.symm = coordinateSwap := by
  simp [coordinateSwap, LinearIsometryEquiv.piLpCongrLeft_symm]

@[simp] theorem coordinateSwap_involutive (x : PlanarSpace) :
    coordinateSwap (coordinateSwap x) = x := by
  ext j
  simp

@[simp] theorem norm_coordinateSwap (x : PlanarSpace) : ‖coordinateSwap x‖ = ‖x‖ :=
  coordinateSwap.norm_map x

theorem measurableEmbedding_coordinateSwap : MeasurableEmbedding coordinateSwap :=
  coordinateSwap.toMeasurableEquiv.measurableEmbedding

theorem measurePreserving_coordinateSwap :
    MeasurePreserving coordinateSwap (volume : Measure PlanarSpace) volume :=
  coordinateSwap.measurePreserving

theorem map_volume_coordinateSwap : (volume : Measure PlanarSpace).map coordinateSwap = volume :=
  measurePreserving_coordinateSwap.map_eq

theorem coordinateSwap_affine (a Z : PlanarSpace) (c : ℝ) :
    coordinateSwap (a + c • Z) = coordinateSwap a + c • coordinateSwap Z := by
  simp only [map_add, map_smul]

theorem volume_image_coordinateSwap (s : Set PlanarSpace) :
    volume (coordinateSwap '' s) = volume s := by
  have h := measurableEmbedding_coordinateSwap.map_apply (volume : Measure PlanarSpace)
    (coordinateSwap '' s)
  rw [map_volume_coordinateSwap, coordinateSwap.injective.preimage_image] at h
  exact h

theorem map_restrict_volume_coordinateSwap (s : Set PlanarSpace) :
    (volume.restrict s).map coordinateSwap = volume.restrict (coordinateSwap '' s) := by
  have h := measurableEmbedding_coordinateSwap.restrict_map (volume : Measure PlanarSpace)
    (coordinateSwap '' s)
  rw [map_volume_coordinateSwap, coordinateSwap.injective.preimage_image] at h
  exact h.symm

/-- This measure identity also applies to translated/scaled sets. It makes no
probability assertion for a zero-volume or infinite-volume set. -/
theorem map_normalized_restrict_coordinateSwap (s : Set PlanarSpace) :
    ((volume s)⁻¹ • volume.restrict s).map coordinateSwap =
      (volume (coordinateSwap '' s))⁻¹ • volume.restrict (coordinateSwap '' s) := by
  rw [Measure.map_smul _ coordinateSwap.continuous.measurable.aemeasurable,
    map_restrict_volume_coordinateSwap, volume_image_coordinateSwap]

def verticalWidth (j : Fin 2) : ℝ := doubleRectangleWidth (swapIndex j)

@[simp] theorem verticalWidth_zero : verticalWidth 0 = 1 := by
  norm_num [verticalWidth, doubleRectangleWidth]
@[simp] theorem verticalWidth_one : verticalWidth 1 = 2 := by
  norm_num [verticalWidth, doubleRectangleWidth]

def closedVerticalRectangle : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j => Icc (0 : ℝ) (verticalWidth j))
def openVerticalRectangle : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j => Ioo (0 : ℝ) (verticalWidth j))
def halfOpenHorizontalRectangle : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j => Ico (0 : ℝ) (doubleRectangleWidth j))
def halfOpenVerticalRectangle : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j => Ico (0 : ℝ) (verticalWidth j))
def halfOpenSquare : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin 2 => Ico (0 : ℝ) 1)

def verticalLebesgue : Measure PlanarSpace :=
  ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict closedVerticalRectangle

theorem measurableSet_closedVerticalRectangle : MeasurableSet closedVerticalRectangle :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Icc).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).measurable

theorem measurableSet_openVerticalRectangle : MeasurableSet openVerticalRectangle :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).measurable

theorem isCompact_closedVerticalRectangle : IsCompact closedVerticalRectangle :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem closedVerticalRectangle_mem_nhds {x : PlanarSpace} (hx : x ∈ openVerticalRectangle) :
    closedVerticalRectangle ∈ 𝓝 x :=
  (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).continuousAt.preimage_mem_nhds
    (set_pi_mem_nhds Set.finite_univ fun j _ =>
      Icc_mem_nhds (hx j (mem_univ j)).1 (hx j (mem_univ j)).2)

theorem coordinateSwap_mem_closedSquare_iff (x : PlanarSpace) :
    coordinateSwap x ∈ closedUnitSquare ↔ x ∈ closedUnitSquare := by
  constructor
  · intro hx j hj
    simpa only [coordinateSwap_apply, swapIndex_swapIndex] using hx (swapIndex j) (mem_univ _)
  · intro hx j hj
    simpa only [coordinateSwap_apply] using hx (swapIndex j) (mem_univ _)

theorem coordinateSwap_mem_halfOpenSquare_iff (x : PlanarSpace) :
    coordinateSwap x ∈ halfOpenSquare ↔ x ∈ halfOpenSquare := by
  constructor
  · intro hx j hj
    simpa only [coordinateSwap_apply, swapIndex_swapIndex] using hx (swapIndex j) (mem_univ _)
  · intro hx j hj
    simpa only [coordinateSwap_apply] using hx (swapIndex j) (mem_univ _)

theorem coordinateSwap_mem_closedVertical_iff (x : PlanarSpace) :
    coordinateSwap x ∈ closedVerticalRectangle ↔ x ∈ closedDoubleRectangle := by
  constructor
  · intro hx j hj
    simpa only [coordinateSwap_apply, verticalWidth, swapIndex_swapIndex] using
      hx (swapIndex j) (mem_univ _)
  · intro hx j hj
    simpa only [coordinateSwap_apply, verticalWidth] using hx (swapIndex j) (mem_univ _)

theorem coordinateSwap_mem_openVertical_iff (x : PlanarSpace) :
    coordinateSwap x ∈ openVerticalRectangle ↔ x ∈ openDoubleRectangle := by
  constructor
  · intro hx j hj
    simpa only [coordinateSwap_apply, verticalWidth, swapIndex_swapIndex] using
      hx (swapIndex j) (mem_univ _)
  · intro hx j hj
    simpa only [coordinateSwap_apply, verticalWidth] using hx (swapIndex j) (mem_univ _)

theorem coordinateSwap_mem_halfOpenVertical_iff (x : PlanarSpace) :
    coordinateSwap x ∈ halfOpenVerticalRectangle ↔ x ∈ halfOpenHorizontalRectangle := by
  constructor
  · intro hx j hj
    simpa only [coordinateSwap_apply, verticalWidth, swapIndex_swapIndex] using
      hx (swapIndex j) (mem_univ _)
  · intro hx j hj
    simpa only [coordinateSwap_apply, verticalWidth] using hx (swapIndex j) (mem_univ _)

theorem preimage_coordinateSwap_closedSquare :
    coordinateSwap ⁻¹' closedUnitSquare = closedUnitSquare := by
  ext x
  exact coordinateSwap_mem_closedSquare_iff x

theorem preimage_coordinateSwap_closedVertical :
    coordinateSwap ⁻¹' closedVerticalRectangle = closedDoubleRectangle := by
  ext x
  exact coordinateSwap_mem_closedVertical_iff x

theorem image_coordinateSwap_closedSquare : coordinateSwap '' closedUnitSquare = closedUnitSquare := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (coordinateSwap_mem_closedSquare_iff y).mpr hy
  · intro hx
    exact ⟨coordinateSwap x, (coordinateSwap_mem_closedSquare_iff x).mpr hx,
      coordinateSwap_involutive x⟩

theorem image_coordinateSwap_closedHorizontal :
    coordinateSwap '' closedDoubleRectangle = closedVerticalRectangle := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (coordinateSwap_mem_closedVertical_iff y).mpr hy
  · intro hx
    refine ⟨coordinateSwap x, ?_, coordinateSwap_involutive x⟩
    exact (coordinateSwap_mem_closedVertical_iff (coordinateSwap x)).mp (by simpa using hx)

theorem image_coordinateSwap_halfOpenHorizontal :
    coordinateSwap '' halfOpenHorizontalRectangle = halfOpenVerticalRectangle := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (coordinateSwap_mem_halfOpenVertical_iff y).mpr hy
  · intro hx
    refine ⟨coordinateSwap x, ?_, coordinateSwap_involutive x⟩
    exact (coordinateSwap_mem_halfOpenVertical_iff (coordinateSwap x)).mp (by simpa using hx)

theorem measurePreserving_swap_restrict_horizontal :
    MeasurePreserving coordinateSwap (volume.restrict closedDoubleRectangle)
      (volume.restrict closedVerticalRectangle) := by
  simpa only [preimage_coordinateSwap_closedVertical] using
    measurePreserving_coordinateSwap.restrict_preimage measurableSet_closedVerticalRectangle

theorem measurePreserving_swap_square :
    MeasurePreserving coordinateSwap squareLebesgue squareLebesgue := by
  simpa only [preimage_coordinateSwap_closedSquare, squareLebesgue] using
    measurePreserving_coordinateSwap.restrict_preimage measurableSet_closedUnitSquare

theorem measurePreserving_swap_horizontal :
    MeasurePreserving coordinateSwap rectangleLebesgue verticalLebesgue := by
  exact measurePreserving_swap_restrict_horizontal.smul_measure (ENNReal.ofReal (1 / 2 : ℝ))

theorem volume_closedVerticalRectangle : volume closedVerticalRectangle = 2 := by
  have h := congrArg (fun μ : Measure PlanarSpace => μ Set.univ)
    measurePreserving_swap_restrict_horizontal.map_eq
  simpa only [Measure.map_apply coordinateSwap.continuous.measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ, volume_closedDoubleRectangle] using h.symm

instance verticalLebesgue_probability : IsProbabilityMeasure verticalLebesgue := by
  constructor
  rw [← measurePreserving_swap_horizontal.map_eq,
    Measure.map_apply coordinateSwap.continuous.measurable MeasurableSet.univ]
  simp

theorem verticalLebesgue_eq_normalized :
    verticalLebesgue = (volume closedVerticalRectangle)⁻¹ • volume.restrict closedVerticalRectangle := by
  rw [volume_closedVerticalRectangle]
  unfold verticalLebesgue
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem volume_restrict_halfOpenVertical_eq_closed :
    volume.restrict halfOpenVerticalRectangle = volume.restrict closedVerticalRectangle :=
  volume_restrict_halfOpenRectangle_eq_closed verticalWidth

theorem verticalLebesgue_eq_normalized_halfOpen :
    verticalLebesgue = (volume halfOpenVerticalRectangle)⁻¹ •
      volume.restrict halfOpenVerticalRectangle := by
  have hv := congrArg (fun μ : Measure PlanarSpace => μ Set.univ)
    volume_restrict_halfOpenVertical_eq_closed
  simp only [Measure.restrict_apply_univ] at hv
  rw [hv, volume_restrict_halfOpenVertical_eq_closed]
  exact verticalLebesgue_eq_normalized

theorem ae_mem_openVerticalRectangle : ∀ᵐ x ∂verticalLebesgue, x ∈ openVerticalRectangle := by
  rw [← measurePreserving_swap_horizontal.map_eq, measurableEmbedding_coordinateSwap.ae_map_iff]
  exact ae_mem_openDoubleRectangle.mono fun x hx => (coordinateSwap_mem_openVertical_iff x).mpr hx

theorem ae_mem_closedVerticalRectangle : ∀ᵐ x ∂verticalLebesgue, x ∈ closedVerticalRectangle :=
  ae_mem_openVerticalRectangle.mono fun _ hx => mem_of_mem_nhds (closedVerticalRectangle_mem_nhds hx)

def swapLaw (μ : Measure PlanarSpace) : Measure PlanarSpace := μ.map coordinateSwap

theorem measurePreserving_swapLaw (μ : Measure PlanarSpace) :
    MeasurePreserving coordinateSwap μ (swapLaw μ) := ⟨coordinateSwap.continuous.measurable, rfl⟩

instance swapLaw_probability (μ : Measure PlanarSpace) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (swapLaw μ) := by
  constructor
  simp [swapLaw, Measure.map_apply coordinateSwap.continuous.measurable]

theorem integral_swapLaw (μ : Measure PlanarSpace) (f : PlanarSpace → ℝ) :
    (∫ Z, f (coordinateSwap Z) ∂μ) = ∫ x, f x ∂swapLaw μ :=
  (measurePreserving_swapLaw μ).integral_comp measurableEmbedding_coordinateSwap f

theorem eLpNorm_swapLaw {E : Type*} [NormedAddCommGroup E]
    (μ : Measure PlanarSpace) (f : PlanarSpace → E) (p : ℝ≥0∞) :
    eLpNorm (fun Z => f (coordinateSwap Z)) p μ = eLpNorm f p (swapLaw μ) :=
  (measurableEmbedding_coordinateSwap.eLpNorm_map_measure (μ := μ) (g := f) (p := p)).symm

theorem lpNorm_swapLaw {E : Type*} [NormedAddCommGroup E]
    (μ : Measure PlanarSpace) (f : PlanarSpace → E) (p : ℝ≥0∞) :
    lpNorm (fun Z => f (coordinateSwap Z)) p μ = lpNorm f p (swapLaw μ) :=
  congrArg ENNReal.toReal (eLpNorm_swapLaw μ f p)

theorem memLp_swapLaw_iff {E : Type*} [NormedAddCommGroup E]
    (μ : Measure PlanarSpace) (f : PlanarSpace → E) (p : ℝ≥0∞) :
    MemLp (fun Z => f (coordinateSwap Z)) p μ ↔ MemLp f p (swapLaw μ) :=
  measurableEmbedding_coordinateSwap.memLp_map_measure_iff.symm

/-- Exact extended entropy transport, including a positive-infinite value. -/
theorem entropy_swapLaw (μ : Measure PlanarSpace) (F : PlanarSpace → ℝ) :
    entropy μ (fun Z => F (coordinateSwap Z)) = entropy (swapLaw μ) F := by
  have hm : (swapLaw μ).real Set.univ = μ.real Set.univ := by
    simp [swapLaw, measureReal_def, Measure.map_apply coordinateSwap.continuous.measurable]
  unfold entropy
  rw [(measurePreserving_swapLaw μ).lintegral_comp_emb measurableEmbedding_coordinateSwap
    (fun x => ENNReal.ofReal (entropyDensity (F x))), integral_swapLaw μ F, hm]

theorem variance_swapLaw (μ : Measure PlanarSpace) (f : PlanarSpace → ℝ) :
    ProbabilityTheory.variance (fun Z => f (coordinateSwap Z)) μ =
      ProbabilityTheory.variance f (swapLaw μ) :=
  (ProbabilityTheory.variance_map_equiv f coordinateSwap.toMeasurableEquiv).symm

theorem centered_lpNorm_swapLaw (μ : Measure PlanarSpace) (f : PlanarSpace → ℝ) (p : ℝ≥0∞) :
    lpNorm (fun Z => f (coordinateSwap Z) - ∫ W, f (coordinateSwap W) ∂μ) p μ =
      lpNorm (fun x => f x - ∫ y, f y ∂swapLaw μ) p (swapLaw μ) := by
  rw [integral_swapLaw μ f]
  exact lpNorm_swapLaw μ (fun x ↦ f x - ∫ y, f y ∂swapLaw μ) p

def horizontalLaw (p : PlanarSpace → ℝ) : Measure PlanarSpace :=
  rectangleLebesgue.withDensity (fun Z => ENNReal.ofReal (p Z))

def verticalLaw (p : PlanarSpace → ℝ) : Measure PlanarSpace :=
  verticalLebesgue.withDensity (fun x => ENNReal.ofReal (p (coordinateSwap x)))

theorem swapLaw_horizontalLaw (p : PlanarSpace → ℝ) :
    swapLaw (horizontalLaw p) = verticalLaw p := by
  apply Measure.ext
  intro s hs
  rw [swapLaw, Measure.map_apply coordinateSwap.continuous.measurable hs,
    horizontalLaw, withDensity_apply _ (coordinateSwap.continuous.measurable hs),
    verticalLaw, withDensity_apply _ hs]
  simpa only [coordinateSwap_involutive] using
    measurePreserving_swap_horizontal.setLIntegral_comp_preimage_emb
      measurableEmbedding_coordinateSwap (fun x => ENNReal.ofReal (p (coordinateSwap x))) s

theorem verticalLaw_probability (p : PlanarSpace → ℝ) [IsProbabilityMeasure (horizontalLaw p)] :
    IsProbabilityMeasure (verticalLaw p) := by
  rw [← swapLaw_horizontalLaw]
  infer_instance

theorem density_lower_iff (p : PlanarSpace → ℝ) (c : ℝ) :
    (∀ᵐ x ∂verticalLebesgue, c ≤ p (coordinateSwap x)) ↔ ∀ᵐ Z ∂rectangleLebesgue, c ≤ p Z := by
  rw [← measurePreserving_swap_horizontal.map_eq, measurableEmbedding_coordinateSwap.ae_map_iff]
  simp only [coordinateSwap_involutive]

theorem density_memLp_iff (p : PlanarSpace → ℝ) (q : ℝ≥0∞) :
    MemLp (fun x => p (coordinateSwap x)) q verticalLebesgue ↔ MemLp p q rectangleLebesgue := by
  rw [← measurePreserving_swap_horizontal.map_eq,
    measurableEmbedding_coordinateSwap.memLp_map_measure_iff]
  simp only [Function.comp_def, coordinateSwap_involutive]

theorem density_lpNorm (p : PlanarSpace → ℝ) (q : ℝ≥0∞) :
    lpNorm (fun x => p (coordinateSwap x)) q verticalLebesgue = lpNorm p q rectangleLebesgue := by
  have he := lpNorm_swapLaw rectangleLebesgue (fun x => p (coordinateSwap x)) q
  simpa only [swapLaw, measurePreserving_swap_horizontal.map_eq, coordinateSwap_involutive] using he.symm

theorem swapLaw_absolutelyContinuous_vertical {μ : Measure PlanarSpace}
    (hμ : μ ≪ rectangleLebesgue) : swapLaw μ ≪ verticalLebesgue := by
  simpa only [swapLaw, measurePreserving_swap_horizontal.map_eq] using
    measurableEmbedding_coordinateSwap.absolutelyContinuous_map hμ

theorem swapLaw_absolutelyContinuous_square {μ : Measure PlanarSpace}
    (hμ : μ ≪ squareLebesgue) : swapLaw μ ≪ squareLebesgue := by
  simpa only [swapLaw, measurePreserving_swap_square.map_eq] using
    measurableEmbedding_coordinateSwap.absolutelyContinuous_map hμ

theorem lipschitzOnWith_verticalPullback {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) :
    LipschitzOnWith K (fun Z => f (coordinateSwap Z)) closedDoubleRectangle := by
  simpa only [mul_one, Function.comp_def] using! hf.comp coordinateSwap.lipschitz.lipschitzOnWith
    (fun Z hZ => (coordinateSwap_mem_closedVertical_iff Z).mpr hZ)

theorem lipschitzOnWith_squarePullback {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedUnitSquare) :
    LipschitzOnWith K (fun Z => f (coordinateSwap Z)) closedUnitSquare := by
  simpa only [mul_one, Function.comp_def] using! hf.comp coordinateSwap.lipschitz.lipschitzOnWith
    (fun Z hZ => (coordinateSwap_mem_closedSquare_iff Z).mpr hZ)

/-- Ordinary differentiability follows from Rademacher and the actual null boundary. -/
theorem ae_differentiableAt_vertical {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) :
    ∀ᵐ x ∂verticalLebesgue, DifferentiableAt ℝ f x := by
  have hd : ∀ᵐ x ∂verticalLebesgue, DifferentiableWithinAt ℝ f closedVerticalRectangle x :=
    Measure.ae_smul_measure
      (hf.ae_differentiableWithinAt (μ := volume) measurableSet_closedVerticalRectangle) _
  filter_upwards [hd, ae_mem_openVerticalRectangle] with x hx hi
  exact hx.differentiableAt (closedVerticalRectangle_mem_nhds hi)

theorem ae_norm_gradient_vertical_le {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) :
    ∀ᵐ x ∂verticalLebesgue, ‖rectangleOrdinaryGradient f x‖ ≤ K := by
  filter_upwards [ae_mem_openVerticalRectangle] with x hx
  rw [norm_rectangleOrdinaryGradient]
  exact norm_fderiv_le_of_lipschitzOn ℝ (closedVerticalRectangle_mem_nhds hx) hf

theorem aestronglyMeasurable_vertical {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) :
    AEStronglyMeasurable f verticalLebesgue :=
  (hf.continuousOn.aestronglyMeasurable measurableSet_closedVerticalRectangle).smul_measure _

theorem memLp_vertical_of_absolutelyContinuous {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ verticalLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) (p : ℝ≥0∞) : MemLp f p ν := by
  obtain ⟨C, hC⟩ := isCompact_closedVerticalRectangle.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound ((aestronglyMeasurable_vertical hf).mono_ac hν) C
  filter_upwards [hν.ae_le ae_mem_closedVerticalRectangle] with x hx
  exact hC x hx

theorem memLp_centered_vertical_of_absolutelyContinuous {ν : Measure PlanarSpace}
    [IsProbabilityMeasure ν] (hν : ν ≪ verticalLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) (p : ℝ≥0∞) :
    MemLp (fun x => f x - ∫ y, f y ∂ν) p ν := by
  exact (memLp_vertical_of_absolutelyContinuous hν hf p).sub (memLp_const _)

theorem memLp_gradient_vertical_of_absolutelyContinuous {ν : Measure PlanarSpace}
    [IsProbabilityMeasure ν] (hν : ν ≪ verticalLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) (p : ℝ≥0∞) :
    MemLp (rectangleOrdinaryGradient f) p ν :=
  MemLp.of_bound (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable K
    (hν.ae_le (ae_norm_gradient_vertical_le hf))

theorem hasFDerivAt_coordinateSwap (x : PlanarSpace) :
    HasFDerivAt coordinateSwap coordinateSwap.toLinearIsometry.toContinuousLinearMap x :=
  coordinateSwap.toLinearIsometry.toContinuousLinearMap.hasFDerivAt

theorem fderiv_swap {f : PlanarSpace → ℝ} {Z : PlanarSpace}
    (hf : DifferentiableAt ℝ f (coordinateSwap Z)) :
    fderiv ℝ (fun W => f (coordinateSwap W)) Z =
      (fderiv ℝ f (coordinateSwap Z)).comp coordinateSwap.toLinearIsometry.toContinuousLinearMap :=
  (hf.hasFDerivAt.comp Z (hasFDerivAt_coordinateSwap Z)).fderiv

/-- The adjoint of this orthogonal involution is the same coordinate swap. -/
theorem gradient_swap {f : PlanarSpace → ℝ} {Z : PlanarSpace}
    (hf : DifferentiableAt ℝ f (coordinateSwap Z)) :
    rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) Z =
      coordinateSwap (rectangleOrdinaryGradient f (coordinateSwap Z)) := by
  apply (InnerProductSpace.toDual ℝ PlanarSpace).injective
  unfold rectangleOrdinaryGradient
  rw [(InnerProductSpace.toDual ℝ PlanarSpace).apply_symm_apply, fderiv_swap hf]
  ext v
  change fderiv ℝ f (coordinateSwap Z) (coordinateSwap v) =
    inner ℝ (coordinateSwap ((InnerProductSpace.toDual ℝ PlanarSpace).symm
      (fderiv ℝ f (coordinateSwap Z)))) v
  rw [coordinateSwap.inner_map_eq_flip, coordinateSwap_symm, InnerProductSpace.toDual_symm_apply]

theorem ae_gradient_swap_of_ae_differentiable {μ : Measure PlanarSpace} {f : PlanarSpace → ℝ}
    (hf : ∀ᵐ x ∂swapLaw μ, DifferentiableAt ℝ f x) :
    rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) =ᵐ[μ]
      fun Z => coordinateSwap (rectangleOrdinaryGradient f (coordinateSwap Z)) :=
  (measurableEmbedding_coordinateSwap.ae_map_iff.mp hf).mono fun _ hZ => gradient_swap hZ

theorem ae_gradient_swap_vertical {μ : Measure PlanarSpace} (hμ : μ ≪ rectangleLebesgue)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedVerticalRectangle) :
    rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) =ᵐ[μ]
      fun Z => coordinateSwap (rectangleOrdinaryGradient f (coordinateSwap Z)) :=
  ae_gradient_swap_of_ae_differentiable
    ((swapLaw_absolutelyContinuous_vertical hμ).ae_le (ae_differentiableAt_vertical hf))

theorem ae_gradient_swap_square {μ : Measure PlanarSpace} (hμ : μ ≪ squareLebesgue)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedUnitSquare) :
    rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) =ᵐ[μ]
      fun Z => coordinateSwap (rectangleOrdinaryGradient f (coordinateSwap Z)) :=
  ae_gradient_swap_of_ae_differentiable
    ((swapLaw_absolutelyContinuous_square hμ).ae_le (ae_differentiableAt_on_square hf))

theorem lpNorm_gradient_swap_of_ae_differentiable {μ : Measure PlanarSpace}
    {f : PlanarSpace → ℝ} (hf : ∀ᵐ x ∂swapLaw μ, DifferentiableAt ℝ f x) (p : ℝ≥0∞) :
    lpNorm (rectangleOrdinaryGradient (fun W => f (coordinateSwap W))) p μ =
      lpNorm (rectangleOrdinaryGradient f) p (swapLaw μ) := by
  have hn : ∀ᵐ Z ∂μ, ‖rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) Z‖ =
      ‖rectangleOrdinaryGradient f (coordinateSwap Z)‖ :=
    (ae_gradient_swap_of_ae_differentiable hf).mono fun Z hZ => by
      rw [hZ, norm_coordinateSwap]
  have he := eLpNorm_congr_norm_ae (p := p)
    (measurable_rectangleOrdinaryGradient _).aestronglyMeasurable
    ((measurable_rectangleOrdinaryGradient f).comp coordinateSwap.continuous.measurable).aestronglyMeasurable hn
  exact (congrArg ENNReal.toReal he).trans (lpNorm_swapLaw μ (rectangleOrdinaryGradient f) p)

theorem integral_energy_swap_of_ae_differentiable {μ : Measure PlanarSpace}
    {f : PlanarSpace → ℝ} (hf : ∀ᵐ x ∂swapLaw μ, DifferentiableAt ℝ f x) :
    (∫ Z, ‖rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) Z‖ ^ 2 ∂μ) =
      ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂swapLaw μ := by
  calc
    _ = ∫ Z, ‖rectangleOrdinaryGradient f (coordinateSwap Z)‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_gradient_swap_of_ae_differentiable hf] with Z hZ
      rw [hZ, norm_coordinateSwap]
    _ = _ := integral_swapLaw μ (fun x ↦ ‖rectangleOrdinaryGradient f x‖ ^ 2)

theorem lpNorm_gradient_swap_vertical {μ : Measure PlanarSpace} (hμ : μ ≪ rectangleLebesgue)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedVerticalRectangle)
    (p : ℝ≥0∞) :
    lpNorm (rectangleOrdinaryGradient (fun W => f (coordinateSwap W))) p μ =
      lpNorm (rectangleOrdinaryGradient f) p (swapLaw μ) :=
  lpNorm_gradient_swap_of_ae_differentiable
    ((swapLaw_absolutelyContinuous_vertical hμ).ae_le (ae_differentiableAt_vertical hf)) p

theorem integral_energy_swap_vertical {μ : Measure PlanarSpace} (hμ : μ ≪ rectangleLebesgue)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedVerticalRectangle) :
    (∫ Z, ‖rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) Z‖ ^ 2 ∂μ) =
      ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂swapLaw μ :=
  integral_energy_swap_of_ae_differentiable
    ((swapLaw_absolutelyContinuous_vertical hμ).ae_le (ae_differentiableAt_vertical hf))

theorem lpNorm_gradient_swap_square {μ : Measure PlanarSpace} (hμ : μ ≪ squareLebesgue)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedUnitSquare)
    (p : ℝ≥0∞) :
    lpNorm (rectangleOrdinaryGradient (fun W => f (coordinateSwap W))) p μ =
      lpNorm (rectangleOrdinaryGradient f) p (swapLaw μ) :=
  lpNorm_gradient_swap_of_ae_differentiable
    ((swapLaw_absolutelyContinuous_square hμ).ae_le (ae_differentiableAt_on_square hf)) p

theorem integral_energy_swap_square {μ : Measure PlanarSpace} (hμ : μ ≪ squareLebesgue)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedUnitSquare) :
    (∫ Z, ‖rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) Z‖ ^ 2 ∂μ) =
      ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂swapLaw μ :=
  integral_energy_swap_of_ae_differentiable
    ((swapLaw_absolutelyContinuous_square hμ).ae_le (ae_differentiableAt_on_square hf))

theorem memLp_gradient_verticalPullback {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≪ rectangleLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) (p : ℝ≥0∞) :
    MemLp (rectangleOrdinaryGradient (fun W => f (coordinateSwap W))) p μ := by
  have hm := memLp_gradient_vertical_of_absolutelyContinuous
    (swapLaw_absolutelyContinuous_vertical hμ) hf p
  have hc := (memLp_swapLaw_iff μ (rectangleOrdinaryGradient f) p).mpr hm
  apply hc.congr_norm (measurable_rectangleOrdinaryGradient _).aestronglyMeasurable
  filter_upwards [ae_gradient_swap_vertical hμ hf] with Z hZ
  rw [hZ, norm_coordinateSwap]

theorem integrable_continuous_comp_vertical {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ verticalLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Integrable (fun x => Φ (f x)) ν := by
  have hc := hΦ.comp_continuousOn hf.continuousOn
  obtain ⟨C, hC⟩ := isCompact_closedVerticalRectangle.exists_bound_of_continuousOn hc
  have hm : AEStronglyMeasurable (fun x => Φ (f x)) ν :=
    ((hc.aestronglyMeasurable measurableSet_closedVerticalRectangle).smul_measure
      (ENNReal.ofReal (1 / 2 : ℝ))).mono_ac hν
  have hl : MemLp (fun x => Φ (f x)) 1 ν := by
    apply MemLp.of_bound hm C
    filter_upwards [hν.ae_le ae_mem_closedVerticalRectangle] with x hx
    exact hC x hx
  exact hl.integrable le_rfl

theorem entropy_sq_eq_integral_vertical {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ verticalLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) :
    entropy ν (fun x => f x ^ 2) =
      ((∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂ν) -
        (∫ x, f x ^ 2 ∂ν) * Real.log (∫ x, f x ^ 2 ∂ν) : ℝ) := by
  apply entropy_eq_integral (Eventually.of_forall fun x => sq_nonneg (f x))
  exact integrable_continuous_comp_vertical hν hf
    (Real.continuous_mul_log.comp (continuous_id.pow 2))

/-- Finite value/centered norms and both actual energies. The hypotheses concern
only the vertical closure and the actual probability density law. -/
theorem vertical_lipschitz_finite (p : PlanarSpace → ℝ)
    [IsProbabilityMeasure (horizontalLaw p)] {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedVerticalRectangle) :
    (∀ r : ℝ≥0∞, MemLp f r (verticalLaw p)) ∧
    (∀ r : ℝ≥0∞, MemLp (fun x => f x - ∫ y, f y ∂verticalLaw p) r (verticalLaw p)) ∧
    (∀ r : ℝ≥0∞, MemLp (fun Z => f (coordinateSwap Z)) r (horizontalLaw p)) ∧
    Integrable (fun x => ‖rectangleOrdinaryGradient f x‖ ^ 2) (verticalLaw p) ∧
    Integrable (fun Z => ‖rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) Z‖ ^ 2)
      (horizontalLaw p) ∧
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (verticalLaw p) := by
  let := verticalLaw_probability p
  have hac : verticalLaw p ≪ verticalLebesgue := withDensity_absolutelyContinuous _ _
  have hac₀ : horizontalLaw p ≪ rectangleLebesgue := withDensity_absolutelyContinuous _ _
  have hmem (r : ℝ≥0∞) : MemLp f r (verticalLaw p) :=
    memLp_vertical_of_absolutelyContinuous hac hf r
  refine ⟨hmem, fun r => memLp_centered_vertical_of_absolutelyContinuous hac hf r, ?_, ?_, ?_, ?_⟩
  · intro r
    apply (memLp_swapLaw_iff (horizontalLaw p) f r).mpr
    simpa only [swapLaw_horizontalLaw] using hmem r
  · exact (memLp_two_iff_integrable_sq_norm
      (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable).mp
      (memLp_gradient_vertical_of_absolutelyContinuous hac hf 2)
  · exact (memLp_two_iff_integrable_sq_norm
      (measurable_rectangleOrdinaryGradient _).aestronglyMeasurable).mp
      (memLp_gradient_verticalPullback hac₀ hf 2)
  · exact integrable_continuous_comp_vertical (ν := verticalLaw p)
      (f := f) (Φ := fun t : ℝ ↦ t ^ 2 * Real.log (t ^ 2)) hac hf
      (Real.continuous_mul_log.comp (continuous_id.pow 2))

theorem memLp_square_of_absolutelyContinuous {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ squareLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedUnitSquare) (p : ℝ≥0∞) : MemLp f p ν := by
  obtain ⟨C, hC⟩ := isCompact_closedUnitSquare.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound ((aestronglyMeasurable_square hf).mono_ac hν) C
  filter_upwards [hν.ae_le (ae_restrict_mem measurableSet_closedUnitSquare)] with x hx
  exact hC x hx

theorem memLp_gradient_square_of_absolutelyContinuous {ν : Measure PlanarSpace}
    [IsProbabilityMeasure ν] (hν : ν ≪ squareLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedUnitSquare) (p : ℝ≥0∞) :
    MemLp (rectangleOrdinaryGradient f) p ν := by
  apply MemLp.of_bound (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable K
  filter_upwards [hν.ae_le (ae_norm_fderiv_on_square_le hf)] with x hx
  simpa only [norm_rectangleOrdinaryGradient] using hx

theorem integrable_continuous_comp_square {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ squareLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedUnitSquare) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Integrable (fun x => Φ (f x)) ν := by
  have hc := hΦ.comp_continuousOn hf.continuousOn
  obtain ⟨C, hC⟩ := isCompact_closedUnitSquare.exists_bound_of_continuousOn hc
  have hm : AEStronglyMeasurable (fun x => Φ (f x)) ν :=
    (hc.aestronglyMeasurable measurableSet_closedUnitSquare).mono_ac hν
  have hl : MemLp (fun x => Φ (f x)) 1 ν := by
    apply MemLp.of_bound hm C
    filter_upwards [hν.ae_le (ae_restrict_mem measurableSet_closedUnitSquare)] with x hx
    exact hC x hx
  exact hl.integrable le_rfl

theorem entropy_sq_eq_integral_square {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    (hν : ν ≪ squareLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedUnitSquare) :
    entropy ν (fun x => f x ^ 2) =
      ((∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂ν) -
        (∫ x, f x ^ 2 ∂ν) * Real.log (∫ x, f x ^ 2 ∂ν) : ℝ) := by
  apply entropy_eq_integral (Eventually.of_forall fun x => sq_nonneg (f x))
  exact integrable_continuous_comp_square hν hf
    (Real.continuous_mul_log.comp (continuous_id.pow 2))

theorem square_lipschitz_finite {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≪ squareLebesgue) {f : PlanarSpace → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f closedUnitSquare) :
    (∀ r : ℝ≥0∞, MemLp f r (swapLaw μ)) ∧
    (∀ r : ℝ≥0∞, MemLp (fun Z => f (coordinateSwap Z)) r μ) ∧
    Integrable (fun x => ‖rectangleOrdinaryGradient f x‖ ^ 2) (swapLaw μ) ∧
    Integrable (fun Z => ‖rectangleOrdinaryGradient (fun W => f (coordinateSwap W)) Z‖ ^ 2) μ := by
  have hac := swapLaw_absolutelyContinuous_square hμ
  have hmem (r : ℝ≥0∞) := memLp_square_of_absolutelyContinuous hac hf r
  refine ⟨hmem, fun r => (memLp_swapLaw_iff μ f r).mpr (hmem r), ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq_norm
      (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable).mp
      (memLp_gradient_square_of_absolutelyContinuous hac hf 2)
  · exact (memLp_two_iff_integrable_sq_norm
      (measurable_rectangleOrdinaryGradient _).aestronglyMeasurable).mp
      (memLp_gradient_square_of_absolutelyContinuous hμ (lipschitzOnWith_squarePullback hf) 2)

/-- Generic transport of a previously proved horizontal Poincaré inequality.
The coefficient is unchanged by this isometry. -/
theorem transport_poincare_vertical (p : PlanarSpace → ℝ)
    [IsProbabilityMeasure (horizontalLaw p)] (C : ℝ)
    (hPI : ∀ (u : PlanarSpace → ℝ) (L : ℝ≥0), LipschitzOnWith L u closedDoubleRectangle →
      ProbabilityTheory.variance u (horizontalLaw p) ≤
        C * ∫ Z, ‖rectangleOrdinaryGradient u Z‖ ^ 2 ∂horizontalLaw p)
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedVerticalRectangle) :
    ProbabilityTheory.variance f (verticalLaw p) ≤
      C * ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂verticalLaw p := by
  have h := hPI (fun Z => f (coordinateSwap Z)) K (lipschitzOnWith_verticalPullback hf)
  rw [variance_swapLaw, integral_energy_swap_vertical (μ := horizontalLaw p)
    (withDensity_absolutelyContinuous _ _) hf,
    swapLaw_horizontalLaw] at h
  exact h

/-- Generic transport of a previously proved horizontal entropy inequality. -/
theorem transport_logSobolev_vertical (p : PlanarSpace → ℝ)
    [IsProbabilityMeasure (horizontalLaw p)] (C : ℝ)
    (hLSI : ∀ (u : PlanarSpace → ℝ) (L : ℝ≥0), LipschitzOnWith L u closedDoubleRectangle →
      entropy (horizontalLaw p) (fun Z => u Z ^ 2) ≤
        ((C * ∫ Z, ‖rectangleOrdinaryGradient u Z‖ ^ 2 ∂horizontalLaw p : ℝ) : EReal))
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedVerticalRectangle) :
    entropy (verticalLaw p) (fun x => f x ^ 2) ≤
      ((C * ∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂verticalLaw p : ℝ) : EReal) := by
  have h := hLSI (fun Z => f (coordinateSwap Z)) K (lipschitzOnWith_verticalPullback hf)
  rw [entropy_swapLaw (horizontalLaw p) (fun x => f x ^ 2),
    integral_energy_swap_vertical (μ := horizontalLaw p) (withDensity_absolutelyContinuous _ _) hf,
    swapLaw_horizontalLaw] at h
  exact h

/-- Generic transport of a previously proved finite-real-exponent moment inequality. -/
theorem transport_moment_vertical (p : PlanarSpace → ℝ)
    [IsProbabilityMeasure (horizontalLaw p)] (C : ℝ) {s : ℝ} (_hs : 2 ≤ s)
    (hMoment : ∀ (u : PlanarSpace → ℝ) (L : ℝ≥0), LipschitzOnWith L u closedDoubleRectangle →
      lpNorm (fun Z => u Z - ∫ W, u W ∂horizontalLaw p) (ENNReal.ofReal s) (horizontalLaw p) ≤
        C * lpNorm (rectangleOrdinaryGradient u) 2 (horizontalLaw p))
    {f : PlanarSpace → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f closedVerticalRectangle) :
    lpNorm (fun x => f x - ∫ y, f y ∂verticalLaw p) (ENNReal.ofReal s) (verticalLaw p) ≤
      C * lpNorm (rectangleOrdinaryGradient f) 2 (verticalLaw p) := by
  have h := hMoment (fun Z => f (coordinateSwap Z)) K (lipschitzOnWith_verticalPullback hf)
  rw [centered_lpNorm_swapLaw, lpNorm_gradient_swap_vertical (μ := horizontalLaw p)
    (withDensity_absolutelyContinuous _ _) hf,
    swapLaw_horizontalLaw] at h
  exact h

end PeriodicAttractiveLogGas.RectangleRotation
