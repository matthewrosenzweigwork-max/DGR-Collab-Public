import LeanResearch.PeriodicAttractiveLogGas.CubeMaximal

/-! The weighted maximal argument on one selected cube. The actual A1
bound is integrated against the nonnegative input, before averaging.
Every measure factor divided out below is proved positive and finite. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.CubeMaximal
open PhysicalCubes WeightedCubeBounds
variable {ι : Type*} [Fintype ι]
variable {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)}

lemma triple_measure_pointwise (h : Bounds w A Z) (c : EuclideanSpace ℝ ι)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {y : EuclideanSpace ℝ ι} (hy : y ∈ openCube c ℓ) (hyZ : y ∉ Z) :
    weightedMeasure w (openCube c (3 * ℓ)) ≤
      ENNReal.ofReal (3 ^ Fintype.card ι * A) * volume (openCube c ℓ) * ENNReal.ofReal (w y) := by
  have hy3 : y ∈ cube c (3 * ℓ) := openCube_subset_cube c _ (openCube_mono c (by linarith) hy)
  have hh := (measure_mono (openCube_subset_cube c (3 * ℓ))).trans
    (h.measure_cube_le c (by positivity) hy3 hyZ)
  have hA : 0 ≤ A := zero_le_one.trans h.constant_ge_one
  apply hh.trans_eq
  rw [openCube_volume c hℓ.le, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ Fintype.card ι * A),
    ← ENNReal.ofReal_mul (by have := h.constant_ge_one; positivity)]
  congr 1
  rw [mul_pow]
  ring

lemma triple_measure_mul_average_le (h : Bounds w A Z) (c : EuclideanSpace ℝ ι)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f) :
    weightedMeasure w (openCube c (3 * ℓ)) * (⨍⁻ y in openCube c ℓ, f y ∂volume) ≤
      ENNReal.ofReal (3 ^ Fintype.card ι * A) * ∫⁻ y in openCube c ℓ, f y ∂weightedMeasure w := by
  let S := openCube c ℓ
  let M := weightedMeasure w (openCube c (3 * ℓ))
  let C := ENNReal.ofReal (3 ^ Fintype.card ι * A)
  have hs : MeasurableSet S := (isOpen_openCube c ℓ).measurableSet
  have hg : Measurable (fun y => ENNReal.ofReal (w y) * f y) := h.measurable.ennreal_ofReal.fun_mul hf
  have hpoint : ∀ᵐ y ∂volume.restrict S, M * f y ≤ (C * volume S) * (ENNReal.ofReal (w y) * f y) := by
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae (compl_mem_ae_iff.mpr h.exceptional_null)] with y hy hyZ
    have hh := mul_le_mul_of_nonneg_right (triple_measure_pointwise h c hℓ hy hyZ) (zero_le : 0 ≤ f y)
    simpa only [mul_assoc] using hh
  have hi : M * (∫⁻ y in S, f y) ≤ (C * volume S) * ∫⁻ y in S, f y ∂weightedMeasure w := by
    calc
      _ = ∫⁻ y in S, M * f y := (lintegral_const_mul M hf).symm
      _ ≤ ∫⁻ y in S, (C * volume S) * (ENNReal.ofReal (w y) * f y) := lintegral_mono_ae hpoint
      _ = (C * volume S) * ∫⁻ y in S, ENNReal.ofReal (w y) * f y := lintegral_const_mul _ hg
      _ = _ := by
        rw [weightedMeasure, setLIntegral_withDensity_eq_setLIntegral_mul volume h.measurable.ennreal_ofReal hf hs]
        rfl
  have hvol0 := (openCube_volume_pos c hℓ).ne'
  have hvoltop := openCube_volume_ne_top c hℓ.le
  change M * (⨍⁻ y in S, f y ∂volume) ≤ C * ∫⁻ y in S, f y ∂weightedMeasure w
  rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
  calc
    _ = (volume S)⁻¹ * (M * ∫⁻ y in S, f y) := by ac_rfl
    _ ≤ (volume S)⁻¹ * ((C * volume S) * ∫⁻ y in S, f y ∂weightedMeasure w) := by gcongr
    _ = _ := by
      rw [mul_assoc C, mul_left_comm C (volume S), ENNReal.inv_mul_cancel_left hvol0 hvoltop]

lemma selected_cube_bound (h : Bounds w A Z) (c : EuclideanSpace ℝ ι)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    {t : ℝ≥0∞} (ht : t < ⨍⁻ y in openCube c ℓ, f y ∂volume) :
    t * weightedMeasure w (openCube c (3 * ℓ)) ≤
      ENNReal.ofReal (3 ^ Fintype.card ι * A) * ∫⁻ y in openCube c ℓ, f y ∂weightedMeasure w := by
  calc
    _ ≤ (⨍⁻ y in openCube c ℓ, f y ∂volume) * weightedMeasure w (openCube c (3 * ℓ)) := by gcongr
    _ = _ := mul_comm _ _
    _ ≤ _ := triple_measure_mul_average_le h c hℓ hf

end PeriodicAttractiveLogGas.CubeMaximal
