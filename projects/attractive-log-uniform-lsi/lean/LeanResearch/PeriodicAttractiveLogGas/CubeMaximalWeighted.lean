import LeanResearch.PeriodicAttractiveLogGas.CubeMaximalLocal
import Mathlib.MeasureTheory.Measure.Regular

/-! The weighted weak maximal inequality in Appendix A. Actual compact
subsets of the open superlevel set are finitely covered; the greedy
triple-cube selection and the integrated A1 bound supply the sharp stated
covering factor. There is no assumed weak maximal estimate. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.CubeMaximal
open PhysicalCubes WeightedCubeBounds
variable {ι : Type*} [Fintype ι]
variable {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)}

lemma compact_superlevel_bound (h : Bounds w A Z) {f : EuclideanSpace ℝ ι → ℝ≥0∞}
    (hf : Measurable f) (t : ℝ≥0∞) {K : Set (EuclideanSpace ℝ ι)}
    (hK : IsCompact K) (hKt : K ⊆ {x | t < maximal f x}) :
    t * weightedMeasure w K ≤ ENNReal.ofReal (3 ^ Fintype.card ι * A) * ∫⁻ x, f x ∂weightedMeasure w := by
  classical
  let Q := {q : EuclideanSpace ℝ ι × ℝ // 0 < q.2 ∧
    t < ⨍⁻ y in openCube q.1 q.2, f y ∂volume}
  let c : Q → EuclideanSpace ℝ ι := fun q => q.val.1
  let ℓ : Q → ℝ := fun q => q.val.2
  have hcover : K ⊆ ⋃ q : Q, openCube (c q) (ℓ q) := by
    intro x hx
    obtain ⟨b, r, hr, hxr, havg⟩ := (lt_maximal_iff f x t).mp (hKt hx)
    exact mem_iUnion.mpr ⟨⟨(b, r), hr, havg⟩, hxr⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun q : Q => openCube (c q) (ℓ q))
    (fun q => isOpen_openCube (c q) (ℓ q)) hcover
  obtain ⟨a, has, hdis, htriple⟩ := finite_disjoint_triple_cover s c ℓ (fun q _ => q.property.1)
  have hsub : K ⊆ ⋃ q ∈ a, openCube (c q) (3 * ℓ q) := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hs hx)
    obtain ⟨j, hj, hqj⟩ := htriple q hq
    exact mem_iUnion₂.mpr ⟨j, hj, hqj hxq⟩
  have hmeasure := (measure_mono hsub).trans
    (measure_biUnion_finset_le (μ := weightedMeasure w) a (fun q => openCube (c q) (3 * ℓ q)))
  calc
    _ ≤ t * ∑ q ∈ a, weightedMeasure w (openCube (c q) (3 * ℓ q)) := by gcongr
    _ = ∑ q ∈ a, t * weightedMeasure w (openCube (c q) (3 * ℓ q)) := by rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ a, ENNReal.ofReal (3 ^ Fintype.card ι * A) *
        ∫⁻ y in openCube (c q) (ℓ q), f y ∂weightedMeasure w := by
      apply Finset.sum_le_sum
      intro q hq
      exact selected_cube_bound h (c q) q.property.1 hf q.property.2
    _ = ENNReal.ofReal (3 ^ Fintype.card ι * A) *
        ∫⁻ y in ⋃ q ∈ a, openCube (c q) (ℓ q), f y ∂weightedMeasure w := by
      rw [← Finset.mul_sum, lintegral_biUnion_finset hdis
        (fun q _ => (isOpen_openCube (c q) (ℓ q)).measurableSet)]
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self

/-- Weighted weak type (1,1) for the literal uncentered cube maximal function.
The lower integrals permit infinite values, so integrability is a consequence
when the right side is finite, rather than a premise of the operator theorem. -/
theorem weak_bound (h : Bounds w A Z) {f : EuclideanSpace ℝ ι → ℝ≥0∞}
    (hf : Measurable f) (t : ℝ≥0∞) :
    t * weightedMeasure w {x | t < maximal f x} ≤
      ENNReal.ofReal (3 ^ Fintype.card ι * A) * ∫⁻ x, f x ∂weightedMeasure w := by
  letI := h.locallyFinite
  have ho : IsOpen {x | t < maximal f x} := (lowerSemicontinuous_maximal f).isOpen_preimage t
  rw [ho.measure_eq_iSup_isCompact (weightedMeasure w)]
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun K => iSup_le fun hKt => iSup_le fun hK => ?_
  exact compact_superlevel_bound h hf t hK hKt

/-- Measurable representatives preserve all cube averages and the actual
weighted integral. This supplies the full almost-everywhere input class
needed for truncation and interpolation. -/
theorem weak_bound_ae (h : Bounds w A Z) {f : EuclideanSpace ℝ ι → ℝ≥0∞}
    (hf : AEMeasurable f (weightedMeasure w)) (t : ℝ≥0∞) :
    t * weightedMeasure w {x | t < maximal f x} ≤
      ENNReal.ofReal (3 ^ Fintype.card ι * A) * ∫⁻ x, f x ∂weightedMeasure w := by
  have he := hf.ae_eq_mk
  have hevol : f =ᵐ[volume] hf.mk f := h.volume_absolutelyContinuous.ae_le he
  rw [maximal_congr_ae hevol, lintegral_congr_ae he]
  exact weak_bound h hf.measurable_mk t

/-- Source strong L2 coefficient, obtained by its truncation and layer-cake
argument in the attributed local interpolation theorem. -/
theorem strong_two (h : Bounds w A Z) {f : EuclideanSpace ℝ ι → ℝ≥0∞}
    (hf : AEMeasurable f (weightedMeasure w)) :
    (∫⁻ x, maximal f x ^ 2 ∂weightedMeasure w) ≤
      ENNReal.ofReal (8 * 3 ^ Fintype.card ι * A) * ∫⁻ x, f x ^ 2 ∂weightedMeasure w := by
  have hadd (g v : EuclideanSpace ℝ ι → ℝ≥0∞) (hg : AEMeasurable g (weightedMeasure w))
      (hv : AEMeasurable v (weightedMeasure w)) : maximal (g + v) ≤ᵐ[weightedMeasure w] maximal g + maximal v :=
    Eventually.of_forall (maximal_add_le (hg.mono_ac h.volume_absolutelyContinuous)
      (hv.mono_ac h.volume_absolutelyContinuous))
  have hweak (g : EuclideanSpace ℝ ι → ℝ≥0∞) (hg : AEMeasurable g (weightedMeasure w)) (t : ℝ≥0∞) :
      t * weightedMeasure w {x | t < maximal g x} ≤
        ENNReal.ofReal (3 ^ Fintype.card ι * A) * ∫⁻ x, ‖g x‖ₑ ∂weightedMeasure w := by
    simpa only [enorm_eq_self] using weak_bound_ae h hg t
  have hinfty (g : EuclideanSpace ℝ ι → ℝ≥0∞) (_hg : AEMeasurable g (weightedMeasure w)) :
      maximal g ≤ᵐ[weightedMeasure w] fun _ => ENNReal.ofReal (1 : ℝ) * eLpNormEssSup g (weightedMeasure w) := by
    filter_upwards [] with x
    simpa only [ENNReal.ofReal_one, one_mul] using maximal_le_eLpNormEssSup h g x
  have hh := ImportedTauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup
    (T := maximal) (p := (2 : ℝ)) hf (measurable_maximal f).aemeasurable (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hadd hweak hinfty
  norm_num only [ENNReal.rpow_two, enorm_eq_self, Real.rpow_neg_one] at hh
  have hA : 0 ≤ A := zero_le_one.trans h.constant_ge_one
  norm_num at hh
  have he : (4 : ℝ≥0∞) * (2 * (3 ^ Fintype.card ι * ENNReal.ofReal A)) =
      ENNReal.ofReal (8 * 3 ^ Fintype.card ι * A) := by
    norm_num [ENNReal.ofReal_mul, ENNReal.ofReal_pow] <;> ring
  simpa only [he] using hh

end PeriodicAttractiveLogGas.CubeMaximal
