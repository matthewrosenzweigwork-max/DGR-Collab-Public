import LeanResearch.PeriodicAttractiveLogGas.OpenPhysicalCubes
import LeanResearch.Imported.TauCetiAppendix.MeasureTheory.Integral.MaximalFunction

/-! The uncentered maximal function over all open axis-parallel cubes,
with ordinary Lebesgue averages, exactly as in Appendix A. Inputs here
are nonnegative extended-real functions; real inputs are handled by norm. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.CubeMaximal
open PhysicalCubes WeightedCubeBounds
variable {ι : Type*} [Fintype ι]

def maximal (f : EuclideanSpace ℝ ι → ℝ≥0∞) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ⨆ c : EuclideanSpace ℝ ι, ⨆ ℓ : ℝ, ⨆ (_ : 0 < ℓ), ⨆ (_ : x ∈ openCube c ℓ),
    ⨍⁻ y in openCube c ℓ, f y ∂volume

lemma average_le_maximal (f : EuclideanSpace ℝ ι → ℝ≥0∞)
    (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ openCube c ℓ) : (⨍⁻ y in openCube c ℓ, f y ∂volume) ≤ maximal f x :=
  le_iSup_of_le c (le_iSup_of_le ℓ (le_iSup_of_le hℓ (le_iSup_of_le hx le_rfl)))

lemma lt_maximal_iff (f : EuclideanSpace ℝ ι → ℝ≥0∞) (x : EuclideanSpace ℝ ι) (t : ℝ≥0∞) :
    t < maximal f x ↔ ∃ c ℓ, 0 < ℓ ∧ x ∈ openCube c ℓ ∧ t < ⨍⁻ y in openCube c ℓ, f y ∂volume := by
  simp only [maximal, lt_iSup_iff, exists_prop]

lemma lowerSemicontinuous_maximal (f : EuclideanSpace ℝ ι → ℝ≥0∞) : LowerSemicontinuous (maximal f) := by
  intro x t ht
  obtain ⟨c, ℓ, hℓ, hx, havg⟩ := (lt_maximal_iff f x t).mp ht
  filter_upwards [(isOpen_openCube c ℓ).mem_nhds hx] with y hy
  exact havg.trans_le (average_le_maximal f c hℓ hy)

lemma measurable_maximal (f : EuclideanSpace ℝ ι → ℝ≥0∞) : Measurable (maximal f) :=
  (lowerSemicontinuous_maximal f).measurable

lemma maximal_mono_ae {f g : EuclideanSpace ℝ ι → ℝ≥0∞} (hfg : f ≤ᵐ[volume] g) :
    maximal f ≤ maximal g := by
  intro x
  apply iSup_le
  intro c
  apply iSup_le
  intro ℓ
  apply iSup_le
  intro hℓ
  apply iSup_le
  intro hx
  exact (setLAverage_mono_ae (openCube c ℓ) hfg).trans (average_le_maximal g c hℓ hx)

lemma maximal_congr_ae {f g : EuclideanSpace ℝ ι → ℝ≥0∞} (hfg : f =ᵐ[volume] g) :
    maximal f = maximal g :=
  le_antisymm (maximal_mono_ae hfg.le) (maximal_mono_ae hfg.symm.le)

lemma maximal_add_le {f g : EuclideanSpace ℝ ι → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    maximal (f + g) ≤ maximal f + maximal g := by
  intro x
  refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hx => ?_
  have he : (⨍⁻ y in openCube c ℓ, (f + g) y ∂volume) =
      (⨍⁻ y in openCube c ℓ, f y ∂volume) + ⨍⁻ y in openCube c ℓ, g y ∂volume := by
    simp only [setLAverage_eq, Pi.add_apply]
    rw [lintegral_add_left' hf.restrict, ENNReal.add_div]
  rw [he]
  exact add_le_add (average_le_maximal f c hℓ hx) (average_le_maximal g c hℓ hx)

lemma maximal_le_constant {f : EuclideanSpace ℝ ι → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ᵐ x ∂volume, f x ≤ C) : maximal f ≤ fun _ => C := by
  intro x
  refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hx => ?_
  exact (setLAverage_mono_ae (openCube c ℓ) h).trans_eq
    (setLAverage_const (openCube_volume_pos c hℓ).ne' (openCube_volume_ne_top c hℓ.le) C)

lemma maximal_le_eLpNormEssSup {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ}
    {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    (f : EuclideanSpace ℝ ι → ℝ≥0∞) :
    maximal f ≤ fun _ => eLpNormEssSup f (weightedMeasure w) := by
  apply maximal_le_constant
  have hh := ae_le_eLpNormEssSup (f := f) (μ := weightedMeasure w)
  filter_upwards [h.volume_absolutelyContinuous.ae_le hh] with x hx
  simpa only [enorm_eq_self] using hx

end PeriodicAttractiveLogGas.CubeMaximal
