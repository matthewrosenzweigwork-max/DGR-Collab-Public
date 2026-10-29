import DGRHS.Commutator.SourceLogStaticGenerator
import DGRHS.Commutator.SourceScalarWeakEvolution

/-! The actual integrated fixed-Cb2 LOG equation gives the genuine derivative
of each fixed test pairing at every interior time. The law is derived by
clamping the original every-time probability law, and the continuous generator
is then used in native FTC. No AE derivative, moving-test identity, density
time derivative or favorable endpoint equality is supplied as a premise. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceLogStaticWeakMeanField.hasDerivAt_static_pairing
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (h : SourceLogStaticWeakMeanField β T ρ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (φ : E → ℝ) (hφ : SourceBoundedC2Test φ)
    (r : ℝ) (hr : r ∈ Ioo 0 T) :
    HasDerivAt (fun u => ∫ x, φ x ∂gaussianRieszDensityMeasure (ρ u))
      (sourceLogStaticMeanTestDrift β (ρ r) φ) r := by
  let c : ℝ → ℝ := fun u => max 0 (min T u)
  have hcm (u : ℝ) : c u ∈ Icc 0 T :=
    ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hce (u : ℝ) (hu : u ∈ Icc 0 T) : c u = u := by
    dsimp only [c]
    rw [min_eq_right hu.2,max_eq_right hu.1]
  obtain ⟨μ,hμ,hρμ⟩ := h.exists_continuous_probability_path β T hT ρ hprob
  let G : ℝ → ℝ := fun u => sourceLogStaticMeanTestDrift β (ρ (c u)) φ
  have hG : Continuous G :=
    hφ.continuous_log_static_generator_probability φ β μ hμ
      (fun u => ρ (c u)) hρμ M hM (fun u => hρ (c u) (hcm u))
  have hrep (u : ℝ) (hu : u ∈ Icc 0 T) :
      (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ u)) =
        (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) + ∫ v in 0..u, G v := by
    rw [(h φ hφ).2 u hu]
    congr 1
    rw [intervalIntegral.integral_of_le hu.1,intervalIntegral.integral_of_le hu.1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    dsimp only [G]
    rw [hce v ⟨hv.1.le,hv.2.trans hu.2⟩]
  have hd : HasDerivAt
      (fun u => (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) + ∫ v in 0..u, G v)
      (G r) r :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 r)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).const_add _
  dsimp only [G] at hd
  rw [hce r ⟨hr.1.le,hr.2.le⟩] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with u hu
  exact hrep u ⟨hu.1.le,hu.2.le⟩

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceLogStaticWeakMeanField.hasDerivAt_static_pairing
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField.hasDerivAt_static_pairing
