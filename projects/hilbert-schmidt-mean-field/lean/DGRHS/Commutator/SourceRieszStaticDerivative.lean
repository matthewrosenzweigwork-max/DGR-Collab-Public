import DGRHS.Commutator.SourceRieszStaticGenerator
import DGRHS.Commutator.SourceRieszWeakProbabilityPath
import DGRHS.Commutator.SourceScalarWeakEvolution

/-! UNCOMPILED actual positive-Riesz frozen-test derivative. The EVERY-time
static weak identity first derives the continuous endpoint-clamped law.
The singular generator's continuity is then a theorem, rather than an extra
source hypothesis. Native FTC and the exact closed-time primitive identify
the derivative at every interior time. This adapts the independently checked
root SourceLogStaticDerivative proof pattern; the physical generator and all
kernel and density inputs here are positive-Riesz data. No LOG specialization
or moving-test, endpoint-duality or density-time-derivative premise is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceRieszStaticWeakMeanField.hasDerivAt_static_pairing
    (s β T : ℝ) (hs : 0<s) (hdim : 2*s<(Fintype.card ι:ℝ))
    (hT : 0≤T) (ρ : ℝ→E→ℝ)
    (h : SourceRieszStaticWeakMeanField s β T ρ)
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0≤M) (hρ : ∀ r∈Icc 0 T,∀ᵐ x ∂volume,ρ r x≤M)
    (φ : E→ℝ) (hφ : SourceBoundedC2Test φ)
    (r : ℝ) (hr : r∈Ioo 0 T) :
    HasDerivAt (fun u => ∫ x,φ x ∂gaussianRieszDensityMeasure (ρ u))
      (sourceRieszStaticMeanTestDrift s β (ρ r) φ) r := by
  let c : ℝ→ℝ := fun u => max 0 (min T u)
  have hcm (u : ℝ) : c u∈Icc 0 T :=
    ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hce (u : ℝ) (hu : u∈Icc 0 T) : c u=u := by
    dsimp only [c]
    rw [min_eq_right hu.2,max_eq_right hu.1]
  obtain ⟨μ,hμ,hρμ⟩ := h.exists_continuous_probability_path s β T hT ρ hprob
  let G : ℝ→ℝ := fun u => sourceRieszStaticMeanTestDrift s β (ρ (c u)) φ
  have hG : Continuous G :=
    hφ.continuous_riesz_static_generator_probability φ s β hs hdim μ hμ
      (fun u => ρ (c u)) hρμ M hM (fun u => hρ (c u) (hcm u))
  have hrep (u : ℝ) (hu : u∈Icc 0 T) :
      (∫ x,φ x ∂gaussianRieszDensityMeasure (ρ u)) =
        (∫ x,φ x ∂gaussianRieszDensityMeasure (ρ 0)) + ∫ v in 0..u,G v := by
    rw [(h φ hφ).2 u hu]
    congr 1
    rw [intervalIntegral.integral_of_le hu.1,intervalIntegral.integral_of_le hu.1]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    dsimp only [G]
    rw [hce v ⟨hv.1.le,hv.2.trans hu.2⟩]
  have hdr : HasDerivAt
      (fun u => (∫ x,φ x ∂gaussianRieszDensityMeasure (ρ 0)) + ∫ v in 0..u,G v)
      (G r) r :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 r)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).const_add _
  dsimp only [G] at hdr
  rw [hce r ⟨hr.1.le,hr.2.le⟩] at hdr
  apply hdr.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with u hu
  exact hrep u ⟨hu.1.le,hu.2.le⟩

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszStaticWeakMeanField.hasDerivAt_static_pairing
#print axioms DGRHS.Commutator.SourceRieszStaticWeakMeanField.hasDerivAt_static_pairing
