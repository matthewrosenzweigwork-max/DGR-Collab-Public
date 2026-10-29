import Mathlib.Analysis.Calculus.Gradient.Basic
import DGRHS.Commutator.SourceBoundedC2Fourier
import DGRHS.Commutator.SourceLogCutoffKernel
import DGRHS.Gaussian.GaussianShortRangeSourceL2
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! UNCHECKED actual LOG static source class. This explicitly realizes the
source865/1046 admissible mean-field class by the integrated fixed-Cb2 equation
of3897--3908, with proper time integrals and specified every-time traces. It
does not assert equivalence with arbitrary distributional/classical solutions.
Actual spatial properness, legitimate density hypotheses and the physical
beta>0 domain are required by source consumers. Scalar AC and narrow
continuity are derived; no moving-test identity or terminal CLT is a premise.
The LOG kernel is literal, never the Riesz potential at zero. -/
noncomputable section
open MeasureTheory Laplacian Set
open scoped Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceLogStaticMeanTestDrift (β : ℝ) (ρ : E→ℝ) (φ : E→ℝ) : ℝ :=
  β⁻¹*(∫ x, laplacian φ x ∂gaussianRieszDensityMeasure ρ) -
    (1/2:ℝ)*(∫ p, sourceLogTransportKernel 1 (gradient φ) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))

def SourceLogStaticWeakMeanField (β T : ℝ) (ρ : ℝ→E→ℝ) : Prop :=
  ∀ φ:E→ℝ, SourceBoundedC2Test φ →
    IntervalIntegrable (fun r => sourceLogStaticMeanTestDrift β (ρ r) φ) volume 0 T ∧
    ∀ r∈Icc 0 T,
      (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceLogStaticMeanTestDrift β (ρ u) φ

lemma SourceLogStaticWeakMeanField.static_pairing_ac
    (β T : ℝ) (hT : 0≤T) (ρ : ℝ→E→ℝ)
    (h : SourceLogStaticWeakMeanField β T ρ)
    (φ : E→ℝ) (hφ : SourceBoundedC2Test φ) :
    AbsolutelyContinuousOnInterval
      (fun r => ∫ x, φ x ∂gaussianRieszDensityMeasure (ρ r)) 0 T := by
  obtain ⟨hi,he⟩ := h φ hφ
  have hprim := hi.absolutelyContinuousOnInterval_intervalIntegral (c:=0) (by simp)
  have hc : LipschitzOnWith 0
      (fun _ : ℝ => ∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) (uIcc 0 T) := by
    intro x hx y hy
    simp
  apply (hc.absolutelyContinuousOnInterval.add hprim).congr
  intro r hr
  change (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) +
    (∫ u in 0..r, sourceLogStaticMeanTestDrift β (ρ u) φ) = _
  exact (he r (by simpa only [uIcc_of_le hT] using hr)).symm


lemma SourceLogStaticWeakMeanField.exists_continuous_probability_path
    (β T : ℝ) (hT : 0≤T) (ρ : ℝ→E→ℝ)
    (h : SourceLogStaticWeakMeanField β T ρ)
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) :
    ∃ μ:ℝ→ProbabilityMeasure E,Continuous μ ∧
      ∀ r,(μ r:Measure E)=gaussianRieszDensityMeasure (ρ (max 0 (min T r))) := by
  let c : ℝ→ℝ := fun r=>max 0 (min T r)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (r : ℝ) : c r∈Icc 0 T :=
    ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hce (r : ℝ) (hr : r∈Icc 0 T) : c r=r := by
    dsimp only [c]
    rw [min_eq_right hr.2,max_eq_right hr.1]
  let μ : ℝ→ProbabilityMeasure E :=
    fun r=>⟨gaussianRieszDensityMeasure (ρ (c r)),hprob (c r) (hcm r)⟩
  have hAC : ∀ φ:E→ℝ,SourceBoundedC2Test φ →
      AbsolutelyContinuousOnInterval (fun r=>∫ x,φ x ∂(μ r:Measure E)) 0 T := by
    intro φ hφ
    apply (h.static_pairing_ac β T hT ρ φ hφ).congr
    intro r hr
    have hr' : r∈Icc 0 T := by simpa only [uIcc_of_le hT] using hr
    simp only [μ,hce r hr']
    rfl
  have hμ : ContinuousOn μ (Icc 0 T) :=
    continuousOn_probability_of_ac_boundedC2_tests μ 0 T hT hAC
  have hcont : Continuous (μ∘c) := hμ.comp_continuous hc hcm
  have he : μ∘c=μ := by
    funext r
    apply Subtype.ext
    change gaussianRieszDensityMeasure (ρ (c (c r)))=gaussianRieszDensityMeasure (ρ (c r))
    rw [hce (c r) (hcm r)]
  refine ⟨μ,?_,fun _=>rfl⟩
  rwa [he] at hcont


end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceLogStaticMeanTestDrift
#print axioms DGRHS.Commutator.sourceLogStaticMeanTestDrift
#check @DGRHS.Commutator.SourceLogStaticWeakMeanField
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField
#check @DGRHS.Commutator.SourceLogStaticWeakMeanField.static_pairing_ac
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField.static_pairing_ac

#check @DGRHS.Commutator.SourceLogStaticWeakMeanField.exists_continuous_probability_path
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField.exists_continuous_probability_path
