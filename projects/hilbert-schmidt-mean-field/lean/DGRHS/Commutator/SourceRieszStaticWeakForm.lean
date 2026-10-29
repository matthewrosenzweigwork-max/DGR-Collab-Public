import DGRHS.Commutator.SourceBoundedC2Fourier
import DGRHS.Commutator.SourceRieszAdjointPhysicalDrift
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! UNCOMPILED proposed source-domain interface. This is the integrated
STATIC weak formulation of source3897--3908 for every fixed bounded C2 test,
including proper time integration. Scalar AC is proved below, not included
as an extra field. It is not the desired time-dependent backward-test or
terminal-duality identity. A separately chosen distributional PDE class must
still be proved equivalent to this formulation before claiming that export. -/
noncomputable section
open MeasureTheory Laplacian Set
open scoped Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszStaticMeanTestDrift (s β : ℝ) (ρ : E→ℝ) (φ : E→ℝ) : ℝ :=
  β⁻¹*(∫ x, laplacian φ x ∂gaussianRieszDensityMeasure ρ) -
    (1/2:ℝ)*(∫ p, sourceRieszTransportKernel 1 s (gradient φ) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))

def SourceRieszStaticWeakMeanField (s β T : ℝ) (ρ : ℝ→E→ℝ) : Prop :=
  ∀ φ:E→ℝ, SourceBoundedC2Test φ →
    IntervalIntegrable (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) φ) volume 0 T ∧
    ∀ r∈Icc 0 T,
      (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, φ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceRieszStaticMeanTestDrift s β (ρ u) φ

lemma SourceRieszStaticWeakMeanField.static_pairing_ac
    (s β T : ℝ) (hT : 0≤T) (ρ : ℝ→E→ℝ)
    (h : SourceRieszStaticWeakMeanField s β T ρ)
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
    (∫ u in 0..r, sourceRieszStaticMeanTestDrift s β (ρ u) φ) = _
  exact (he r (by simpa only [uIcc_of_le hT] using hr)).symm

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceRieszStaticMeanTestDrift
#print axioms DGRHS.Commutator.sourceRieszStaticMeanTestDrift
#check @DGRHS.Commutator.SourceRieszStaticWeakMeanField
#print axioms DGRHS.Commutator.SourceRieszStaticWeakMeanField
#check @DGRHS.Commutator.SourceRieszStaticWeakMeanField.static_pairing_ac
#print axioms DGRHS.Commutator.SourceRieszStaticWeakMeanField.static_pairing_ac
