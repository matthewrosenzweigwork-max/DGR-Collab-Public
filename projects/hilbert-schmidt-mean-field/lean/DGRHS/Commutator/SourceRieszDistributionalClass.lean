import DGRHS.Commutator.SourceC2ApproximationConstructions
import DGRHS.Commutator.SourceRieszC2PointwiseLimit
import DGRHS.Commutator.SourceRieszPrincipalValueForce
import DGRHS.Commutator.SourceScalarDistributionalTrace
import DGRHS.Commutator.SourceCompactTestTrace

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Positive-Riesz source-class bridges, `0 < s`, `2s < d`, uniform density cap `M`
on the closed horizon (source 878):

* compact C-infinity every-time testing  ->  compact C2 every-time testing
  (mollifier + singular local domination);
* compact C2 every-time testing  ->  existing bounded-C2 `SourceRieszStaticWeakMeanField`
  (geometric cutoff + singular local domination);
* distributional-in-time testing against compact smooth tests, with the
  literal force read as a principal value, plus the continuous trace of the
  supplied law  ->  compact smooth every-time testing  ->  static class.

No moving-test identity, force L1, moment, or desired conclusion is a premise.
The density cap is used in every singular dominated-convergence step; it is a
source assumption, not a new one. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval ContDiff
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def SourceRieszCompactSmoothStaticWeakMeanField (s β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    IntervalIntegrable (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) ψ) volume 0 T ∧
    ∀ r ∈ Icc 0 T,
      (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceRieszStaticMeanTestDrift s β (ρ u) ψ

def SourceRieszCompactStaticWeakMeanField (s β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
    IntervalIntegrable (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) ψ) volume 0 T ∧
    ∀ r ∈ Icc 0 T,
      (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceRieszStaticMeanTestDrift s β (ρ u) ψ

def SourceRieszDistributionalWeakMeanField (s β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    IntervalIntegrable (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) ψ) volume 0 T ∧
    SourceScalarDistributionalDerivOn
      (fun r => ∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r))
      (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) ψ) 0 T

def SourceRieszPVDistributionalWeakMeanField (s β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    IntervalIntegrable
      (fun r => sourceRieszPVMeanTestDrift s β (gaussianRieszDensityMeasure (ρ r)) ψ)
        volume 0 T ∧
    SourceScalarDistributionalDerivOn
      (fun r => ∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r))
      (fun r => sourceRieszPVMeanTestDrift s β (gaussianRieszDensityMeasure (ρ r)) ψ) 0 T

section Bridges

theorem SourceRieszCompactSmoothStaticWeakMeanField.to_compactC2
    {ι : Type*} [Fintype ι]
    (s β T : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card ι : ℝ)) (hT : 0 ≤ T)
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (hweak : SourceRieszCompactSmoothStaticWeakMeanField s β T ρ) :
    SourceRieszCompactStaticWeakMeanField s β T ρ := by
  intro ψ hψ hc
  obtain ⟨a, ha⟩ := exists_source_mollifier_pointwiseApproximation ψ hψ hc
  have hw (n : ℕ) := hweak (a.test n) (ha n).1 (ha n).2
  exact a.riesz_integrated_identity s β T hs hd hT ρ hprob M hM hρ
    (fun n => (hw n).1) (fun n => (hw n).2)

theorem SourceRieszCompactStaticWeakMeanField.to_bounded
    {ι : Type*} [Fintype ι]
    (s β T : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card ι : ℝ)) (hT : 0 ≤ T)
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (hweak : SourceRieszCompactStaticWeakMeanField s β T ρ) :
    SourceRieszStaticWeakMeanField s β T ρ := by
  intro φ hφ
  obtain ⟨a, ha⟩ := exists_source_cutoff_pointwiseApproximation φ hφ
  have hw (n : ℕ) := hweak (a.test n) (a.smooth n) (ha n)
  exact a.riesz_integrated_identity s β T hs hd hT ρ hprob M hM hρ
    (fun n => (hw n).1) (fun n => (hw n).2)

theorem SourceRieszCompactSmoothStaticWeakMeanField.to_bounded
    {ι : Type*} [Fintype ι]
    (s β T : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card ι : ℝ)) (hT : 0 ≤ T)
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (hweak : SourceRieszCompactSmoothStaticWeakMeanField s β T ρ) :
    SourceRieszStaticWeakMeanField s β T ρ :=
  SourceRieszCompactStaticWeakMeanField.to_bounded s β T hs hd hT ρ hprob M hM hρ
    (SourceRieszCompactSmoothStaticWeakMeanField.to_compactC2 s β T hs hd hT ρ hprob M hM hρ
      hweak)

lemma sourceRieszPVDistributional_iff
    {ι : Type*} [Fintype ι]
    (s β T : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card ι : ℝ)) (hT : 0 ≤ T)
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    :
    SourceRieszPVDistributionalWeakMeanField s β T ρ ↔
      SourceRieszDistributionalWeakMeanField s β T ρ := by
  have he (ψ : EuclideanSpace ℝ ι → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      EqOn (fun r => sourceRieszPVMeanTestDrift s β (gaussianRieszDensityMeasure (ρ r)) ψ)
        (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) ψ) (Icc 0 T) := by
    intro r hr
    letI := hprob r hr
    exact sourceRieszPVMeanTestDrift_eq s β hs hd (ρ r) M hM (hρ r hr) ψ
      (sourceBoundedC2Test_of_compact ψ (hψ.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hc)
  have hI {F G : ℝ → ℝ} (hFG : EqOn F G (Icc 0 T)) :
      IntervalIntegrable F volume 0 T ↔ IntervalIntegrable G volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT,
      intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact ⟨fun h => h.congr_fun (hFG.mono Ioc_subset_Icc_self) measurableSet_Ioc,
      fun h => h.congr_fun (hFG.symm.mono Ioc_subset_Icc_self) measurableSet_Ioc⟩
  constructor
  · intro h ψ hψ hc
    obtain ⟨hi, hdd⟩ := h ψ hψ hc
    exact ⟨(hI (he ψ hψ hc)).mp hi, hdd.congr_right hT (he ψ hψ hc)⟩
  · intro h ψ hψ hc
    obtain ⟨hi, hdd⟩ := h ψ hψ hc
    exact ⟨(hI (he ψ hψ hc)).mpr hi, hdd.congr_right hT (he ψ hψ hc).symm⟩

/-- **Positive-Riesz source-class bridge.** -/
theorem SourceRieszDistributionalWeakMeanField.to_static
    {ι : Type*} [Fintype ι]
    (s β T : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card ι : ℝ)) (hT : 0 ≤ T)
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (hdist : SourceRieszDistributionalWeakMeanField s β T ρ)
    (htrace : SourceCompactTestContinuousTrace T ρ) :
    SourceRieszStaticWeakMeanField s β T ρ := by
  apply SourceRieszCompactSmoothStaticWeakMeanField.to_bounded s β T hs hd hT ρ hprob M hM hρ
  intro ψ hψ hc
  obtain ⟨hi, hdd⟩ := hdist ψ hψ hc
  exact ⟨hi, source_scalar_trace_eq_primitive hT _ _ (htrace ψ hψ hc) hi hdd⟩

/-- **Positive-Riesz source-class bridge, principal-value reading of the literal
force.** -/
theorem SourceRieszPVDistributionalWeakMeanField.to_static
    {ι : Type*} [Fintype ι]
    (s β T : ℝ) (hs : 0 < s) (hd : 2 * s < (Fintype.card ι : ℝ)) (hT : 0 ≤ T)
    (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (hdist : SourceRieszPVDistributionalWeakMeanField s β T ρ)
    (htrace : SourceCompactTestContinuousTrace T ρ) :
    SourceRieszStaticWeakMeanField s β T ρ :=
  SourceRieszDistributionalWeakMeanField.to_static s β T hs hd hT ρ hprob M hM hρ
    ((sourceRieszPVDistributional_iff s β T hs hd hT ρ hprob M hM hρ).mp hdist) htrace

end Bridges

end DGRHS.Commutator
