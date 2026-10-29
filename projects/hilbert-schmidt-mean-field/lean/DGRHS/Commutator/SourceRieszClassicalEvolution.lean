import DGRHS.Commutator.SourceRieszMovingDerivative
import DGRHS.Commutator.SourceRieszNamedUpropDynamicCLT
import DGRHS.Commutator.SourceRieszAdjointMeanDrift

/-! UNCOMPILED RECORDS-ONLY positive-Riesz classical evolution constructor.
Adaptation of the checked root SourceLogClassicalEvolution pattern, whose
exact source/hash is retained beside this draft. Riesz properness and the
actual canceled half-pair identity come from the checked positive-Riesz
chain. The mean-field moving derivative/AC is derived from the static class;
no endpoint/phase identity or tested-class predicate is an input assumption.
All endpoint traces and singleton horizons are retained. -/
noncomputable section
open MeasureTheory Set Filter Laplacian
open scoped Topology NNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceRieszStaticWeakMeanField.continuousOn_classical_moving_pairing
    (s β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (h : SourceRieszStaticWeakMeanField s β T ρ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (φ : E → ℝ) (f : ℝ → E → ℝ)
    (hf : SourceRieszClassicalBackwardSolution s β ρ t φ f) :
    ContinuousOn (fun u => ∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u))
      (Icc 0 (t : ℝ)) := by
  obtain ⟨μ,hμ,hρμ⟩ := h.exists_continuous_probability_path s β T hT ρ hprob
  have hμe (u : ℝ) (hu : u ∈ Icc 0 T) :
      (μ u : Measure E) = gaussianRieszDensityMeasure (ρ u) := by
    rw [hρμ u,min_eq_right hu.2,max_eq_right hu.1]
  obtain ⟨C,hC,hb⟩ := hf.bounded
  let c : ℝ → ℝ := fun u => max 0 (min (t : ℝ) u)
  have hcm (u : ℝ) : c u ∈ Icc 0 (t : ℝ) :=
    ⟨le_max_left _ _,max_le t.coe_nonneg (min_le_left _ _)⟩
  have hce (u : ℝ) (hu : u ∈ Icc 0 (t : ℝ)) : c u = u := by
    dsimp only [c]
    rw [min_eq_right hu.2,max_eq_right hu.1]
  let fExt : ℝ × E → ℝ := fun p => f (c p.1) p.2
  have hc : Continuous (fun p : ℝ × E => (c p.1,p.2)) :=
    (continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd
  have hfc : Continuous fExt :=
    hf.value_continuous.comp_continuous hc (fun p => ⟨hcm p.1,mem_univ _⟩)
  have hfb (p : ℝ × E) : |fExt p| ≤ C := (hb (c p.1) (hcm p.1) p.2).1
  have hg := continuous_integral_moving_probability
    (fun u : ℝ => u) continuous_id μ hμ fExt hfc C hfb
  apply hg.continuousOn.congr
  intro u hu
  change (∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u)) =
    ∫ x, f (c u) x ∂(μ u : Measure E)
  rw [hμe u ⟨hu.1,hu.2.trans ht⟩]
  rw [hce u hu]

lemma SourceRieszClassicalBackwardSolution.interior_mean_drift_bound
    (s β : ℝ) (hs : 0 < s) (hdim : 2*s < (Fintype.card ι : ℝ))
    (ρ : ℝ → E → ℝ) (t : ℝ≥0) (φ : E → ℝ) (f : ℝ → E → ℝ)
    (hf : SourceRieszClassicalBackwardSolution s β ρ t φ f)
    (hprob : ∀ r ∈ Icc 0 (t : ℝ),
      IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ r ∈ Icc 0 (t : ℝ), ∀ᵐ x ∂volume, ρ r x ≤ M)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ r ∈ Icc 0 (t : ℝ), ∀ x, ‖iteratedFDeriv ℝ 2 (f r) x‖ ≤ C)
    (r : ℝ) (hr : r ∈ Ioo 0 (t : ℝ)) :
    ‖sourceRieszMeanTestDrift s β (ρ r) f r‖ ≤
      (1/2 : ℝ) * (sourceRieszLocalProfileConstant (ι:=ι) s 1 * C^1 *
        gaussianRieszPhysicalPotentialConstant s M ι) := by
  have hrcc : r ∈ Icc 0 (t : ℝ) := ⟨hr.1.le,hr.2.le⟩
  letI := hprob r hrcc
  let K : ℝ≥0 := ⟨C,hC⟩
  obtain ⟨δ,hδc,hδb,hδ,hEq⟩ := hf.time_equation
  have hback (x : E) : deriv (fun u => f u x) r + β⁻¹ * laplacian (f r) x =
      ∫ y, ⟪sourceRieszForce s (x-y), gradient (f r) x-gradient (f r) y⟫
        ∂gaussianRieszDensityMeasure (ρ r) := by
    rw [(hδ r hr x).deriv]
    exact hEq r hrcc x
  have he := sourceRiesz_adjoint_mean_drift_eq_half_pair s β hs hdim
    (ρ r) M hM (hρ r hrcc) f r (hf.spatial_contdiff r hrcc) K (hb r hrcc) hback
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound (f r)
    (hf.spatial_contdiff r hrcc) K (hb r hrcc)
  have hp := (sourceRieszLocalTransport_pair s 1 hs hdim hv (ρ r) M hM (hρ r hrcc)).2
  rw [he,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have hK : (K : ℝ) = C := rfl
  rw [hK] at hp
  exact mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 1/2)

lemma SourceRieszStaticWeakMeanField.classical_test_evolution
    (s β T : ℝ) (hs : 0 < s) (hdim : 2*s < (Fintype.card ι : ℝ))
    (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (h : SourceRieszStaticWeakMeanField s β T ρ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (φ : E → ℝ) (f : ℝ → E → ℝ)
    (hf : SourceRieszClassicalBackwardSolution s β ρ t φ f) :
    SourceRieszMeanFieldTestEvolution s β (t : ℝ) ρ f := by
  have hp (r : ℝ) (hr : r ∈ Icc 0 (t : ℝ)) :
      IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)) :=
    hprob r ⟨hr.1,hr.2.trans ht⟩
  have hρt (r : ℝ) (hr : r ∈ Icc 0 (t : ℝ)) : ∀ᵐ x ∂volume, ρ r x ≤ M :=
    hρ r ⟨hr.1,hr.2.trans ht⟩
  have hd (r : ℝ) (hr : r ∈ Ioo 0 (t : ℝ)) :=
    h.hasDerivAt_classical_moving_pairing s β T hs hdim hT ρ hprob M hM hρ t ht φ f hf r hr
  refine ⟨?_,?_⟩
  · by_cases ht0 : (t : ℝ) = 0
    · simpa only [ht0] using AbsolutelyContinuousOnInterval.refl
        (fun u => ∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u)) 0
    · obtain ⟨C,hC,hb⟩ := hf.bounded
      let Cb : ℝ := (1/2 : ℝ) * (sourceRieszLocalProfileConstant (ι:=ι) s 1 * C^1 *
        gaussianRieszPhysicalPotentialConstant s M ι)
      let K : ℝ≥0 := ⟨|Cb|,abs_nonneg Cb⟩
      apply ac_of_continuousOn_bounded_interior_derivative
        (fun u => ∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u))
        (fun r => sourceRieszMeanTestDrift s β (ρ r) f r)
        0 (t : ℝ) (lt_of_le_of_ne t.coe_nonneg (Ne.symm ht0))
        (h.continuousOn_classical_moving_pairing s β T hT ρ hprob t ht φ f hf) hd K
      intro r hr
      exact (hf.interior_mean_drift_bound s β hs hdim ρ t φ f hp M hM hρt C hC
        (fun u hu x => (hb u hu x).2.2) r hr).trans (le_abs_self Cb)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (t : ℝ))] with r hr hrt
    exact hd r ⟨hr.1,lt_of_le_of_ne hr.2 hrt⟩

lemma SourceRieszStaticWeakMeanField.classical_tested
    (T : ℝ≥0) (s β : ℝ) (hs : 0 < s) (hdim : 2*s < (Fintype.card ι : ℝ))
    (ρ : ℝ → E → ℝ) (D : Submodule ℝ (E → ℝ))
    (h : SourceRieszStaticWeakMeanField s β (T : ℝ) ρ)
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ x ∂volume, ρ r x ≤ M) :
    SourceRieszMeanFieldClassicalTested T s β ρ D := by
  intro t ht φ hφ f hf
  exact h.classical_test_evolution s β (T : ℝ) hs hdim T.coe_nonneg ρ hprob M hM hρ
    t (by exact_mod_cast ht) φ f hf

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszStaticWeakMeanField.continuousOn_classical_moving_pairing
#print axioms DGRHS.Commutator.SourceRieszStaticWeakMeanField.continuousOn_classical_moving_pairing
#check @DGRHS.Commutator.SourceRieszClassicalBackwardSolution.interior_mean_drift_bound
#print axioms DGRHS.Commutator.SourceRieszClassicalBackwardSolution.interior_mean_drift_bound
#check @DGRHS.Commutator.SourceRieszStaticWeakMeanField.classical_test_evolution
#print axioms DGRHS.Commutator.SourceRieszStaticWeakMeanField.classical_test_evolution
#check @DGRHS.Commutator.SourceRieszStaticWeakMeanField.classical_tested
#print axioms DGRHS.Commutator.SourceRieszStaticWeakMeanField.classical_tested
