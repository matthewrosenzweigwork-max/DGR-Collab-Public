import DGRHS.Commutator.SourceLogMovingDerivative
import DGRHS.Commutator.SourceLogClassicalTestSupport
import DGRHS.Dynamics.SourceLogAdjointTimeMeasurable

/-! Derive the original classical moving-test evolution from the integrated
fixed-Cb2 LOG class. Closed-horizon traces come from the continuous probability
path and the bounded classical value test. The proper half-pair identity gives
the interior derivative bound. The singleton horizon is handled separately.
Neither moving absolute continuity nor a moving equation is a premise. -/
noncomputable section
open MeasureTheory Set Filter Laplacian
open scoped Topology NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceLogStaticWeakMeanField.continuousOn_classical_moving_pairing
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (h : SourceLogStaticWeakMeanField β T ρ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (φ : E → ℝ) (f : ℝ → E → ℝ)
    (hf : SourceLogClassicalBackwardSolution β ρ t φ f) :
    ContinuousOn (fun u => ∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u))
      (Icc 0 (t : ℝ)) := by
  obtain ⟨μ,hμ,hρμ⟩ := h.exists_continuous_probability_path β T hT ρ hprob
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

lemma SourceLogClassicalBackwardSolution.interior_mean_drift_bound
    (β : ℝ) (ρ : ℝ → E → ℝ) (t : ℝ≥0) (φ : E → ℝ) (f : ℝ → E → ℝ)
    (hf : SourceLogClassicalBackwardSolution β ρ t φ f)
    (hprob : ∀ r ∈ Icc 0 (t : ℝ),
      IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ r ∈ Icc 0 (t : ℝ), ∀ x, ‖iteratedFDeriv ℝ 2 (f r) x‖ ≤ C)
    (r : ℝ) (hr : r ∈ Ioo 0 (t : ℝ)) :
    ‖sourceLogMeanTestDrift β f r (gaussianRieszDensityMeasure (ρ r))‖ ≤ C / 2 := by
  have hrcc : r ∈ Icc 0 (t : ℝ) := ⟨hr.1.le,hr.2.le⟩
  letI := hprob r hrcc
  let K : ℝ≥0 := ⟨C,hC⟩
  obtain ⟨δ,hδc,hδb,hδ,hEq⟩ := hf.time_equation
  have hback (x : E) : deriv (fun u => f u x) r + β⁻¹ * laplacian (f r) x =
      ∫ y, sourceLogTransportKernel 1 (gradient (f r)) (x,y)
        ∂gaussianRieszDensityMeasure (ρ r) := by
    rw [(hδ r hr x).deriv]
    exact hEq r hrcc x
  have he := sourceLog_adjoint_mean_drift_eq_half_pair β f r
    (hf.spatial_contdiff r hrcc) K (hb r hrcc)
    (gaussianRieszDensityMeasure (ρ r)) hback
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound (f r)
    (hf.spatial_contdiff r hrcc) K (hb r hrcc)
  have ha := abs_integral_le_bound
    ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r)))
    (measurable_sourceLogTransportKernel_one hv) (abs_sourceLogTransportKernel_one_le hv)
  rw [he,Real.norm_eq_abs,abs_mul]
  norm_num
  change |∫ p, sourceLogTransportKernel 1 (gradient (f r)) p
    ∂(gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r))| ≤ C at ha
  linarith

lemma SourceLogStaticWeakMeanField.classical_test_evolution
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (h : SourceLogStaticWeakMeanField β T ρ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (φ : E → ℝ) (f : ℝ → E → ℝ)
    (hf : SourceLogClassicalBackwardSolution β ρ t φ f) :
    SourceLogMeanFieldTestEvolution β (t : ℝ) ρ f := by
  have hp (r : ℝ) (hr : r ∈ Icc 0 (t : ℝ)) :
      IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)) :=
    hprob r ⟨hr.1,hr.2.trans ht⟩
  have hd (r : ℝ) (hr : r ∈ Ioo 0 (t : ℝ)) :=
    h.hasDerivAt_classical_moving_pairing β T hT ρ hprob M hM hρ t ht φ f hf r hr
  refine ⟨?_,?_⟩
  · by_cases ht0 : (t : ℝ) = 0
    · simpa only [ht0] using AbsolutelyContinuousOnInterval.refl
        (fun u => ∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u)) 0
    · obtain ⟨C,hC,hb⟩ := hf.bounded
      let K : ℝ≥0 := ⟨C/2,div_nonneg hC (by norm_num)⟩
      apply ac_of_continuousOn_bounded_interior_derivative
        (fun u => ∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u))
        (fun r => sourceLogMeanTestDrift β f r (gaussianRieszDensityMeasure (ρ r)))
        0 (t : ℝ) (lt_of_le_of_ne t.coe_nonneg (Ne.symm ht0))
        (h.continuousOn_classical_moving_pairing β T hT ρ hprob t ht φ f hf) hd K
      intro r hr
      exact hf.interior_mean_drift_bound β ρ t φ f hp C hC
        (fun u hu x => (hb u hu x).2.2) r hr
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (t : ℝ))] with r hr hrt
    exact hd r ⟨hr.1,lt_of_le_of_ne hr.2 hrt⟩

lemma SourceLogStaticWeakMeanField.classical_tested
    (T : ℝ≥0) (β : ℝ) (ρ : ℝ → E → ℝ) (D : Submodule ℝ (E → ℝ))
    (h : SourceLogStaticWeakMeanField β (T : ℝ) ρ)
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ x ∂volume, ρ r x ≤ M) :
    SourceLogMeanFieldClassicalTested T β ρ D := by
  intro t ht φ hφ f hf
  exact h.classical_test_evolution β (T : ℝ) T.coe_nonneg ρ hprob M hM hρ
    t (by exact_mod_cast ht) φ f hf

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceLogStaticWeakMeanField.continuousOn_classical_moving_pairing
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField.continuousOn_classical_moving_pairing
#check @DGRHS.Commutator.SourceLogClassicalBackwardSolution.interior_mean_drift_bound
#print axioms DGRHS.Commutator.SourceLogClassicalBackwardSolution.interior_mean_drift_bound
#check @DGRHS.Commutator.SourceLogStaticWeakMeanField.classical_test_evolution
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField.classical_test_evolution
#check @DGRHS.Commutator.SourceLogStaticWeakMeanField.classical_tested
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField.classical_tested
