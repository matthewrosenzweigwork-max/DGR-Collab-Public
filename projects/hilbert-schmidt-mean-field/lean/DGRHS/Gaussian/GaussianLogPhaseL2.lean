import DGRHS.Gaussian.GaussianLogPhaseBandIntegrals
import DGRHS.Gaussian.GaussianLogPhaseMeasure
import DGRHS.Gaussian.GaussianLogCutoffPositivity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Supporting development. Construct every-x infinite-scale L2 membership from actual
finite-band raw Gram identities and a proper source majorant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DGRHS.Gaussian

lemma nonnegative_integrable_of_ae_tendsto_uniform_integral {P : Type*} [MeasurableSpace P]
    (ν : Measure P) (f : ℕ → P → ℝ) (F : P → ℝ)
    (hf : ∀ j, Integrable (f j) ν) (hfn : ∀ j, ∀ p, 0 ≤ f j p)
    (hF : StronglyMeasurable F) (hFn : ∀ p, 0 ≤ F p)
    (M : ℝ) (hB : ∀ j, ∫ p, f j p ∂ν ≤ M)
    (hc : ∀ᵐ p ∂ν, Tendsto (fun j => f j p) atTop (𝓝 (F p))) :
    Integrable F ν ∧ (∫ p,F p ∂ν) ≤ M := by
  have hNNLim : ∀ᵐ p ∂ν,Tendsto (fun j => ENNReal.ofReal (f j p)) atTop
      (𝓝 (ENNReal.ofReal (F p))) := hc.mono fun _ h => ENNReal.tendsto_ofReal h
  have hNnm : ∀ j,AEMeasurable (fun p => ENNReal.ofReal (f j p)) ν :=
    fun j => ENNReal.measurable_ofReal.comp_aemeasurable (hf j).aestronglyMeasurable.aemeasurable
  have hNnBound : ∀ j,(∫⁻ p,ENNReal.ofReal (f j p) ∂ν) ≤ ENNReal.ofReal M := by
    intro j
    rw [← ofReal_integral_eq_lintegral_ofReal (hf j) (Eventually.of_forall (hfn j))]
    exact ENNReal.ofReal_le_ofReal (hB j)
  have hFatou : (∫⁻ p,ENNReal.ofReal (F p) ∂ν) ≤ ENNReal.ofReal M := by
    calc
      _ = ∫⁻ p,liminf (fun j => ENNReal.ofReal (f j p)) atTop ∂ν :=
        lintegral_congr_ae (hNNLim.mono fun _ h => h.liminf_eq.symm)
      _ ≤ liminf (fun j => ∫⁻ p,ENNReal.ofReal (f j p) ∂ν) atTop := lintegral_liminf_le' hNnm
      _ ≤ ENNReal.ofReal M := liminf_le_of_frequently_le' (Frequently.of_forall hNnBound)
  have hi : Integrable F ν := ⟨hF.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hFn)).mpr (hFatou.trans_lt ENNReal.ofReal_lt_top)⟩
  have hM : 0 ≤ M := (integral_nonneg (hfn 0)).trans (hB 0)
  refine ⟨hi,?_⟩
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hFn)] at hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hFn),ENNReal.toReal_ofReal hM] using hb

variable {ι : Type*} [Fintype ι]

lemma stronglyMeasurable_gaussianLogCenteredPhase_section
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    StronglyMeasurable (gaussianLogCenteredPhase μ x) := by
  have hm : StronglyMeasurable (gaussianLogSpatialPhaseMean μ) :=
    measurable_gaussianLogSpatialPhase_joint.stronglyMeasurable.integral_prod_left'
  exact (measurable_gaussianScaleMixtureCharacter (gaussianRieszEuclideanCoordinates x)).stronglyMeasurable.sub hm

lemma integrable_gaussianLogCenteredPhase_sq_finiteBand (η T : ℝ) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (x : EuclideanSpace ℝ ι) :
    Integrable (fun p => ‖gaussianLogCenteredPhase μ x p‖^2)
      ((gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)) := by
  letI := finite_gaussianLogBandMeasure η T hη
  have hm : StronglyMeasurable (gaussianLogCenteredPhase μ x) :=
    stronglyMeasurable_gaussianLogCenteredPhase_section μ x
  have h2 : MemLp (gaussianLogCenteredPhase μ x) 2
      ((gaussianLogBandMeasure η T).prod (finiteStandardGaussian ι)) := by
    apply (memLp_const (2 : ℝ)).of_le hm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      exact norm_gaussianLogCenteredPhase_le μ x p)
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp h2

lemma integrable_gaussianLogCenteredPhase_sq (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun p => ‖gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p‖^2)
      (gaussianLogPhaseMeasure ι η) ∧
    (∫ p, ‖gaussianLogCenteredPhase (gaussianRieszDensityMeasure ρ) x p‖^2
      ∂gaussianLogPhaseMeasure ι η) ≤
      gaussianLogBandDiagonalMajorant η M (gaussianRieszDensityMeasure ρ) x := by
  let μ := gaussianRieszDensityMeasure ρ
  let ν := gaussianLogPhaseMeasure ι η
  let T : ℕ → ℝ := fun j => max η (j+1 : ℕ)
  let E : ℕ → Set (ℝ × (ι → ℝ)) := fun j => Iic (T j) ×ˢ univ
  let F := fun p => ‖gaussianLogCenteredPhase μ x p‖^2
  let f : ℕ → (ℝ × (ι → ℝ)) → ℝ := fun j => (E j).indicator F
  have hEj (j : ℕ) : MeasurableSet (E j) := measurableSet_Iic.prod MeasurableSet.univ
  have hTη (j : ℕ) : η ≤ T j := le_max_left _ _
  have hT1 (j : ℕ) : 1 ≤ T j := by
    have hj : (1 : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 j)
    exact hj.trans (le_max_right _ _)
  have hi (j : ℕ) : Integrable (f j) ν := by
    apply (integrable_indicator_iff (hEj j)).mpr
    change Integrable F (ν.restrict (E j))
    rw [gaussianLogPhaseMeasure_restrict]
    exact integrable_gaussianLogCenteredPhase_sq_finiteBand η (T j) hη μ x
  have hB (j : ℕ) : (∫ p,f j p ∂ν) ≤ gaussianLogBandDiagonalMajorant η M μ x := by
    rw [integral_indicator (hEj j),gaussianLogPhaseMeasure_restrict,
      integral_gaussianLogCenteredPhase_sq_band η (T j) hη (hTη j) μ x]
    exact norm_sq_centeredGaussianLogBandFeature_general_majorized η (T j) hη (hTη j) (hT1 j)
      hd ρ M hM hρ hpair x
  have hFn (p) : 0 ≤ F p := sq_nonneg _
  have hfn (j p) : 0 ≤ f j p := by
    by_cases hp : p ∈ E j
    · simpa only [f,indicator_of_mem hp] using hFn p
    · simp only [f,indicator_of_notMem hp,le_refl]
  have hc (p : ℝ × (ι → ℝ)) : Tendsto (fun j => f j p) atTop (𝓝 (F p)) := by
    have hex : ∃ j,p ∈ E j := by
      have he := gaussianLogPhase_band_exhaustion ι η
      have hp : p ∈ ⋃ j,E j := by rw [he];exact mem_univ p
      exact mem_iUnion.mp hp
    obtain ⟨J,hJ⟩ := hex
    have hE : ∀ᶠ j in atTop,p ∈ E j := by
      filter_upwards [eventually_ge_atTop J] with j hj
      have hJ' : p.1 ≤ T J := hJ.1
      have ht : T J ≤ T j := max_le_max_left η (by exact_mod_cast (Nat.add_le_add_right hj 1))
      exact ⟨hJ'.trans ht,mem_univ _⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hE] with j hj
    simp only [f,indicator_of_mem hj]
  have hm : StronglyMeasurable F :=
    (stronglyMeasurable_gaussianLogCenteredPhase_section μ x).norm.pow 2
  exact nonnegative_integrable_of_ae_tendsto_uniform_integral ν f F hi hfn hm hFn
    (gaussianLogBandDiagonalMajorant η M μ x) hB (Eventually.of_forall hc)

end DGRHS.Gaussian
#check @DGRHS.Gaussian.nonnegative_integrable_of_ae_tendsto_uniform_integral
#print axioms DGRHS.Gaussian.nonnegative_integrable_of_ae_tendsto_uniform_integral
#check @DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_sq_finiteBand
#print axioms DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_sq_finiteBand
#check @DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_sq
#print axioms DGRHS.Gaussian.integrable_gaussianLogCenteredPhase_sq

#check @DGRHS.Gaussian.stronglyMeasurable_gaussianLogCenteredPhase_section
#print axioms DGRHS.Gaussian.stronglyMeasurable_gaussianLogCenteredPhase_section
