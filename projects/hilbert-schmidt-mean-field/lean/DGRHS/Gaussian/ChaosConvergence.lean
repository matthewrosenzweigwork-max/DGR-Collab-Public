/- Unchecked preparation outside root proof. DGR second-chaos convergence
adapters, using pinned subsequence criterion, Holder and Vitali. -/
import DGRHS.Gaussian.CenteredChaos
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace DGRHS.Gaussian
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Continuity transports actual convergence in probability, proved by the
existing subsequence/AE criterion. No desired exponential limit is assumed. -/
lemma tendstoInMeasure_continuous_real_comp {F : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hFG : TendstoInMeasure μ F atTop G) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    TendstoInMeasure μ (fun n ω ↦ φ (F n ω)) atTop (fun ω ↦ φ (G ω)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n ↦ hφ.comp_aestronglyMeasurable (hF n))).mpr
  intro ns hns
  obtain ⟨ms,hms,hae⟩ := (hFG.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,hae.mono ?_⟩
  intro ω hω
  exact hφ.continuousAt.tendsto.comp hω

/-- An actual uniform L2 bound supplies both parts of probabilistic L1 uniform
integrability, by restricted Holder on arbitrary small-measure sets. -/
lemma uniformIntegrable_one_of_uniform_L2_bound {j : Type*} (F : j → Ω → ℝ)
    (hF : ∀ i, MemLp (F i) 2 μ) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (F i) 2 μ ≤ C) : UniformIntegrable F 1 μ := by
  constructor
  · unfold UnifIntegrable
    have ht := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
      (c := (C : ℝ≥0∞)) (by simp) (y := (1/2 : ℝ)) (by norm_num)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ ↦ zero_le)
    intro ε
    apply iSup_le
    intro i
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    calc
      eLpNorm (F i) 1 (μ.restrict s) ≤ eLpNorm (F i) 2 (μ.restrict s) *
          (μ s) ^ (1/2 : ℝ) := by
        convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
          ((hF i).aestronglyMeasurable.restrict (s := s)) using 1 <;> norm_num
      _ ≤ (C : ℝ≥0∞) * ε ^ (1/2 : ℝ) := by
        have hb := (eLpNorm_restrict_le (F i) 2 μ s).trans (hC i)
        gcongr
  · exact ⟨C,fun i ↦ (eLpNorm_le_eLpNorm_of_exponent_le (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)).trans (hC i)⟩

/-- This criterion will be instantiated with the proved finite Gaussian
regularized-product bound; it is not an assumption of the final chaos theorem. -/
lemma tendsto_integral_of_L2_bound_and_inMeasure (F : ℕ → Ω → ℝ) (G : Ω → ℝ)
    (hF : ∀ n, MemLp (F n) 2 μ) (C : ℝ≥0)
    (hC : ∀ n, eLpNorm (F n) 2 μ ≤ C)
    (hFG : TendstoInMeasure μ F atTop G) :
    Integrable G μ ∧ Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) := by
  have hui := uniformIntegrable_one_of_uniform_L2_bound F hF C hC
  have hg := hui.integrable_of_tendstoInMeasure hFG
  refine ⟨hg,?_⟩
  apply tendsto_integral_of_L1' G
    (Eventually.of_forall (fun n ↦ (hF n).integrable (by norm_num)))
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num)
    (fun n ↦ (hF n).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg)
    hui.unifIntegrable hFG

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.tendstoInMeasure_continuous_real_comp
#print axioms DGRHS.Gaussian.uniformIntegrable_one_of_uniform_L2_bound
#print axioms DGRHS.Gaussian.tendsto_integral_of_L2_bound_and_inMeasure
