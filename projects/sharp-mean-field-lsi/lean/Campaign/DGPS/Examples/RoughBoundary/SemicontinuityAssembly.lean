import DGPS.Examples.RoughBoundary.SemicontinuitySequenceSEM011
import DGPS.Examples.RoughBoundary.SemicontinuityUpperSEM014

/-!
# SEM015: both semicontinuity failures (final assembly)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 8 (S1 lower, S2 upper) and
`ROUGH_COUNTEREXAMPLE_FINAL_AUDIT_REPORT.md` section 6.

One landscape parameter `L` is selected once and serves both families. It is at least the
bounded-profile certificate threshold of SEM011 and at least the small-amplitude threshold of
SEM012. The lower family is the smooth mollification sequence of the rough primary kernel at
amplitude `1/L` (rates `0`, limit rates `a0`). The upper family is the rough sequence
`ε_j = e₀/(j+1)` (rates `a0`, limit the smooth zero-amplitude base with rates `0`). Both families
converge in every fixed `C^α` and `W^{1,p}` topology, and neither `r_*` nor `r_ms` is lower or
upper semicontinuous on any of these spaces.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal NNReal

namespace DGPS.RegularityBoundary

open DGPS.Analysis.PeriodicMollification
open DGPS.Analysis.RateTopology
open DGPS.Examples.RoughBoundary
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape (RoughLandscapeCertificate)

/-- Lower family at a fixed landscape parameter `L`: the rough primary kernel at amplitude `1/L`
has both rates `a0`, and its smooth mollification approximants are smooth with both rates `0`. -/
lemma lower_family_SEM015 {L : ℝ} (hL : 0 < L)
    (hcert : ∀ f : Torus 1 → ℝ, Measurable f → (∀ y, |f y| ≤ Spikes.hMean) →
      RoughLandscapeCertificate (UfeatF L (1 / L) f)) :
    scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      ∀ j : ℕ, IsSmoothPeriodic (approximation_SEM011 hL (1 / L) j).W ∧
        scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
        speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 := by
  have hc : RoughLandscapeCertificate (Feature.Ufeat L (1 / L)) :=
    hcert Spikes.gT continuous_gT.measurable Spikes.abs_gT_le
  have hr := primary_rates_SEM011 hL (one_div_ne_zero hL.ne') hc
  have hz : ∀ j : ℕ, scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
      speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 := fun j =>
    smoothKernel_rates_zero_SEM011 hL (1 / L) (smooth_profile_SEM011 j)
      (hcert _ (continuous_mollify_gT (width_pos_SEM011 j)).measurable
        (abs_mollify_gT_le (width_pos_SEM011 j))) _
  exact ⟨hr.1, hr.2, fun j => ⟨isSmoothPeriodic_prodKernel_SEM011
    (isSmoothPeriodic_UfeatF_SEM011 hL (1 / L) (smooth_profile_SEM011 j)), (hz j).1, (hz j).2⟩⟩

/-- Lower failures on one fixed `C^α` topology at the rough primary point. -/
lemma holder_lower_SEM015 {L : ℝ} (hL : 0 < L)
    (hz : ∀ j : ℕ, scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
      speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0)
    (hr : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2))
    (α : ℝ≥0) (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1) :
    @Tendsto ℕ (HolderKernel α)
        (fun j => ⟨approximation_SEM011 hL (1 / L) j, approximation_holder_SEM011 hL (1 / L) h0 h1 j⟩)
        atTop (@nhds _ (holderTopology α)
          ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL (1 / L) h0 h1⟩) ∧
      (haveI := holderTopology α
       ¬ LowerSemicontinuous (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1) ∧
       ¬ LowerSemicontinuous (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1)) := by
  have ht := tendsto_holder_approximation_SEM011 hL (1 / L) h0 h1
  have hpos1 : (0 : ℝ≥0∞) < scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) := by
    rw [hr.1]; exact positive_a0_SEM011
  have hpos2 : (0 : ℝ≥0∞) < speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) := by
    rw [hr.2]; exact positive_a0_SEM011
  refine ⟨ht, ?_⟩
  let _ := holderTopology α
  exact ⟨fun h => zero_sequence_not_lsc_SEM011
      (f := fun K : HolderKernel α => scalarKernelRate_SEM011 K.1) ht (fun j => (hz j).1) hpos1
      (h ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL (1 / L) h0 h1⟩),
    fun h => zero_sequence_not_lsc_SEM011
      (f := fun K : HolderKernel α => speciesKernelRate_SEM011 K.1) ht (fun j => (hz j).2) hpos2
      (h ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL (1 / L) h0 h1⟩)⟩

/-- Both failures on one fixed `C^α` topology, with the two explicit families at the same `L`. -/
lemma holder_SEM015 {L : ℝ} (hL : 0 < L) {e : ℕ → ℝ}
    (hz : ∀ j : ℕ, scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
      speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0)
    (hr : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2))
    (hε1 : ∀ j : ℕ, |e j| ≤ 1) (he : Tendsto e atTop (𝓝 0))
    (hA : ∀ j : ℕ, scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) =
        ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) = ENNReal.ofReal (4 * π ^ 2))
    (hA0 : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0 ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0)
    (α : ℝ≥0) (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1) :
    @Tendsto ℕ (HolderKernel α)
        (fun j => ⟨approximation_SEM011 hL (1 / L) j, approximation_holder_SEM011 hL (1 / L) h0 h1 j⟩)
        atTop (@nhds _ (holderTopology α)
          ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL (1 / L) h0 h1⟩) ∧
      (haveI := holderTopology α
       ¬ LowerSemicontinuous (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1) ∧
       ¬ LowerSemicontinuous (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1)) ∧
    @Tendsto ℕ (HolderKernel α)
        (fun j => ⟨primaryKernel_SEM011 hL (e j), primary_holder_SEM011 hL (e j) h0 h1⟩)
        atTop (@nhds _ (holderTopology α)
          ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩) ∧
      (haveI := holderTopology α
       ¬ UpperSemicontinuous (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1) ∧
       ¬ UpperSemicontinuous (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1)) := by
  obtain ⟨hlT, hlN⟩ := holder_lower_SEM015 hL hz hr α h0 h1
  obtain ⟨huT, huN⟩ := holder_part_SEM014 hL hε1 he hA hA0 α h0 h1
  refine ⟨hlT, hlN, huT, ?_⟩
  let _ := holderTopology α
  exact ⟨fun h => huN.1 (h ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩),
    fun h => huN.2 (h ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩)⟩

/-- Lower failures on one fixed `W^{1,p}` topology at the rough primary point. -/
lemma sobolev_lower_SEM015 {L : ℝ} (hL : 0 < L)
    (hz : ∀ j : ℕ, scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
      speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0)
    (hr : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2))
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
    @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
        (fun j => ⟨approximation_SEM011 hL (1 / L) j, approximation_sobolev_SEM011 hL (1 / L) _ j⟩)
        atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
          ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL (1 / L) hp hp2⟩) ∧
      (haveI := sobolevTopology (ENNReal.ofReal p)
       ¬ LowerSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
          scalarKernelRate_SEM011 K.1) ∧
       ¬ LowerSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
          speciesKernelRate_SEM011 K.1)) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
  have ht := tendsto_sobolev_approximation_SEM011 hL (1 / L) hp hp2
  have hpos1 : (0 : ℝ≥0∞) < scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) := by
    rw [hr.1]; exact positive_a0_SEM011
  have hpos2 : (0 : ℝ≥0∞) < speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) := by
    rw [hr.2]; exact positive_a0_SEM011
  refine ⟨ht, ?_⟩
  let _ := sobolevTopology (ENNReal.ofReal p)
  exact ⟨fun h => zero_sequence_not_lsc_SEM011
      (f := fun K : SobolevKernel (ENNReal.ofReal p) => scalarKernelRate_SEM011 K.1)
      ht (fun j => (hz j).1) hpos1
      (h ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL (1 / L) hp hp2⟩),
    fun h => zero_sequence_not_lsc_SEM011
      (f := fun K : SobolevKernel (ENNReal.ofReal p) => speciesKernelRate_SEM011 K.1)
      ht (fun j => (hz j).2) hpos2
      (h ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL (1 / L) hp hp2⟩)⟩

/-- Both failures on one fixed `W^{1,p}` topology, with the two explicit families at the same `L`. -/
lemma sobolev_SEM015 {L : ℝ} (hL : 0 < L) {e : ℕ → ℝ}
    (hz : ∀ j : ℕ, scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
      speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0)
    (hr : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2))
    (he : Tendsto e atTop (𝓝 0))
    (hA : ∀ j : ℕ, scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) =
        ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (e j)) = ENNReal.ofReal (4 * π ^ 2))
    (hA0 : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0 ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
    @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
        (fun j => ⟨approximation_SEM011 hL (1 / L) j, approximation_sobolev_SEM011 hL (1 / L) _ j⟩)
        atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
          ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL (1 / L) hp hp2⟩) ∧
      (haveI := sobolevTopology (ENNReal.ofReal p)
       ¬ LowerSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
          scalarKernelRate_SEM011 K.1) ∧
       ¬ LowerSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
          speciesKernelRate_SEM011 K.1)) ∧
    @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
        (fun j => ⟨primaryKernel_SEM011 hL (e j), primary_sobolev_SEM011 hL (e j) hp hp2⟩)
        atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
          ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩) ∧
      (haveI := sobolevTopology (ENNReal.ofReal p)
       ¬ UpperSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
          scalarKernelRate_SEM011 K.1) ∧
       ¬ UpperSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
          speciesKernelRate_SEM011 K.1)) := by
  obtain ⟨hlT, hlN⟩ := sobolev_lower_SEM015 hL hz hr hp hp2
  obtain ⟨huT, huN⟩ := sobolev_part_SEM014 hL hp hp2 he hA hA0
  refine ⟨hlT, hlN, huT, ?_⟩
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
  let _ := sobolevTopology (ENNReal.ofReal p)
  exact ⟨fun h => huN.1 (h ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩),
    fun h => huN.2 (h ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩)⟩

/-- **SEM015.** Both semicontinuity failures for both absolute nonlinear rates. There are
`e₀ > 0` and one finite `L > 0` such that:

* the lower family `W_{L,1/L}` has both rates `a0 = 4π²` at the rough primary kernel, while its
  smooth mollification approximants are smooth with both rates `0`;
* the upper family `W_{L,e₀/(j+1)}` has both rates `a0`, converging to the smooth base `W_{L,0}`,
  which has both rates `0`;
* for every fixed `0 < α < 1` (resp. `1 ≤ p < 2`), the lower witness converges in `C^α`
  (resp. `W^{1,p}`) and neither `r_*` nor `r_ms` is lower semicontinuous there, and the upper
  witness converges and neither rate is upper semicontinuous there. -/
theorem rates_neither_semicontinuous :
    ∃ (e0 L : ℝ) (hL : 0 < L), 0 < e0 ∧
      (scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
        speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) = ENNReal.ofReal (4 * π ^ 2) ∧
        ∀ j : ℕ, IsSmoothPeriodic (approximation_SEM011 hL (1 / L) j).W ∧
          scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
          speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0) ∧
      ((∀ j : ℕ, scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1))) =
            ENNReal.ofReal (4 * π ^ 2) ∧
          speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1))) =
            ENNReal.ofReal (4 * π ^ 2)) ∧
        scalarKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0 ∧
        speciesKernelRate_SEM011 (primaryKernel_SEM011 hL 0) = 0) ∧
      (∀ (α : ℝ≥0) (h0 : 0 < (α : ℝ)) (h1 : (α : ℝ) < 1),
        @Tendsto ℕ (HolderKernel α)
            (fun j => ⟨approximation_SEM011 hL (1 / L) j,
              approximation_holder_SEM011 hL (1 / L) h0 h1 j⟩)
            atTop (@nhds _ (holderTopology α)
              ⟨primaryKernel_SEM011 hL (1 / L), primary_holder_SEM011 hL (1 / L) h0 h1⟩) ∧
          (haveI := holderTopology α
           ¬ LowerSemicontinuous (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1) ∧
           ¬ LowerSemicontinuous (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1)) ∧
        @Tendsto ℕ (HolderKernel α)
            (fun j => ⟨primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1)),
              primary_holder_SEM011 hL (e0 / ((j : ℝ) + 1)) h0 h1⟩)
            atTop (@nhds _ (holderTopology α)
              ⟨primaryKernel_SEM011 hL 0, primary_holder_SEM011 hL 0 h0 h1⟩) ∧
          (haveI := holderTopology α
           ¬ UpperSemicontinuous (fun K : HolderKernel α => scalarKernelRate_SEM011 K.1) ∧
           ¬ UpperSemicontinuous (fun K : HolderKernel α => speciesKernelRate_SEM011 K.1))) ∧
      (∀ (p : ℝ) (hp : 1 ≤ p) (hp2 : p < 2),
        haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hp⟩
        @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
            (fun j => ⟨approximation_SEM011 hL (1 / L) j,
              approximation_sobolev_SEM011 hL (1 / L) _ j⟩)
            atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
              ⟨primaryKernel_SEM011 hL (1 / L), primary_sobolev_SEM011 hL (1 / L) hp hp2⟩) ∧
          (haveI := sobolevTopology (ENNReal.ofReal p)
           ¬ LowerSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
              scalarKernelRate_SEM011 K.1) ∧
           ¬ LowerSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
              speciesKernelRate_SEM011 K.1)) ∧
        @Tendsto ℕ (SobolevKernel (ENNReal.ofReal p))
            (fun j => ⟨primaryKernel_SEM011 hL (e0 / ((j : ℝ) + 1)),
              primary_sobolev_SEM011 hL (e0 / ((j : ℝ) + 1)) hp hp2⟩)
            atTop (@nhds _ (sobolevTopology (ENNReal.ofReal p))
              ⟨primaryKernel_SEM011 hL 0, primary_sobolev_SEM011 hL 0 hp hp2⟩) ∧
          (haveI := sobolevTopology (ENNReal.ofReal p)
           ¬ UpperSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
              scalarKernelRate_SEM011 K.1) ∧
           ¬ UpperSemicontinuous (fun K : SobolevKernel (ENNReal.ofReal p) =>
              speciesKernelRate_SEM011 K.1))) := by
  obtain ⟨L1, hL1, hcert⟩ := certificate_of_bounded_profile
  obtain ⟨ε₀, L₀, hε₀, -, -, hmain⟩ := every_small_nonzero_amplitude_has_exact_positive_rates
  obtain ⟨L, hLL1, hLL0⟩ : ∃ L : ℝ, L1 ≤ L ∧ L₀ ≤ L :=
    ⟨max L1 L₀, le_max_left _ _, le_max_right _ _⟩
  have hL : 0 < L := lt_of_lt_of_le one_pos (hL1.trans hLL1)
  have hlow := lower_family_SEM015 hL (fun f hf hfb => hcert L hLL1 f hf hfb)
  have hr : scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) =
        ENNReal.ofReal (4 * π ^ 2) ∧
      speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (1 / L)) =
        ENNReal.ofReal (4 * π ^ 2) := ⟨hlow.1, hlow.2.1⟩
  have hz : ∀ j : ℕ, scalarKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 ∧
      speciesKernelRate_SEM011 (approximation_SEM011 hL (1 / L) j) = 0 := fun j =>
    ⟨(hlow.2.2 j).2.1, (hlow.2.2 j).2.2⟩
  have hm := hmain L hLL0 hL
  have hε : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  have hrate : ∀ j : ℕ,
      scalarKernelRate_SEM011 (primaryKernel_SEM011 hL (min ε₀ 1 / ((j : ℝ) + 1))) =
          ENNReal.ofReal (4 * π ^ 2) ∧
        speciesKernelRate_SEM011 (primaryKernel_SEM011 hL (min ε₀ 1 / ((j : ℝ) + 1))) =
          ENNReal.ofReal (4 * π ^ 2) := by
    intro j
    obtain ⟨hpos, hle, -⟩ := eps_seq_SEM014 hε₀ j
    exact kernel_rates_of_model_SEM014 hL _
      ((hm.1 _ (abs_pos_of_pos hpos) (by rw [abs_of_pos hpos]; exact hle)).2.2)
  have hr0 := kernel_rates_of_model_SEM014 hL 0 hm.2
  have hε1 : ∀ j : ℕ, |min ε₀ 1 / ((j : ℝ) + 1)| ≤ 1 := by
    intro j
    obtain ⟨hpos, -, hle1⟩ := eps_seq_SEM014 hε₀ j
    rw [abs_of_pos hpos]
    exact hle1
  have he := tendsto_eps_seq_SEM014 ε₀
  exact ⟨min ε₀ 1, L, hL, hε, hlow,
    ⟨hrate, hr0.1, hr0.2⟩,
    fun α h0 h1 => holder_SEM015 (e := fun j : ℕ => min ε₀ 1 / ((j : ℝ) + 1)) hL hz hr
      hε1 he hrate hr0 α h0 h1,
    fun p hp hp2 => sobolev_SEM015 (e := fun j : ℕ => min ε₀ 1 / ((j : ℝ) + 1)) hL hz hr
      he hrate hr0 hp hp2⟩

end DGPS.RegularityBoundary
