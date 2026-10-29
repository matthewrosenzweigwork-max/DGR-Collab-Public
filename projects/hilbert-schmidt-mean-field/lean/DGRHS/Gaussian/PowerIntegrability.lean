/- UNCHECKED outside frozen proof. Actual uniform Lq bounds at ANY finite
q>1 imply both parts of probabilistic L1 uniform integrability. This permits
the source weak spectral threshold, rather than requiring a doubled margin. -/
import DGRHS.Gaussian.ChaosConvergence
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace DGRHS.Gaussian
variable {Ω j : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem uniformIntegrable_one_of_uniform_Lq_bound (F : j → Ω → ℝ)
    (q : ℝ≥0∞) (hq : 1 < q) (hqtop : q ≠ ∞)
    (hF : ∀ i, MemLp (F i) q μ) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (F i) q μ ≤ C) : UniformIntegrable F 1 μ := by
  have hqr : 1 < q.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by simp) hqtop).mpr hq
  have hexp : 0 < 1-q.toReal⁻¹ := by
    have hi : q.toReal⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hqr
    linarith
  constructor
  · unfold UnifIntegrable
    have ht := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
      (c := (C : ℝ≥0∞)) (by simp) (y := 1-q.toReal⁻¹) hexp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => zero_le)
    intro ε
    apply iSup_le
    intro i
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    calc
      eLpNorm (F i) 1 (μ.restrict s) ≤
          eLpNorm (F i) q (μ.restrict s)*(μ s)^(1-q.toReal⁻¹) := by
        simpa only [ENNReal.toReal_one, div_one, one_div, Measure.restrict_apply_univ]
          using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (p := (1 : ℝ≥0∞)) (q := q) hq.le
            ((hF i).aestronglyMeasurable.restrict (s := s))
      _ ≤ (C : ℝ≥0∞)*ε^(1-q.toReal⁻¹) := by
        have hb := (eLpNorm_restrict_le (F i) q μ s).trans (hC i)
        gcongr
  · exact ⟨C, fun i => (eLpNorm_le_eLpNorm_of_exponent_le
      (p := (1 : ℝ≥0∞)) (q := q) hq.le).trans (hC i)⟩

theorem tendsto_integral_of_Lq_bound_and_inMeasure (F : ℕ → Ω → ℝ) (G : Ω → ℝ)
    (q : ℝ≥0∞) (hq : 1 < q) (hqtop : q ≠ ∞)
    (hF : ∀ i, MemLp (F i) q μ) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (F i) q μ ≤ C)
    (hFG : TendstoInMeasure μ F atTop G) :
    Integrable G μ ∧ Tendsto (fun n => ∫ ω, F n ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) := by
  have hui := uniformIntegrable_one_of_uniform_Lq_bound F q hq hqtop hF C hC
  have hg := hui.integrable_of_tendstoInMeasure hFG
  refine ⟨hg, ?_⟩
  apply tendsto_integral_of_L1' G
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hui.memLp n)))
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num)
    (fun n => (hF n).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg)
    hui.unifIntegrable hFG

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.uniformIntegrable_one_of_uniform_Lq_bound
#print axioms DGRHS.Gaussian.tendsto_integral_of_Lq_bound_and_inMeasure
