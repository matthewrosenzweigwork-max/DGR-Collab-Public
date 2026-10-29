import DGPS.Examples.RoughBoundary.BottleneckGaussianRUF039

set_option maxHeartbeats 2000000

open MeasureTheory

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape

/-- The log moment generating function is at most `‖t‖`, since `‖U‖ = 1`. -/
lemma featureLogPartition_le_norm_RUF040 {L ε : ℝ} (hL : 0 < L) (t : E2) :
    Real.log (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1) ≤ ‖t‖ := by
  have hpos := integral_exp_inner_pos_RUF039 (ε := ε) hL t
  have hle : ∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1 ≤ Real.exp ‖t‖ := by
    calc ∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1
        ≤ ∫ _y, Real.exp ‖t‖ ∂haar 1 := by
          refine integral_mono (integrable_exp_tilt hL ε t) (integrable_const _) fun y => ?_
          apply Real.exp_le_exp.mpr
          simpa [norm_Ufeat] using real_inner_le_norm t (Ufeat L ε y)
      _ = Real.exp ‖t‖ := by simp
  calc Real.log (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1)
      ≤ Real.log (Real.exp ‖t‖) := Real.log_le_log hpos hle
    _ = ‖t‖ := Real.log_exp _

/-- For `4κ ≤ ‖t‖` the feature potential dominates `‖t‖² / (4κ)`. -/
lemma featurePotential_lower_RUF040 {L ε κ : ℝ} (hκ : 0 < κ) (hL : 0 < L) {t : E2}
    (ht : 4 * κ ≤ ‖t‖) :
    ‖t‖ ^ 2 / (4 * κ) ≤ featurePotential κ (Ufeat L ε) t := by
  have hlog := featureLogPartition_le_norm_RUF040 (ε := ε) hL t
  have hq : ‖t‖ ≤ ‖t‖ ^ 2 / (4 * κ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left ht (norm_nonneg t)]
  have hsplit : ‖t‖ ^ 2 / (2 * κ) = ‖t‖ ^ 2 / (4 * κ) + ‖t‖ ^ 2 / (4 * κ) := by
    field_simp
    ring
  unfold featurePotential featureLogPartition
  linarith

/-- `x e^{-x} ≤ e^{-1}` for `x ≥ 0`. -/
lemma mul_exp_neg_le_RUF040 (x : ℝ) :
    x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (x - 1)
  have hE : 0 < Real.exp x := Real.exp_pos x
  have h1 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have hsplit : Real.exp (x - 1) = Real.exp (-1) * Real.exp x := by
    rw [← Real.exp_add]
    ring_nf
  refine le_of_mul_le_mul_right ?_ hE
  calc x * Real.exp (-x) * Real.exp x = x * (Real.exp (-x) * Real.exp x) := by ring
    _ = x := by rw [h1, mul_one]
    _ ≤ Real.exp (x - 1) := by linarith
    _ = Real.exp (-1) * Real.exp x := hsplit

/-- Uniform bound on the unnormalized Gibbs-tilted exponential integral over the plane,
from the three-region decomposition. -/
lemma integral_exp_neg_bound_RUF040 {L ε κ a r₀ R₀ b₀ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (N : ℕ+) (ha : 0 < a) (_hb₀ : 0 < b₀) (hR : max r₀ (4 * κ) < R₀)
    (hloc : ∀ t : E2, ‖t‖ ≤ r₀ → a * ‖t‖ ^ 2 ≤ featurePotential κ (Ufeat L ε) t)
    (hmin : IsLeast ((fun t : E2 => featurePotential κ (Ufeat L ε) t) ''
      {t : E2 | r₀ ≤ ‖t‖ ∧ ‖t‖ ≤ R₀}) b₀) :
    ∫ t : E2, Real.exp (-(N : ℝ) * featurePotential κ (Ufeat L ε) t) ≤
      Real.pi / ((N : ℝ) * a) +
        Real.pi * R₀ ^ 2 * Real.exp (-((N : ℝ) * b₀)) +
        Real.pi / ((N : ℝ) / (4 * κ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have h4 : 4 * κ < R₀ := lt_of_le_of_lt (le_max_right _ _) hR
  have hR0 : 0 < R₀ := by linarith
  have hc1 : (0 : ℝ) < (N : ℝ) * a := mul_pos hN ha
  have hc3 : (0 : ℝ) < (N : ℝ) / (4 * κ) := by positivity
  have hpt : ∀ t : E2, Real.exp (-(N : ℝ) * featurePotential κ (Ufeat L ε) t) ≤
      Real.exp (-((N : ℝ) * a) * ‖t‖ ^ 2) +
        (Metric.closedBall (0 : E2) R₀).indicator
          (fun _ => Real.exp (-((N : ℝ) * b₀))) t +
        Real.exp (-((N : ℝ) / (4 * κ)) * ‖t‖ ^ 2) := by
    intro t
    have hg₁ : 0 ≤ Real.exp (-((N : ℝ) * a) * ‖t‖ ^ 2) := (Real.exp_pos _).le
    have hg₃ : 0 ≤ Real.exp (-((N : ℝ) / (4 * κ)) * ‖t‖ ^ 2) := (Real.exp_pos _).le
    have hg₂ : 0 ≤ (Metric.closedBall (0 : E2) R₀).indicator
        (fun _ => Real.exp (-((N : ℝ) * b₀))) t :=
      Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) t
    by_cases h1 : ‖t‖ ≤ r₀
    · have hl := hloc t h1
      have hm := mul_le_mul_of_nonneg_left hl hN.le
      have hle : -(N : ℝ) * featurePotential κ (Ufeat L ε) t ≤ -((N : ℝ) * a) * ‖t‖ ^ 2 := by
        nlinarith
      have e := Real.exp_le_exp.mpr hle
      linarith
    · by_cases h2 : ‖t‖ ≤ R₀
      · have hgt : r₀ ≤ ‖t‖ := (not_le.mp h1).le
        have hann : b₀ ≤ featurePotential κ (Ufeat L ε) t :=
          hmin.2 ⟨t, ⟨hgt, h2⟩, rfl⟩
        have hm := mul_le_mul_of_nonneg_left hann hN.le
        have hle : -(N : ℝ) * featurePotential κ (Ufeat L ε) t ≤ -((N : ℝ) * b₀) := by
          nlinarith
        have e := Real.exp_le_exp.mpr hle
        have hmem : t ∈ Metric.closedBall (0 : E2) R₀ := by
          rw [mem_closedBall_zero_iff]
          exact h2
        rw [Set.indicator_of_mem hmem]
        linarith
      · have h4t : 4 * κ ≤ ‖t‖ := by linarith [not_le.mp h2]
        have hq := featurePotential_lower_RUF040 (ε := ε) hκ hL h4t
        have hm := mul_le_mul_of_nonneg_left hq hN.le
        have hle : -(N : ℝ) * featurePotential κ (Ufeat L ε) t ≤
            -((N : ℝ) / (4 * κ)) * ‖t‖ ^ 2 := by
          have e : (N : ℝ) * (‖t‖ ^ 2 / (4 * κ)) = (N : ℝ) / (4 * κ) * ‖t‖ ^ 2 := by
            ring
          nlinarith
        have e := Real.exp_le_exp.mpr hle
        have hnmem : t ∉ Metric.closedBall (0 : E2) R₀ := by
          rw [mem_closedBall_zero_iff]
          exact h2
        rw [Set.indicator_of_notMem hnmem]
        linarith
  have hI1 := integrable_gauss_E2_RUF039 hc1
  have hI3 := integrable_gauss_E2_RUF039 hc3
  have hI2 : Integrable ((Metric.closedBall (0 : E2) R₀).indicator
      (fun _ => Real.exp (-((N : ℝ) * b₀)))) := by
    refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    exact integrableOn_const (measure_closedBall_lt_top (μ := (volume : Measure E2))).ne
  have hint : ∫ t : E2, Real.exp (-(N : ℝ) * featurePotential κ (Ufeat L ε) t) ≤
      ∫ t : E2, (Real.exp (-((N : ℝ) * a) * ‖t‖ ^ 2) +
        (Metric.closedBall (0 : E2) R₀).indicator
          (fun _ => Real.exp (-((N : ℝ) * b₀))) t +
        Real.exp (-((N : ℝ) / (4 * κ)) * ‖t‖ ^ 2)) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
      ((hI1.add hI2).add hI3) (Filter.Eventually.of_forall hpt)
  have hI12 : Integrable (fun t : E2 => Real.exp (-((N : ℝ) * a) * ‖t‖ ^ 2) +
      (Metric.closedBall (0 : E2) R₀).indicator (fun _ => Real.exp (-((N : ℝ) * b₀))) t) :=
    hI1.add hI2
  rw [integral_add hI12 hI3, integral_add hI1 hI2] at hint
  have hG1 : ∫ t : E2, Real.exp (-((N : ℝ) * a) * ‖t‖ ^ 2) = Real.pi / ((N : ℝ) * a) :=
    gauss_integral_E2_RUF039 hc1
  have hG3 : ∫ t : E2, Real.exp (-((N : ℝ) / (4 * κ)) * ‖t‖ ^ 2) =
      Real.pi / ((N : ℝ) / (4 * κ)) :=
    gauss_integral_E2_RUF039 hc3
  have hG2 : ∫ t : E2, (Metric.closedBall (0 : E2) R₀).indicator
      (fun _ => Real.exp (-((N : ℝ) * b₀))) t =
      Real.pi * R₀ ^ 2 * Real.exp (-((N : ℝ) * b₀)) := by
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
    rw [Measure.real, EuclideanSpace.volume_closedBall_fin_two]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR0.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  rw [hG1, hG2, hG3] at hint
  exact hint

/-- RUF040, the uniform particle normalizer from three regions. For the selected feature
parameter `L` (from the RUF039 Gaussian representation), with `a, r₀` a local quadratic lower
bound on `Ψ`, `R₀ > max{r₀, 4κ}`, and `b₀ = min` of `Ψ` on the annulus `r₀ ≤ |t| ≤ R₀` positive,
the particle normalizer `Z_N` satisfies `1 ≤ Z_N ≤ (2κa)⁻¹ + 2 + R₀² / (2κ e b₀)` for all
`N ≥ 1`. -/
theorem uniform_particle_normalizer_from_three_regions :
    ∃ L : ℝ, 0 < L ∧ FreeEnergyDecomposition L (1 / L) ∧
      ∀ a r₀ R₀ b₀ : ℝ, 0 < a → 0 < r₀ →
        (∀ t : E2, ‖t‖ ≤ r₀ → a * ‖t‖ ^ 2 ≤ featurePotential kappa0 (Ufeat L (1 / L)) t) →
        max r₀ (4 * kappa0) < R₀ → 0 < b₀ →
        IsLeast ((fun t : E2 => featurePotential kappa0 (Ufeat L (1 / L)) t) ''
          {t : E2 | r₀ ≤ ‖t‖ ∧ ‖t‖ ≤ R₀}) b₀ →
        ∀ N : ℕ+,
          1 ≤ ∫ x : ParticleSpace 1 N,
              Real.exp ((N : ℝ) * kappa0 * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L (1 / L) (x i)‖ ^ 2 / 2)
                ∂particleHaar 1 N ∧
          ∫ x : ParticleSpace 1 N,
              Real.exp ((N : ℝ) * kappa0 * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L (1 / L) (x i)‖ ^ 2 / 2)
                ∂particleHaar 1 N ≤
            (2 * kappa0 * a)⁻¹ + 2 + R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := by
  obtain ⟨L, hL, hFree, hrep⟩ := exact_gaussian_representation_of_shifted_partition
  refine ⟨L, hL, hFree, ?_⟩
  intro a r₀ R₀ b₀ ha _hr₀ hloc hR hb₀ hmin N
  have hκ : 0 < kappa0 := kappa0_pos_RUF039
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlow : (1 : ℝ) ≤ ∫ x : ParticleSpace 1 N,
      Real.exp ((N : ℝ) * kappa0 * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L (1 / L) (x i)‖ ^ 2 / 2)
        ∂particleHaar 1 N := by
    have hU : Continuous (Ufeat L (1 / L)) := continuous_Ufeat hL (1 / L)
    have hcont : Continuous (fun x : ParticleSpace 1 N =>
        Real.exp ((N : ℝ) * kappa0 * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L (1 / L) (x i)‖ ^ 2 / 2)) := by
      fun_prop
    have hgi : Integrable (fun x : ParticleSpace 1 N =>
        Real.exp ((N : ℝ) * kappa0 * ‖(N : ℝ)⁻¹ • ∑ i, Ufeat L (1 / L) (x i)‖ ^ 2 / 2))
        (particleHaar 1 N) :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc (1 : ℝ) = ∫ _x : ParticleSpace 1 N, (1 : ℝ) ∂particleHaar 1 N := by simp
      _ ≤ _ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => zero_le_one)
          hgi (Filter.Eventually.of_forall fun x => ?_)
        apply Real.one_le_exp
        positivity
  refine ⟨hlow, ?_⟩
  rw [hrep N]
  have hbound := integral_exp_neg_bound_RUF040 (ε := 1 / L) hL hκ N ha hb₀ hR hloc hmin
  have hNE : (N : ℝ) * Real.exp (-((N : ℝ) * b₀)) ≤ Real.exp (-1) / b₀ := by
    rw [le_div_iff₀ hb₀]
    have hx := mul_exp_neg_le_RUF040 ((N : ℝ) * b₀)
    calc (N : ℝ) * Real.exp (-((N : ℝ) * b₀)) * b₀
        = (N : ℝ) * b₀ * Real.exp (-((N : ℝ) * b₀)) := by ring
      _ ≤ Real.exp (-1) := hx
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have key : (N : ℝ) / (2 * Real.pi * kappa0) *
      (Real.pi / ((N : ℝ) * a) + Real.pi * R₀ ^ 2 * Real.exp (-((N : ℝ) * b₀)) +
        Real.pi / ((N : ℝ) / (4 * kappa0))) =
      (2 * kappa0 * a)⁻¹ + 2 +
        ((N : ℝ) * Real.exp (-((N : ℝ) * b₀))) * (R₀ ^ 2 / (2 * kappa0)) := by
    field_simp
    ring
  have hfin : (N : ℝ) * Real.exp (-((N : ℝ) * b₀)) * (R₀ ^ 2 / (2 * kappa0)) ≤
      Real.exp (-1) / b₀ * (R₀ ^ 2 / (2 * kappa0)) :=
    mul_le_mul_of_nonneg_right hNE (by positivity)
  have hexp : Real.exp (-1) / b₀ * (R₀ ^ 2 / (2 * kappa0)) =
      R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := by
    rw [Real.exp_neg]
    field_simp
  calc (N : ℝ) / (2 * Real.pi * kappa0) * ∫ t : E2,
        Real.exp (-(N : ℝ) * featurePotential kappa0 (Ufeat L (1 / L)) t)
      ≤ (N : ℝ) / (2 * Real.pi * kappa0) *
          (Real.pi / ((N : ℝ) * a) + Real.pi * R₀ ^ 2 * Real.exp (-((N : ℝ) * b₀)) +
            Real.pi / ((N : ℝ) / (4 * kappa0))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (2 * kappa0 * a)⁻¹ + 2 +
        ((N : ℝ) * Real.exp (-((N : ℝ) * b₀))) * (R₀ ^ 2 / (2 * kappa0)) := key
    _ ≤ (2 * kappa0 * a)⁻¹ + 2 + R₀ ^ 2 / (2 * kappa0 * Real.exp 1 * b₀) := by
        linarith [hfin, hexp]

end DGPS.Examples.RoughBoundary.Bottleneck
