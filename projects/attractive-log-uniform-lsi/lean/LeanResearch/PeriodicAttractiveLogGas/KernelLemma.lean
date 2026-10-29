import LeanResearch.PeriodicAttractiveLogGas.GreenIntegrability

/-! Complete development statement of source Lemma 2.1 (`lem:kernel`), for the
actual mean-zero Green representative. The preceding files supply the Fourier,
distributional fundamental-solution, Weyl, compactness and polar-integrability
proofs. This module neither asserts Gibbs normalization nor Theorem 1.1. -/

noncomputable section
open MeasureTheory InnerProductSpace Metric Set
open scoped ContDiff

namespace PeriodicAttractiveLogGas

theorem regularGreenRepresentative_test_integrable (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) :
    Integrable (fun x ↦ regularGreenRepresentative x * torusNegativeLaplacian f hf x)
      torusMeasure := by
  apply (greenRealRepresentative_test_integrable f hf).congr
  filter_upwards [regularGreenRepresentative_ae] with x hx
  rw [hx]

theorem regularGreenRepresentative_weak_equation (f : C(Torus, ℝ))
    (hf : ContDiff ℝ ∞ (fun y ↦ f (torusQuotient y))) :
    (∫ x, regularGreenRepresentative x * torusNegativeLaplacian f hf x ∂torusMeasure) =
      (2 * Real.pi) * (f 0 - ∫ x, f x ∂torusMeasure) := by
  apply Eq.trans (integral_congr_ae ?_) (greenRealRepresentative_weak_equation f hf)
  filter_upwards [regularGreenRepresentative_ae] with x hx
  rw [hx]

/-- The exact kernel conclusions, with genuine Euclidean gradient and Hessian
and every finite real exponent in the source ranges. Four constants are chosen
before the point is quantified. The source radius-one-half chart is explicit. -/
theorem kernelLemma :
    (∀ z : Torus, regularGreenRepresentative (-z) = regularGreenRepresentative z) ∧
    ContDiffOn ℝ ∞ (fun x : PlanarSpace ↦ regularGreenRepresentative (torusQuotient x))
      {x | torusQuotient x ≠ 0} ∧
    (∀ k : Frequency,
      UnitAddTorus.mFourierCoeff (fun z ↦ (regularGreenRepresentative z : ℂ)) k =
        if k = 0 then 0 else ((1 / (2 * Real.pi * frequencySq k) : ℝ) : ℂ)) ∧
    (∃ h : PlanarSpace → ℝ,
      ContDiffOn ℝ ∞ h (ball 0 (1 / 2 : ℝ)) ∧ HarmonicOnNhd h (ball 0 (1 / 2 : ℝ)) ∧
      ∀ x : PlanarSpace, ‖x‖ < (1 / 2 : ℝ) → x ≠ 0 →
        regularGreenRepresentative (torusQuotient x) =
          -Real.log ‖x‖ + (Real.pi / 2) * ‖x‖ ^ 2 + h x) ∧
    (∃ C₀ Cg C₁ C₂ : ℝ, 0 < C₀ ∧ 0 < Cg ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ z : Torus, z ≠ 0 →
        |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀ ∧
        -Cg ≤ regularGreenRepresentative z ∧
        ‖greenGradient z‖ ≤ C₁ / torusEuclideanNorm z ∧
        ‖greenHessianOperator z‖ ≤ C₂ / (torusEuclideanNorm z ^ 2)) ∧
    (∀ p : ℝ, 1 ≤ p → MemLp regularGreenRepresentative (ENNReal.ofReal p) torusMeasure) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 → MemLp greenGradient (ENNReal.ofReal p) torusMeasure) := by
  refine ⟨regularGreenRepresentative_even, contDiffOn_regularGreenRepresentative_lift,
    regularGreenRepresentative_fourierCoeff, ?_, ?_, memLp_regularGreenRepresentative,
    memLp_greenGradient⟩
  · have hsubset : ball (0 : PlanarSpace) (1 / 2 : ℝ) ⊆
        euclideanOpenBox (centeredBoxAnchor 0) := by
      intro x hx
      exact mem_centeredOpenBox_of_norm_lt_half (mem_ball_zero_iff.mp hx)
    refine ⟨smoothGreenLogRemainder, contDiffOn_smoothGreenLogRemainder.mono hsubset,
      harmonicOnNhd_smoothGreenLogRemainder.mono hsubset, ?_⟩
    intro x hx hne
    exact regularGreenRepresentative_local_expansion
      (mem_centeredOpenBox_of_norm_lt_half hx) hne
  · obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_torus_bounds
    obtain ⟨B, hB, hlow⟩ := exists_regularGreenRepresentative_lower_bound
    exact ⟨C, B, C, C, hC, hB, hC, hC,
      fun z hz ↦ ⟨(hb z hz).1, hlow z, (hb z hz).2.1, (hb z hz).2.2.2⟩⟩

end PeriodicAttractiveLogGas
