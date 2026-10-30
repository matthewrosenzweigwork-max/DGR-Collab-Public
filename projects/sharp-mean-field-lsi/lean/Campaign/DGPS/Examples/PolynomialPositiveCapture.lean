import DGPS.Examples.PolynomialOriginCapture
import DGPS.Foundations.CircleRegularity

/-! Actual positive continuous representatives along the same near-origin
scalar sublevels. The bound is deduced from original sqrt-H1 capture and the
one-dimensional embedding, with no pointwise stored-root assumption. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.PolynomialSpecies

private theorem norm_tendsto_of_real {f : ℕ → ℝ≥0∞} (hf : ∀ n, f n ≠ ⊤)
    (ht : Tendsto (fun n => (f n).toReal) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal_iff hf ENNReal.zero_ne_top).1 (by simpa using ht)

/-- Near-baseline original competitors at fields tending to zero have, along
one strictly increasing subsequence, actual continuous root representatives
converging uniformly to one and eventually bounded below by one half. -/
theorem polynomial_scalar_origin_positive_capture (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (Mq : ℝ) (hMq : 0 ≤ Mq) (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hQ : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) ≤ ENNReal.ofReal Mq)
    (hnear : ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
      scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) ≤
        ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 + t)) :
    ∃ φ : ℕ → ℕ, ∃ v : ℕ → Torus 1 → ℝ, StrictMono φ ∧
      (∀ n, Continuous (v n) ∧ (ρ (φ n)).sqrt =ᵐ[haar 1] v n) ∧
      TendstoUniformly v (fun _ : Torus 1 => (1 : ℝ)) atTop ∧
      (∀ᶠ n in atTop, ∀ x, (1 / 2 : ℝ) ≤ v n x) := by
  obtain ⟨φ, hφ, hsum⟩ := polynomial_scalar_origin_capture h hh b Mq hMq ρ hG hQ hnear
  let τ := fun n => ρ (φ n)
  have hw := fun n => isWeakGradient_weakGradient (τ n).sqrt_mem
  choose v hv hae hvosc hvmean using fun n => circle_H1_holder_half (hw n)
  have hroot : Tendsto (fun n => (eLpNorm (fun x => (τ n).sqrt x - 1) 2 (haar 1)).toReal)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hsum
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  have hgrad : Tendsto (fun n => (eLpNorm (weakGradient (τ n).sqrt (τ n).sqrt_mem) 2 (haar 1)).toReal)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hsum
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hroot' : Tendsto (fun n => eLpNorm (fun x => (τ n).sqrt x - 1) 2 (haar 1)) atTop (𝓝 0) :=
    norm_tendsto_of_real (fun n => ((τ n).memLp_sqrt.sub (memLp_const (1 : ℝ))).eLpNorm_ne_top) hroot
  have hgrad' : Tendsto (fun n => eLpNorm (fun x =>
      weakGradient (τ n).sqrt (τ n).sqrt_mem x - (0 : Tangent 1)) 2 (haar 1)) atTop (𝓝 0) := by
    simpa only [sub_zero] using norm_tendsto_of_real (fun n => (hw n).memLp_grad.eLpNorm_ne_top) hgrad
  have hU : TendstoUniformly v (fun _ : Torus 1 => (1 : ℝ)) atTop :=
    circle_H1_tendstoUniformly hw (isWeakGradient_const (d := 1) 1) hv hae
      continuous_const (EventuallyEq.refl _ _) hroot' hgrad'
  refine ⟨φ, v, hφ, fun n => ⟨hv n, (hae n).symm⟩, hU, ?_⟩
  have he := (Metric.tendstoUniformly_iff.1 hU) (1 / 2 : ℝ) (by norm_num)
  filter_upwards [he] with n hn x
  have hx : |v n x - 1| < (1 / 2 : ℝ) := by
    simpa only [Real.dist_eq, abs_sub_comm] using hn x
  linarith [(abs_lt.mp hx).1]

end DGPS.Examples.PolynomialSpecies
