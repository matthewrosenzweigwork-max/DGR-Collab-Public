import DGRHS.Gaussian.HoeffdingLinearity

/-!
Packet P9h, unit 2 (part 22): generic short-range absorption inequality for Hoeffding-centered kernels
(the pointwise heart of TeX 3405-3411 `eq:shortAbsorb`).

If `|κ| ≤ A f` with `f ≥ 0`, `4 ε A ≤ γ`, and `f` has row/column potentials at most `P`, then pointwise
`σ ε κ̃ - (γ/2) f̃ ≤ (7/4) γ P` for `|σ| ≤ 1`, where `h̃` is the `μ`-centering of `h`.
-/

noncomputable section
open MeasureTheory
namespace DGRHS.Periodic
open DGRHS.Gaussian

theorem centered_short_absorption {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (κ f : X × X → ℝ) (hκm : StronglyMeasurable κ)
    (ε γ A P σ : ℝ) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hσ : |σ| ≤ 1)
    (hκf : ∀ p, |κ p| ≤ A * f p) (hf0 : ∀ p, 0 ≤ f p) (hεA : 4 * ε * A ≤ γ)
    (hfp : Integrable f (μ.prod μ))
    (hrow : ∀ x, Integrable (fun y => f (x, y)) μ) (hcol : ∀ y, Integrable (fun x => f (x, y)) μ)
    (hProw : ∀ x, ∫ y, f (x, y) ∂μ ≤ P) (hPcol : ∀ y, ∫ x, f (x, y) ∂μ ≤ P)
    (p : X × X) :
    σ * ε * hoeffdingCentered μ κ p - γ / 2 * hoeffdingCentered μ f p ≤ (7 / 4) * γ * P := by
  have hAf : ∀ q, |κ q| ≤ A * f q := hκf
  have hκint : Integrable κ (μ.prod μ) :=
    (hfp.const_mul A).mono' hκm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 q)] using hAf q)
  have hκrow : ∀ x, Integrable (fun y => κ (x, y)) μ := fun x =>
    ((hrow x).const_mul A).mono'
      (hκm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hAf (x, y))
  have hκcol : ∀ y, Integrable (fun x => κ (x, y)) μ := fun y =>
    ((hcol y).const_mul A).mono'
      (hκm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hAf (x, y))
  -- potentials of κ
  have ha1 : |∫ y, κ (p.1, y) ∂μ| ≤ A * P := by
    calc _ ≤ ∫ y, |κ (p.1, y)| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => κ (p.1, y))
      _ ≤ ∫ y, A * f (p.1, y) ∂μ := integral_mono (hκrow p.1).abs ((hrow p.1).const_mul A)
          (fun y => hAf (p.1, y))
      _ = A * ∫ y, f (p.1, y) ∂μ := integral_const_mul _ _
      _ ≤ A * P := mul_le_mul_of_nonneg_left (hProw p.1) hA
  have ha2 : |∫ x, κ (x, p.2) ∂μ| ≤ A * P := by
    calc _ ≤ ∫ x, |κ (x, p.2)| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => κ (x, p.2))
      _ ≤ ∫ x, A * f (x, p.2) ∂μ := integral_mono (hκcol p.2).abs ((hcol p.2).const_mul A)
          (fun x => hAf (x, p.2))
      _ = A * ∫ x, f (x, p.2) ∂μ := integral_const_mul _ _
      _ ≤ A * P := mul_le_mul_of_nonneg_left (hPcol p.2) hA
  have hfmean : (∫ z, f z ∂μ.prod μ) ≤ P := by
    rw [integral_prod _ hfp]
    calc _ ≤ ∫ _ : X, P ∂μ := integral_mono hfp.integral_prod_left (integrable_const _) hProw
      _ = P := by simp
  have hf0m : 0 ≤ ∫ z, f z ∂μ.prod μ := integral_nonneg hf0
  have hkmean : |∫ z, κ z ∂μ.prod μ| ≤ A * P := by
    calc _ ≤ ∫ z, |κ z| ∂μ.prod μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm κ
      _ ≤ ∫ z, A * f z ∂μ.prod μ := integral_mono hκint.abs (hfp.const_mul A) hAf
      _ = A * ∫ z, f z ∂μ.prod μ := integral_const_mul _ _
      _ ≤ A * P := mul_le_mul_of_nonneg_left hfmean hA
  have hb1 : 0 ≤ ∫ y, f (p.1, y) ∂μ := integral_nonneg fun y => hf0 _
  have hb2 : 0 ≤ ∫ x, f (x, p.2) ∂μ := integral_nonneg fun x => hf0 _
  have hP0 : 0 ≤ P := hb1.trans (hProw p.1)
  -- unfold the centerings
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change σ * ε * (κ p - (∫ y, κ (p.1, y) ∂μ) - (∫ x, κ (x, p.2) ∂μ) + (∫ z, κ z ∂μ.prod μ)) -
    γ / 2 * (f p - (∫ y, f (p.1, y) ∂μ) - (∫ x, f (x, p.2) ∂μ) + (∫ z, f z ∂μ.prod μ)) ≤ _
  set a1 := ∫ y, κ (p.1, y) ∂μ
  set a2 := ∫ x, κ (x, p.2) ∂μ
  set c := ∫ z, κ z ∂μ.prod μ
  set b1 := ∫ y, f (p.1, y) ∂μ
  set b2 := ∫ x, f (x, p.2) ∂μ
  set d := ∫ z, f z ∂μ.prod μ
  have hσε : |σ * ε| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hε]
    exact mul_le_of_le_one_left hε hσ
  have hk1 : σ * ε * κ p ≤ ε * (A * f p) := by
    calc σ * ε * κ p ≤ |σ * ε * κ p| := le_abs_self _
      _ = |σ * ε| * |κ p| := abs_mul _ _
      _ ≤ ε * (A * f p) := mul_le_mul hσε (hAf p) (abs_nonneg _) hε
  have hk2 : -(σ * ε * a1) ≤ ε * (A * P) := by
    calc -(σ * ε * a1) ≤ |σ * ε * a1| := neg_le_abs _
      _ = |σ * ε| * |a1| := abs_mul _ _
      _ ≤ ε * (A * P) := mul_le_mul hσε ha1 (abs_nonneg _) hε
  have hk3 : -(σ * ε * a2) ≤ ε * (A * P) := by
    calc -(σ * ε * a2) ≤ |σ * ε * a2| := neg_le_abs _
      _ = |σ * ε| * |a2| := abs_mul _ _
      _ ≤ ε * (A * P) := mul_le_mul hσε ha2 (abs_nonneg _) hε
  have hk4 : σ * ε * c ≤ ε * (A * P) := by
    calc σ * ε * c ≤ |σ * ε * c| := le_abs_self _
      _ = |σ * ε| * |c| := abs_mul _ _
      _ ≤ ε * (A * P) := mul_le_mul hσε hkmean (abs_nonneg _) hε
  have hεAP : ε * A ≤ γ / 4 := by linarith
  have hf1 : ε * (A * f p) ≤ γ / 4 * f p := by
    have := mul_le_mul_of_nonneg_right hεAP (hf0 p)
    linarith [this]
  have hfp0 := hf0 p
  have h5 : ε * (A * P) ≤ γ / 4 * P := by
    have := mul_le_mul_of_nonneg_right hεAP hP0
    linarith [this]
  have h6 : γ / 2 * b1 ≤ γ / 2 * P := mul_le_mul_of_nonneg_left (hProw p.1) (by positivity)
  have h7 : γ / 2 * b2 ≤ γ / 2 * P := mul_le_mul_of_nonneg_left (hPcol p.2) (by positivity)
  have h8 : 0 ≤ γ / 2 * d := mul_nonneg (by positivity) hf0m
  nlinarith [hk1, hk2, hk3, hk4, hf1, h5, h6, h7, h8, mul_nonneg hγ hfp0]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.centered_short_absorption
