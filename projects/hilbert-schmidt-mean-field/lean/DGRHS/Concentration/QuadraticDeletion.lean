import DGRHS.Concentration.ReplacementEntropy
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace DGRHS.Concentration

lemma entropyPsi_neg_le_sq (s : ℝ) (hs : 0 ≤ s) : entropyPsi (-s) ≤ s^2/2 := by
  let f : ℝ → ℝ := fun x ↦ x^2/2 - Real.exp (-x) - x + 1
  have hd : ∀ x, HasDerivAt f (x + Real.exp (-x) - 1) x := by
    intro x
    convert ((((hasDerivAt_pow 2 x).div_const 2).sub
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg)).sub
      (hasDerivAt_id x)).add_const 1 using 1 <;> norm_num [f]
  have hm : Monotone f := monotone_of_deriv_nonneg
    (fun x ↦ (hd x).differentiableAt) (fun x ↦ by
      rw [(hd x).deriv]
      have h := Real.add_one_le_exp (-x)
      linarith)
  have h := hm hs
  dsimp [f] at h
  simp only [zero_pow (by omega : 2 ≠ 0), zero_div, neg_zero, Real.exp_zero] at h
  unfold entropyPsi
  linarith

lemma bounded_weighted_difference_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z a : Ω → ℝ} {B D : ℝ}
    (hz : AEStronglyMeasurable z μ) (ha : AEStronglyMeasurable a μ)
    (hB : ∀ᵐ x ∂μ, |z x| ≤ B) (hD : ∀ᵐ x ∂μ, |a x| ≤ D) (lam : ℝ) :
    Integrable (fun x ↦ Real.exp (lam*z x)*(z x-a x)^2) μ := by
  have hs := scalar_mul_ae_bounded hz hB lam
  have hf := bounded_exp_positive hs.1 hs.2
  have hd := difference_ae_bounded hz ha hB hD
  have hsq := bounded_square hd.1 hd.2
  exact bounded_mul_integrable hf.measurable hsq.1
    (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hsq.2

lemma finite_product_weighted_deletion_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (Z_i : Fin n → (Fin n → Ω) → ℝ)
    (B : ℝ) (D : Fin n → ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hZi : ∀ i, AEStronglyMeasurable (Z_i i) (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B)
    (hD : ∀ i, ∀ᵐ ω ∂Measure.pi μ, |Z_i i ω| ≤ D i) (lam : ℝ) :
    Integrable (fun ω ↦ Real.exp (lam*Z ω)*(∑ i : Fin n, (Z ω-Z_i i ω)^2)) (Measure.pi μ) := by
  have h := integrable_finsetSum Finset.univ
    (fun i _ ↦ bounded_weighted_difference_square_integrable hZ (hZi i) hB (hD i) lam)
  exact h.congr (Filter.Eventually.of_forall fun ω ↦ by simp only [Finset.mul_sum])

/-- Quadratic deletion entropy follows from the actual invariant-deletion theorem. -/
theorem finite_product_quadratic_deletion_entropy {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (Z_i : Fin n → (Fin n → Ω) → ℝ)
    (B : ℝ) (D : Fin n → ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hZi : ∀ i, AEStronglyMeasurable (Z_i i) (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B)
    (hD : ∀ i, ∀ᵐ ω ∂Measure.pi μ, |Z_i i ω| ≤ D i)
    (hInv : ∀ i ω x, Z_i i (Function.update ω i x) = Z_i i ω)
    (hDiff : ∀ i, ∀ᵐ ω ∂Measure.pi μ, 0 ≤ Z ω-Z_i i ω)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) ≤
      (lam^2/2)*(∫ ω, Real.exp (lam*Z ω)*(∑ i : Fin n, (Z ω-Z_i i ω)^2) ∂Measure.pi μ) := by
  have h := finite_product_deletion_entropy n μ Z Z_i B D hZ hZi hB hD hInv lam hlam
  have hR := finite_product_weighted_deletion_square_integrable n μ Z Z_i B D hZ hZi hB hD lam
  have hpoint : ∀ᵐ ω ∂Measure.pi μ,
      Real.exp (lam*Z ω)*(∑ i : Fin n, entropyPsi (lam*(Z_i i ω-Z ω))) ≤
        (lam^2/2)*(Real.exp (lam*Z ω)*(∑ i : Fin n, (Z ω-Z_i i ω)^2)) := by
    filter_upwards [ae_all_iff.mpr hDiff] with ω hω
    have hi : ∀ i, entropyPsi (lam*(Z_i i ω-Z ω)) ≤ (lam^2/2)*(Z ω-Z_i i ω)^2 := by
      intro i
      have hh := entropyPsi_neg_le_sq (lam*(Z ω-Z_i i ω)) (mul_nonneg hlam (hω i))
      have he : lam*(Z_i i ω-Z ω) = -(lam*(Z ω-Z_i i ω)) := by ring
      rw [he]
      convert hh using 1
      ring
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
    have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (lam*Z ω)).le
    rw [← Finset.mul_sum] at hh'
    nlinarith [hh']
  have hi := integral_mono_ae
    (finite_product_deletion_integrand_integrable n μ Z Z_i B D hZ hZi hB hD lam)
    (hR.const_mul (lam^2/2)) hpoint
  rw [integral_const_mul] at hi
  exact h.trans hi

lemma deletion_squares_self_bound {n : ℕ} (z : ℝ) (a : Fin n → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (ha : ∀ i, 0 ≤ z-a i ∧ z-a i ≤ L)
    (hsum : (∑ i : Fin n, (z-a i)) ≤ z) : (∑ i : Fin n, (z-a i)^2) ≤ L*z := by
  calc
    _ ≤ ∑ i : Fin n, L*(z-a i) := Finset.sum_le_sum fun i _ ↦ by
      have h := mul_le_mul_of_nonneg_left (ha i).2 (ha i).1
      nlinarith
    _ = L*(∑ i : Fin n, (z-a i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hL

theorem finite_product_self_bounding_deletion_entropy {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (Z_i : Fin n → (Fin n → Ω) → ℝ)
    (B : ℝ) (D : Fin n → ℝ) (L : ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hZi : ∀ i, AEStronglyMeasurable (Z_i i) (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B)
    (hD : ∀ i, ∀ᵐ ω ∂Measure.pi μ, |Z_i i ω| ≤ D i)
    (hInv : ∀ i ω x, Z_i i (Function.update ω i x) = Z_i i ω)
    (hL : 0 ≤ L)
    (hDiff : ∀ i, ∀ᵐ ω ∂Measure.pi μ, 0 ≤ Z ω-Z_i i ω ∧ Z ω-Z_i i ω ≤ L)
    (hSum : ∀ᵐ ω ∂Measure.pi μ, (∑ i : Fin n, (Z ω-Z_i i ω)) ≤ Z ω)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) ≤
      (lam^2*L/2)*(∫ ω, Real.exp (lam*Z ω)*Z ω ∂Measure.pi μ) := by
  have h := finite_product_quadratic_deletion_entropy n μ Z Z_i B D hZ hZi hB hD hInv
    (fun i ↦ (hDiff i).mono fun _ hh ↦ hh.1) lam hlam
  have hs := scalar_mul_ae_bounded hZ hB lam
  have hf := bounded_exp_positive hs.1 hs.2
  have hzI : Integrable (fun ω ↦ Real.exp (lam*Z ω)*Z ω) (Measure.pi μ) :=
    bounded_mul_integrable hf.measurable hZ
      (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hB
  have hpoint : ∀ᵐ ω ∂Measure.pi μ,
      Real.exp (lam*Z ω)*(∑ i : Fin n, (Z ω-Z_i i ω)^2) ≤ L*(Real.exp (lam*Z ω)*Z ω) := by
    filter_upwards [ae_all_iff.mpr hDiff,hSum] with ω hω hsω
    have hh := mul_le_mul_of_nonneg_left
      (deletion_squares_self_bound (Z ω) (fun i ↦ Z_i i ω) L hL hω hsω)
      (Real.exp_pos (lam*Z ω)).le
    nlinarith [hh]
  have hi := integral_mono_ae
    (finite_product_weighted_deletion_square_integrable n μ Z Z_i B D hZ hZi hB hD lam)
    (hzI.const_mul L) hpoint
  rw [integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ lam^2/2)
  calc
    _ ≤ (lam^2/2)*(∫ ω, Real.exp (lam*Z ω)*(∑ i : Fin n, (Z ω-Z_i i ω)^2) ∂Measure.pi μ) := h
    _ ≤ (lam^2/2)*(L*(∫ ω, Real.exp (lam*Z ω)*Z ω ∂Measure.pi μ)) := hh
    _ = _ := by ring

#print axioms DGRHS.Concentration.entropyPsi_neg_le_sq
#print axioms DGRHS.Concentration.finite_product_weighted_deletion_square_integrable
#print axioms DGRHS.Concentration.finite_product_quadratic_deletion_entropy
#print axioms DGRHS.Concentration.finite_product_self_bounding_deletion_entropy
#check @DGRHS.Concentration.finite_product_self_bounding_deletion_entropy

end DGRHS.Concentration
