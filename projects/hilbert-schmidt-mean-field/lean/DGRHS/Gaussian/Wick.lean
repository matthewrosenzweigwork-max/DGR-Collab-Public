/- Supporting draft: exact Wick identity from scalar Gaussian fourth moments
and the same actual linear Gaussian process. Not yet Lean checked. -/
import DGRHS.Gaussian.IndexedGaussianLaw
import DGRHS.Gaussian.SixthMoment
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace DGRHS.Gaussian
variable {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace Ω] {γ : Measure Ω} [IsProbabilityMeasure γ]
variable (W : H →ₗ[ℝ] Lp ℝ 2 γ)
  (hG : ∀ v, γ.map (W v) = gaussianReal 0 (Real.toNNReal (‖v‖^2)))

include hG

lemma memLp_gaussian_linear (v : H) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (W v : Ω → ℝ) p γ := by
  have hm : MemLp id p (γ.map (W v)) := by
    rw [hG v]
    exact memLp_id_gaussianReal' p hp
  simpa only [Function.comp_def, id_eq] using
    hm.comp_of_map (Lp.aestronglyMeasurable (W v)).aemeasurable

lemma integrable_pow_four_gaussian_linear (v : H) :
    Integrable (fun ω ↦ W v ω ^ 4) γ := by
  have hm := memLp_gaussian_linear W hG v 4 (by norm_num)
  simpa only [Real.norm_eq_abs, show (4:ℕ)=2*2 by rfl, pow_mul, sq_abs]
    using hm.integrable_norm_pow (by decide : (4:ℕ) ≠ 0)

lemma integral_pow_four_gaussian_linear (v : H) :
    (∫ ω, W v ω ^ 4 ∂γ) = 3 * ‖v‖ ^ 4 := by
  have hi := integral_map (Lp.aestronglyMeasurable (W v)).aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ ↦ x ^ 4) (γ.map (W v)) by fun_prop)
  rw [hG v] at hi
  rw [← hi, integral_pow_four_gaussianReal_sq]

lemma integrable_gaussian_linear_sq_mul_sq (v w : H) :
    Integrable (fun ω ↦ W v ω ^ 2 * W w ω ^ 2) γ := by
  apply ((integrable_pow_four_gaussian_linear W hG v).add
    (integrable_pow_four_gaussian_linear W hG w)).mono'
  · exact ((Lp.aestronglyMeasurable (W v)).pow 2).mul
      ((Lp.aestronglyMeasurable (W w)).pow 2)
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    change (W v ω)^2 * (W w ω)^2 ≤ (W v ω)^4 + (W w ω)^4
    nlinarith [sq_nonneg ((W v ω)^2 - (W w ω)^2)]

/-- Exact two-point Wick identity, derived from one coherent linear process. -/
theorem gaussian_linear_wick (v w : H) :
    (∫ ω, W v ω ^ 2 * W w ω ^ 2 ∂γ) =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 + 2 * (inner ℝ v w) ^ 2 := by
  have hadd : (W (v+w) : Ω → ℝ) =ᵐ[γ] fun ω ↦ W v ω + W w ω := by
    rw [W.map_add]
    exact Lp.coeFn_add (W v) (W w)
  have hsub : (W (v-w) : Ω → ℝ) =ᵐ[γ] fun ω ↦ W v ω - W w ω := by
    rw [W.map_sub]
    exact Lp.coeFn_sub (W v) (W w)
  have hp : Integrable (fun ω ↦ (W v ω + W w ω)^4) γ :=
    (integrable_pow_four_gaussian_linear W hG (v+w)).congr
      (hadd.mono fun ω h ↦ congrArg (fun x : ℝ ↦ x^4) h)
  have hm : Integrable (fun ω ↦ (W v ω - W w ω)^4) γ :=
    (integrable_pow_four_gaussian_linear W hG (v-w)).congr
      (hsub.mono fun ω h ↦ congrArg (fun x : ℝ ↦ x^4) h)
  have hpval : (∫ ω, (W v ω + W w ω)^4 ∂γ) = 3 * ‖v+w‖^4 := by
    rw [← integral_pow_four_gaussian_linear W hG (v+w)]
    apply integral_congr_ae
    exact hadd.symm.mono fun ω h ↦ congrArg (fun x : ℝ ↦ x^4) h
  have hmval : (∫ ω, (W v ω - W w ω)^4 ∂γ) = 3 * ‖v-w‖^4 := by
    rw [← integral_pow_four_gaussian_linear W hG (v-w)]
    apply integral_congr_ae
    exact hsub.symm.mono fun ω h ↦ congrArg (fun x : ℝ ↦ x^4) h
  have hav := integrable_pow_four_gaussian_linear W hG v
  have haw := integrable_pow_four_gaussian_linear W hG w
  have hab := integrable_gaussian_linear_sq_mul_sq W hG v w
  have hpoly : (∫ ω, (W v ω + W w ω)^4 ∂γ) +
      (∫ ω, (W v ω - W w ω)^4 ∂γ) =
      2*(∫ ω, W v ω^4 ∂γ) + 12*(∫ ω, W v ω^2*W w ω^2 ∂γ) +
        2*(∫ ω, W w ω^4 ∂γ) := by
    rw [← integral_add hp hm]
    calc
      _ = ∫ ω, 2*(W v ω)^4 + 12*((W v ω)^2*(W w ω)^2) + 2*(W w ω)^4 ∂γ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = _ := by
        have htwo : Integrable (fun ω ↦ 2*(W v ω)^4 + 12*((W v ω)^2*(W w ω)^2)) γ :=
          (hav.const_mul 2).add (hab.const_mul 12)
        rw [integral_add htwo (haw.const_mul 2),
          integral_add (hav.const_mul 2) (hab.const_mul 12), integral_const_mul,
          integral_const_mul, integral_const_mul]
  rw [hpval, hmval, integral_pow_four_gaussian_linear W hG v,
    integral_pow_four_gaussian_linear W hG w] at hpoly
  simp only [show (4:ℕ)=2*2 by rfl, pow_mul] at hpoly
  rw [norm_add_sq_real, norm_sub_sq_real] at hpoly
  nlinarith

omit hG

/-- Actual downstream instantiation in the constructed indexed process. -/
theorem indexedGaussianIsometry_wick {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f) (v w : H) :
    (∫ ω, indexedGaussianIsometry b f hf v ω ^ 2 *
      indexedGaussianIsometry b f hf w ω ^ 2 ∂IsonormalProcess.iidStdGaussian) =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 + 2 * (inner ℝ v w) ^ 2 := by
  exact gaussian_linear_wick (indexedGaussianIsometry b f hf).toLinearMap
    (map_indexedGaussianIsometry_eq_gaussianReal b f hf) v w

/-- Wick transfers to fibers of the same actual joint feature representative. -/
theorem ae_featureGaussian_wick {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {μ : Measure X} (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω ↦ g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      (∫ ω, g (x,ω)^2 * g (y,ω)^2 ∂IsonormalProcess.iidStdGaussian) =
        ‖k x‖^2 * ‖k y‖^2 + 2 * (inner ℝ (k x) (k y))^2 := by
  filter_upwards [hW] with x hx
  filter_upwards [hW] with y hy
  calc
    _ = ∫ ω, indexedGaussianIsometry b f hf (k x) ω ^ 2 *
        indexedGaussianIsometry b f hf (k y) ω ^ 2 ∂IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [hx,hy] with ω hxx hyy
      change g (x,ω)^2 * g (y,ω)^2 = _
      rw [hxx,hyy]
    _ = _ := indexedGaussianIsometry_wick b f hf (k x) (k y)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.gaussian_linear_wick

#print axioms DGRHS.Gaussian.indexedGaussianIsometry_wick
#print axioms DGRHS.Gaussian.ae_featureGaussian_wick
#check DGRHS.Gaussian.indexedGaussianIsometry_wick
#check DGRHS.Gaussian.ae_featureGaussian_wick
