import DGPS.SingularCounterexample.MeanField.Definitions
import DGPS.SingularCounterexample.MeanField.DensityRegularity
import DGPS.SingularCounterexample.MeanField.FourierEnergy

/-!
# Scalar dissipation and PL inequality for singular circle kernels

The square expansion uses the absolute square-root score, including densities that vanish.
Its integrability follows from the existing density regularity and convolution estimates.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.SingularCounterexample

/-- The actual scalar score belongs to `L²` for every absolute density and `L²` kernel. -/
theorem memLp_scalarScore (k : Torus 1 → ℝ) (hk : MemLp k 2 (haar 1))
    (ρ : AbsoluteDensity 1) : MemLp (scalarScore k ρ) 2 (haar 1) := by
  have hg := Examples.PositiveH1.Nonlinear.memLp_coord
    (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad
  have hc : Continuous (singularForce k ρ) := conv_densityDeriv_continuous k hk ρ
  have hcb := Examples.PositiveH1.Nonlinear.memLp_of_cont hc ⊤
  have hw : MemLp (fun x => ρ.sqrt x * singularForce k ρ x) 2 (haar 1) :=
    ρ.memLp_sqrt.smul hcb
  exact (hg.const_mul 2).add hw

theorem integrable_densityDeriv_mul_of_continuous (ρ : AbsoluteDensity 1)
    (b : Torus 1 → ℝ) (hb : Continuous b) :
    Integrable (fun x => densityDeriv ρ x * b x) (haar 1) :=
  (memLp_densityDeriv ρ).integrable_mul
    (Examples.PositiveH1.Nonlinear.memLp_of_cont hb 2)

theorem integrable_density_mul_sq_of_continuous (ρ : AbsoluteDensity 1)
    (b : Torus 1 → ℝ) (hb : Continuous b) :
    Integrable (fun x => ρ.density x * (b x) ^ 2) (haar 1) :=
  ρ.integrable_density.mul_of_top_left
    (Examples.PositiveH1.Nonlinear.memLp_of_cont (hb.pow 2) ⊤)

/-- The square expansion for a continuous force, also used for a common species force.
Each term is integrable before the pointwise expansion is integrated. -/
theorem dissipation_expansion_of_continuous (ρ : AbsoluteDensity 1)
    (b : Torus 1 → ℝ) (hb : Continuous b) :
    (∫ x, |2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 + ρ.sqrt x * b x| ^ 2 ∂haar 1) =
      Analysis.circleFisherInformation ρ + 2 * (∫ x, densityDeriv ρ x * b x ∂haar 1) +
      ∫ x, ρ.density x * (b x) ^ 2 ∂haar 1 := by
  let g : Torus 1 → ℝ := fun x => weakGradient ρ.sqrt ρ.sqrt_mem x 0
  have hg : MemLp g 2 (haar 1) := Examples.PositiveH1.Nonlinear.memLp_coord
    (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad
  have hi1 : Integrable (fun x => 4 * g x ^ 2) (haar 1) := hg.integrable_sq.const_mul 4
  have hi2 : Integrable (fun x => 2 * (densityDeriv ρ x * b x)) (haar 1) :=
    (integrable_densityDeriv_mul_of_continuous ρ b hb).const_mul 2
  have hi3 := integrable_density_mul_sq_of_continuous ρ b hb
  have hpt : ∀ x, |2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 + ρ.sqrt x * b x| ^ 2 =
      4 * g x ^ 2 + 2 * (densityDeriv ρ x * b x) + ρ.density x * (b x) ^ 2 := by
    intro x
    simp only [sq_abs, densityDeriv, Examples.PositiveH1.Nonlinear.densityDeriv,
      AbsoluteDensity.density, g]
    ring
  have hI : Analysis.circleFisherInformation ρ = 4 * ∫ x, g x ^ 2 ∂haar 1 := by
    unfold Analysis.circleFisherInformation
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [g, EuclideanSpace.norm_sq_eq]
  simp_rw [hpt]
  have h12 := integral_add hi1 hi2
  have h123 := integral_add (hi1.add hi2) hi3
  simp only [Pi.add_apply] at h123
  rw [h123, h12, integral_const_mul, integral_const_mul, hI]

/-- SLC-M017: the exact scalar dissipation expansion on the full absolute-density domain. -/
theorem scalarDissipation_expansion (k : Torus 1 → ℝ) (hk : MemLp k 2 (haar 1))
    (ρ : AbsoluteDensity 1) :
    scalarDissipation k ρ = Analysis.circleFisherInformation ρ +
      2 * (∫ x, densityDeriv ρ x * singularForce k ρ x ∂haar 1) +
      ∫ x, ρ.density x * (singularForce k ρ x) ^ 2 ∂haar 1 :=
  dissipation_expansion_of_continuous ρ (singularForce k ρ)
    (conv_densityDeriv_continuous k hk ρ)

/-- SLC-M015: nonnegative nonzero Fourier coefficients make the Haar-relative interaction
energy nonnegative. -/
theorem interactionGap_nonneg (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) (ρ : AbsoluteDensity 1) :
    0 ≤ interactionGap k ρ := by
  refine HasSum.nonneg ?_ (hasSum_interactionGap hk ρ)
  intro n
  split_ifs with hn
  · exact le_rfl
  · exact mul_nonneg (hfourier n hn).2 (sq_nonneg _)

/-- The free-energy gap is nonnegative on the full absolute-density domain. -/
theorem scalarGap_nonneg (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) (ρ : AbsoluteDensity 1) :
    0 ≤ scalarGap k ρ := by
  unfold scalarGap
  exact add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (by norm_num) (interactionGap_nonneg k hk hfourier ρ))

/-- SLC-M016: only Haar can have zero free-energy gap. Nonnegative Fourier coefficients
already suffice; strict positivity is not needed for this uniqueness conclusion. -/
theorem density_ae_one_of_scalarGap_eq_zero (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) (ρ : AbsoluteDensity 1)
    (hzero : scalarGap k ρ = 0) : ρ.density =ᵐ[haar 1] fun _ => 1 := by
  have hQ := interactionGap_nonneg k hk hfourier ρ
  have hH : 0 ≤ Analysis.circleEntropy ρ := ENNReal.toReal_nonneg
  have hH0 : Analysis.circleEntropy ρ = 0 := by
    unfold scalarGap at hzero
    linarith
  have hE : homogeneousEntropy (haar 1) ρ.density = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hH0).resolve_right (haar_circle_lsi ρ).1
  have h := (homogeneousEntropy_eq_zero_iff
    (Filter.Eventually.of_forall ρ.density_nonneg)
    ρ.integrable_density.aestronglyMeasurable.aemeasurable
    (by rw [ρ.integral_density]; norm_num)).mp hE
  simpa only [ρ.integral_density] using h

/-- SLC-M018: the first nonzero circle frequency controls the density-force pairing. -/
theorem crossEnergy_lower_bound (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) (ρ : AbsoluteDensity 1) :
    4 * Real.pi ^ 2 * interactionGap k ρ ≤
      ∫ x, densityDeriv ρ x * singularForce k ρ x ∂haar 1 := by
  have hsum := (hasSum_crossEnergy hk ρ).sub
    (HasSum.mul_left (4 * Real.pi ^ 2) (hasSum_interactionGap hk ρ))
  have hnonneg : 0 ≤ (∫ x, densityDeriv ρ x * singularForce k ρ x ∂haar 1) -
      4 * Real.pi ^ 2 * interactionGap k ρ := by
    refine HasSum.nonneg ?_ hsum
    intro n
    apply sub_nonneg.mpr
    by_cases hn : n = 0
    · simp [hn]
    · simp only [ite_eq_right hn]
      have habs : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        nlinarith [sq_abs (n : ℝ), sq_nonneg (|(n : ℝ)| - 1)]
      have hfreq : 4 * Real.pi ^ 2 ≤ (2 * Real.pi * (n : ℝ)) ^ 2 := by
        calc
          4 * Real.pi ^ 2 = (4 * Real.pi ^ 2) * 1 := by ring
          _ ≤ (4 * Real.pi ^ 2) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hnsq (by positivity)
          _ = (2 * Real.pi * (n : ℝ)) ^ 2 := by ring
      have h := mul_le_mul_of_nonneg_right hfreq
        (mul_nonneg (hfourier n hn).2 (sq_nonneg ‖coeff1 ρ.density n‖))
      simpa only [mul_assoc] using h
  exact sub_nonneg.mp hnonneg

/-- SLC-M019: the scalar PL inequality has the DGPS factor-of-two normalization. -/
theorem scalar_PL (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) (ρ : AbsoluteDensity 1) :
    8 * Real.pi ^ 2 * scalarGap k ρ ≤ scalarDissipation k ρ := by
  have hlsi := (haar_circle_lsi ρ).2.2
  have hcross := crossEnergy_lower_bound k hk hfourier ρ
  have hQ := interactionGap_nonneg k hk hfourier ρ
  have hsquare : 0 ≤ ∫ x, ρ.density x * (singularForce k ρ x) ^ 2 ∂haar 1 :=
    integral_nonneg fun x => mul_nonneg (ρ.density_nonneg x) (sq_nonneg _)
  rw [scalarDissipation_expansion k hk ρ]
  unfold scalarGap
  nlinarith [mul_nonneg (sq_nonneg Real.pi) hQ]

/-- SLC-M020: every positive-gap scalar quotient has rate at least `4π²`. -/
theorem scalar_PL_rate_lower (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ singularScalarPLRate k := by
  unfold singularScalarPLRate
  refine le_iInf fun ρ => ?_
  unfold scalarQuotient
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ (mul_pos (by norm_num) ρ.2)]
  have h := scalar_PL k hk hfourier ρ.1
  nlinarith

end DGPS.SingularCounterexample
