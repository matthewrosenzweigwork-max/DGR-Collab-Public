import DGPS.SingularCounterexample.MeanField.ScalarPL
import DGPS.Variational.ScoreDecomposition

/-!
# Species PL inequality for singular circle kernels

The species data and functionals are the existing `SpeciesFamily 1`, barycenter,
`speciesGap`, and `speciesDissipation`. Thus every finite family with strictly positive
weights is admitted, including species densities that vanish.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.SingularCounterexample

/-- The existing absolute barycenter is the weighted density average. -/
theorem species_barycenter_density (F : SpeciesFamily 1) (x : Torus 1) :
    (barycenter F).density x = ∑ s, F.weight s * (F.density s).density x :=
  F.barycenter_density_apply x

/-- The species barycenter is a nonnegative probability density on the absolute domain. -/
theorem species_barycenter_probability (F : SpeciesFamily 1) :
    (∀ x, 0 ≤ (barycenter F).density x) ∧
      (∫ x, (barycenter F).density x ∂haar 1) = 1 :=
  ⟨(barycenter F).density_nonneg, (barycenter F).integral_density⟩

/-- SLC-S002: canonical density derivatives commute with the weighted species average
almost everywhere. The imported root-gradient identity uses weak-gradient uniqueness. -/
theorem densityDeriv_barycenter (F : SpeciesFamily 1) :
    densityDeriv (barycenter F) =ᵐ[haar 1]
      fun x => ∑ s, F.weight s * densityDeriv (F.density s) x := by
  filter_upwards [F.sum_smul_grad_ae] with x hx
  have hcoord := congrArg (fun v : Tangent 1 => v 0) hx
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    SpeciesFamily.sqrtGradient, SpeciesFamily.barycenterWeakGrad] at hcoord
  change 2 * (barycenter F).sqrt x *
      weakGradient (barycenter F).sqrt (barycenter F).sqrt_mem x 0 =
    ∑ s, F.weight s *
      (2 * (F.density s).sqrt x *
        weakGradient (F.density s).sqrt (F.density s).sqrt_mem x 0)
  calc
    _ = 2 * ((barycenter F).sqrt x *
        weakGradient (barycenter F).sqrt (barycenter F).sqrt_mem x 0) := by ring
    _ = 2 * ∑ s, F.weight s * (F.density s).sqrt x *
        weakGradient (F.density s).sqrt (F.density s).sqrt_mem x 0 := by
      rw [← hcoord]
      simp only [mul_assoc]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring

/-- SLC-S005: the sharp Haar circle LSI summed with every positive species weight. -/
theorem species_fisher_ge_entropy (F : SpeciesFamily 1) :
    8 * Real.pi ^ 2 * (∑ s, F.weight s * Analysis.circleEntropy (F.density s)) ≤
      ∑ s, F.weight s * Analysis.circleFisherInformation (F.density s) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have hs := mul_le_mul_of_nonneg_left (haar_circle_lsi (F.density s)).2.2
    (F.weight_nonneg s)
  nlinarith

private theorem species_cross_sum (F : SpeciesFamily 1) (b : Torus 1 → ℝ)
    (hb : Continuous b) :
    (∑ s, F.weight s * ∫ x, densityDeriv (F.density s) x * b x ∂haar 1) =
      ∫ x, densityDeriv (barycenter F) x * b x ∂haar 1 := by
  have hi (s : Fin F.count) :
      Integrable (fun x => densityDeriv (F.density s) x * b x) (haar 1) :=
    integrable_densityDeriv_mul_of_continuous (F.density s) b hb
  calc
    _ = ∫ x, ∑ s, F.weight s * (densityDeriv (F.density s) x * b x) ∂haar 1 := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ fun s _ => (hi s).const_mul (F.weight s)).symm
    _ = _ := by
      refine integral_congr_ae ?_
      filter_upwards [densityDeriv_barycenter F] with x hx
      rw [hx, Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring

private theorem species_density_sq_sum (F : SpeciesFamily 1) (b : Torus 1 → ℝ)
    (hb : Continuous b) :
    (∑ s, F.weight s * ∫ x, (F.density s).density x * (b x) ^ 2 ∂haar 1) =
      ∫ x, (barycenter F).density x * (b x) ^ 2 ∂haar 1 := by
  have hi (s : Fin F.count) :
      Integrable (fun x => (F.density s).density x * (b x) ^ 2) (haar 1) :=
    integrable_density_mul_sq_of_continuous (F.density s) b hb
  calc
    _ = ∫ x, ∑ s, F.weight s * ((F.density s).density x * (b x) ^ 2) ∂haar 1 := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ fun s _ => (hi s).const_mul (F.weight s)).symm
    _ = _ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [species_barycenter_density, Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring

/-- SLC-S004: the actual common-force species dissipation expands into weighted Fisher
information, twice the barycenter cross term, and its nonnegative force square. -/
theorem speciesDissipation_expansion (k : Torus 1 → ℝ) (hk : MemLp k 2 (haar 1))
    (F : SpeciesFamily 1) :
    speciesDissipation k F =
      (∑ s, F.weight s * Analysis.circleFisherInformation (F.density s)) +
      2 * (∫ x, densityDeriv (barycenter F) x *
        singularForce k (barycenter F) x ∂haar 1) +
      ∫ x, (barycenter F).density x * (singularForce k (barycenter F) x) ^ 2 ∂haar 1 := by
  let b := singularForce k (barycenter F)
  have hb : Continuous b := conv_densityDeriv_continuous k hk (barycenter F)
  have hs (s : Fin F.count) :
      (∫ x, |speciesScore k F s x| ^ 2 ∂haar 1) =
        Analysis.circleFisherInformation (F.density s) +
        2 * (∫ x, densityDeriv (F.density s) x * b x ∂haar 1) +
        ∫ x, (F.density s).density x * (b x) ^ 2 ∂haar 1 :=
    dissipation_expansion_of_continuous (F.density s) b hb
  unfold speciesDissipation
  simp_rw [hs]
  calc
    _ = (∑ s, F.weight s * Analysis.circleFisherInformation (F.density s)) +
        (∑ s, 2 * (F.weight s * ∫ x, densityDeriv (F.density s) x * b x ∂haar 1)) +
        ∑ s, F.weight s * ∫ x, (F.density s).density x * (b x) ^ 2 ∂haar 1 := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    _ = _ := by
      rw [← Finset.mul_sum, species_cross_sum F b hb,
        species_density_sq_sum F b hb]

/-- SLC-S006: the common-force PL inequality for every finite positive-weight family. -/
theorem species_PL (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) (F : SpeciesFamily 1) :
    8 * Real.pi ^ 2 * speciesGap k F ≤ speciesDissipation k F := by
  have hlsi := species_fisher_ge_entropy F
  have hcross := crossEnergy_lower_bound k hk hfourier (barycenter F)
  have hQ := interactionGap_nonneg k hk hfourier (barycenter F)
  have hsquare : 0 ≤ ∫ x, (barycenter F).density x *
      (singularForce k (barycenter F) x) ^ 2 ∂haar 1 :=
    integral_nonneg fun x => mul_nonneg ((barycenter F).density_nonneg x) (sq_nonneg _)
  rw [speciesDissipation_expansion k hk F]
  unfold speciesGap
  nlinarith [mul_nonneg (sq_nonneg Real.pi) hQ]

/-- SLC-S007: the species variational rate has the DGPS lower bound. -/
theorem species_PL_rate_lower (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ singularSpeciesPLRate k := by
  unfold singularSpeciesPLRate
  refine le_iInf fun F => ?_
  unfold speciesQuotient
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ (mul_pos (by norm_num) F.2)]
  have h := species_PL k hk hfourier F.1
  nlinarith

end DGPS.SingularCounterexample
