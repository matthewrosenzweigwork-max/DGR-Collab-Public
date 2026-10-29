import DGPS.Examples.HarmonicFamilyDeficit
import DGPS.Circle.QuantitativeLSI
import DGPS.Foundations.NormalizationChecks

/-!
# Quantitative positive harmonic deficit (EX078)

For a finite species family `F` with weights `θ_s`, a0 = 4π², `E = ∑ θ_s H(ρ_s | Haar)`,
`I = ∑ θ_s I(ρ_s)`, `ρ̄` the barycenter with first Fourier moments `c, s`, `M = c² + s²` and
`P = ∫ (c sin - s cos)² dρ̄`, put `U = I / (2 a0) - E`, `V = E - M` and `Z = 2P - M`.

* `U ≥ ∑ θ_s H_s² / 12 ≥ E² / 12`: the quantitative circle LSI (FOU016) species by species,
  then the weighted Jensen inequality.
* `V ≥ 0`: the entropy--Fourier inequality (EX076) and Jensen for the barycenter.
* `U + V + Z ≥ 0`: at coupling `κ = 2` the squared-score dissipation equals `2 a0 (U + V + Z)`,
  and it is nonnegative.

The deficit identity of EX077 gives `(D - 2 a0 (1 - k) G) / (2 a0) = U + k V + k² Z` for
`0 ≤ k < 1`. If `Z ≤ 0` the identity `U + k V + k² Z = (1 - k) U + k (U + V + Z) - k (1 - k) Z`
gives the bound `(1 - k) U`; if `Z > 0` the bound `U` holds directly. Both give
`(1 - k) E² / 12`.

Design choices (R5 notes).
* This is a new module because `HarmonicNonattainment` is the EX076 module.
* The EX077 identity is stated only for the coupling `2k` with `k < 1`, and the critical coupling
  `κ = 2` is needed for `U + V + Z ≥ 0`. So the squared-score identity is re-proved here for an
  arbitrary coupling `κ` (helper `dissipation_toReal_ex078`), reusing the EX077 force and
  dissipation helpers. The critical statement holds for any drift, and the critical drift is
  `attractiveXYDrift 2 0`.
* The gap identity `G = E - k M` and the `0 ≤ k < 1` deficit identity are imported from EX077.
* Helper lemmas carry the suffix `_ex078`.
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal

namespace DGPS.Examples

open DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical DGPS.Models

/-- EX078 helper: the circle entropy of an absolute density is the real part of its relative
entropy with respect to Haar. -/
theorem circleEntropy_eq_ex078 (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.Analysis.circleEntropy ρ =
      (DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))
        (DGPS.haar 1)).toReal := by
  unfold DGPS.Analysis.circleEntropy
  rw [DGPS.relativeEntropy_density_eq]

/-- EX078 helper: the quantitative circle LSI (FOU016) for one species, in the form
`2 a0 H + (a0 / 6) H² ≤ I` with `a0 = 4π²`. -/
theorem fou016_species_ex078 (ρ : DGPS.AbsoluteDensity 1) :
    2 * (4 * Real.pi ^ 2) *
        (DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))
          (DGPS.haar 1)).toReal +
      (4 * Real.pi ^ 2) / 6 *
        (DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))
          (DGPS.haar 1)).toReal ^ 2 ≤
      DGPS.Analysis.circleFisherInformation ρ := by
  rw [← circleEntropy_eq_ex078 ρ]
  exact (DGPS.Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ).2.2.1

/-- EX078 helper: a weighted sum of `θ_i (c₁ H_i + c₂ H_i²)` splits into the two weighted sums. -/
theorem sum_split_ex078 {ι : Type*} (s : Finset ι) (θ H : ι → ℝ) (c₁ c₂ : ℝ) :
    ∑ i ∈ s, θ i * (c₁ * H i + c₂ * H i ^ 2) =
      c₁ * ∑ i ∈ s, θ i * H i + c₂ * ∑ i ∈ s, θ i * H i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- EX078 helper: the weighted FOU016 bound gives `U ≥ E² / 12` for `U = I / (2 a0) - E`. -/
theorem U_bound_ex078 {ι : Type*} (s : Finset ι) (θ H fi : ι → ℝ) (hθ : ∀ i ∈ s, 0 ≤ θ i)
    (hθ1 : ∑ i ∈ s, θ i = 1)
    (hfi : ∀ i ∈ s, 2 * (4 * Real.pi ^ 2) * H i + (4 * Real.pi ^ 2) / 6 * H i ^ 2 ≤ fi i) :
    (∑ i ∈ s, θ i * H i) ^ 2 / 12 ≤
      (∑ i ∈ s, θ i * fi i) / (2 * (4 * Real.pi ^ 2)) - ∑ i ∈ s, θ i * H i := by
  have h1 : ∑ i ∈ s, θ i * (2 * (4 * Real.pi ^ 2) * H i + (4 * Real.pi ^ 2) / 6 * H i ^ 2) ≤
      ∑ i ∈ s, θ i * fi i :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hfi i hi) (hθ i hi)
  rw [sum_split_ex078 s θ H (2 * (4 * Real.pi ^ 2)) ((4 * Real.pi ^ 2) / 6)] at h1
  have h2 : (∑ i ∈ s, θ i * H i) ^ 2 ≤ ∑ i ∈ s, θ i * H i ^ 2 :=
    sq_weighted_sum_le_ex076 s θ H hθ hθ1
  have hpi : 0 ≤ (4 * Real.pi ^ 2) / 6 := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hpi
  have ha : 0 < 2 * (4 * Real.pi ^ 2) := by positivity
  rw [le_sub_iff_add_le, le_div_iff₀ ha]
  linarith [h1, h3]

/-- EX078 helper: the barycenter entropy--Fourier bound `V = E - M ≥ 0`. -/
theorem V_nonneg_ex078 (F : DGPS.SpeciesFamily 1) :
    0 ≤ (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) -
      (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
        xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2) := by
  have h1 := norm_sq_barycenter_le_ex076 F
  have h2 : ∑ s, F.weight s * (xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ^ 2 +
      xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ^ 2) ≤
      ∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal :=
    Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (species_fourier_ex076 (F.density s)) (F.weight_nonneg s)
  linarith

/-- EX078 helper: real algebra of the critical identity. -/
theorem critical_real_ex078 (fi E M P : ℝ)
    (hD : 0 ≤ fi - 8 * Real.pi ^ 2 * 2 * M + 4 * Real.pi ^ 2 * 2 ^ 2 * P) :
    0 ≤ (fi / (2 * (4 * Real.pi ^ 2)) - E) + (E - M) + (2 * P - M) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have e : (fi / (2 * (4 * Real.pi ^ 2)) - E) + (E - M) + (2 * P - M) =
      (fi - 8 * Real.pi ^ 2 * 2 * M + 4 * Real.pi ^ 2 * 2 ^ 2 * P) /
        (2 * (4 * Real.pi ^ 2)) := by
    field_simp
    ring
  rw [e]
  exact div_nonneg hD (by positivity)

/-- EX078 helper: the squared-score dissipation of `attractiveXY κ 0`, for any coupling `κ`
and any drift, is finite and its real value is `I - 8π² κ M + 4π² κ² P`. This is the EX077
computation with `κ = 2k` replaced by a general `κ` (the force and dissipation helpers of EX077
are reused unchanged). -/
theorem dissipation_toReal_ex078 (κ : ℝ) (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY κ 0))
    (F : DGPS.SpeciesFamily 1) :
    DGPS.speciesDissipation (DGPS.Models.attractiveXY κ 0) b F ≠ ⊤ ∧
      (DGPS.speciesDissipation (DGPS.Models.attractiveXY κ 0) b F).toReal =
        (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s)) -
          8 * Real.pi ^ 2 * κ *
            (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
              xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2) +
          4 * Real.pi ^ 2 * κ ^ 2 *
            ∫ x, (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) *
                (xyMode x).im - xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) :
                Measure (DGPS.Torus 1)) * (xyMode x).re) ^ 2
              ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * Real.pi * (-(κ *
      xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = -(2 * Real.pi) * (-(0 + κ *
      xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)))) := ⟨_, rfl⟩
  have hf : ∀ᵐ x ∂DGPS.haar 1, b.force (DGPS.barycenter F) x 0 = xyTrig A B 0 x :=
    force_ae_ex077 κ 0 b (DGPS.barycenter F) A B hA hB
  have hD := speciesDissipation_real_ex077 κ 0 b F A B hf
  have hI0 : 0 ≤ ∑ s, F.weight s * ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
      (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1 :=
    Finset.sum_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (integral_nonneg fun x => sq_nonneg _)
  refine ⟨by rw [hD]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hD, ENNReal.toReal_ofReal hI0]
  -- per-species Fisher, flux and quadratic decomposition
  have hsp : ∀ s, ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
      (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1 =
      DGPS.Analysis.circleFisherInformation (F.density s) -
        2 * ∫ x, (F.density s).density x * DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1 +
        ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 := fun s =>
    (score_ex077 (F.density s) A B _ hf).2
  have key : ∑ s, F.weight s * ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
      (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1 =
      (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s)) -
        2 * (∑ s, F.weight s *
          ∫ x, (F.density s).density x * DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1) +
        ∑ s, F.weight s * ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hsp s]
    ring
  -- the flux term: the derivative of the first-harmonic force, summed over the species
  have hcp : DGPS.coordPartial 0 (xyTrig A B 0) =
      xyTrig (2 * Real.pi * B) (-(2 * Real.pi) * A) 0 :=
    funext fun x => coordPartial_xyTrig A B 0 x
  have hX : ∑ s, F.weight s * ∫ x, (F.density s).density x *
      DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1 =
      (2 * Real.pi * B) * xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) +
        (-(2 * Real.pi) * A) *
          xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) := by
    have e : ∀ s, F.weight s * ∫ x, (F.density s).density x *
        DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1 =
        (2 * Real.pi * B) * (F.weight s *
          xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))) +
        (-(2 * Real.pi) * A) * (F.weight s *
          xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))) := fun s => by
      rw [hcp, integral_density_mul_xyTrig_ex077]
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← xyZ1_barycenter, ← xyZ2_barycenter]
  -- the quadratic term: integrate over the barycenter
  have hφc : Continuous (fun x => xyTrig A B 0 x ^ 2) := (continuous_xyTrig A B 0).pow 2
  have hφb : ∀ x, ‖xyTrig A B 0 x ^ 2‖ ≤ (|A| + |B|) ^ 2 := fun x => by
    have h0 := abs_xyTrig_zero_le A B x
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hBar : ∑ s, F.weight s * ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 =
      ∫ x, (DGPS.barycenter F).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 :=
    barycenter_integral_ex077 F (fun x => xyTrig A B 0 x ^ 2) fun s =>
      (F.density s).integrable_density.mul_bdd hφc.aestronglyMeasurable
        (Filter.Eventually.of_forall hφb)
  have hI : ∫ x, (DGPS.barycenter F).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 =
      ∫ x, xyTrig A B 0 x ^ 2 ∂(DGPS.densityMeasure (DGPS.barycenter F) :
        Measure (DGPS.Torus 1)) :=
    (integral_densityMeasure (DGPS.barycenter F) (fun x => xyTrig A B 0 x ^ 2)).symm
  have hsq : ∀ x, xyTrig A B 0 x ^ 2 = 4 * Real.pi ^ 2 * κ ^ 2 *
      (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) * (xyMode x).im -
        xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) *
          (xyMode x).re) ^ 2 :=
    fun x => by
      rw [hA, hB]
      simp only [xyTrig, add_zero]
      ring
  have hY : ∑ s, F.weight s * ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 =
      4 * Real.pi ^ 2 * κ ^ 2 * ∫ x, (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) :
          Measure (DGPS.Torus 1)) * (xyMode x).im - xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) :
          Measure (DGPS.Torus 1)) * (xyMode x).re) ^ 2
        ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) := by
    rw [hBar, hI, integral_congr_ae (Filter.Eventually.of_forall hsq), integral_const_mul]
  rw [key, hX, hY]
  subst hA hB
  ring

/-- EX078 helper: the critical squared-score identity `U + V + Z = D_crit / (2 a0) ≥ 0`, where
`D_crit` is the dissipation of `attractiveXY 2 0` with its canonical drift. -/
theorem critical_nonneg_ex078 (F : DGPS.SpeciesFamily 1) :
    0 ≤ ((∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s)) /
          (2 * (4 * Real.pi ^ 2)) -
        (∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal)) +
      ((∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) -
        (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
          xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2)) +
      (2 * (∫ x, (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) *
          (xyMode x).im - xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) :
          Measure (DGPS.Torus 1)) * (xyMode x).re) ^ 2
        ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1))) -
        (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
          xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2)) := by
  obtain ⟨-, hid⟩ := dissipation_toReal_ex078 2 (DGPS.Models.attractiveXYDrift 2 0) F
  have hnn := (ENNReal.toReal_nonneg :
    0 ≤ (DGPS.speciesDissipation (DGPS.Models.attractiveXY 2 0)
      (DGPS.Models.attractiveXYDrift 2 0) F).toReal)
  rw [hid] at hnn
  exact critical_real_ex078 _ _ _ _ hnn

/-- EX078 helper: the real algebra of the deficit bound. -/
theorem deficit_algebra_ex078 (k U V Z E : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hU : E ^ 2 / 12 ≤ U) (hV : 0 ≤ V) (hUVZ : 0 ≤ U + V + Z) :
    (1 - k) * E ^ 2 / 12 ≤ U + k * V + k ^ 2 * Z := by
  have h1k : 0 ≤ 1 - k := sub_nonneg.2 hk1.le
  have hE2 : 0 ≤ E ^ 2 / 12 := by positivity
  rcases le_total Z 0 with hZ | hZ
  · have e : U + k * V + k ^ 2 * Z = (1 - k) * U + k * (U + V + Z) + k * (1 - k) * (-Z) := by
      ring
    have a1 : (1 - k) * (E ^ 2 / 12) ≤ (1 - k) * U := mul_le_mul_of_nonneg_left hU h1k
    have a2 : 0 ≤ k * (U + V + Z) := mul_nonneg hk0 hUVZ
    have a3 : 0 ≤ k * (1 - k) * (-Z) := mul_nonneg (mul_nonneg hk0 h1k) (by linarith)
    have e2 : (1 - k) * E ^ 2 / 12 = (1 - k) * (E ^ 2 / 12) := by ring
    rw [e, e2]
    linarith
  · have a1 : 0 ≤ k * V := mul_nonneg hk0 hV
    have a2 : 0 ≤ k ^ 2 * Z := mul_nonneg (sq_nonneg k) hZ
    have a3 : 0 ≤ k * (E ^ 2 / 12) := mul_nonneg hk0 hE2
    have e2 : (1 - k) * E ^ 2 / 12 = E ^ 2 / 12 - k * (E ^ 2 / 12) := by ring
    rw [e2]
    linarith

/-- EX078: quantitative positive harmonic deficit. For `0 ≤ k < 1` the species dissipation of the
first-harmonic model is finite, and `(D - 2 a0 (1 - k) G) / (2 a0) ≥ (1 - k) E² / 12`, with
`a0 = 4π²`, `G` the species gap and `E = ∑ θ_s H(ρ_s | Haar)`. -/
theorem quantitative_positive_harmonic_deficit (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) (F : DGPS.SpeciesFamily 1) :
    DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b F ≠ ⊤ ∧
      (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) ^ 2 /
          12 ≤
        ((DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b F).toReal -
          2 * (4 * Real.pi ^ 2 * (1 - k)) *
            (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ)) /
          (2 * (4 * Real.pi ^ 2)) := by
  obtain ⟨hDfin, hdef⟩ := exact_harmonic_family_deficit_polynomial k hk0 hk1 b F
  refine ⟨hDfin, ?_⟩
  rw [hdef]
  have hU := U_bound_ex078 Finset.univ F.weight
    (fun s => (DGPS.relativeEntropy
      (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal)
    (fun s => DGPS.Analysis.circleFisherInformation (F.density s))
    (fun s _ => F.weight_nonneg s) F.weight_sum
    (fun s _ => fou016_species_ex078 (F.density s))
  exact deficit_algebra_ex078 k _ _ _ _ hk0 hk1 hU (V_nonneg_ex078 F) (critical_nonneg_ex078 F)

end DGPS.Examples
