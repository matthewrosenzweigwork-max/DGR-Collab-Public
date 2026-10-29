import DGPS.Examples.AttractiveXYCritical
import DGPS.Model.SpeciesRate
import DGPS.Model.Barycenter

/-!
# Subcritical harmonic model and gap (EX076)

For `0 ≤ k < 1` the model `attractiveXY (2k) 0` has `V = 0` and
`W(x,y) = 2k (1 - cos 2π(x-y))` on the period-one torus (the first-harmonic family of T12).
Its free energy is `F(ν) = H(ν | Haar) + k - k |ν̂(1)|²`, with `|ν̂(1)|² = z₁² + z₂²`.

* `Haar` is the unique global minimiser of `F`, and `F_* = k`.
* For a finite species family `F`, with `E = ∑ θ_s H(ρ_s | Haar)` and `M = |ρ̄(e^{2πi·})|²`,
  the species gap is `G = E - k M`, and `(1 - k) E ≤ G ≤ E`.
* `G > 0` iff some species with positive weight is not Haar.

Proof.  The entropy--Fourier inequality (EX019) gives `|ν̂(1)|² ≤ H(ν | Haar)` for every
probability `ν`, so `M ≤ E` by the weighted Jensen inequality applied to the linear mixing of
the Fourier coefficients of the barycenter.  The gap identity follows by unfolding
`speciesRawGap` with `V = 0`, the interaction energy formula of EX018, and `F_* = k`.

Design choices (R5 notes).
* "Equilibrium" is read as the unique global minimiser of the free energy, the convention of
  EX019 (`Haar is the unique global minimizer`).
* The model is `DGPS.Models.attractiveXY (2 * k) 0`; `W` is written with `(xyMode (x - y)).re`,
  which is `cos 2π(x - y)` (EX018 convention).
* The gap is the Lean `DGPS.speciesGap`, whose real value is `speciesRawGap`; the identity
  `G = E - k M` is proved by unfolding it, not through the DEF014 decomposition theorem.
* Helper lemmas carry the suffix `_ex076` to avoid project-wide name clashes.
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal

namespace DGPS.Examples

open DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical DGPS.Models

/-- EX076 helper: weighted Jensen inequality for the square of a real weighted mean. -/
theorem sq_weighted_sum_le_ex076 {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i * a i) ^ 2 ≤ ∑ i ∈ s, w i * a i ^ 2 := by
  have h := (Even.convexOn_pow even_two : ConvexOn ℝ Set.univ fun x : ℝ => x ^ 2).map_sum_le
    hw hw1 (fun i _ => Set.mem_univ (a i))
  simpa [smul_eq_mul] using h

/-- EX076 helper: weighted Jensen inequality for the squared modulus of a planar mean. -/
theorem sq_norm_weighted_sum_le_ex076 {ι : Type*} (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i * a i) ^ 2 + (∑ i ∈ s, w i * b i) ^ 2 ≤
      ∑ i ∈ s, w i * (a i ^ 2 + b i ^ 2) := by
  have h1 := sq_weighted_sum_le_ex076 s w a hw hw1
  have h2 := sq_weighted_sum_le_ex076 s w b hw hw1
  have h3 : ∑ i ∈ s, w i * (a i ^ 2 + b i ^ 2) =
      ∑ i ∈ s, w i * a i ^ 2 + ∑ i ∈ s, w i * b i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- EX076 helper: the free energy of `attractiveXY (2k) 0` on probability measures. -/
theorem freeEnergy_formula_ex076 (k : ℝ) (ν : ProbabilityMeasure (DGPS.Torus 1)) :
    DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) ν =
      ((DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
        ((k - k * (xyZ1 (ν : Measure (DGPS.Torus 1)) ^ 2 +
          xyZ2 (ν : Measure (DGPS.Torus 1)) ^ 2) : ℝ) : EReal) := by
  rw [freeEnergy_attractiveXY]
  congr 2
  ring

/-- EX076 helper: the first Fourier coefficient of Haar vanishes. -/
theorem xyZ1_haar_ex076 : xyZ1 (DGPS.haar 1) = 0 := by
  rw [← re_integral_xyMode_xyc, integral_xyMode_haar_xyc]
  rfl

/-- EX076 helper: the second Fourier coefficient of Haar vanishes. -/
theorem xyZ2_haar_ex076 : xyZ2 (DGPS.haar 1) = 0 := by
  rw [← im_integral_xyMode_xyc, integral_xyMode_haar_xyc]
  rfl

/-- EX076 helper: the free energy of the Haar probability is `k`. -/
theorem freeEnergy_haar_ex076 (k : ℝ) :
    DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) (DGPS.haarProbability 1) =
      (k : EReal) := by
  rw [freeEnergy_formula_ex076]
  have h0 : DGPS.relativeEntropy (DGPS.haar 1) (DGPS.haar 1) = 0 :=
    DGPS.relativeEntropy_self _
  show ((DGPS.relativeEntropy (DGPS.haar 1) (DGPS.haar 1) : ℝ≥0∞) : EReal) +
      ((k - k * (xyZ1 (DGPS.haar 1) ^ 2 + xyZ2 (DGPS.haar 1) ^ 2) : ℝ) : EReal) = _
  rw [h0, xyZ1_haar_ex076, xyZ2_haar_ex076]
  simp

/-- EX076 helper: every non-Haar probability has strictly larger free energy than Haar. -/
theorem freeEnergy_gt_ex076 (k : ℝ) (_hk0 : 0 ≤ k) (hk1 : k < 1)
    (ν : ProbabilityMeasure (DGPS.Torus 1)) (hν : ν ≠ DGPS.haarProbability 1) :
    DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) (DGPS.haarProbability 1) <
      DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) ν := by
  rw [freeEnergy_haar_ex076, freeEnergy_formula_ex076]
  have hs := (strict_entropy_fourier_inequality_at_criticality).1 ν hν
  rw [norm_sq_integral_xyMode_xyc] at hs
  by_cases htop : DGPS.relativeEntropy (ν : Measure (DGPS.Torus 1)) (DGPS.haar 1) = ⊤
  · rw [htop, EReal.coe_ennreal_top, EReal.top_add_coe]
    exact EReal.coe_lt_top _
  · rw [← EReal.coe_ennreal_toReal htop, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    have hQ := (ENNReal.ofReal_lt_iff_lt_toReal
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) htop).mp hs
    have hQ0 : 0 ≤ xyZ1 (ν : Measure (DGPS.Torus 1)) ^ 2 +
        xyZ2 (ν : Measure (DGPS.Torus 1)) ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.2 hk1.le) hQ0]

/-- EX076: the minimal free energy of `attractiveXY (2k) 0` is `k`. -/
theorem freeEnergyMinimum_ex076 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY (2 * k) 0) = (k : EReal) := by
  refine le_antisymm ?_ (le_iInf fun ν => ?_)
  · have h := iInf_le (fun μ : ProbabilityMeasure (DGPS.Torus 1) =>
      DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) μ) (DGPS.haarProbability 1)
    rwa [freeEnergy_haar_ex076] at h
  · by_cases hν : ν = DGPS.haarProbability 1
    · rw [hν, freeEnergy_haar_ex076]
    · rw [← freeEnergy_haar_ex076 k]
      exact (freeEnergy_gt_ex076 k hk0 hk1 ν hν).le

/-- EX076: the real minimal free energy of `attractiveXY (2k) 0` is `k`. -/
theorem freeEnergyMinimumReal_ex076 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    DGPS.freeEnergyMinimumReal (DGPS.Models.attractiveXY (2 * k) 0) = k := by
  have h := DGPS.coe_freeEnergyMinimumReal (DGPS.Models.attractiveXY (2 * k) 0)
  rw [freeEnergyMinimum_ex076 k hk0 hk1] at h
  exact_mod_cast h

/-- EX076 helper: the entropy--Fourier inequality for an absolute density, real form. -/
theorem species_fourier_ex076 (ρ : DGPS.AbsoluteDensity 1) :
    xyZ1 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) ^ 2 +
        xyZ2 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) ^ 2 ≤
      (DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))
        (DGPS.haar 1)).toReal := by
  by_cases h : DGPS.densityMeasure ρ = DGPS.haarProbability 1
  · have h' : (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) = DGPS.haar 1 :=
      congrArg Subtype.val h
    rw [h', xyZ1_haar_ex076, xyZ2_haar_ex076, DGPS.relativeEntropy_self]
    simp
  · have hs := (strict_entropy_fourier_inequality_at_criticality).1 _ h
    rw [norm_sq_integral_xyMode_xyc] at hs
    have hfin := (DGPS.absoluteDensity_entropy_finite ρ).2.2.1
    exact ((ENNReal.ofReal_lt_iff_lt_toReal
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) hfin).mp hs).le

/-- EX076 helper: `ν̂(1)` of a barycenter is the weighted mean of the species coefficients
(real part). -/
theorem xyZ1_barycenter_ex076 (F : DGPS.SpeciesFamily 1) :
    xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) =
      ∑ s, F.weight s * xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) := by
  have hc : Continuous fun x : DGPS.Torus 1 => (xyMode x).re :=
    Complex.continuous_re.comp continuous_xyMode
  have hb : ∀ x : DGPS.Torus 1, ‖(xyMode x).re‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs]; exact abs_xyMode_re_le x
  have key : ∀ ρ : DGPS.AbsoluteDensity 1,
      ∫ x, (xyMode x).re ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) =
        ∫ x, ρ.density x * (xyMode x).re ∂DGPS.haar 1 := fun ρ =>
    integral_densityMeasure ρ _
  unfold xyZ1
  rw [key (DGPS.barycenter F)]
  simp_rw [key]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun s _ =>
    ((F.density s).integrable_density.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).const_mul (F.weight s))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [F.barycenter_density_apply x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [DGPS.AbsoluteDensity.density]
  ring

/-- EX076 helper: the imaginary part of `ν̂(1)` of a barycenter is the weighted mean. -/
theorem xyZ2_barycenter_ex076 (F : DGPS.SpeciesFamily 1) :
    xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) =
      ∑ s, F.weight s * xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) := by
  have hc : Continuous fun x : DGPS.Torus 1 => (xyMode x).im :=
    Complex.continuous_im.comp continuous_xyMode
  have hb : ∀ x : DGPS.Torus 1, ‖(xyMode x).im‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs]; exact abs_xyMode_im_le x
  have key : ∀ ρ : DGPS.AbsoluteDensity 1,
      ∫ x, (xyMode x).im ∂(DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) =
        ∫ x, ρ.density x * (xyMode x).im ∂DGPS.haar 1 := fun ρ =>
    integral_densityMeasure ρ _
  unfold xyZ2
  rw [key (DGPS.barycenter F)]
  simp_rw [key]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun s _ =>
    ((F.density s).integrable_density.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)).const_mul (F.weight s))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [F.barycenter_density_apply x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [DGPS.AbsoluteDensity.density]
  ring

/-- EX076 helper: the squared Fourier modulus of the barycenter is at most the weighted sum of
the species squared moduli (Jensen). -/
theorem norm_sq_barycenter_le_ex076 (F : DGPS.SpeciesFamily 1) :
    xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
        xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 ≤
      ∑ s, F.weight s * (xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ^ 2 +
        xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ^ 2) := by
  rw [xyZ1_barycenter_ex076, xyZ2_barycenter_ex076]
  exact sq_norm_weighted_sum_le_ex076 Finset.univ F.weight
    (fun s => xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)))
    (fun s => xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)))
    (fun s _ => F.weight_nonneg s) F.weight_sum

/-- EX076 helper: the species gap of `attractiveXY (2k) 0` is `E - k M`. -/
theorem speciesGap_identity_ex076 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (F : DGPS.SpeciesFamily 1) :
    (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) =
      (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) -
        k * ‖∫ x, xyMode x ∂(DGPS.densityMeasure (DGPS.barycenter F) :
          Measure (DGPS.Torus 1))‖ ^ 2 := by
  rw [DGPS.coe_speciesGap, DGPS.speciesRawGap, potentialEnergy_attractiveXY,
    interactionEnergy_attractiveXY (2 * k) 0 (DGPS.densityMeasure (DGPS.barycenter F)),
    freeEnergyMinimumReal_ex076 k hk0 hk1, norm_sq_integral_xyMode_xyc]
  ring

/-- EX076 helper: `(1 - k) E ≤ G ≤ E` for the species gap of `attractiveXY (2k) 0`. -/
theorem speciesGap_bounds_ex076 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (F : DGPS.SpeciesFamily 1) :
    (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) ≤
      (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) ∧
    (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) ≤
      ∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal := by
  set E := ∑ s, F.weight s * (DGPS.relativeEntropy
    (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal with hE
  set Q := ‖∫ x, xyMode x ∂(DGPS.densityMeasure (DGPS.barycenter F) :
    Measure (DGPS.Torus 1))‖ ^ 2 with hQdef
  have hQE : Q ≤ E := by
    have h1 := norm_sq_barycenter_le_ex076 F
    have h2 : ∑ s, F.weight s * (xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ^ 2 +
        xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ^ 2) ≤ E :=
      Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (species_fourier_ex076 (F.density s)) (F.weight_nonneg s)
    rw [hQdef, norm_sq_integral_xyMode_xyc]
    linarith
  have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
  have hg := speciesGap_identity_ex076 k hk0 hk1 F
  rw [← hE, ← hQdef] at hg
  rw [hg]
  constructor
  · nlinarith [mul_nonneg hk0 (sub_nonneg.2 hQE)]
  · nlinarith [mul_nonneg hk0 hQ0]

/-- EX076 helper: `G > 0` iff some species with positive weight is not Haar. -/
theorem speciesGap_pos_iff_ex076 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (F : DGPS.SpeciesFamily 1) :
    0 < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) ↔
      ∃ s, (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ≠ DGPS.haar 1 := by
  have hb := speciesGap_bounds_ex076 k hk0 hk1 F
  have hg := speciesGap_identity_ex076 k hk0 hk1 F
  have hQ0 : 0 ≤ k * ‖∫ x, xyMode x ∂(DGPS.densityMeasure (DGPS.barycenter F) :
      Measure (DGPS.Torus 1))‖ ^ 2 := mul_nonneg hk0 (sq_nonneg _)
  constructor
  · intro hpos
    by_contra hcon
    push Not at hcon
    have hE0 : (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) = 0 :=
      Finset.sum_eq_zero fun s _ => by
        rw [hcon s, DGPS.relativeEntropy_self]
        simp
    linarith [hb.2]
  · rintro ⟨s, hs⟩
    have hH0 : DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1) ≠ 0 :=
      fun h => hs (DGPS.relativeEntropy_zero_iff.mp h)
    have hHtop := (DGPS.absoluteDensity_entropy_finite (F.density s)).2.2.1
    have hHpos : 0 < (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal :=
      ENNReal.toReal_pos hH0 hHtop
    have hsingle : F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal ≤
        ∑ t, F.weight t * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density t) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal :=
      Finset.single_le_sum (f := fun t => F.weight t * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density t) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal)
        (fun t _ => mul_nonneg (F.weight_nonneg t) ENNReal.toReal_nonneg) (Finset.mem_univ s)
    have hEpos : 0 < ∑ t, F.weight t * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density t) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal :=
      lt_of_lt_of_le (mul_pos (F.weight_pos s) hHpos) hsingle
    have := mul_pos (sub_pos.2 hk1) hEpos
    linarith [hb.1]

/-- EX076: subcritical harmonic model and gap.  For `0 ≤ k < 1` the model `attractiveXY (2k) 0`
has `V = 0`, `W(x,y) = 2k(1 - cos 2π(x-y))`; Haar is the unique global minimiser of the free
energy with minimal value `F_* = k`; and every finite species family `F` has species gap
`G = E - k M` (with `E = ∑ θ_s H(ρ_s | Haar)`, `M = |ρ̄(e^{2πi·})|²`) satisfying
`(1 - k) E ≤ G ≤ E`, with `G > 0` iff some species of positive weight is not Haar. -/
theorem subcritical_harmonic_model_and_gap (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    (DGPS.Models.attractiveXY (2 * k) 0).V = (fun _ => 0) ∧
    (∀ x y : DGPS.Torus 1, (DGPS.Models.attractiveXY (2 * k) 0).W x y =
        2 * k * (1 - (xyMode (x - y)).re)) ∧
    DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) (DGPS.haarProbability 1) = (k : EReal) ∧
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1), ν ≠ DGPS.haarProbability 1 →
      DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) (DGPS.haarProbability 1) <
        DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) ν) ∧
    DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY (2 * k) 0) = (k : EReal) ∧
    DGPS.freeEnergyMinimumReal (DGPS.Models.attractiveXY (2 * k) 0) = k ∧
    (∀ ν : ProbabilityMeasure (DGPS.Torus 1),
      DGPS.freeEnergy (DGPS.Models.attractiveXY (2 * k) 0) ν =
        DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY (2 * k) 0) →
        ν = DGPS.haarProbability 1) ∧
    (∀ F : DGPS.SpeciesFamily 1,
      (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) =
          (∑ s, F.weight s * (DGPS.relativeEntropy
            (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) -
            k * ‖∫ x, xyMode x ∂(DGPS.densityMeasure (DGPS.barycenter F) :
              Measure (DGPS.Torus 1))‖ ^ 2 ∧
        (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
            (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) ≤
          (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) ∧
        (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) ≤
          ∑ s, F.weight s * (DGPS.relativeEntropy
            (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal ∧
        (0 < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) ↔
          ∃ s, (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) ≠
            DGPS.haar 1)) := by
  refine ⟨?_, fun x y => attractiveXY_W _ _ x y, freeEnergy_haar_ex076 k,
    fun ν hν => freeEnergy_gt_ex076 k hk0 hk1 ν hν, freeEnergyMinimum_ex076 k hk0 hk1,
    freeEnergyMinimumReal_ex076 k hk0 hk1, ?_, ?_⟩
  · funext x
    rw [attractiveXY_V]
    simp
  · intro ν hν
    by_contra hne
    have h := freeEnergy_gt_ex076 k hk0 hk1 ν hne
    rw [hν, freeEnergy_haar_ex076, freeEnergyMinimum_ex076 k hk0 hk1] at h
    exact lt_irrefl _ h
  · intro F
    have hb := speciesGap_bounds_ex076 k hk0 hk1 F
    exact ⟨speciesGap_identity_ex076 k hk0 hk1 F, hb.1, hb.2,
      speciesGap_pos_iff_ex076 k hk0 hk1 F⟩

end DGPS.Examples
