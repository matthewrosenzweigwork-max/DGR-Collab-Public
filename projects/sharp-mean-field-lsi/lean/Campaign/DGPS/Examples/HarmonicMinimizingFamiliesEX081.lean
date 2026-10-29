import DGPS.Examples.HarmonicStrictQuotientEX080
import DGPS.Foundations.TotalVariation

/-!
# Minimizing families have vanishing weighted entropy (EX081)

Fix `0 ≤ k < 1` and put `r = 4π² (1 - k)`. Let `F n` be finite species families (the count and the
weights may vary arbitrarily with `n`) with positive gaps and quotients `Q_n = D/(2G)` converging
to `r` in `ℝ≥0∞`. Then

* the weighted Haar entropies `E_n = ∑_s θ_{n,s} H(ρ_{n,s} | Haar)` tend to `0`
  (in `ℝ≥0∞`, in the form of T12, and in real form);
* the weighted full variations `∑_s θ_{n,s} ‖ρ_{n,s} - 1‖_{L¹} = ∑_s θ_{n,s} ‖ρ_{n,s} m - m‖_TV`
  tend to `0`;
* for scalar minimizing sequences `ρ n` (positive gap, `Q(ρ n) → r`), the entropy `H(ρ n | Haar)`
  and the full total variation `‖ρ n m - m‖_TV` both tend to `0`.

Route. EX080 gives `ofReal (r + r E_n / 12) ≤ Q_n`, i.e. `0 ≤ E_n ≤ 12 (Q_n - r) / r`; with `Q_n → r`
this forces `E_n → 0` (`tendsto_zero_of_le_quotient_ex081`). Pinsker (DEF029) and the weighted
Jensen inequality give `(∑ θ TV)² ≤ ∑ θ TV² ≤ 2 E_n`. The `L¹` norm equals the full variation
(`DGPS.fullVariation_eq_integral_abs`). No uniform convergence of the individual species is claimed
(species with weight tending to zero may stay far from Haar), and `k` is fixed throughout.

Design choices (R5 notes).
* The listed module `DGPS/Examples/HarmonicNonattainment.lean` already holds the EX076 content, so
  this result is placed in the new module `DGPS/Examples/HarmonicMinimizingFamiliesEX081.lean`.
* The result holds for every absolute drift `b` of the model (the quotient uses `b`), which is
  at least as general as the canonical drift of T12.
* The `ℝ≥0∞` form of the entropy sum is the T12 form
  `∑ ofReal θ * H(ρ | Haar)`; the real form uses `toReal` of each (finite) entropy.
* "`‖ρ - 1‖_{L¹}`" is `∫ |ρ - 1| d Haar`, proved equal to `fullVariation (ρ m) m`.
* Helper lemmas carry the suffix `_ex081`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples

/-- EX081 helper: a nonnegative real sequence squeezed by `ofReal (r + c E_n) ≤ Q_n → ofReal r`
tends to zero. -/
theorem tendsto_zero_of_le_quotient_ex081 (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n) (Q : ℕ → ℝ≥0∞)
    (hle : ∀ n, ENNReal.ofReal (r + c * E n) ≤ Q n)
    (hQ : Tendsto Q atTop (𝓝 (ENNReal.ofReal r))) :
    Tendsto E atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (hE n),
    fun a ha => ?_⟩
  have hpos : 0 < r + c * a := by positivity
  have hlt : ENNReal.ofReal r < ENNReal.ofReal (r + c * a) :=
    (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by nlinarith)
  filter_upwards [(tendsto_order.1 hQ).2 _ hlt] with n hn
  have h1 : ENNReal.ofReal (r + c * E n) < ENNReal.ofReal (r + c * a) := lt_of_le_of_lt (hle n) hn
  have h2 := (ENNReal.ofReal_lt_ofReal_iff hpos).1 h1
  nlinarith

/-- EX081 helper: the entropy of a density relative to Haar is finite. -/
theorem entropy_ne_top_ex081 (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) (DGPS.haar 1) ≠ ⊤ :=
  (DGPS.absoluteDensity_entropy_finite ρ).2.2.1

/-- EX081 helper: the `L¹(Haar)` distance of a density to `1` is the full variation of
`ρ m - m`. -/
theorem l1_eq_fullVariation_ex081 (ρ : DGPS.AbsoluteDensity 1) :
    ∫ x, |ρ.density x - 1| ∂DGPS.haar 1 =
      DGPS.fullVariation (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) (DGPS.haar 1) := by
  have hν : (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) ≪ DGPS.haar 1 := by
    rw [DGPS.densityMeasure_coe]
    exact withDensity_absolutelyContinuous _ _
  rw [DGPS.fullVariation_eq_integral_abs _ _ (DGPS.haar 1) hν Measure.AbsolutelyContinuous.rfl]
  refine integral_congr_ae ?_
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ.sqrt x ^ 2)) (DGPS.haar 1) :=
    (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have h1 := Measure.rnDeriv_withDensity₀ (DGPS.haar 1) hm
  have h2 : (DGPS.haar 1).rnDeriv (DGPS.haar 1) =ᵐ[DGPS.haar 1] 1 := Measure.rnDeriv_self _
  rw [DGPS.densityMeasure_coe]
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]
  simp [DGPS.AbsoluteDensity.density, abs_sub_comm, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- EX081 helper: the weighted full variation squared is at most twice the weighted entropy. -/
theorem weighted_variation_sq_le_ex081 (F : DGPS.SpeciesFamily 1) :
    (∑ s, F.weight s * DGPS.fullVariation
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)) ^ 2 ≤
      2 * ∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal := by
  have hj := sq_weighted_sum_le_ex076 (Finset.univ : Finset (Fin F.count)) F.weight
    (fun s => DGPS.fullVariation
      (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1))
    (fun s _ => F.weight_nonneg s) F.weight_sum
  refine le_trans hj ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have hp := DGPS.pinsker_fullVariation_real
    (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)
    (entropy_ne_top_ex081 (F.density s))
  have hw := F.weight_nonneg s
  nlinarith

/-- EX081 helper: the weighted entropy sum of a family is nonnegative. -/
theorem weighted_entropy_nonneg_ex081 (F : DGPS.SpeciesFamily 1) :
    0 ≤ ∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal :=
  Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) ENNReal.toReal_nonneg

/-- EX081 helper: the weighted full variation is nonnegative. -/
theorem weighted_variation_nonneg_ex081 (F : DGPS.SpeciesFamily 1) :
    0 ≤ ∑ s, F.weight s * DGPS.fullVariation
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1) :=
  Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (DGPS.fullVariation_nonneg _ _)

/-- EX081 helper: the `ℝ≥0∞` weighted entropy equals the embedding of the real one. -/
theorem weighted_entropy_ennreal_ex081 (F : DGPS.SpeciesFamily 1) :
    ∑ s, ENNReal.ofReal (F.weight s) * DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1) =
      ENNReal.ofReal (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) ENNReal.toReal_nonneg]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ENNReal.ofReal_mul (F.weight_nonneg s), ENNReal.ofReal_toReal (entropy_ne_top_ex081 _)]

/-- EX081 helper: weighted entropy tends to zero along a minimizing family sequence (real form). -/
theorem weighted_entropy_tendsto_ex081 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0))
    (F : ℕ → DGPS.SpeciesFamily 1)
    (hG : ∀ n, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) (F n))
    (hQ : Tendsto (fun n => DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b (F n))
      atTop (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k))))) :
    Tendsto (fun n => ∑ s, (F n).weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure ((F n).density s) : Measure (DGPS.Torus 1))
          (DGPS.haar 1)).toReal) atTop (𝓝 0) := by
  have hk' : 0 < 1 - k := by linarith
  have hr : 0 < 4 * Real.pi ^ 2 * (1 - k) := by positivity
  refine tendsto_zero_of_le_quotient_ex081 (4 * Real.pi ^ 2 * (1 - k))
    (4 * Real.pi ^ 2 * (1 - k) / 12) hr (by positivity) _
    (fun n => weighted_entropy_nonneg_ex081 (F n)) _ (fun n => ?_) hQ
  have h := (strict_quotient_and_both_nonattainment_conclusions k hk0 hk1 b).1 (F n) (hG n)
  have h5 := h.2.2.2.2
  convert h5 using 3
  ring

/-- EX081 helper: weighted variation tends to zero along a minimizing family sequence. -/
theorem weighted_variation_tendsto_ex081 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0))
    (F : ℕ → DGPS.SpeciesFamily 1)
    (hG : ∀ n, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) (F n))
    (hQ : Tendsto (fun n => DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b (F n))
      atTop (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k))))) :
    Tendsto (fun n => ∑ s, (F n).weight s * DGPS.fullVariation
        (DGPS.densityMeasure ((F n).density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1))
      atTop (𝓝 0) := by
  have hE := weighted_entropy_tendsto_ex081 k hk0 hk1 b F hG hQ
  have hsq : Tendsto (fun n => Real.sqrt (2 * ∑ s, (F n).weight s * (DGPS.relativeEntropy
      (DGPS.densityMeasure ((F n).density s) : Measure (DGPS.Torus 1))
        (DGPS.haar 1)).toReal)) atTop (𝓝 0) := by
    have h2 := hE.const_mul 2
    rw [mul_zero] at h2
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero (fun n => weighted_variation_nonneg_ex081 (F n)) (fun n => ?_) hsq
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (weighted_variation_sq_le_ex081 (F n)))

/-- EX081: minimizing families have vanishing weighted entropy. Fix `0 ≤ k < 1` and
`r = 4π² (1 - k)`.

* For every sequence `F n` of finite species families (arbitrary counts, strictly positive weights
  summing to one) with positive gaps and quotients `D/(2G)` tending to `r`, the weighted Haar
  entropies `∑_s θ_{n,s} H(ρ_{n,s} | Haar)` tend to `0` (in `ℝ≥0∞`, and in real form), and the
  weighted `L¹` distances `∑_s θ_{n,s} ∫ |ρ_{n,s} - 1| dHaar` and weighted full variations
  `∑_s θ_{n,s} ‖ρ_{n,s} m - m‖_TV` tend to `0`.
* For every scalar minimizing sequence `ρ n` (positive gap, quotient tending to `r`), the entropy
  `H(ρ n | Haar)`, the `L¹` distance `∫ |ρ n - 1|` and the full total variation
  `‖ρ n m - m‖_TV` all tend to `0`.

No uniform convergence of the individual species is asserted, and `k` is fixed. -/
theorem minimizing_families_have_vanishing_weighted_entropy (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) :
    (∀ F : ℕ → DGPS.SpeciesFamily 1,
      (∀ n, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) (F n)) →
      Tendsto (fun n => DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b (F n))
        atTop (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)))) →
      Tendsto (fun n => ∑ s : Fin (F n).count, ENNReal.ofReal ((F n).weight s) *
        DGPS.relativeEntropy (DGPS.densityMeasure ((F n).density s) : Measure (DGPS.Torus 1))
          (DGPS.haar 1)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∑ s, (F n).weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure ((F n).density s) : Measure (DGPS.Torus 1))
          (DGPS.haar 1)).toReal) atTop (𝓝 0) ∧
      Tendsto (fun n => ∑ s, (F n).weight s *
        ∫ x, |((F n).density s).density x - 1| ∂DGPS.haar 1) atTop (𝓝 0) ∧
      Tendsto (fun n => ∑ s, (F n).weight s * DGPS.fullVariation
        (DGPS.densityMeasure ((F n).density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1))
          atTop (𝓝 0)) ∧
    (∀ ρ : ℕ → DGPS.AbsoluteDensity 1,
      (∀ n, 0 < DGPS.scalarGap (DGPS.Models.attractiveXY (2 * k) 0) (ρ n)) →
      Tendsto (fun n => DGPS.scalarQuotient (DGPS.Models.attractiveXY (2 * k) 0) b (ρ n))
        atTop (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)))) →
      Tendsto (fun n => DGPS.relativeEntropy
        (DGPS.densityMeasure (ρ n) : Measure (DGPS.Torus 1)) (DGPS.haar 1)) atTop (𝓝 0) ∧
      Tendsto (fun n => (DGPS.relativeEntropy
        (DGPS.densityMeasure (ρ n) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal)
          atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, |(ρ n).density x - 1| ∂DGPS.haar 1) atTop (𝓝 0) ∧
      Tendsto (fun n => DGPS.fullVariation
        (DGPS.densityMeasure (ρ n) : Measure (DGPS.Torus 1)) (DGPS.haar 1)) atTop (𝓝 0)) := by
  refine ⟨fun F hG hQ => ?_, fun ρ hG hQ => ?_⟩
  · have hE := weighted_entropy_tendsto_ex081 k hk0 hk1 b F hG hQ
    have hV := weighted_variation_tendsto_ex081 k hk0 hk1 b F hG hQ
    refine ⟨?_, hE, ?_, hV⟩
    · have h := (ENNReal.continuous_ofReal.tendsto 0).comp hE
      simp only [ENNReal.ofReal_zero] at h
      refine h.congr fun n => ?_
      exact (weighted_entropy_ennreal_ex081 (F n)).symm
    · refine hV.congr fun n => ?_
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [l1_eq_fullVariation_ex081]
  · have hG' : ∀ n, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0)
        (DGPS.SpeciesFamily.single (ρ n)) := fun n => by
      rw [DGPS.speciesGap_single]
      exact hG n
    have hQ' : Tendsto (fun n => DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b
        (DGPS.SpeciesFamily.single (ρ n))) atTop
        (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)))) := by
      simpa only [DGPS.speciesQuotient_single] using hQ
    have hE := weighted_entropy_tendsto_ex081 k hk0 hk1 b _ hG' hQ'
    simp only [single_entropy_sum_ex079] at hE
    have hTV : Tendsto (fun n => DGPS.fullVariation
        (DGPS.densityMeasure (ρ n) : Measure (DGPS.Torus 1)) (DGPS.haar 1)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun n => Real.sqrt (2 * (DGPS.relativeEntropy
          (DGPS.densityMeasure (ρ n) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal))
          atTop (𝓝 0) := by
        have h2 := hE.const_mul 2
        rw [mul_zero] at h2
        have := (Real.continuous_sqrt.tendsto 0).comp h2
        rw [Real.sqrt_zero] at this
        exact this
      refine squeeze_zero (fun n => DGPS.fullVariation_nonneg _ _) (fun n => ?_) hsq
      exact le_trans (le_abs_self _) (Real.abs_le_sqrt
        (DGPS.pinsker_fullVariation_real _ _ (entropy_ne_top_ex081 (ρ n))))
    refine ⟨?_, hE, ?_, hTV⟩
    · have h := (ENNReal.continuous_ofReal.tendsto 0).comp hE
      simp only [ENNReal.ofReal_zero] at h
      refine h.congr fun n => ?_
      simp [ENNReal.ofReal_toReal (entropy_ne_top_ex081 (ρ n))]
    · refine hTV.congr fun n => ?_
      rw [l1_eq_fullVariation_ex081]

end DGPS.Examples
