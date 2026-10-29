import FullLabeledLSI.Nonvacuity.Prop82.Algebra

/-!
# Admissible sublevel bounds and minimizing sequences

All results in this file concern the ORIGINAL admissible class. In particular
no smoothness, uniform lower bound on the densities, optimizer existence, or
finite-dimensional restriction is smuggled into the minimizing sequence.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Prop82

theorem firstMode_le_two_entropy {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) : firstMode rho ≤ 2 * entropy rho := by
  have hc := cosine_entropy_comparison_aux (by norm_num : (0 : Real) < 1) h.1 h.2.1
  have hq := hc.1.trans hc.2.1
  have hkl : klDiv (densMeasure rho) (haar 1) = ENNReal.ofReal (entropy rho) :=
    (ENNReal.ofReal_toReal (entropy_fisher_finite h).1).symm
  rw [hkl, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)] at hq
  exact (ENNReal.ofReal_le_ofReal_iff (by have := entropy_nonneg rho; positivity)).mp hq

theorem entropy_pos {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) : 0 < entropy rho := by
  have hG := realGap_pos h
  have hQ := firstMode_le_two_entropy h
  have hH0 := entropy_nonneg rho
  have hQ0 := firstMode_nonneg rho
  unfold realGap at hG
  nlinarith

theorem deficit_bound {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    aCos / 6 * entropy rho ^ 2 ≤ fisher rho - 2 * aCos * entropy rho :=
  (circle_quantitative_lsi_aux h.1 h.2.1 h.2.2.1).2.2.2

theorem realRate_le_realQuotient {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    realRate ≤ realDiss rho / (2 * realGap rho) := by
  have hq := rate_le_quotient h
  rw [quotient_eq_real h] at hq
  exact ENNReal.toReal_le_of_le_ofReal
    (div_nonneg (realDiss_nonneg h.1) (by have := realGap_pos h; positivity)) hq

/-- Explicit bounds on the entire finite-Fisher sublevel, not just on smooth
positive trial densities. -/
theorem subthreshold_bounds {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho)
    (hq : realDiss rho / (2 * realGap rho) < aCos * (3 / 2)) :
    fisher rho < 3 * aCos * entropy rho ∧
      entropy rho < 6 ∧ fisher rho < 18 * aCos := by
  have hG := realGap_pos h
  have hD : realDiss rho < 3 * aCos * realGap rho := by
    have hd := (div_lt_iff₀ (by positivity : 0 < 2 * realGap rho)).mp hq
    nlinarith
  have hI : fisher rho < 3 * aCos * entropy rho := by
    apply fisher_lt_three_entropy a_pos (firstMode_nonneg rho) (forceEnergy_nonneg h.1)
    exact hD
  exact ⟨hI, compactness_bounds a_pos (entropy_pos h) (deficit_bound h) hI⟩

theorem fisher_eq_sqrt_energy {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    fisher rho = 4 * ∫ x, weakGrad (fun y => Real.sqrt (rho y)) x 0 ^ 2 ∂haar 1 := by
  unfold fisher
  rw [fisherInfo_densMeasure_eq h.1 h.2.1 h.2.2.1, ENNReal.toReal_ofReal]
  exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)

/-- The concrete bound that can be passed to `SharpLSI.rellich_torus`. -/
theorem sqrt_H1_energy_bound {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho)
    (hq : realDiss rho / (2 * realGap rho) < aCos * (3 / 2)) :
    (∫ x, Real.sqrt (rho x) ^ 2 ∂haar 1) +
      (∑ j : Fin 1, ∫ x, weakGrad (fun y => Real.sqrt (rho y)) x j ^ 2 ∂haar 1) <
      1 + 9 * aCos / 2 := by
  have hI := (subthreshold_bounds h hq).2.2
  rw [fisher_eq_sqrt_energy h] at hI
  simp_rw [Real.sq_sqrt (h.1 _)]
  rw [h.2.1, Fin.sum_univ_one]
  nlinarith

/-- The `ENNReal` optimizer equation is exactly the real one on this domain. -/
theorem optimizer_equation_iff {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    (dissipation cosV (cosW 1) rho =
      2 * mfRate * (gap cosV (cosW 1) (densMeasure rho)).toENNReal) ↔
      realDiss rho = 2 * realRate * realGap rho := by
  have hD := realDiss_nonneg h.1
  have hG := realGap_pos h
  have hR := realRate_nonneg
  rw [dissipation_eq_real h, gap_eq_real h, EReal.real_coe_toENNReal,
    ← ofReal_realRate, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_eq_ofReal_iff hD (by positivity)

theorem RawOptimizer.real_equation {rho : Torus 1 → Real} (h : RawOptimizer rho) :
    realDiss rho = 2 * realRate * realGap rho :=
  (optimizer_equation_iff h.1).mp h.2

theorem RawOptimizer.real_quotient {rho : Torus 1 → Real} (h : RawOptimizer rho) :
    realDiss rho / (2 * realGap rho) = realRate := by
  rw [h.real_equation]
  have hG := (realGap_pos h.1).ne'
  field_simp [hG] <;> ring

/-- An admissible minimizing sequence exists by the definition of the full
infimum and the already-proved finiteness of `mfRate`. -/
theorem exists_minimizing_sequence :
    ∃ rho : Nat → Torus 1 → Real,
      (∀ n, Admissible cosV (cosW 1) (rho n)) ∧
      Tendsto (fun n => realDiss (rho n) / (2 * realGap (rho n)))
        atTop (𝓝 realRate) := by
  have hex : ∀ n : Nat, ∃ rho : Torus 1 → Real,
      Admissible cosV (cosW 1) rho ∧
        quotient rho < ENNReal.ofReal (realRate + 1 / ((n : Real) + 1)) := by
    intro n
    have hlt : mfRate < ENNReal.ofReal (realRate + 1 / ((n : Real) + 1)) := by
      rw [← ofReal_realRate]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg realRate_nonneg).mpr
      have : (0 : Real) < 1 / ((n : Real) + 1) := by positivity
      linarith
    change (⨅ rho ∈ {rho | Admissible cosV (cosW 1) rho}, quotient rho) < _ at hlt
    obtain ⟨rho, hrho⟩ := iInf_lt_iff.mp hlt
    obtain ⟨ha, hq⟩ := iInf_lt_iff.mp hrho
    exact ⟨rho, ha, hq⟩
  choose rho ha hq using hex
  refine ⟨rho, ha, ?_⟩
  have hl : ∀ n, realRate ≤ realDiss (rho n) / (2 * realGap (rho n)) :=
    fun n => realRate_le_realQuotient (ha n)
  have hu : ∀ n, realDiss (rho n) / (2 * realGap (rho n)) ≤
      realRate + 1 / ((n : Real) + 1) := by
    intro n
    have hh := hq n
    rw [quotient_eq_real (ha n)] at hh
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (div_nonneg (realDiss_nonneg (ha n).1)
        (by have := realGap_pos (ha n); positivity))).mp hh).le
  have huLim : Tendsto (fun n : Nat => realRate + 1 / ((n : Real) + 1))
      atTop (𝓝 realRate) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add realRate
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds huLim hl hu

/-- Discarding an initial segment produces a uniformly bounded minimizing
sequence. Compactness, exclusion of the zero-gap limit, and regularity remain
separate analytic obligations; none follows just by defining this sequence. -/
theorem exists_subthreshold_minimizing_sequence
    (hR : realRate < aCos * (3 / 2)) :
    ∃ rho : Nat → Torus 1 → Real,
      (∀ n, Admissible cosV (cosW 1) (rho n)) ∧
      (∀ n, realDiss (rho n) / (2 * realGap (rho n)) < aCos * (3 / 2)) ∧
      (∀ n, entropy (rho n) < 6 ∧ fisher (rho n) < 18 * aCos) ∧
      Tendsto (fun n => realDiss (rho n) / (2 * realGap (rho n)))
        atTop (𝓝 realRate) := by
  obtain ⟨rho, ha, hlim⟩ := exists_minimizing_sequence
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hR))
  have hshift : StrictMono (fun n : Nat => n + N) :=
    fun i j hij => Nat.add_lt_add_right hij N
  refine ⟨fun n => rho (n + N), fun n => ha (n + N), ?_, ?_, hlim.comp hshift.tendsto_atTop⟩
  · intro n
    exact hN (n + N) (by omega)
  · intro n
    exact (subthreshold_bounds (ha (n + N)) (hN (n + N) (by omega))).2

end SharpLSI.FL.Prop82
