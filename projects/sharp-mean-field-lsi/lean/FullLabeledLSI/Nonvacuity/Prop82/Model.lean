import FullLabeledLSI.Statements.S13_Prop_8_2
import SharpSymmetricLSI.Paper.CosineHyp
import SharpSymmetricLSI.Paper.CosineStrict
import SharpSymmetricLSI.Paper.CosineExpansion

/-!
# Proposition 8.2: the coupling-one model and the exact nonvacuity target

This is an extension of the supplied 6b9f4ca source, not a replacement of any
of its definitions. All rates, gaps, dissipations and Sobolev predicates below
are the originals. In particular `mfRate` is still an infimum over the full
`Admissible` class, not an infimum over the two-harmonic trial family.

Verification status: proof source; not compiled in the authoring environment.
The unconditional nonvacuity theorem is NOT asserted in this file.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

noncomputable abbrev mfRate : ENNReal := rStar cosV (cosW 1)

noncomputable def realRate : Real := mfRate.toReal

noncomputable def entropy (rho : Torus 1 → Real) : Real :=
  (klDiv (densMeasure rho) (haar 1)).toReal

/-- Physical, not angular, Fisher information. -/
noncomputable def fisher (rho : Torus 1 → Real) : Real :=
  (fisherInfo (densMeasure rho) (haar 1)).toReal

/-- Physical force energy. This contains the factor `aCos`. -/
noncomputable def forceEnergy (rho : Torus 1 → Real) : Real :=
  ∫ x, rho x * weakGrad (gConv rho) x 0 ^ 2 ∂haar 1

noncomputable def realGap (rho : Torus 1 → Real) : Real :=
  entropy rho + firstMode rho / 2

noncomputable def realDiss (rho : Torus 1 → Real) : Real :=
  fisher rho + 2 * aCos * firstMode rho + forceEnergy rho

noncomputable def quotient (rho : Torus 1 → Real) : ENNReal :=
  dissipation cosV (cosW 1) rho /
    (2 * (gap cosV (cosW 1) (densMeasure rho)).toENNReal)

/-- The actual standing hypotheses, with the numerical coupling fixed. -/
theorem model_hyp : Hyp cosV (cosW 1) 0 (2 * aCos) := by
  simpa using (cosine_hyp_aux (κ := 1) (by norm_num : (0 : Real) < 1))

/-- `aCos = 4 pi^2` is strictly positive. -/
theorem a_pos : 0 < aCos := by
  unfold aCos
  positivity

theorem rate_ne_top : mfRate ≠ ⊤ :=
  (Sec8.rStar_lt_top (by norm_num : 1 ≤ (1 : Nat)) model_hyp).ne

theorem ofReal_realRate : ENNReal.ofReal realRate = mfRate :=
  ENNReal.ofReal_toReal rate_ne_top

theorem realRate_nonneg : 0 ≤ realRate := ENNReal.toReal_nonneg

/-- Reuses the source's strict cosine lower bound; this is not a new axiom. -/
theorem a_lt_realRate : aCos < realRate := by
  have h : ENNReal.ofReal aCos < ENNReal.ofReal realRate := by
    rw [ofReal_realRate]
    exact cosine_strict_aux (by norm_num : (0 : Real) < 1)
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg a_pos.le).mp h

theorem realRate_pos : 0 < realRate := a_pos.trans a_lt_realRate

/-- The old source proves only the non-strict upper bound. The strict bound
needed for attainment is a genuinely additional proof obligation. -/
theorem rate_le_threshold : mfRate ≤ ENNReal.ofReal (aCos * (3 / 2)) := by
  convert (cosine_rStar_le_aux (κ := 1) (by norm_num : (0 : Real) < 1)) using 1 <;>
    norm_num

theorem realRate_le_threshold : realRate ≤ aCos * (3 / 2) :=
  ENNReal.toReal_le_of_le_ofReal (by have := a_pos.le; positivity) rate_le_threshold

theorem entropy_nonneg (rho : Torus 1 → Real) : 0 ≤ entropy rho :=
  ENNReal.toReal_nonneg

theorem fisher_nonneg (rho : Torus 1 → Real) : 0 ≤ fisher rho :=
  ENNReal.toReal_nonneg

theorem firstMode_nonneg (rho : Torus 1 → Real) : 0 ≤ firstMode rho :=
  Complex.normSq_nonneg _

theorem forceEnergy_nonneg {rho : Torus 1 → Real} (h0 : ∀ x, 0 ≤ rho x) :
    0 ≤ forceEnergy rho :=
  integral_nonneg fun x => mul_nonneg (h0 x) (sq_nonneg _)

theorem realDiss_nonneg {rho : Torus 1 → Real} (h0 : ∀ x, 0 ≤ rho x) :
    0 ≤ realDiss rho := by
  unfold realDiss
  exact add_nonneg (add_nonneg (fisher_nonneg rho)
    (mul_nonneg (mul_nonneg (by norm_num) a_pos.le) (firstMode_nonneg rho)))
    (forceEnergy_nonneg h0)

/-- Finiteness is established before any real-valued identity is used. -/
theorem entropy_fisher_finite {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    klDiv (densMeasure rho) (haar 1) ≠ ⊤ ∧
      fisherInfo (densMeasure rho) (haar 1) ≠ ⊤ := by
  have hq := circle_quantitative_lsi_aux h.1 h.2.1 h.2.2.1
  exact ⟨hq.1, hq.2.1⟩

theorem gap_eq_real {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    gap cosV (cosW 1) (densMeasure rho) = (realGap rho : EReal) := by
  have hkl : klDiv (densMeasure rho) (haar 1) = ENNReal.ofReal (entropy rho) :=
    (ENNReal.ofReal_toReal (entropy_fisher_finite h).1).symm
  rw [(cosine_free_energy_aux (by norm_num : (0 : Real) < 1)).2.2.2.1 rho h.1 h.2.1,
    hkl, EReal.coe_ennreal_ofReal, max_eq_left (entropy_nonneg rho), ← EReal.coe_add]
  congr 1
  unfold realGap
  ring

theorem realGap_pos {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) : 0 < realGap rho := by
  have hp := h.2.2.2
  rw [gap_eq_real h] at hp
  exact_mod_cast hp

theorem dissipation_eq_real {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    dissipation cosV (cosW 1) rho = ENNReal.ofReal (realDiss rho) := by
  have hQ := firstMode_nonneg rho
  have ha := a_pos
  have hP := forceEnergy_nonneg h.1
  have hI := fisher_nonneg rho
  have hfi : fisherInfo (densMeasure rho) (haar 1) = ENNReal.ofReal (fisher rho) :=
    (ENNReal.ofReal_toReal (entropy_fisher_finite h).2).symm
  rw [cosine_dissipation_expansion_aux (by norm_num : (0 : Real) < 1)
    h.1 h.2.1 (entropy_fisher_finite h).2, hfi]
  simp only [mul_one, one_pow, one_mul]
  change _ + ENNReal.ofReal (forceEnergy rho) = _
  rw [← ENNReal.ofReal_add (fisher_nonneg rho) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (forceEnergy_nonneg h.1)]
  rfl

theorem quotient_eq_real {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) :
    quotient rho = ENNReal.ofReal (realDiss rho / (2 * realGap rho)) := by
  unfold quotient
  rw [dissipation_eq_real h, gap_eq_real h, EReal.real_coe_toENNReal,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by have := realGap_pos h; positivity)]

theorem rate_le_quotient {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) : mfRate ≤ quotient rho :=
  iInf₂_le rho h

structure SmoothProbability (rho : Torus 1 → Real) : Prop where
  smooth : IsSmoothT rho
  positive : ∀ x, 0 < rho x
  mass : ∫ x, rho x ∂haar 1 = 1

namespace SmoothProbability

theorem nonneg {rho : Torus 1 → Real} (h : SmoothProbability rho) (x : Torus 1) :
    0 ≤ rho x := (h.positive x).le

theorem sqrt_memH1 {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    MemH1 (haar 1) (fun x => Real.sqrt (rho x)) :=
  Sec8.memH1_of_smooth (Sec8.isSmoothT_sqrt h.smooth h.positive)

theorem admissible {rho : Torus 1 → Real} (h : SmoothProbability rho)
    (hG : 0 < gap cosV (cosW 1) (densMeasure rho)) :
    Admissible cosV (cosW 1) rho :=
  ⟨h.nonneg, h.mass, h.sqrt_memH1, hG⟩

end SmoothProbability

/-- A full-domain optimizer before regularity or representative selection. -/
def RawOptimizer (rho : Torus 1 → Real) : Prop :=
  Admissible cosV (cosW 1) rho ∧
    dissipation cosV (cosW 1) rho =
      2 * mfRate * (gap cosV (cosW 1) (densMeasure rho)).toENNReal

structure SmoothOptimizer (rho : Torus 1 → Real) : Prop where
  probability : SmoothProbability rho
  gap_pos : 0 < gap cosV (cosW 1) (densMeasure rho)
  attained : dissipation cosV (cosW 1) rho =
    2 * mfRate * (gap cosV (cosW 1) (densMeasure rho)).toENNReal

theorem SmoothOptimizer.admissible {rho : Torus 1 → Real}
    (h : SmoothOptimizer rho) : Admissible cosV (cosW 1) rho :=
  h.probability.admissible h.gap_pos

theorem SmoothOptimizer.raw {rho : Torus 1 → Real}
    (h : SmoothOptimizer rho) : RawOptimizer rho := ⟨h.admissible, h.attained⟩

/-- Exactly the density-dependent antecedents of S13 in the explicit model. -/
def Nonvacuous : Prop :=
  ∃ rho : Torus 1 → Real,
    IsSmoothT rho ∧ (∀ x, 0 < rho x) ∧
    (∫ x, rho x ∂haar 1 = 1) ∧
    0 < gap cosV (cosW 1) (densMeasure rho) ∧
    dissipation cosV (cosW 1) rho =
      2 * mfRate * (gap cosV (cosW 1) (densMeasure rho)).toENNReal ∧
    poincareConst (densMeasure rho) < mfRate

theorem nonvacuous_iff : Nonvacuous ↔
    ∃ rho : Torus 1 → Real,
      SmoothOptimizer rho ∧ poincareConst (densMeasure rho) < mfRate := by
  constructor
  · rintro ⟨rho, hs, hp, hm, hG, ha, hP⟩
    exact ⟨rho, ⟨⟨hs, hp, hm⟩, hG, ha⟩, hP⟩
  · rintro ⟨rho, h, hP⟩
    exact ⟨rho, h.probability.smooth, h.probability.positive,
      h.probability.mass, h.gap_pos, h.attained, hP⟩

/-- The original proposition is applied without changing any antecedent. -/
theorem obstruction_of_witness {rho : Torus 1 → Real}
    (h : SmoothOptimizer rho) (hP : poincareConst (densMeasure rho) < mfRate) :
    Tendsto (fun N => rAll cosV (cosW 1) N) atTop (𝓝 (rMs cosV (cosW 1))) ∧
    rMs cosV (cosW 1) < mfRate ∧
    Tendsto (fun N => rSym cosV (cosW 1) N) atTop (𝓝 mfRate) := by
  exact quotient_optimizer_obstruction (by norm_num : 1 ≤ (1 : Nat)) model_hyp rho
    h.probability.smooth h.probability.positive h.probability.mass h.gap_pos h.attained hP

end SharpLSI.FL.Prop82
