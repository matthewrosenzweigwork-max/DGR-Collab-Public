import FullLabeledLSI.Paper.Sec3Equil
import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Statements.R22_Reference_LSI

/-!
# Proposition 3.4: the one-particle LSI for the equilibrium

`rLS` is positive for a reference density bounded above and below (`reference_lsi`), and for
each density `ρ` with finite relative Fisher information `rLS · H(ρ|q) ≤ I(ρ|q)/2`.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ}

theorem dirichlet_lt_top {P : Measure (Torus d)} [IsFiniteMeasure P] {f : Torus d → ℝ}
    (h : MemH1 P f) : dirichlet P f < ⊤ := by
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad f x))) P :=
    h.2.2.aestronglyMeasurable
  have := (memLp_two_iff_integrable_sq hm).1 h.2.2
  unfold dirichlet
  have h2 := this.2
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)] at h2
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [Real.sq_sqrt (sqNorm_nonneg _)]

theorem rLS_lower {q : Torus d → ℝ} {cm cp : ℝ} (hcm : 0 < cm) (hb : ∀ x, cm ≤ q x ∧ q x ≤ cp)
    (hq1 : ∫ x, q x ∂haar d = 1) (hqm : Measurable q) :
    ENNReal.ofReal (cm / cp) ≤ rLS (densMeasure q) := by
  unfold rLS
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hfH, hent⟩ := hf
  have hcp : 0 < cp := hcm.trans_le ((hb 0).1.trans (hb 0).2)
  have hlsi := reference_lsi hcm hb hq1 hqm hfH
  have hr : 0 < cm / cp := div_pos hcm hcp
  have hP : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hcm.trans_le (hb x).1).le) hq1
  have hD := dirichlet_lt_top hfH
  have hEt : ent (densMeasure q) (fun x => f x ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.ne) hlsi
  rw [ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hEt)]
  calc ENNReal.ofReal (cm / cp) * ent (densMeasure q) (fun x => f x ^ 2)
      ≤ ENNReal.ofReal (cm / cp) * (ENNReal.ofReal (2 / (cm / cp)) *
          dirichlet (densMeasure q) f) := by
        gcongr
        exact hlsi
    _ = 2 * dirichlet (densMeasure q) f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le]
        have : cm / cp * (2 / (cm / cp)) = 2 := by field_simp
        rw [this]
        simp


theorem klDiv_eq_ent_rn {P Q : Measure (Torus d)} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P ≪ Q) :
    klDiv P Q = ent Q (fun x => (P.rnDeriv Q x).toReal) := by
  rw [klDiv_eq_lintegral_klFun_of_ac hac, ent_normalized Q Measure.integrable_toReal_rnDeriv
    (by rw [Measure.integral_toReal_rnDeriv hac]; simp)]

theorem rLS_mul_klDiv_le {ρ q : Torus d → ℝ} {c C : ℝ} (hρm : AEMeasurable ρ (haar d))
    (hρ0 : ∀ x, 0 ≤ ρ x) (hc : 0 < c) (hbd : ∀ x, c ≤ q x ∧ q x ≤ C)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) (hq1 : ∫ x, q x ∂haar d = 1) (hqm : Measurable q)
    (ha : MemH1 (haar d) fun x => Real.sqrt (ρ x))
    (hb' : MemH1 (haar d) fun x => Real.sqrt (q x)) :
    2 * (rLS (densMeasure q) * klDiv (densMeasure ρ) (densMeasure q)) ≤ relFisher ρ q := by
  by_cases hI : relFisher ρ q = ⊤
  · rw [hI]; exact le_top
  have hq0 : ∀ x, 0 < q x := fun x => hc.trans_le (hbd x).1
  have hQ : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  have hν : IsProbabilityMeasure (densMeasure ρ) := isProbabilityMeasure_densMeasure' hρ0 hρ1
  have hQvol : haar d ≪ densMeasure q := withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_of_integral_eq_one' hq1).aestronglyMeasurable.aemeasurable)
    (Filter.Eventually.of_forall fun x => by simpa using hq0 x)
  have hac : densMeasure ρ ≪ densMeasure q :=
    (withDensity_absolutelyContinuous _ _).trans hQvol
  have hfi := relFisher_eq_fisherInfo_aux hρ0 hρ1 ⟨c, C, hc, hbd⟩ hq1 ha hb'
  rw [hfi] at hI
  -- unfold `fisherInfo`
  have hcond : densMeasure ρ ≪ densMeasure q ∧ MemH1 (densMeasure q)
      (fun x => Real.sqrt ((densMeasure ρ).rnDeriv (densMeasure q) x).toReal) := by
    by_contra hn
    apply hI
    unfold fisherInfo
    rw [if_neg hn]
  have hfv : relFisher ρ q = 4 * dirichlet (densMeasure q)
      (fun x => Real.sqrt ((densMeasure ρ).rnDeriv (densMeasure q) x).toReal) := by
    rw [hfi]; unfold fisherInfo; rw [if_pos hcond]
  rw [hfv, klDiv_eq_ent_rn hac]
  set f0 : Torus d → ℝ := fun x => Real.sqrt ((densMeasure ρ).rnDeriv (densMeasure q) x).toReal
    with hf0
  have hsq : (fun x => f0 x ^ 2) = fun x => ((densMeasure ρ).rnDeriv (densMeasure q) x).toReal := by
    funext x; simp only [hf0]; rw [Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [← hsq]
  by_cases hE : 0 < ent (densMeasure q) (fun x => f0 x ^ 2)
  · have h1 : rLS (densMeasure q) ≤ 2 * dirichlet (densMeasure q) f0 /
        ent (densMeasure q) (fun x => f0 x ^ 2) := by
      unfold rLS
      exact iInf₂_le f0 ⟨hcond.2, hE⟩
    have hEt : ent (densMeasure q) (fun x => f0 x ^ 2) ≠ ⊤ := by
      have hl := reference_lsi hc hbd hq1 hqm hcond.2
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (dirichlet_lt_top hcond.2).ne) hl
    rw [ENNReal.le_div_iff_mul_le (Or.inl hE.ne') (Or.inl hEt)] at h1
    calc 2 * (rLS (densMeasure q) * ent (densMeasure q) fun x => f0 x ^ 2)
        ≤ 2 * (2 * dirichlet (densMeasure q) f0) := by gcongr
      _ = 4 * dirichlet (densMeasure q) f0 := by rw [← mul_assoc]; norm_num
  · have : ent (densMeasure q) (fun x => f0 x ^ 2) = 0 := by
      simpa using hE
    rw [this]; simp

end SharpLSI.FL
