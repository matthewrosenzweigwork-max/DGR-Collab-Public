import FullLabeledLSI.Examples.E01h6_Core

/-!
# Lane D, Task D (E01h6): Haar measure is the unique minimizer for a small mean-zero kernel
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem exists_density (μ : ProbabilityMeasure (Torus 1)) (hfin : klDiv (μ : Measure (Torus 1)) (haar 1) ≠ ⊤) :
    ∃ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧ (μ : Measure (Torus 1)) = densMeasure ρ := by
  have hac : (μ : Measure (Torus 1)) ≪ haar 1 := (klDiv_ne_top_iff.1 hfin).1
  refine ⟨fun x => ((μ : Measure (Torus 1)).rnDeriv (haar 1) x).toReal, fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [Measure.integral_toReal_rnDeriv hac]; simp
  · unfold densMeasure
    have hae : (fun x => ENNReal.ofReal (((μ : Measure (Torus 1)).rnDeriv (haar 1) x).toReal)) =ᵐ[haar 1]
        (μ : Measure (Torus 1)).rnDeriv (haar 1) := by
      filter_upwards [Measure.rnDeriv_lt_top (μ : Measure (Torus 1)) (haar 1)] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae hae]
    exact ((Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq).1 hac).symm

/-- Free energy of a probability measure with finite entropy. -/
theorem freeEnergy_eq_dens {C : Torus 1 → ℝ} (hC : GoodKernel C) {ρ : Torus 1 → ℝ}
    (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hfin : klDiv (densMeasure ρ) (haar 1) ≠ ⊤) :
    freeEnergy zeroV (attrW C) (densMeasure ρ) = ((entR ρ + (C 0 - cqR C ρ) / 2 : ℝ) : EReal) := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have hCc := continuous_of_smooth hC.smooth
  have hGc : Continuous (fun x => -C x) := hCc.neg
  have e : (zeroV : Torus 1 → ℝ) = fun _ => (0 : ℝ) := rfl
  rw [attrW_eq, e, Sec8.freeEnergy_WG hGc (densMeasure ρ)]
  have hQ : Sec8.Qint (densMeasure ρ) (fun x => -C x) = - cqR C ρ := by
    rw [← Qint_eq_cqR hCc h0 h1]
    unfold Sec8.Qint
    simp [integral_neg]
  rw [hQ]
  have hkl : ((klDiv (densMeasure ρ) (haar 1) : ℝ≥0∞) : EReal) = ((entR ρ : ℝ) : EReal) := by
    unfold entR
    rw [← EReal.coe_ennreal_toReal hfin]
  rw [hkl, ← EReal.coe_add]
  congr 1
  ring

theorem freeEnergy_haar {C : Torus 1 → ℝ} (hC : GoodKernel C) :
    freeEnergy zeroV (attrW C) haarPM = ((C 0 / 2 : ℝ) : EReal) := by
  have hGc : Continuous (fun x => -C x) := (continuous_of_smooth hC.smooth).neg
  have e : (zeroV : Torus 1 → ℝ) = fun _ => (0 : ℝ) := rfl
  rw [attrW_eq, e]
  show freeEnergy (fun _ => (0 : ℝ)) (Sec8.WG fun x => -C x) (haar 1) = _
  rw [Sec8.freeEnergy_WG_haar hGc]
  congr 1
  have : Sec8.meanT (fun x : Torus 1 => -C x) = 0 := by
    unfold Sec8.meanT; rw [integral_neg, hC.meanZero]; simp
  rw [this]; ring

/-- Haar measure is the unique minimizer when `|C| ≤ M < 1`. -/
theorem haarUnique_of_bound {C : Torus 1 → ℝ} (hC : GoodKernel C) {M : ℝ} (hM : ∀ x, |C x| ≤ M)
    (hM1 : M < 1) : HaarUniqueMinimizer (attrW C) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- lower bound and equality case for every probability measure
  have key : ∀ μ : ProbabilityMeasure (Torus 1),
      ((C 0 / 2 : ℝ) : EReal) ≤ freeEnergy zeroV (attrW C) μ ∧
        (freeEnergy zeroV (attrW C) μ = ((C 0 / 2 : ℝ) : EReal) → (μ : Measure (Torus 1)) = haar 1) := by
    intro μ
    by_cases hfin : klDiv (μ : Measure (Torus 1)) (haar 1) = ⊤
    · have hcont : Continuous (fun x => -C x) := (continuous_of_smooth hC.smooth).neg
      have e : (zeroV : Torus 1 → ℝ) = fun _ => (0 : ℝ) := rfl
      have hF : freeEnergy zeroV (attrW C) μ = ⊤ := by
        unfold freeEnergy
        rw [hfin]
        simp
      rw [hF]
      exact ⟨le_top, fun h => absurd h (by simp)⟩
    · obtain ⟨ρ, h0, h1, hμ⟩ := exists_density μ hfin
      have hfin' : klDiv (densMeasure ρ) (haar 1) ≠ ⊤ := by rw [← hμ]; exact hfin
      have hF : freeEnergy zeroV (attrW C) μ = ((entR ρ + (C 0 - cqR C ρ) / 2 : ℝ) : EReal) := by
        show freeEnergy zeroV (attrW C) (μ : Measure (Torus 1)) = _
        rw [hμ]; exact freeEnergy_eq_dens hC h0 h1 hfin'
      have hq := cqR_le_ent hC hM h0 h1 hfin'
      have hent0 : 0 ≤ entR ρ := ENNReal.toReal_nonneg
      rw [hF]
      refine ⟨EReal.coe_le_coe_iff.2 (by nlinarith), fun h => ?_⟩
      have h' := EReal.coe_eq_coe_iff.1 h
      have hz : entR ρ = 0 := by nlinarith
      have hkl : klDiv (densMeasure ρ) (haar 1) = 0 := by
        unfold entR at hz
        rcases (ENNReal.toReal_eq_zero_iff _).1 hz with h | h
        · exact h
        · exact absurd h hfin'
      haveI := isProbabilityMeasure_densMeasure' h0 h1
      rw [hμ]
      exact (klDiv_eq_zero_iff).1 hkl
  have hFstar : Fstar zeroV (attrW C) = ((C 0 / 2 : ℝ) : EReal) := by
    apply le_antisymm
    · exact (iInf_le (fun μ : ProbabilityMeasure (Torus 1) => freeEnergy zeroV (attrW C) μ) haarPM).trans
        (freeEnergy_haar hC).le
    · exact le_iInf fun μ => (key μ).1
  refine ⟨?_, fun μ hμ => ?_⟩
  · unfold IsMinimizer; rw [hFstar]; exact freeEnergy_haar hC
  · unfold IsMinimizer at hμ
    rw [hFstar] at hμ
    exact Subtype.ext ((key μ).2 hμ)

end SharpLSI.FL.Ex.LaneD
