import FullLabeledLSI.Examples.E01g1_Basic

/-!
# Lane D, Task C (E01g6): zero gap forces the uniform density; quotient bookkeeping
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem freeEnergy_eq {C : Torus 1 → ℝ} (hC : GoodKernel C) {ρ : Torus 1 → ℝ}
    (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    freeEnergy zeroV (attrW C) (densMeasure ρ) =
      ((entR ρ + (C 0 - cqR C ρ) / 2 : ℝ) : EReal) := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have hCc := continuous_of_smooth hC.smooth
  have hGc : Continuous (fun x => -C x) := hCc.neg
  have hfin := (circle_quantitative_lsi_aux h0 h1 hH).1
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

theorem eq_one_of_GR_zero {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (huniq : HaarUniqueMinimizer (attrW C)) {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x)))
    (hG : GR C ρ = 0) : ρ =ᵐ[haar 1] fun _ => 1 := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have hmin := huniq.1
  have hF := Fstar_attr hC hmin
  have hmin' : IsMinimizer zeroV (attrW C) (⟨densMeasure ρ, inferInstance⟩ : ProbabilityMeasure (Torus 1)) := by
    unfold IsMinimizer
    rw [hF]
    show freeEnergy zeroV (attrW C) (densMeasure ρ) = _
    rw [freeEnergy_eq hC h0 h1 hH]
    congr 1
    unfold GR at hG
    linarith
  have := huniq.2 _ hmin'
  have hμ : densMeasure ρ = haar 1 := by
    have := congrArg (fun μ : ProbabilityMeasure (Torus 1) => (μ : Measure (Torus 1))) this
    simpa [haarPM] using this
  have hi := integrable_of_integral_eq_one' h1
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have hlin : ∫⁻ x, ENNReal.ofReal (ρ x) ∂haar 1 ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0)]
    exact ENNReal.ofReal_ne_top
  have hw : (haar 1 : Measure (Torus 1)).withDensity (fun x => ENNReal.ofReal (ρ x)) =
      (haar 1 : Measure (Torus 1)).withDensity (1 : Torus 1 → ℝ≥0∞) := by
    rw [withDensity_one]; exact hμ
  have h' := (withDensity_eq_iff hm (aemeasurable_const : AEMeasurable (1 : Torus 1 → ℝ≥0∞) (haar 1)) hlin).1 hw
  filter_upwards [h'] with x hx
  exact ENNReal.ofReal_eq_one.1 hx

/-- Real form of the scalar quotient of an admissible density. -/
theorem quot_real {C : Torus 1 → ℝ} (hC : GoodKernel C) (hmin : IsMinimizer zeroV (attrW C) haarPM)
    {ρ : Torus 1 → ℝ} (h : Admissible zeroV (attrW C) ρ) :
    dissipation zeroV (attrW C) ρ / (2 * (gap zeroV (attrW C) (densMeasure ρ)).toENNReal) =
      ENNReal.ofReal (DR C ρ / (2 * GR C ρ)) := by
  obtain ⟨h0, h1, hH, hg⟩ := (admissible_iff hC hmin).1 h
  rw [diss_eq hC h0 h1 hH, gap_eq hC hmin h0 h1 hH, EReal.real_coe_toENNReal]
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num)]
  simp

theorem DR_nonneg (C ρ : Torus 1 → ℝ) : 0 ≤ DR C ρ :=
  integral_nonneg fun x => sq_nonneg _

end SharpLSI.FL.Ex.LaneD
