import FullLabeledLSI.Paper.Sec3RecSmooth
import FullLabeledLSI.Paper.Sec3RecoveryReg
import FullLabeledLSI.Paper.Sec3Dilute
import FullLabeledLSI.Infra.Diag
import FullLabeledLSI.Defs.F07_Sanity

/-!
# Proposition 3.2: regularization, the diagonal argument, and the last assertion
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem product_recovery_aux (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible) :
    ∃ dens : (N : ℕ) → Fin N → Torus d → ℝ,
      (∀ N i, Measurable (dens N i) ∧ (∀ x, 0 ≤ dens N i x) ∧ ∫ x, dens N i x ∂haar d = 1) ∧
      Tendsto (fun N : ℕ => klDiv (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msGap V W F).toENNReal) ∧
      Tendsto (fun N : ℕ =>
          fisherInfoC (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msDiss V W F)) := by
  obtain ⟨Fs, hFs, hG, hD⟩ := family_regularization hyp F hF
  have hsm : ∀ n, ∃ dens : (N : ℕ) → Fin N → Torus d → ℝ,
      (∀ N i, Measurable (dens N i) ∧ (∀ x, 0 ≤ dens N i x) ∧ ∫ x, dens N i x ∂haar d = 1) ∧
      Tendsto (fun N : ℕ => klDiv (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msGap V W (Fs n)).toENNReal) ∧
      Tendsto (fun N : ℕ =>
          fisherInfoC (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)
        atTop (𝓝 (msDiss V W (Fs n))) := fun n =>
    product_recovery_smooth hyp (Fs n) (hFs n).1 (hFs n).2.1 (hFs n).2.2
  choose dens hdens hKL hFI using hsm
  obtain ⟨φ, hφ⟩ := exists_diag_tendsto
    (fun n N => (klDiv (Measure.pi fun i => densMeasure (dens n N i)) (gibbs V W N) / N,
      fisherInfoC (Measure.pi fun i => densMeasure (dens n N i)) (gibbs V W N) / N))
    (fun n => ((msGap V W (Fs n)).toENNReal, msDiss V W (Fs n)))
    ((msGap V W F).toENNReal, msDiss V W F)
    (fun n => (hKL n).prodMk_nhds (hFI n)) (hG.prodMk_nhds hD)
  exact ⟨fun N i => dens (φ N) N i, fun N i => hdens (φ N) N i,
    (Filter.Tendsto.fst_nhds hφ), (Filter.Tendsto.snd_nhds hφ)⟩


/-- Proposition 3.2, last assertion: every uniform defective rate is at most `r_ms`. -/
theorem le_rMs_of_uniform_defective_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (r : ℝ) (C : ℝ)
    (h : ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      ENNReal.ofReal (2 * r) * klDiv ν (gibbs V W N) ≤
        fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C) :
    ENNReal.ofReal r ≤ rMs V W := by
  refine le_iInf₂ fun F hF => ?_
  obtain ⟨hAd, hpos⟩ := hF
  obtain ⟨hGt, -, hDt⟩ := msGap_msDiss_lt_top hd hyp hAd
  obtain ⟨dens, hdens, hKL, hFI⟩ := product_recovery_aux hyp F hAd
  set G := (msGap V W F).toENNReal with hG
  set D := msDiss V W F with hD
  have hG0 : G ≠ 0 := (EReal.toENNReal_pos_iff.2 hpos).ne'
  have hGt' : G ≠ ⊤ := by
    rw [hG]; intro hc
    have := EReal.toENNReal_eq_top_iff.1 hc
    exact absurd this hGt.ne
  have hprob : ∀ N, IsProbabilityMeasure (Measure.pi fun i : Fin N => densMeasure (dens N i)) := by
    intro N
    haveI : ∀ i, IsProbabilityMeasure (densMeasure (dens N i)) := fun i =>
      isProbabilityMeasure_densMeasure' (hdens N i).2.1 (hdens N i).2.2
    infer_instance
  have hlim1 : Tendsto (fun N : ℕ => ENNReal.ofReal (2 * r) *
      (klDiv (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N)) atTop
      (𝓝 (ENNReal.ofReal (2 * r) * G)) :=
    ENNReal.Tendsto.const_mul hKL (Or.inr ENNReal.ofReal_ne_top)
  have hlim2 : Tendsto (fun N : ℕ =>
      fisherInfoC (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) / N +
        ENNReal.ofReal C * (N : ℝ≥0∞)⁻¹) atTop (𝓝 (D + ENNReal.ofReal C * 0)) := by
    refine hFI.add (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero ?_)
    exact Or.inr ENNReal.ofReal_ne_top
  rw [mul_zero, add_zero] at hlim2
  have hle : ENNReal.ofReal (2 * r) * G ≤ D := by
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have := h N hN _ (hprob N)
    simp only [div_eq_mul_inv]
    calc ENNReal.ofReal (2 * r) * (klDiv (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N)
          * (N : ℝ≥0∞)⁻¹)
        = (ENNReal.ofReal (2 * r) * klDiv (Measure.pi fun i => densMeasure (dens N i))
            (gibbs V W N)) * (N : ℝ≥0∞)⁻¹ := by rw [mul_assoc]
      _ ≤ (fisherInfoC (Measure.pi fun i => densMeasure (dens N i)) (gibbs V W N) +
            ENNReal.ofReal C) * (N : ℝ≥0∞)⁻¹ := by gcongr
      _ = _ := by rw [add_mul]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hG0)) (Or.inl (ENNReal.mul_ne_top (by simp) hGt'))]
  calc ENNReal.ofReal r * (2 * G) = ENNReal.ofReal (2 * r) * G := by
        rw [ENNReal.ofReal_mul (by norm_num), mul_comm (ENNReal.ofReal 2), mul_assoc]; simp
    _ ≤ D := hle

end SharpLSI.FL
