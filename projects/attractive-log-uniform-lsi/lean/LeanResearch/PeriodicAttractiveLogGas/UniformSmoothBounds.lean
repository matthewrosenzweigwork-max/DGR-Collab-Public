import LeanResearch.PeriodicAttractiveLogGas.FixedParticleBounds
import LeanResearch.PeriodicAttractiveLogGas.PhysicalEntropyTightening

/-! The manuscript's final finite/large-particle assembly, before Rothaus.
The maxima are taken over the fixed-particle constants and the independently
proved large-particle PI and defective entropy constants. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
namespace PeriodicAttractiveLogGas.UniformSmoothBounds

lemma smooth_energy {N : ℕ} (β : ℝ) (s : SmoothPair N) :
    ResolutionEnergy.energy β s.value =
      ∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  unfold ResolutionEnergy.energy
  simp_rw [PhysicalEntropyTightening.smooth_descended_gradient]

/-- The source two global inputs, with constants chosen before N, beta,
and the smooth observable. Neither inequality is assumed or deduced from
an already asserted global LSI. -/
theorem exists_uniform_smooth_bounds {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) :
    ∃ Cpi A B : ℝ, 0 ≤ Cpi ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ s : SmoothPair N,
        variance s.value (gibbsMeasure greenRealRepresentative N β) ≤
            Cpi * ∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β ∧
          entropy (gibbsMeasure greenRealRepresentative N β) (fun X => s.value X ^ 2) ≤
            ((A * (∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β) +
              B * (∫ X, s.value X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) : ℝ) : EReal) := by
  classical
  obtain ⟨CpL, AL, BL, hCpL, hAL, hBL, N₀, hN₀, hlarge⟩ :=
    LargeParticleBounds.exists_large_particle_bounds hβ₀ hsub
  let : Nonempty (Fin N₀) := ⟨⟨0, by omega⟩⟩
  have hsmall (n : Fin N₀) : ∃ Cpi A B : ℝ, 0 ≤ Cpi ∧ 0 ≤ A ∧ 0 ≤ B ∧
      (2 ≤ (n : ℕ) → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ s : SmoothPair n,
        variance s.value (gibbsMeasure greenRealRepresentative n β) ≤
            Cpi * ∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative n β ∧
          entropy (gibbsMeasure greenRealRepresentative n β) (fun X => s.value X ^ 2) ≤
            ((A * (∫ X, ‖s.gradient X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative n β) +
              B * (∫ X, s.value X ^ 2 ∂gibbsMeasure greenRealRepresentative n β) : ℝ) : EReal)) := by
    by_cases hn : 2 ≤ (n : ℕ)
    · obtain ⟨Cpi, A, B, hC, hA, hB, hb⟩ := FixedParticleBounds.exists_fixed_particle_bounds n hn hβ₀ hsub
      exact ⟨Cpi, A, B, hC, hA, hB, fun _ => hb⟩
    · exact ⟨0, 0, 0, le_rfl, le_rfl, le_rfl, fun h => (hn h).elim⟩
  choose CpS AS BS hCpS hAS hBS hsmall using hsmall
  let Cpi := max CpL (Finset.univ.sup' Finset.univ_nonempty CpS)
  let A := max AL (Finset.univ.sup' Finset.univ_nonempty AS)
  let B := max BL (Finset.univ.sup' Finset.univ_nonempty BS)
  have hCL : CpL ≤ Cpi := le_max_left _ _
  have hAL' : AL ≤ A := le_max_left _ _
  have hBL' : BL ≤ B := le_max_left _ _
  have hCS (n : Fin N₀) : CpS n ≤ Cpi :=
    (Finset.le_sup' CpS (Finset.mem_univ n)).trans (le_max_right _ _)
  have hAS' (n : Fin N₀) : AS n ≤ A :=
    (Finset.le_sup' AS (Finset.mem_univ n)).trans (le_max_right _ _)
  have hBS' (n : Fin N₀) : BS n ≤ B :=
    (Finset.le_sup' BS (Finset.mem_univ n)).trans (le_max_right _ _)
  refine ⟨Cpi, A, B, hCpL.trans hCL, hAL.trans hAL', hBL.trans hBL', ?_⟩
  intro N hN β hβ hle s
  let μ := gibbsMeasure greenRealRepresentative N β
  let E := ∫ X, ‖s.gradient X‖ ^ 2 ∂μ
  let m := ∫ X, s.value X ^ 2 ∂μ
  have hE : 0 ≤ E := integral_nonneg fun X => sq_nonneg ‖s.gradient X‖
  have hm : 0 ≤ m := integral_nonneg fun X => sq_nonneg (s.value X)
  have hbase : ∃ cp a b : ℝ, cp ≤ Cpi ∧ a ≤ A ∧ b ≤ B ∧
      variance s.value μ ≤ cp * E ∧
      entropy μ (fun X => s.value X ^ 2) ≤ ((a * E + b * m : ℝ) : EReal) := by
    by_cases hNL : N₀ ≤ N
    · have hh := hlarge N hNL β hβ hle s.value ‖s.gradient‖₊ s.lipschitz_configurationLift
      rw [smooth_energy] at hh
      exact ⟨CpL, AL, BL, hCL, hAL', hBL', hh⟩
    · let n : Fin N₀ := ⟨N, lt_of_not_ge hNL⟩
      exact ⟨CpS n, AS n, BS n, hCS n, hAS' n, hBS' n, hsmall n hN β hβ hle s⟩
  obtain ⟨cp, a, b, hc, ha, hb, hpi, hd⟩ := hbase
  refine ⟨hpi.trans (mul_le_mul_of_nonneg_right hc hE), ?_⟩
  exact hd.trans (EReal.coe_le_coe_iff.mpr (add_le_add
    (mul_le_mul_of_nonneg_right ha hE) (mul_le_mul_of_nonneg_right hb hm)))

end PeriodicAttractiveLogGas.UniformSmoothBounds
