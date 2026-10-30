import DGPS.FiniteN.AnisotropicQuarticPosteriorBox

/-! Actual posterior transfer of an auxiliary rare-strip upper bound to the empirical
support event. The positive noise event is imposed conditionally, with no subtraction
of an unconditional tail. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
open scoped ENNReal

namespace DGPS.FiniteN

def quarticFieldBox (δ s : ℝ) : Set (Fin 2 → ℝ) :=
  {w | |w 0 + 4| ≤ δ ∧ |w 1| ≤ s}

theorem quarticFieldBox_measurable (δ s : ℝ) : MeasurableSet (quarticFieldBox δ s) := by
  exact (isClosed_le (show Continuous (fun w : Fin 2 → ℝ => |w 0 + 4|) by fun_prop)
    (continuous_const (y := δ))).measurableSet.inter
    (isClosed_le (show Continuous (fun w : Fin 2 → ℝ => |w 1|) by fun_prop)
      (continuous_const (y := s))).measurableSet

/-- A uniform positive factor times the ACTUAL canonical empirical-box probability
is bounded above by the enlarged auxiliary-box probability. The field is precisely
the posterior center of the original zero-diagonal Hamiltonian. -/
theorem quartic_empirical_box_posterior_upper :
    ∃ L : ℝ, 0 < L ∧ ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧
      ∀ N : ℕ+, ∀ δ s rx ry : ℝ,
        (Real.sqrt (N : ℝ))⁻¹ * L ≤ rx →
        (Real.sqrt (N : ℝ))⁻¹ * L ≤ ry →
        p * particleLaw anisotropicQuarticSaddle N
          ((posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N) ⁻¹'
            quarticFieldBox δ s) ≤
          auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
            (DGPS.haar 1) N (quarticFieldBox (δ + rx) (s + ry)) := by
  obtain ⟨L, hL, p, hp, hp1, hbox⟩ := quartic_posterior_box_probability
  refine ⟨L, hL, p, hp, hp1, fun N δ s rx ry hx hy => ?_⟩
  let Z := posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N
  let S := Z ⁻¹' quarticFieldBox δ s
  let A := quarticFieldBox (δ + rx) (s + ry)
  have hSm : MeasurableSet S := (quarticFieldBox_measurable δ s).preimage
    (measurable_posteriorCenter quartic_hubbard_hyp quarticHubbardD quarticHubbardField N)
  have hAm : MeasurableSet A := quarticFieldBox_measurable _ _
  have haux : auxLaw quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
      (DGPS.haar 1) N A =
      ∫⁻ x, gaussLaw quarticHubbardD N (Z x) A ∂particleLaw anisotropicQuarticSaddle N := by
    rw [← hubbardJoint_map_fst quartic_hubbard_hyp quartic_hubbard_D_posDef quarticHubbardField N,
      Measure.map_apply measurable_fst hAm,
      hubbardJoint_eq_gauss quartic_hubbard_hyp quartic_hubbard_D_posDef quarticHubbardField N
        (hAm.preimage measurable_fst), quartic_hubbard_particle_law]
    rfl
  have hpoint : ∀ x, S.indicator (fun _ => p) x ≤ gaussLaw quarticHubbardD N (Z x) A := by
    intro x
    by_cases hxs : x ∈ S
    · rw [Set.indicator_of_mem hxs]
      refine (hbox N (Z x) rx ry hx hy).trans (measure_mono ?_)
      intro w hw
      have hzx : |Z x 0 + 4| ≤ δ := hxs.1
      have hzy : |Z x 1| ≤ s := hxs.2
      change |w 0 + 4| ≤ δ + rx ∧ |w 1| ≤ s + ry
      constructor
      · have ht := abs_add_le (w 0 - Z x 0) (Z x 0 + 4)
        rw [show (w 0 - Z x 0) + (Z x 0 + 4) = w 0 + 4 by ring] at ht
        exact ht.trans (by linarith [hw.1])
      · have ht := abs_add_le (w 1 - Z x 1) (Z x 1)
        rw [sub_add_cancel] at ht
        exact ht.trans (by linarith [hw.2])
    · rw [Set.indicator_of_notMem hxs]
      exact bot_le
  change p * particleLaw anisotropicQuarticSaddle N S ≤ _
  rw [haux]
  calc
    _ = ∫⁻ x, S.indicator (fun _ => p) x ∂particleLaw anisotropicQuarticSaddle N := by
      rw [lintegral_indicator hSm, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter]
    _ ≤ _ := lintegral_mono hpoint

end DGPS.FiniteN
