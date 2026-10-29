import FullLabeledLSI.Nonvacuity.Prop82.DBridge
import FullLabeledLSI.Nonvacuity.Prop82.DBessel
import FullLabeledLSI.Nonvacuity.Prop82.DGibbs
import FullLabeledLSI.Nonvacuity.Prop82.DConvex
import FullLabeledLSI.Nonvacuity.Prop82.DHalfLSI

/-!
# Lane D: `HalfTurnEntropyEstimates`

Assembly of the half-turn estimates from the interval lemmas
(`halfperiod_lsi`, `fisher_half_average_le`, `klFun_le_half_average_add_log_two`,
`gibbs_interval`, `integral_exp_cos_le`) through the bridge `pf ρ = ρ ∘ lineT`.
-/

open MeasureTheory InformationTheory Filter Topology intervalIntegral
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

/-! ### Pure real-variable shift/doubling lemma -/

theorem integral_double_shift {G : Real → Real} (hc : Continuous G)
    (hper : ∀ t, G (t + 1) = G t) (c : Real) :
    ∫ t in (0 : Real)..1, G (2 * t + c) = ∫ t in (0 : Real)..1, G t := by
  have hP : Function.Periodic G 1 := hper
  rw [intervalIntegral.integral_comp_mul_add G (by norm_num : (2 : Real) ≠ 0) c]
  have h1 : ∫ x in (2 * 0 + c)..(2 * 1 + c), G x =
      (∫ x in c..(c + 1), G x) + ∫ x in (c + 1)..(c + 1 + 1), G x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    congr 1 <;> ring
  rw [h1, hP.intervalIntegral_add_eq c 0, hP.intervalIntegral_add_eq (c + 1) 0]
  simp only [zero_add]
  rw [smul_eq_mul]
  ring

/-! ### The half-turn average of a smooth probability density -/

theorem halfSymmetrize_probability {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    SmoothProbability (halfSymmetrize rho) := by
  refine ⟨halfSymmetrize_smooth h.smooth, ?_, ?_⟩
  · intro x
    unfold halfSymmetrize
    have := h.positive x
    have := h.positive (x + halfTurn)
    linarith
  · unfold halfSymmetrize
    have hi : Integrable rho (haar 1) := Sec8.integrable_of_smooth h.smooth
    have hi2 : Integrable (fun x => rho (x + halfTurn)) (haar 1) :=
      hi.comp_add_right halfTurn
    rw [MeasureTheory.integral_div, integral_add hi hi2]
    have := integral_add_right_eq_self (μ := haar 1) rho halfTurn
    rw [this, h.mass]
    norm_num

/-! ### Entropy and Fisher information as interval integrals -/

theorem entropy_eq_integral_D {tau : Torus 1 → Real} (h : SmoothProbability tau) :
    entropy tau = ∫ x, klFun (tau x) ∂haar 1 := by
  have hi : Integrable (fun x => klFun (tau x)) (haar 1) :=
    SharpLSI.integrable_bdd (continuous_klFun.comp (Sec8.continuous_of_smooth h.smooth))
  have hn := fun x => klFun_nonneg (h.nonneg x)
  unfold entropy
  rw [klDiv_densMeasure h.nonneg h.mass,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn)]

theorem entropy_eq_interval {tau : Torus 1 → Real} (h : SmoothProbability tau) :
    entropy tau = ∫ t in (0 : Real)..1, klFun (pf tau t) := by
  rw [entropy_eq_integral_D h]
  exact integral_torus_eq (continuous_klFun.comp (Sec8.continuous_of_smooth h.smooth))

theorem fisher_eq_interval {tau : Torus 1 → Real} (h : SmoothProbability tau) :
    fisher tau = ∫ t in (0 : Real)..1, deriv (pf tau) t ^ 2 / pf tau t := by
  rw [fisher_eq_dpart_integral h]
  have hc : Continuous (fun x => dpart tau 0 x ^ 2 / tau x) := by
    have hd : Continuous (dpart tau 0) :=
      Sec8.continuous_of_smooth (Sec8.isSmoothT_dpart h.smooth 0)
    exact (hd.pow 2).div (Sec8.continuous_of_smooth h.smooth) fun x => (h.positive x).ne'
  rw [integral_torus_eq hc]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [deriv_pf h.smooth, pf]

theorem integral_pf_eq_one {tau : Torus 1 → Real} (h : SmoothProbability tau) :
    ∫ t in (0 : Real)..1, pf tau t = 1 := by
  calc ∫ t in (0 : Real)..1, pf tau t = ∫ y, tau y ∂haar 1 :=
        (integral_torus_eq (Sec8.continuous_of_smooth h.smooth)).symm
    _ = 1 := h.mass

/-! ### The first three conjuncts -/

theorem halfTurn_finite {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    klDiv (densMeasure (halfSymmetrize rho)) (haar 1) ≠ ⊤ := by
  have hs := halfSymmetrize_probability h
  exact klDiv_densMeasure_ne_top_of_continuous (Sec8.continuous_of_smooth hs.smooth)
    hs.nonneg hs.mass

theorem halfTurn_fisher {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    8 * aCos * entropy (halfSymmetrize rho) ≤ fisher rho := by
  have hs := halfSymmetrize_probability h
  have hfun : pf (halfSymmetrize rho) = fun u => (pf rho u + pf rho (u + 1 / 2)) / 2 :=
    funext (pf_halfSymmetrize rho)
  have hper : ∀ t, pf (halfSymmetrize rho) (t + 1 / 2) = pf (halfSymmetrize rho) t := by
    intro t
    rw [hfun]
    simp only
    have e : t + 1 / 2 + 1 / 2 = t + 1 := by ring
    rw [e, pf_periodic rho t]
    ring
  have hlsi := halfperiod_lsi (pf_smooth hs.smooth) (pf_pos hs.positive) hper
    (integral_pf_eq_one hs)
  have hconv := fisher_half_average_le (pf_smooth h.smooth) (pf_pos h.positive)
    (pf_periodic rho)
  rw [entropy_eq_interval hs]
  rw [fisher_eq_interval h]
  refine hlsi.trans (le_trans ?_ hconv)
  rw [hfun]

theorem halfTurn_entropy {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    entropy rho ≤ entropy (halfSymmetrize rho) + Real.log 2 := by
  have hs := halfSymmetrize_probability h
  have hfun : pf (halfSymmetrize rho) = fun u => (pf rho u + pf rho (u + 1 / 2)) / 2 :=
    funext (pf_halfSymmetrize rho)
  rw [entropy_eq_interval hs, entropy_eq_interval h, hfun]
  exact klFun_le_half_average_add_log_two (pf_smooth h.smooth) (pf_pos h.positive)
    (pf_periodic rho) (integral_pf_eq_one h)

end SharpLSI.FL.Prop82
