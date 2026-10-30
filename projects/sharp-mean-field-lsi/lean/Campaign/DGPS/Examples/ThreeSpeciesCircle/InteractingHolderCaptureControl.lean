import DGPS.Frontier.STR029.T69

/-! Genuine control of the retained full C2 Holder norm by derivatives through
order three. This is a calculus support lemma; actual minimizer derivative
convergence must still be proved before applying it to branch capture. -/

noncomputable section
open Filter Topology
open DGPS.Frontier.STR029 DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The exact retained circular Holder seminorm is controlled, not replaced
by a C2 sup norm. Boundedness of the third derivative is explicit. -/
theorem c2Holder_norm_le_third_derivative (f : PeriodicC2_STR02969)
    (hd : Differentiable ℝ (deriv (deriv f.val)))
    (hb : Bdd (deriv (deriv (deriv f.val)))) :
    ‖f‖ ≤ supNorm f.val + supNorm (deriv f.val) + supNorm (deriv (deriv f.val)) +
      Real.pi ^ (1 / 2 : ℝ) * supNorm (deriv (deriv (deriv f.val))) := by
  have hp := periodic_deriv_STR02901 (periodic_deriv_STR02901 f.isC2.1)
  have hc := (c0_of_deriv_STR02953 (α := (1 / 2 : ℝ)) half_pos_STR02968
    (by norm_num) hp hd hb).2
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at hc
  rw [PeriodicC2_STR02969.norm_def]
  unfold c2Norm_STR02901 c0Norm_STR02953 at *
  linarith

/-- Uniform convergence through third derivatives gives convergence in the
full retained Holder norm, with every sup norm used on a bounded function. -/
theorem c2Holder_norm_tendsto_zero_of_third_derivatives
    (f : ℕ → PeriodicC2_STR02969)
    (hd : ∀ n, Differentiable ℝ (deriv (deriv (f n).val)))
    (hb : ∀ n, Bdd (deriv (deriv (deriv (f n).val))))
    (h0 : Tendsto (fun n => supNorm (f n).val) atTop (𝓝 0))
    (h1 : Tendsto (fun n => supNorm (deriv (f n).val)) atTop (𝓝 0))
    (h2 : Tendsto (fun n => supNorm (deriv (deriv (f n).val))) atTop (𝓝 0))
    (h3 : Tendsto (fun n => supNorm (deriv (deriv (deriv (f n).val)))) atTop (𝓝 0)) :
    Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => supNorm (f n).val + supNorm (deriv (f n).val) +
      supNorm (deriv (deriv (f n).val)) + Real.pi ^ (1 / 2 : ℝ) *
        supNorm (deriv (deriv (deriv (f n).val)))) atTop (𝓝 0) := by
    simpa using ((h0.add h1).add h2).add (h3.const_mul (Real.pi ^ (1 / 2 : ℝ)))
  exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
    c2Holder_norm_le_third_derivative (f n) (hd n) (hb n)) ht

end DGPS.Examples.ThreeSpeciesCircle
