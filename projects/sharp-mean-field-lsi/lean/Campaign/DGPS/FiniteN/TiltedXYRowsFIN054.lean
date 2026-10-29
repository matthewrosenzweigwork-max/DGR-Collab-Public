import DGPS.FiniteN.TiltedXYPosteriorFIN050
import DGPS.FiniteN.TiltedXYAllTestFIN052
import DGPS.FiniteN.TiltedXYProductFIN053
import DGPS.FiniteN.TiltedXY
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.Examples.AttractiveXYTiltRemoteEX025

/-!
# FIN054: tilted row separated rate powers

At the fixed tilted XY model `tiltedXYData (1/2) 4` (`κ = 4`, `h = 1/2`):

* the unrestricted particle Poincare rate `λ_N` satisfies `Θ_0` (FIN050 lower bound, FIN051 upper
  bound);
* the all-test rate `r_N^all` and the symmetric rate `r_N^sym` satisfy `Θ_1`: the lower bound
  `c/N` for `r_N^all` comes from FIN052, the upper bound `8 a0 / N` for `r_N^sym` from FIN053 at a
  root `s ∈ (1,4)` of `4 g(s) - s = 1/2` (existence from EX025), and `r_N^all ≤ r_N^sym` transfers
  both bounds to the other rate.

Finiteness of the three rates for every `N ≥ 1` is taken from FIN001
(`finite_positive_particle_rate_and_real_bridge`), which is what converts the `ENNReal` bounds to
real bounds on `toReal`.

The sequences are indexed by `n : ℕ` through `Nat.toPNat' n`, which equals `n` for `n ≥ 1`; the
`Θ_p` predicate is the project's `ThetaScale`, with the eventual threshold `N₀ = 1`.
-/

open DGPS

namespace DGPS.FiniteN

/-- Transfers `ℕ+`-indexed two-sided power bounds to the `ℕ`-indexed `ThetaScale` form
`n ↦ g (Nat.toPNat' n)`, which agrees with `g` on `n ≥ 1`. -/
theorem thetaScale_of_pnat_FIN054 (p c C : ℝ) (g : ℕ+ → ℝ) (hc : 0 < c) (hC : 0 < C)
    (h : ∀ N : ℕ+, c * (N : ℝ) ^ (-p) ≤ g N ∧ g N ≤ C * (N : ℝ) ^ (-p)) :
    ThetaScale p (fun n : ℕ => g (Nat.toPNat' n)) := by
  refine ⟨c, C, hc, hC, 1, le_rfl, fun n hn => ?_⟩
  have hn0 : 0 < n := hn
  have hcoe : ((Nat.toPNat' n : ℕ+) : ℕ) = n := by
    rw [Nat.toPNat'_coe]
    simp [hn0]
  have key := h (Nat.toPNat' n)
  rw [hcoe] at key
  exact key

/-- **FIN054.** For the fixed tilted XY model `tiltedXYData (1/2) 4` (FIN050, FIN051, FIN052,
FIN053, FIN001): `λ_N` satisfies `Θ_0` and `r_N^all`, `r_N^sym` satisfy `Θ_1`, as eventual
two-sided bounds `c N^(-p) ≤ a_N ≤ C N^(-p)` on the real parts (`toReal`) of the rates.
No finite-`N` equality or optimal prefactor is claimed. -/
theorem tilted_row_separated_rate_powers :
    ThetaScale 0 (fun n : ℕ =>
      (particlePoincareRate (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) (Nat.toPNat' n)).toReal) ∧
    ThetaScale 1 (fun n : ℕ =>
      (particleRateAll (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) (Nat.toPNat' n)).toReal) ∧
    ThetaScale 1 (fun n : ℕ =>
      (particleRateSym (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) (Nat.toPNat' n)).toReal) := by
  -- Finiteness of the three rates for every N ≥ 1 (FIN001).
  have hfin : ∀ N : ℕ+,
      particleRateAll (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N ≠ ⊤ ∧
      particleRateSym (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N ≠ ⊤ ∧
      particlePoincareRate (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N ≠ ⊤ := by
    intro N
    obtain ⟨_, _, ⟨_, aT⟩, ⟨_, sT⟩, ⟨_, pT⟩, _⟩ :=
      finite_positive_particle_rate_and_real_bridge (TiltedXY.Fin051.tiltedXYData (1 / 2) 4)
        (by norm_num : 0 < 1) N
    exact ⟨aT.ne, sT.ne, pT.ne⟩
  -- Poincare lower bound (FIN050) and the all-test lower bound (FIN052).
  obtain ⟨lam0, hlam, hpoinLow⟩ :=
    (posterior_averaged_conditional_constants_and_uniform_pi).2
  obtain ⟨c1, hc1, hallLow⟩ := tilted_all_test_inverse_n_lsi_lower.1
  -- Symmetric upper bound (FIN053) at a root s ∈ (1,4) of 4 g(s) - s = 1/2 (EX025).
  obtain ⟨_, s₂, _, _, hs2a, hs2b, _, hroot⟩ :=
    DGPS.Examples.AttractiveXYTiltRemoteEX025.remote_roots_exist_EX025
  have hS : ∀ N : ℕ+, particleRateSym (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N ≤
      ENNReal.ofReal (8 * (4 * Real.pi ^ 2) * (1 / (N : ℝ))) := by
    intro N
    obtain ⟨_, _, _, _, hR, hT⟩ :=
      (tilted_exact_stationary_product_upper_test N hs2a hs2b hroot).2.2.2
    rw [mul_one_div]
    exact hR.trans hT
  -- Poincare two-sided bound (FIN050 lower, FIN051 upper), for every N ≥ 1.
  have hP : ∀ N : ℕ+,
      lam0 ≤ (particlePoincareRate (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal ∧
      (particlePoincareRate (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal ≤
        2 * DGPS.Circle.AngularNormalization.a0 * Real.exp (2 * ((1 / 2 : ℝ) + 4)) := by
    intro N
    refine ⟨?_, ?_⟩
    · exact (ENNReal.ofReal_le_iff_le_toReal (hfin N).2.2).1 (hpoinLow N)
    · exact ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (mul_nonneg zero_le_two DGPS.Circle.AngularNormalization.a0_pos.le)
          (Real.exp_pos _).le)
        (tilted_tagged_upper_poincare_bound N)
  -- Rate powers: (N : ℝ) ^ (-1) = 1 / N.
  have hrp : ∀ N : ℕ+, (N : ℝ) ^ (-(1 : ℝ)) = 1 / (N : ℝ) := fun N => by
    rw [Real.rpow_neg_one, one_div]
  -- All-test two-sided bound (FIN052 lower; upper through r^all ≤ r^sym and FIN053).
  have hAll : ∀ N : ℕ+,
      c1 * (N : ℝ) ^ (-(1 : ℝ)) ≤ (particleRateAll (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal ∧
      (particleRateAll (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal ≤
        8 * (4 * Real.pi ^ 2) * (N : ℝ) ^ (-(1 : ℝ)) := by
    intro N
    rw [hrp N, mul_one_div]
    refine ⟨?_, ?_⟩
    · exact (ENNReal.ofReal_le_iff_le_toReal (hfin N).1).1 (hallLow N)
    · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        ((particleRateAll_le_sym _ N).trans (hS N))
  -- Symmetric two-sided bound (lower through r^all ≤ r^sym; upper FIN053).
  have hSym : ∀ N : ℕ+,
      c1 * (N : ℝ) ^ (-(1 : ℝ)) ≤ (particleRateSym (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal ∧
      (particleRateSym (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal ≤
        8 * (4 * Real.pi ^ 2) * (N : ℝ) ^ (-(1 : ℝ)) := by
    intro N
    rw [hrp N, mul_one_div]
    refine ⟨?_, ?_⟩
    · exact (ENNReal.ofReal_le_iff_le_toReal (hfin N).1).1 (hallLow N) |>.trans
        (ENNReal.toReal_mono (hfin N).2.1 (particleRateAll_le_sym _ N))
    · exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hS N)
  have hC0 : 0 < 2 * DGPS.Circle.AngularNormalization.a0 * Real.exp (2 * ((1 / 2 : ℝ) + 4)) :=
    mul_pos (mul_pos two_pos DGPS.Circle.AngularNormalization.a0_pos) (Real.exp_pos _)
  have hC8 : (0 : ℝ) < 8 * (4 * Real.pi ^ 2) := by positivity
  refine ⟨thetaScale_of_pnat_FIN054 0 lam0 _ (fun N =>
      (particlePoincareRate (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal) hlam hC0
      (fun N => by
        simp only [neg_zero, Real.rpow_zero, mul_one]
        exact hP N),
    thetaScale_of_pnat_FIN054 1 c1 _ (fun N =>
      (particleRateAll (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal) hc1 hC8 hAll,
    thetaScale_of_pnat_FIN054 1 c1 _ (fun N =>
      (particleRateSym (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N).toReal) hc1 hC8 hSym⟩

end DGPS.FiniteN
