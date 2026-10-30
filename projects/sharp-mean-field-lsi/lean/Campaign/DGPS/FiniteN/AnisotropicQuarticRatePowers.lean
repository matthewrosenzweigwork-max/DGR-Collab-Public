import DGPS.FiniteN.AnisotropicQuarticParticleUpper
import DGPS.FiniteN.AnisotropicQuarticParticleLower

/-! The actual quartic row: full production variational domains and fixed model
parameters, with finite positive rates at every positive particle number and
separate eventual Poincare and LSI powers. No rare-event or spectral estimate is
assumed by any public declaration in this module. -/

open DGPS.Models
open scoped ENNReal

namespace DGPS.FiniteN

/-- Real two-sided bounds on all three original rates, including the conversion
from ENNReal using their genuine finite-N finiteness. -/
theorem quartic_particle_rates_two_sided :
    ∃ cp cl C : ℝ, 0 < cp ∧ 0 < cl ∧ 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ+, N0 ≤ (N : ℕ) →
        (cp * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (particlePoincareRate anisotropicQuarticSaddle N).toReal ∧
          (particlePoincareRate anisotropicQuarticSaddle N).toReal ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        (cl * (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (particleRateAll anisotropicQuarticSaddle N).toReal ∧
          (particleRateAll anisotropicQuarticSaddle N).toReal ≤ C * (N : ℝ) ^ (-(3 / 2 : ℝ))) ∧
        (cl * (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (particleRateSym anisotropicQuarticSaddle N).toReal ∧
          (particleRateSym anisotropicQuarticSaddle N).toReal ≤ C * (N : ℝ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨cp, hcp, hp⟩ := quartic_particle_poincare_lower
  obtain ⟨cl, hcl, hl⟩ := quartic_particle_lsi_lower
  obtain ⟨C, hC, N0, hu⟩ := quartic_particle_rates_upper
  refine ⟨cp, cl, C, hcp, hcl, hC, N0, fun N hN => ?_⟩
  obtain ⟨⟨_, hAt⟩, ⟨_, hSt⟩, ⟨_, hPt⟩⟩ :=
    rates_pos_lt_top anisotropicQuarticSaddle N (by norm_num : 0 < 1)
  obtain ⟨hPu, hAu, hSu⟩ := hu N hN
  have hpL := (ENNReal.ofReal_le_iff_le_toReal hPt.ne).mp (hp N)
  have haL := (ENNReal.ofReal_le_iff_le_toReal hAt.ne).mp (hl N)
  have hsL := (ENNReal.ofReal_le_iff_le_toReal hSt.ne).mp
    ((hl N).trans (particleRateAll_le_sym anisotropicQuarticSaddle N))
  exact ⟨⟨hpL, ENNReal.toReal_le_of_le_ofReal (by positivity) hPu⟩,
    ⟨haL, ENNReal.toReal_le_of_le_ofReal (by positivity) hAu⟩,
    ⟨hsL, ENNReal.toReal_le_of_le_ofReal (by positivity) hSu⟩⟩

private theorem quartic_theta_of_eventual_pnat (p c C : ℝ) (r : ℕ+ → ℝ)
    (hc : 0 < c) (hC : 0 < C) (N0 : ℕ)
    (h : ∀ N : ℕ+, N0 ≤ (N : ℕ) → c * (N : ℝ) ^ (-p) ≤ r N ∧ r N ≤ C * (N : ℝ) ^ (-p)) :
    ThetaScale p (fun n : ℕ => if hn : 0 < n then r ⟨n, hn⟩ else 0) := by
  refine ⟨c, C, hc, hC, max N0 1, le_max_right _ _, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hn)
  have hh := h ⟨n, hn0⟩ ((le_max_left _ _).trans hn)
  change c * (n : ℝ) ^ (-p) ≤ r ⟨n, hn0⟩ ∧
    r ⟨n, hn0⟩ ≤ C * (n : ℝ) ^ (-p) at hh
  simpa only [dif_pos hn0] using hh

/-- FIN075 exact power row, indexed by natural particle numbers; the zero-particle
convention occurs strictly before the chosen positive threshold and is irrelevant. -/
theorem quartic_symmetric_test_and_exact_power_row :
    ThetaScale (1 / 2) (fun n : ℕ => if h : 0 < n then
      (particlePoincareRate anisotropicQuarticSaddle ⟨n, h⟩).toReal else 0) ∧
    ThetaScale (3 / 2) (fun n : ℕ => if h : 0 < n then
      (particleRateAll anisotropicQuarticSaddle ⟨n, h⟩).toReal else 0) ∧
    ThetaScale (3 / 2) (fun n : ℕ => if h : 0 < n then
      (particleRateSym anisotropicQuarticSaddle ⟨n, h⟩).toReal else 0) := by
  obtain ⟨cp, cl, C, hcp, hcl, hC, N0, h⟩ := quartic_particle_rates_two_sided
  exact ⟨quartic_theta_of_eventual_pnat (1 / 2) cp C _ hcp hC N0 (fun N hN => (h N hN).1),
    quartic_theta_of_eventual_pnat (3 / 2) cl C _ hcl hC N0 (fun N hN => (h N hN).2.1),
    quartic_theta_of_eventual_pnat (3 / 2) cl C _ hcl hC N0 (fun N hN => (h N hN).2.2)⟩

namespace Taxonomy

/-- Frozen T13 quartic cluster for kappa=5/g(4), eta=4/5 and external field one.
All rates are positive and finite at every positive particle number; the powers
use the original unscaled physical particle energy and full canonical domains. -/
theorem anisotropic_quartic_saddle :
    (∀ N : ℕ+,
      (0 < particleRateAll anisotropicQuarticSaddle N ∧ particleRateAll anisotropicQuarticSaddle N < ⊤) ∧
      (0 < particleRateSym anisotropicQuarticSaddle N ∧ particleRateSym anisotropicQuarticSaddle N < ⊤) ∧
      (0 < particlePoincareRate anisotropicQuarticSaddle N ∧ particlePoincareRate anisotropicQuarticSaddle N < ⊤)) ∧
    ThetaScale (1 / 2) (fun n : ℕ => if h : 0 < n then
      (particlePoincareRate anisotropicQuarticSaddle ⟨n, h⟩).toReal else 0) ∧
    ThetaScale (3 / 2) (fun n : ℕ => if h : 0 < n then
      (particleRateAll anisotropicQuarticSaddle ⟨n, h⟩).toReal else 0) ∧
    ThetaScale (3 / 2) (fun n : ℕ => if h : 0 < n then
      (particleRateSym anisotropicQuarticSaddle ⟨n, h⟩).toReal else 0) := by
  exact ⟨fun N => rates_pos_lt_top anisotropicQuarticSaddle N (by norm_num : 0 < 1),
    quartic_symmetric_test_and_exact_power_row⟩

end Taxonomy
end DGPS.FiniteN
