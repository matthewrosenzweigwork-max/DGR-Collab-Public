import DGPS.Lipschitz.T01Regularization

/-!
# From measurable positive bounded tests to every canonical particle test

A genuine measurable representative is chosen before regularizing. The energy, entropy,
and square mass depend only on the almost-everywhere class, so the proof stage imposes no
additional regularity, sign, or finite-entropy restriction on the final competitor.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Complete domain reduction for the current defective inequality at fixed particle number.
The constants are unchanged, so uniform constants at the proof stage remain uniform. -/
theorem particle_defective_of_positive_bounded {d : ℕ} (A : InteractionData d) (N : ℕ+)
    {a B : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ g : ParticleH1 A N, Measurable g.1 → ∀ c C : ℝ, 0 < c →
      (∀ x, c ≤ g x) → (∀ x, g x ≤ C) →
      particleEntropy A N g ≤ ENNReal.ofReal (a * particleEnergy A N g) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂particleLaw A N)
    (f : ParticleH1 A N) :
    particleEntropy A N f ≤ ENNReal.ofReal (a * particleEnergy A N f) +
      ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N := by
  obtain ⟨g, hgm, hfg, hE, hEnt, -⟩ := exists_measurable_particleH1_representative f
  have hreg : ∀ n, particleEntropy A N (regularizedParticleTest g n) ≤
      ENNReal.ofReal (a * particleEnergy A N (regularizedParticleTest g n)) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (regularizedParticleTest g n x ^ 2)
          ∂particleLaw A N := by
    intro n
    apply hbound (regularizedParticleTest g n)
      ((SharpLSI.contDiff_psiReg n).continuous.measurable.comp hgm)
      (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) (by positivity)
    · exact fun x => (regularizedParticleTest_bounds g n x).1
    · exact fun x => (regularizedParticleTest_bounds g n x).2
  have hm : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N) =
      ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂particleLaw A N :=
    lintegral_congr_ae (hfg.mono fun x hx => congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hx)
  rw [hEnt, hE, hm]
  exact particle_defective_of_regularized g hreg ha

end DGPS.Lipschitz
