import DGPS.Lipschitz.T01DefectiveDomainClosure

/-!
# Symmetry-preserving canonical domain closure

The test symmetry is the actual almost-everywhere permutation invariance. It survives the
measurable representative and the scalar positive regularization; neither a pointwise
symmetric representative nor a narrower smooth test class is required.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

/-- A bound on measurable positive bounded symmetric tests extends to every canonical
symmetric test, with exactly the same coefficients and unscaled energy. -/
theorem particle_symmetric_defective_of_positive_bounded {d : ℕ}
    (A : InteractionData d) (N : ℕ+) {a B : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ g : ParticleH1 A N, Measurable g.1 → IsSymmetricParticleTest g →
      ∀ c C : ℝ, 0 < c → (∀ x, c ≤ g x) → (∀ x, g x ≤ C) →
      particleEntropy A N g ≤ ENNReal.ofReal (a * particleEnergy A N g) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂particleLaw A N)
    (f : ParticleH1 A N) (hsym : IsSymmetricParticleTest f) :
    particleEntropy A N f ≤ ENNReal.ofReal (a * particleEnergy A N f) +
      ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N := by
  obtain ⟨g, hgm, hfg, hE, hEnt, hsymg⟩ := exists_measurable_particleH1_representative f
  have hgs : IsSymmetricParticleTest g := hsymg.mp hsym
  have hreg : ∀ n, particleEntropy A N (regularizedParticleTest g n) ≤
      ENNReal.ofReal (a * particleEnergy A N (regularizedParticleTest g n)) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (regularizedParticleTest g n x ^ 2)
          ∂particleLaw A N := by
    intro n
    apply hbound (regularizedParticleTest g n)
      ((SharpLSI.contDiff_psiReg n).continuous.measurable.comp hgm)
      (hgs.comp_scalar (SharpLSI.psiReg n) rfl)
      (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) (by positivity)
    · exact fun x => (regularizedParticleTest_bounds g n x).1
    · exact fun x => (regularizedParticleTest_bounds g n x).2
  have hm : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N) =
      ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂particleLaw A N :=
    lintegral_congr_ae (hfg.mono fun x hx => congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) hx)
  rw [hEnt, hE, hm]
  exact particle_defective_of_regularized g hreg ha

end DGPS.Lipschitz
