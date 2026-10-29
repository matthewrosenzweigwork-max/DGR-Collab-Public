import DGPS.Foundations.Entropy
import DGPS.Particle.Sobolev
import DGPS.Particle.Symmetry

/-!
# Particle logarithmic Sobolev rates and ordering (DEF019)

INTERFACES/definitions.md §4, common_lemmas.md DEF019, `PINNED_MANUSCRIPT/introduction.tex`
eq:r-all and eq:r-sym.

* `particleEntropy A N f = Ent_{P_N}(f²)` (`homogeneousEntropy` of `f²` for `particleLaw A N`);
* `particleQuotient A N f = 2 E_N(f) / Ent_{P_N}(f²)` in `ℝ≥0∞`;
* `particleRateAll A N = inf_{f ∈ H¹(P_N), Ent(f²) > 0} 2 E_N(f) / Ent(f²)`;
* `particleRateSym A N` is the same infimum over `SymmetricParticleH1 A N`;
* `particleRateAll_le_sym : particleRateAll A N ≤ particleRateSym A N`.

Both rates are extended nonnegative infima (`ℝ≥0∞`); an empty competitor set gives `⊤`.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS

/-- `Ent_{P_N}(f²)` for a test `f ∈ H¹(P_N)`. -/
noncomputable def particleEntropy {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleH1 A N) : ℝ≥0∞ :=
  homogeneousEntropy (particleLaw A N) fun x => f x ^ 2

/-- The quotient `2 E_N(f) / Ent_{P_N}(f²)` in `ℝ≥0∞`. -/
noncomputable def particleQuotient {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleH1 A N) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * particleEnergy A N f) / particleEntropy A N f

/-- DEF019: `r_N^all = inf_{f ∈ H¹(P_N), Ent(f²) > 0} 2 E_N(f) / Ent(f²)`. -/
noncomputable def particleRateAll {d : ℕ} (A : InteractionData d) (N : ℕ+) : ℝ≥0∞ :=
  ⨅ f : {f : ParticleH1 A N // 0 < particleEntropy A N f}, particleQuotient A N f.1

/-- DEF019: `r_N^sym`, the same infimum over symmetric tests. -/
noncomputable def particleRateSym {d : ℕ} (A : InteractionData d) (N : ℕ+) : ℝ≥0∞ :=
  ⨅ f : {f : SymmetricParticleH1 A N // 0 < particleEntropy A N f.1},
    particleQuotient A N f.1.1

/-- DEF019: `r_N^all ≤ r_N^sym` (the symmetric competitors are among all competitors). -/
theorem particleRateAll_le_sym {d : ℕ} (A : InteractionData d) (N : ℕ+) :
    particleRateAll A N ≤ particleRateSym A N :=
  le_iInf fun f => iInf_le (fun g : {f : ParticleH1 A N // 0 < particleEntropy A N f} =>
    particleQuotient A N g.1) ⟨f.1.1, f.2⟩

theorem particleRateAll_le_quotient {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleH1 A N) (hf : 0 < particleEntropy A N f) :
    particleRateAll A N ≤ particleQuotient A N f :=
  iInf_le (fun g : {f : ParticleH1 A N // 0 < particleEntropy A N f} =>
    particleQuotient A N g.1) ⟨f, hf⟩

theorem particleRateSym_le_quotient {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (f : ParticleH1 A N) (hs : IsSymmetricParticleTest f) (hf : 0 < particleEntropy A N f) :
    particleRateSym A N ≤ particleQuotient A N f :=
  iInf_le (fun g : {f : SymmetricParticleH1 A N // 0 < particleEntropy A N f.1} =>
    particleQuotient A N g.1.1) ⟨⟨f, hs⟩, hf⟩

end DGPS
