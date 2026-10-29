import DGPS.Foundations.Entropy
import DGPS.Foundations.RateArithmetic
import DGPS.Particle.Rates

/-!
# Positive-entropy LSI versus the rates `r_N^all`, `r_N^sym` (DEF034)

For fixed `N` and real `r > 0`:

* `particleRate_iff_lsi`: `(∀ f ∈ H¹(P_N), Ent(f²) ≤ 2 E_N(f) / r) ↔ r ≤ r_N^all`;
* `particleRateSym_iff_lsi`: the same with both sides restricted to symmetric `f`.

The LSI quantifies over all tests, including zero-entropy and zero functions. The inequality
`Ent(f²) ≤ 2 E_N(f) / r` is read in `ℝ≥0∞` (`ENNReal.ofReal (2 E_N(f) / r)` on the right), and
`r ≤ r_N^all` as `ENNReal.ofReal r ≤ particleRateAll A N`.
-/

open scoped ENNReal

namespace DGPS

/-- Pointwise core: for `e > 0` and `r > 0`, `r ≤ 2E / e` iff `e ≤ 2E / r` (in `ℝ≥0∞`). -/
private theorem def034_core {r : ℝ} (hr : 0 < r) {e : ℝ≥0∞} (he : 0 < e) (E : ℝ) :
    ENNReal.ofReal r ≤ ENNReal.ofReal (2 * E) / e ↔ e ≤ ENNReal.ofReal (2 * E / r) := by
  have hr' : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl he.ne') (Or.inr ENNReal.ofReal_ne_top),
    ENNReal.ofReal_div_of_pos hr, ENNReal.le_div_iff_mul_le (Or.inl hr') (Or.inl ENNReal.ofReal_ne_top), mul_comm]

/-- DEF034: the all-tests positive-entropy LSI at `r > 0` is equivalent to `r ≤ r_N^all`. -/
theorem particleRate_iff_lsi {d : ℕ} (A : InteractionData d) (N : ℕ+) {r : ℝ} (hr : 0 < r) :
    (∀ f : ParticleH1 A N,
        particleEntropy A N f ≤ ENNReal.ofReal (2 * particleEnergy A N f / r)) ↔
      ENNReal.ofReal r ≤ particleRateAll A N := by
  constructor
  · intro h
    refine le_iInf fun f => ?_
    exact (def034_core hr f.2 _).2 (h f.1)
  · intro h f
    rcases eq_or_ne (particleEntropy A N f) 0 with h0 | h0
    · rw [h0]; exact bot_le
    · exact (def034_core hr (pos_iff_ne_zero.2 h0) _).1
        (h.trans (particleRateAll_le_quotient A N f (pos_iff_ne_zero.2 h0)))

/-- DEF034 (symmetric): the symmetric positive-entropy LSI at `r > 0` is equivalent to
`r ≤ r_N^sym`. -/
theorem particleRateSym_iff_lsi {d : ℕ} (A : InteractionData d) (N : ℕ+) {r : ℝ} (hr : 0 < r) :
    (∀ f : ParticleH1 A N, IsSymmetricParticleTest f →
        particleEntropy A N f ≤ ENNReal.ofReal (2 * particleEnergy A N f / r)) ↔
      ENNReal.ofReal r ≤ particleRateSym A N := by
  constructor
  · intro h
    refine le_iInf fun f => ?_
    exact (def034_core hr f.2 _).2 (h f.1.1 f.1.2)
  · intro h f hs
    rcases eq_or_ne (particleEntropy A N f) 0 with h0 | h0
    · rw [h0]; exact bot_le
    · exact (def034_core hr (pos_iff_ne_zero.2 h0) _).1
        (h.trans (particleRateSym_le_quotient A N f hs (pos_iff_ne_zero.2 h0)))

end DGPS
