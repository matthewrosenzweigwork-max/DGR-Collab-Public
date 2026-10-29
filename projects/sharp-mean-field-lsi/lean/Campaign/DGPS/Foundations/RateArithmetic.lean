import Mathlib.Basic.ENNReal.Inv

/-!
# Extended quotient finite-witness bridge (DEF031)

Rates are infima over positive-gap competitors of the extended quotient `D / (2 * (G : ℝ≥0∞))`
with `D : ℝ≥0∞` (possibly `⊤`) and `G : ℝ≥0`; the empty infimum is `⊤`.

Main results:
* `DGPS.positiveGap_quotient_top_iff`: for `0 < G`, `D / (2 G) = ⊤ ↔ D = ⊤`.
* `DGPS.rate_finite_of_finite_witness`: a positive-gap competitor with finite `D` bounds the
  rate infimum above by a finite number, so the rate is not `⊤`.
* `DGPS.FiniteRate`, `DGPS.realRate`: the real value of a rate, available only with a finiteness
  receipt.
-/

namespace DGPS

open scoped ENNReal NNReal

/-- The denominator `2 * G` of a positive finite gap is nonzero and not `⊤` in `ℝ≥0∞`. -/
theorem two_mul_gap_ne_zero {G : ℝ≥0} (hG : 0 < G) : (2 : ℝ≥0∞) * (G : ℝ≥0∞) ≠ 0 := by
  have : (G : ℝ≥0∞) ≠ 0 := by exact_mod_cast hG.ne'
  simpa using this

theorem two_mul_gap_ne_top (G : ℝ≥0) : (2 : ℝ≥0∞) * (G : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top

/-- For a finite strictly positive gap, `D / (2 G) = ⊤` exactly when `D = ⊤`. -/
theorem positiveGap_quotient_top_iff (D : ℝ≥0∞) {G : ℝ≥0} (hG : 0 < G) :
    D / (2 * (G : ℝ≥0∞)) = ⊤ ↔ D = ⊤ := by
  rw [ENNReal.div_eq_top]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (two_mul_gap_ne_zero hG)
    · exact h
  · intro h
    exact Or.inr ⟨h, two_mul_gap_ne_top G⟩

/-- Finite-D companion: the quotient is finite iff `D` is. -/
theorem positiveGap_quotient_ne_top_iff (D : ℝ≥0∞) {G : ℝ≥0} (hG : 0 < G) :
    D / (2 * (G : ℝ≥0∞)) ≠ ⊤ ↔ D ≠ ⊤ :=
  not_congr (positiveGap_quotient_top_iff D hG)

/-- A positive-gap competitor with finite `D` gives a finite upper bound on the rate infimum
(`⨅` over positive-gap competitors of `D / (2 G)`). -/
theorem rate_le_quotient_of_witness {ι : Type*} (D : ι → ℝ≥0∞) (G : ι → ℝ≥0) (i : ι)
    (hG : 0 < G i) :
    (⨅ j : {j : ι // 0 < G j}, D j.1 / (2 * (G j.1 : ℝ≥0∞))) ≤ D i / (2 * (G i : ℝ≥0∞)) :=
  iInf_le (fun j : {j : ι // 0 < G j} => D j.1 / (2 * (G j.1 : ℝ≥0∞))) ⟨i, hG⟩

/-- Finite-witness bridge: if some positive-gap competitor has finite `D`, the rate is finite. -/
theorem rate_finite_of_finite_witness {ι : Type*} (D : ι → ℝ≥0∞) (G : ι → ℝ≥0) (i : ι)
    (hG : 0 < G i) (hD : D i ≠ ⊤) :
    (⨅ j : {j : ι // 0 < G j}, D j.1 / (2 * (G j.1 : ℝ≥0∞))) ≠ ⊤ :=
  ne_top_of_le_ne_top ((positiveGap_quotient_ne_top_iff (D i) hG).2 hD)
    (rate_le_quotient_of_witness D G i hG)

/-- Finiteness of an extended rate. -/
def FiniteRate (r : ℝ≥0∞) : Prop := r ≠ ⊤

/-- The real value of a finite rate, carried with its finiteness receipt. -/
noncomputable def realRate (r : ℝ≥0∞) (_hr : FiniteRate r) : ℝ := r.toReal

theorem realRate_nonneg (r : ℝ≥0∞) (hr : FiniteRate r) : 0 ≤ realRate r hr :=
  ENNReal.toReal_nonneg

theorem ofReal_realRate (r : ℝ≥0∞) (hr : FiniteRate r) :
    ENNReal.ofReal (realRate r hr) = r :=
  ENNReal.ofReal_toReal hr

theorem realRate_pos_iff (r : ℝ≥0∞) (hr : FiniteRate r) : 0 < realRate r hr ↔ 0 < r :=
  ENNReal.toReal_pos_iff.trans ⟨fun h => h.1, fun h => ⟨h, lt_top_iff_ne_top.2 hr⟩⟩

theorem realRate_le_iff {r s : ℝ≥0∞} (hr : FiniteRate r) (hs : FiniteRate s) :
    realRate r hr ≤ realRate s hs ↔ r ≤ s :=
  ENNReal.toReal_le_toReal hr hs

end DGPS
