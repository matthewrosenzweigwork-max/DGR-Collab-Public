/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.EntropyExpIntegerEvaluator

namespace DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate

structure Entry where
  numerator : ℤ
  denominator : ℤ
  lower : ℤ
  upper : ℤ
  deriving DecidableEq, Repr

def entryCheck (e : Entry) : Bool := decide (
  0 ≤ e.numerator ∧ 0 < e.denominator ∧ e.numerator ≤ 1024*e.denominator ∧
  (e.lower : ℚ)/10^60 ≤ (integerNegExpInterval e.numerator e.denominator).lower ∧
  (integerNegExpInterval e.numerator e.denominator).upper ≤ (e.upper : ℚ)/10^60)

def rowsCheck (es : List Entry) : Bool := es.all entryCheck

theorem entryCheck_sound (e : Entry) (h : entryCheck e = true) :
    (e.lower : ℝ)/10^60 ≤ Real.exp (-((e.numerator : ℝ)/e.denominator)) ∧
      Real.exp (-((e.numerator : ℝ)/e.denominator)) ≤ (e.upper : ℝ)/10^60 := by
  have hc : 0 ≤ e.numerator ∧ 0 < e.denominator ∧ e.numerator ≤ 1024*e.denominator ∧
      (e.lower : ℚ)/10^60 ≤ (integerNegExpInterval e.numerator e.denominator).lower ∧
      (integerNegExpInterval e.numerator e.denominator).upper ≤ (e.upper : ℚ)/10^60 :=
    of_decide_eq_true h
  have hh := integer_certificate_sound e.numerator e.denominator
    ((e.lower : ℚ)/10^60) ((e.upper : ℚ)/10^60) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast] using hh

theorem rowsCheck_sound (es : List Entry) (h : rowsCheck es = true) (e : Entry) (he : e ∈ es) :
    (e.lower : ℝ)/10^60 ≤ Real.exp (-((e.numerator : ℝ)/e.denominator)) ∧
      Real.exp (-((e.numerator : ℝ)/e.denominator)) ≤ (e.upper : ℝ)/10^60 :=
  entryCheck_sound e (List.all_eq_true.mp h e he)

#print axioms rowsCheck_sound
end DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
