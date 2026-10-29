/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! A rational Taylor enclosure for the actual real exponential.
This is a sound elementary evaluator, not a certificate of a torus grid. -/

open scoped BigOperators

namespace DGRHS.Gaussian.D11Imported.CertifiedExp

def taylor (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, q ^ k / k.factorial

def remainder (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * n)

structure Interval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

def Interval.Contains (I : Interval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

/-- Endpoint Taylor bounds; soundness is proved for n>0 and endpoints in [-1,1]. -/
def expInterval (I : Interval) (n : ℕ) : Interval :=
  ⟨taylor I.lower n - remainder I.lower n,
   taylor I.upper n + remainder I.upper n⟩

theorem taylor_cast (q : ℚ) (n : ℕ) :
    (taylor q n : ℝ) = ∑ k ∈ Finset.range n, (q : ℝ)^k / k.factorial := by
  simp [taylor]

theorem remainder_cast (q : ℚ) (n : ℕ) :
    (remainder q n : ℝ) = |(q : ℝ)|^n * (n + 1) / ((n.factorial : ℝ) * n) := by
  simp [remainder]

theorem point_enclosure (q : ℚ) (n : ℕ) (hn : 0 < n) (hq : |q| ≤ 1) :
    ((taylor q n - remainder q n : ℚ) : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ ((taylor q n + remainder q n : ℚ) : ℝ) := by
  have hq' : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hq' hn
  rw [← taylor_cast, ← mul_div_assoc, Nat.cast_succ, ← remainder_cast] at h
  have ha := abs_le.mp h
  push_cast
  constructor <;> linarith

theorem expInterval_sound (I : Interval) (n : ℕ) (hn : 0 < n)
    (hlo : |I.lower| ≤ 1) (hhi : |I.upper| ≤ 1)
    {x : ℝ} (hx : I.Contains x) : (expInterval I n).Contains (Real.exp x) := by
  have hl := (point_enclosure I.lower n hn hlo).1
  have hu := (point_enclosure I.upper n hn hhi).2
  exact ⟨hl.trans (Real.exp_le_exp.mpr hx.1),
    (Real.exp_le_exp.mpr hx.2).trans hu⟩

/-- A failed domain check returns none rather than an unchecked enclosure. -/
def checkedExp (I : Interval) (n : ℕ) : Option Interval :=
  if 0 < n ∧ |I.lower| ≤ 1 ∧ |I.upper| ≤ 1 then some (expInterval I n) else none

theorem checkedExp_sound {I J : Interval} {n : ℕ}
    (h : checkedExp I n = some J) {x : ℝ} (hx : I.Contains x) :
    J.Contains (Real.exp x) := by
  unfold checkedExp at h
  split_ifs at h with hc
  · cases h
    exact expInterval_sound I n hc.1 hc.2.1 hc.2.2 hx

end DGRHS.Gaussian.D11Imported.CertifiedExp
