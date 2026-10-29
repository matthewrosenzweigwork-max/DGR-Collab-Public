/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.CertifiedExp
import Mathlib.Algebra.Order.Floor.Ring

/-! Sound dyadic range reduction with rational directed rounding after each
squaring. This module does not assert acceptance of any generated data file. -/
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
open DGRHS.Gaussian.D11Imported.CertifiedExp

def roundDown (P : ℕ) (q : ℚ) : ℚ := (⌊q*P⌋ : ℚ)/P

def roundUp (P : ℕ) (q : ℚ) : ℚ := (⌈q*P⌉ : ℚ)/P

def roundInterval (P : ℕ) (I : Interval) : Interval :=
  ⟨roundDown P I.lower, roundUp P I.upper⟩

def squaredInterval (P : ℕ) (I : Interval) : Interval :=
  roundInterval P ⟨(max I.lower 0)^2, (max I.upper 0)^2⟩

def squareIter (P : ℕ) (I : Interval) : ℕ → Interval
  | 0 => I
  | m+1 => squaredInterval P (squareIter P I m)

def negExpInterval (P n m : ℕ) (q : ℚ) : Interval :=
  squareIter P (roundInterval P (expInterval ⟨-q/2^m,-q/2^m⟩ n)) m

theorem roundDown_le (P : ℕ) (hP : 0 < P) (q : ℚ) : roundDown P q ≤ q := by
  unfold roundDown
  exact (div_le_iff₀ (Nat.cast_pos.mpr hP)).mpr (Int.floor_le _)

theorem le_roundUp (P : ℕ) (hP : 0 < P) (q : ℚ) : q ≤ roundUp P q := by
  unfold roundUp
  exact (le_div_iff₀ (Nat.cast_pos.mpr hP)).mpr (Int.le_ceil _)

theorem roundInterval_sound (P : ℕ) (hP : 0 < P) (I : Interval) {x : ℝ}
    (hx : I.Contains x) : (roundInterval P I).Contains x := by
  constructor
  · exact ((Rat.cast_le (K := ℝ)).mpr (roundDown_le P hP I.lower)).trans hx.1
  · exact hx.2.trans ((Rat.cast_le (K := ℝ)).mpr (le_roundUp P hP I.upper))

theorem squaredInterval_sound (P : ℕ) (hP : 0 < P) (I : Interval) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : I.Contains x) : (squaredInterval P I).Contains (x^2) := by
  apply roundInterval_sound P hP
  constructor
  · change (((max I.lower 0)^2 : ℚ) : ℝ) ≤ x^2
    push_cast
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le hx.1 hx0) 2
  · change x^2 ≤ (((max I.upper 0)^2 : ℚ) : ℝ)
    push_cast
    exact pow_le_pow_left₀ hx0 (hx.2.trans (le_max_left _ _)) 2

theorem squareIter_sound (P : ℕ) (hP : 0 < P) (I : Interval) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : I.Contains x) (m : ℕ) :
    (squareIter P I m).Contains (x^(2^m)) := by
  induction m with
  | zero => simpa only [squareIter, pow_zero, pow_one] using hx
  | succ m ih =>
    have h := squaredInterval_sound P hP (squareIter P I m) (pow_nonneg hx0 _) ih
    simpa only [squareIter, pow_succ, pow_mul] using h

theorem negExpInterval_sound (P n m : ℕ) (q : ℚ)
    (hP : 0 < P) (hn : 0 < n) (hq : |(-q/2^m : ℚ)| ≤ 1) :
    (negExpInterval P n m q).Contains (Real.exp (-(q : ℝ))) := by
  have hb := expInterval_sound (⟨-q/2^m,-q/2^m⟩ : Interval) n hn hq hq
    (x := ((-q/2^m : ℚ) : ℝ)) ⟨le_rfl,le_rfl⟩
  have h := squareIter_sound P hP _ (Real.exp_pos _).le (roundInterval_sound P hP _ hb) m
  change (negExpInterval P n m q).Contains _ at h
  have he : Real.exp (((-q/2^m : ℚ) : ℝ))^(2^m) = Real.exp (-(q : ℝ)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    field_simp
  rwa [he] at h

theorem certificate_sound (P n m : ℕ) (q L U : ℚ)
    (hP : 0 < P) (hn : 0 < n) (hq : |(-q/2^m : ℚ)| ≤ 1)
    (hL : L ≤ (negExpInterval P n m q).lower)
    (hU : (negExpInterval P n m q).upper ≤ U) :
    (L : ℝ) ≤ Real.exp (-(q : ℝ)) ∧ Real.exp (-(q : ℝ)) ≤ (U : ℝ) := by
  have h := negExpInterval_sound P n m q hP hn hq
  exact ⟨((Rat.cast_le (K := ℝ)).mpr hL).trans h.1,
    h.2.trans ((Rat.cast_le (K := ℝ)).mpr hU)⟩

#print axioms certificate_sound
end DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
