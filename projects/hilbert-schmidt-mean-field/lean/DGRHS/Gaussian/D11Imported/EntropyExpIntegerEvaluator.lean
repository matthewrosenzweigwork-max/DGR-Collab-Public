/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.EntropyExpInteger

namespace DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
open DGRHS.Gaussian.D11Imported.CertifiedExp

def certificatePrecision : ℕ := 10^90

def intHornerNear (q D : ℤ) (n : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, ceilDiv ((n+1)*certificatePrecision) n)
  | r+1 => intHornerStep certificatePrecision q D (n+1) (intHornerNear q D (n+1) r)

theorem intHornerNear_eq (q D : ℤ) (hq : 0 ≤ q) (hD : 0 < D)
    (r n : ℕ) (hnr : n+r = 40) :
    ratPair certificatePrecision (intHornerNear q D n r) =
      hornerNear certificatePrecision (-(q : ℚ)/D) n r := by
  induction r generalizing n with
  | zero =>
    have hn : n = 40 := by omega
    subst n
    norm_num [intHornerNear, hornerNear, ratPair, ceilDiv, certificatePrecision]
  | succ r ih =>
    rw [intHornerNear, intHornerStep_eq certificatePrecision (by norm_num [certificatePrecision])
      q D hq hD (n+1) (by omega), ih (n+1) (by omega)]
    rfl

def intSquaredInterval (P : ℕ) (c : ℤ × ℤ) : ℤ × ℤ :=
  ((max c.1 0)^2/P, ceilDiv ((max c.2 0)^2) P)

def intAsInterval (P : ℕ) (c : ℤ × ℤ) : Interval :=
  ⟨(c.1 : ℚ)/P, (c.2 : ℚ)/P⟩

theorem intSquaredInterval_eq (P : ℕ) (hP : 0 < P) (c : ℤ × ℤ) :
    intAsInterval P (intSquaredInterval P c) = squaredInterval P (intAsInterval P c) := by
  have hm (z : ℤ) : max ((z : ℚ)/P) 0 = ((max z 0 : ℤ) : ℚ)/P := by
    rw [← zero_div (P : ℚ), max_div_div_right (by positivity)]
    simp
  have he (z : ℤ) : (((max z 0 : ℤ) : ℚ)/P)^2 = (((max z 0)^2 : ℤ) : ℚ)/((P : ℤ)*P) := by
    push_cast
    ring
  unfold intAsInterval intSquaredInterval squaredInterval roundInterval
  dsimp only
  rw [hm, hm, he, he, roundDown_ratio P hP _ P (by exact_mod_cast hP),
    roundUp_ratio P hP _ P (by exact_mod_cast hP)]

def intSquareIter (P : ℕ) (c : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => c
  | r+1 => intSquaredInterval P (intSquareIter P c r)

theorem intSquareIter_eq (P : ℕ) (hP : 0 < P) (c : ℤ × ℤ) (m : ℕ) :
    intAsInterval P (intSquareIter P c m) = squareIter P (intAsInterval P c) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [intSquareIter, intSquaredInterval_eq P hP, ih, squareIter]

def integerNegExpInterval (qn qd : ℤ) : Interval :=
  let c := intHornerNear qn (qd*1024) 0 40
  intAsInterval certificatePrecision (intSquareIter certificatePrecision (c.1-c.2,c.1+c.2) 10)

theorem integerNegExpInterval_eq (qn qd : ℤ) (hn : 0 ≤ qn) (hd : 0 < qd) :
    integerNegExpInterval qn qd = negExpHornerInterval certificatePrecision 40 10 ((qn : ℚ)/qd) := by
  let c := intHornerNear qn (qd*1024) 0 40
  have hc := intHornerNear_eq qn (qd*1024) hn (by positivity) 40 0 (by norm_num)
  have hq : -(qn : ℚ)/(qd*1024) = -((qn : ℚ)/qd)/2^10 := by ring
  norm_num only [Int.cast_mul, Int.cast_ofNat] at hc
  rw [hq] at hc
  have he : intAsInterval certificatePrecision (c.1-c.2,c.1+c.2) =
      hornerInterval certificatePrecision (-((qn : ℚ)/qd)/2^10) 40 := by
    have h := congrArg (fun p : ℚ × ℚ => (⟨p.1-p.2,p.1+p.2⟩ : Interval)) hc
    simpa only [intAsInterval, ratPair, hornerInterval, Int.cast_sub, Int.cast_add, sub_div, add_div]
      using h
  unfold integerNegExpInterval negExpHornerInterval
  rw [intSquareIter_eq certificatePrecision (by norm_num [certificatePrecision]), he]

theorem integer_certificate_sound (qn qd : ℤ) (L U : ℚ)
    (hn : 0 ≤ qn) (hd : 0 < qd) (hscale : qn ≤ 1024*qd)
    (hL : L ≤ (integerNegExpInterval qn qd).lower)
    (hU : (integerNegExpInterval qn qd).upper ≤ U) :
    (L : ℝ) ≤ Real.exp (-((qn : ℝ)/qd)) ∧ Real.exp (-((qn : ℝ)/qd)) ≤ (U : ℝ) := by
  have hq : |(-((qn : ℚ)/qd)/2^10 : ℚ)| ≤ 1 := by
    have hn' : (0 : ℚ) ≤ qn := by exact_mod_cast hn
    have hd' : (0 : ℚ) < qd := by exact_mod_cast hd
    have hs : (qn : ℚ) ≤ 1024*qd := by exact_mod_cast hscale
    have hv : (qn : ℚ)/qd ≤ 1024 := (div_le_iff₀ hd').mpr hs
    have hneg : -((qn : ℚ)/qd)/2^10 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hn' hd'.le)) (by norm_num)
    rw [abs_of_nonpos hneg]
    norm_num only [show (2 : ℚ)^10 = 1024 by norm_num]
    simp only [neg_div, neg_neg]
    exact (div_le_iff₀ (by norm_num : (0 : ℚ) < 1024)).mpr (by simpa using hv)
  rw [integerNegExpInterval_eq qn qd hn hd] at hL hU
  have h := horner_certificate_sound certificatePrecision 40 10 ((qn : ℚ)/qd) L U
    (by norm_num [certificatePrecision]) (by norm_num) hq hL hU
  simpa only [Rat.cast_div, Rat.cast_intCast] using h

#print axioms integer_certificate_sound
end DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
