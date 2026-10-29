/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.EntropyExpCertificate

/-! A fixed-precision Horner recurrence for exponential enclosures. It keeps
intermediate rational sizes bounded instead of expanding forty powers. -/
namespace DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
open DGRHS.Gaussian.D11Imported.CertifiedExp

def hornerStep (P : ℕ) (q : ℚ) (m : ℕ) (c : ℚ × ℚ) : ℚ × ℚ :=
  let v := 1+q/m*c.1
  let a := roundDown P v
  (a, roundUp P (|v-a|+|q|/m*c.2))

def hornerNear (P : ℕ) (q : ℚ) (n : ℕ) : ℕ → ℚ × ℚ
  | 0 => (0, (n+1 : ℚ)/n)
  | r+1 => hornerStep P q (n+1) (hornerNear P q (n+1) r)

theorem hornerStep_bound (P : ℕ) (hP : 0 < P) (q : ℚ) (m : ℕ) (c : ℚ × ℚ) :
    |1+q/m*c.1-(hornerStep P q m c).1| ≤
      (hornerStep P q m c).2-|q|/m*c.2 := by
  unfold hornerStep
  dsimp only
  have h := le_roundUp P hP (|1+q/m*c.1-roundDown P (1+q/m*c.1)|+|q|/m*c.2)
  linarith

theorem hornerNear_sound (P : ℕ) (hP : 0 < P) (q : ℚ) (hq : |q| ≤ 1)
    (r n : ℕ) (hnr : 0 < n+r) :
    |Real.exp (q : ℝ)-Real.expNear n (q : ℝ) ((hornerNear P q n r).1 : ℝ)| ≤
      |(q : ℝ)|^n/(n.factorial : ℝ)*((hornerNear P q n r).2 : ℝ) := by
  induction r generalizing n with
  | zero =>
    have hn : 0 < n := by omega
    have h := Real.exp_approx_end (n-1) n (q : ℝ) (by omega) (by exact_mod_cast hq)
    simpa only [hornerNear, Rat.cast_zero, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one] using h
  | succ r ih =>
    let c := hornerNear P q (n+1) r
    have hc := hornerStep_bound P hP q (n+1) c
    have hcR : |1+(q : ℝ)/(n+1 : ℕ)*(c.1 : ℝ)-((hornerStep P q (n+1) c).1 : ℝ)| ≤
        ((hornerStep P q (n+1) c).2 : ℝ)-|(q : ℝ)|/(n+1 : ℕ)*(c.2 : ℝ) := by
      exact_mod_cast hc
    exact Real.exp_approx_succ (n+1) rfl (c.1 : ℝ) (c.2 : ℝ) hcR (ih (n+1) (by omega))

def hornerInterval (P : ℕ) (q : ℚ) (N : ℕ) : Interval :=
  let c := hornerNear P q 0 N
  ⟨c.1-c.2,c.1+c.2⟩

theorem hornerInterval_sound (P : ℕ) (hP : 0 < P) (q : ℚ) (hq : |q| ≤ 1)
    (N : ℕ) (hN : 0 < N) : (hornerInterval P q N).Contains (Real.exp (q : ℝ)) := by
  have h := hornerNear_sound P hP q hq N 0 (by simpa using hN)
  simp only [Real.expNear_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at h
  have hh := abs_le.mp h
  change (((hornerNear P q 0 N).1-(hornerNear P q 0 N).2 : ℚ) : ℝ) ≤ _ ∧
    _ ≤ (((hornerNear P q 0 N).1+(hornerNear P q 0 N).2 : ℚ) : ℝ)
  push_cast
  constructor <;> linarith

def negExpHornerInterval (P N m : ℕ) (q : ℚ) : Interval :=
  squareIter P (hornerInterval P (-q/2^m) N) m

theorem negExpHornerInterval_sound (P N m : ℕ) (q : ℚ)
    (hP : 0 < P) (hN : 0 < N) (hq : |(-q/2^m : ℚ)| ≤ 1) :
    (negExpHornerInterval P N m q).Contains (Real.exp (-(q : ℝ))) := by
  have hb := hornerInterval_sound P hP (-q/2^m) hq N hN
  have h := squareIter_sound P hP _ (Real.exp_pos _).le hb m
  change (negExpHornerInterval P N m q).Contains _ at h
  have he : Real.exp (((-q/2^m : ℚ) : ℝ))^(2^m) = Real.exp (-(q : ℝ)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    field_simp
  rwa [he] at h

theorem horner_certificate_sound (P N m : ℕ) (q L U : ℚ)
    (hP : 0 < P) (hN : 0 < N) (hq : |(-q/2^m : ℚ)| ≤ 1)
    (hL : L ≤ (negExpHornerInterval P N m q).lower)
    (hU : (negExpHornerInterval P N m q).upper ≤ U) :
    (L : ℝ) ≤ Real.exp (-(q : ℝ)) ∧ Real.exp (-(q : ℝ)) ≤ (U : ℝ) := by
  have h := negExpHornerInterval_sound P N m q hP hN hq
  exact ⟨((Rat.cast_le (K := ℝ)).mpr hL).trans h.1,
    h.2.trans ((Rat.cast_le (K := ℝ)).mpr hU)⟩

#print axioms horner_certificate_sound
end DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
