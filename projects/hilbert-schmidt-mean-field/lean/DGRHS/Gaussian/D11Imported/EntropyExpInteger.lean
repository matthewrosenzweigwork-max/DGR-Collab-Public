/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.EntropyExpHorner

/-! Integer implementation of directed rational rounding. These identities
are the bridge required before the fast integer rehearsal can be kernel used. -/
namespace DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate

def ceilDiv (v d : ℤ) : ℤ := -((-v)/d)

theorem roundDown_ratio (P : ℕ) (hP : 0 < P) (v d : ℤ) (hd : 0 < d) :
    roundDown P ((v : ℚ)/((d : ℚ)*P)) = ((v/d : ℤ) : ℚ)/P := by
  have hp : (P : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  unfold roundDown
  rw [show (v : ℚ)/((d : ℚ)*P)*P = (v : ℚ)/d by field_simp]
  rw [Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast]

theorem roundUp_ratio (P : ℕ) (hP : 0 < P) (v d : ℤ) (hd : 0 < d) :
    roundUp P ((v : ℚ)/((d : ℚ)*P)) = (ceilDiv v d : ℚ)/P := by
  have hp : (P : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  unfold roundUp ceilDiv
  rw [show (v : ℚ)/((d : ℚ)*P)*P = (v : ℚ)/d by field_simp]
  have he : ⌈(v : ℚ)/(d : ℚ)⌉ = -((-v)/d) := by
    rw [← neg_neg ((v : ℚ)/(d : ℚ)), Int.ceil_neg]
    congr 1
    rw [show -((v : ℚ)/(d : ℚ)) = ((-v : ℤ) : ℚ)/d by push_cast; ring,
      Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast]
  rw [he]

def intHornerStep (P : ℕ) (q D : ℤ) (m : ℕ) (c : ℤ × ℤ) : ℤ × ℤ :=
  let d := D*m
  let v := d*P-q*c.1
  let a := v/d
  (a, ceilDiv (v-a*d+q*c.2) d)

def ratPair (P : ℕ) (c : ℤ × ℤ) : ℚ × ℚ := ⟨(c.1 : ℚ)/P, (c.2 : ℚ)/P⟩

theorem intHornerStep_eq (P : ℕ) (hP : 0 < P) (q D : ℤ) (hq : 0 ≤ q) (hD : 0 < D)
    (m : ℕ) (hm : 0 < m) (c : ℤ × ℤ) :
    ratPair P (intHornerStep P q D m c) = hornerStep P (-(q : ℚ)/D) m (ratPair P c) := by
  let d : ℤ := D*m
  let v : ℤ := d*P-q*c.1
  let a : ℤ := v/d
  have hd : 0 < d := mul_pos hD (Nat.cast_pos.mpr hm)
  have hp : (P : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hv : 1+ (-(q : ℚ)/D)/m*((c.1 : ℚ)/P) = (v : ℚ)/((d : ℚ)*P) := by
    dsimp [v, d]
    push_cast
    field_simp <;> ring
  have ha : roundDown P ((v : ℚ)/((d : ℚ)*P)) = (a : ℚ)/P := roundDown_ratio P hP v d hd
  have hrem : 0 ≤ v-a*d := sub_nonneg.mpr (Int.ediv_mul_le v (ne_of_gt hd))
  have hrem' : (0 : ℚ) ≤ ((v-a*d : ℤ) : ℚ)/((d : ℚ)*P) := by
    apply div_nonneg
    · exact_mod_cast hrem
    · positivity
  have he : (v : ℚ)/((d : ℚ)*P)-(a : ℚ)/P = ((v-a*d : ℤ) : ℚ)/((d : ℚ)*P) := by
    push_cast
    field_simp <;> ring
  have hq' : (0 : ℚ) ≤ (q : ℚ)/D := div_nonneg (by exact_mod_cast hq) (by exact_mod_cast hD.le)
  have hb : |(v : ℚ)/((d : ℚ)*P)-(a : ℚ)/P| + |-(q : ℚ)/D|/m*((c.2 : ℚ)/P) =
      ((v-a*d+q*c.2 : ℤ) : ℚ)/((d : ℚ)*P) := by
    rw [he, abs_of_nonneg hrem', neg_div, abs_neg, abs_of_nonneg hq']
    dsimp [d]
    push_cast
    field_simp <;> ring
  change ((a : ℚ)/P, (ceilDiv (v-a*d+q*c.2) d : ℚ)/P) = _
  unfold hornerStep ratPair
  dsimp only
  rw [hv, ha, hb, roundUp_ratio P hP _ d hd]

#print axioms intHornerStep_eq
end DGRHS.Gaussian.D11Imported.HighDim.EntropyTail.ExpCertificate
