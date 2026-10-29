/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ElevenShellData
import DGRHS.Gaussian.D11Imported.ElevenShellEnergy
import DGRHS.Gaussian.D11Imported.EntropyExpRows

/-! Rational lower certificates for the one hundred Fourier shells. The
checker validates square-root brackets, a proved exponential interval, and
the final rational rounding; no external numerical result is trusted. -/
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell
open scoped BigOperators

def rootScale : ℕ := 10^20
def polynomialRat (z : ℚ) : ℚ := z^5+15*z^4+105*z^3+420*z^2+945*z+945

structure EnergyEntry where
  rootFloor : ℕ
  expLower : ℤ
  expUpper : ℤ
  energyFloor : ℕ
  deriving DecidableEq, Repr, Inhabited

def EnergyEntry.rootLo (e : EnergyEntry) : ℚ := e.rootFloor/rootScale
def EnergyEntry.rootHi (e : EnergyEntry) : ℚ := (e.rootFloor+1)/rootScale
def EnergyEntry.zLo (e : EnergyEntry) : ℚ := 2*(103993/33102)*e.rootLo/5
def EnergyEntry.expEntry (e : EnergyEntry) : EntropyTail.ExpCertificate.Entry :=
  ⟨4*104348*((e.rootFloor:ℤ)+1), 5*33215*rootScale, e.expLower, e.expUpper⟩
def EnergyEntry.lower (m : ℕ) (e : EnergyEntry) : ℚ :=
  ((stage11[m]!:ℚ)/2) * (1/((m:ℚ)^5*e.rootHi)) *
    polynomialRat e.zLo^2 * ((e.expLower:ℚ)/10^60) / 945^2

def energyCheck (m : ℕ) (e : EnergyEntry) : Bool := decide (
  0 < e.rootFloor ∧ e.rootFloor^2 ≤ m*rootScale^2 ∧
  m*rootScale^2 ≤ (e.rootFloor+1)^2 ∧ 0 ≤ e.expLower ∧
  EntropyTail.ExpCertificate.entryCheck e.expEntry = true ∧
  (e.energyFloor:ℚ)/10^12 < e.lower m)

noncomputable section

lemma fourierPolynomial_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    fourierPolynomial x ≤ fourierPolynomial y := by
  unfold fourierPolynomial
  gcongr

lemma weight_eq (m : ℕ) : weight m =
    (1/((m:ℝ)^5*Real.sqrt (m:ℝ))) *
      fourierPolynomial (2*Real.pi*Real.sqrt (m:ℝ)/5)^2 *
        Real.exp (-2*(2*Real.pi*Real.sqrt (m:ℝ)/5))/945^2 := by
  have hs : Real.sqrt (m:ℝ)^11 = (m:ℝ)^5*Real.sqrt (m:ℝ) := by
    calc
      _ = (Real.sqrt (m:ℝ)^2)^5*Real.sqrt (m:ℝ) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg m)]
  have he (z : ℝ) : Real.exp (-z)^2 = Real.exp (-2*z) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold weight fourierProfile
  rw [hs, div_pow, mul_pow, he]
  ring

lemma root_bounds {m : ℕ} {e : EnergyEntry} (h : energyCheck m e = true) :
    (e.rootLo:ℝ) ≤ Real.sqrt (m:ℝ) ∧ Real.sqrt (m:ℝ) ≤ (e.rootHi:ℝ) := by
  have hc := of_decide_eq_true h
  change 0<e.rootFloor ∧ e.rootFloor^2 ≤ m*rootScale^2 ∧
    m*rootScale^2 ≤ (e.rootFloor+1)^2 ∧ _ at hc
  have hl : ((e.rootFloor:ℝ)/rootScale)^2 ≤ (m:ℝ) := by
    have hi : (e.rootFloor:ℝ)^2 ≤ (m:ℝ)*(rootScale:ℝ)^2 := by exact_mod_cast hc.2.1
    rw [div_pow, div_le_iff₀ (by norm_num [rootScale])]
    exact hi
  have hu : (m:ℝ) ≤ (((e.rootFloor:ℝ)+1)/rootScale)^2 := by
    have hi : (m:ℝ)*(rootScale:ℝ)^2 ≤ ((e.rootFloor:ℝ)+1)^2 := by exact_mod_cast hc.2.2.1
    rw [div_pow, le_div_iff₀ (by norm_num [rootScale])]
    exact hi
  constructor
  · rw [EnergyEntry.rootLo, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
    exact (Real.le_sqrt (by positivity) (Nat.cast_nonneg m)).mpr hl
  · rw [EnergyEntry.rootHi]
    push_cast
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hu⟩

lemma entry_lower_le_shell {m : ℕ} (hm : 0 < m) {e : EnergyEntry}
    (h : energyCheck m e = true) :
    (e.lower m:ℝ) ≤ ((stage11[m]!:ℝ)/2)*weight m := by
  have hc := of_decide_eq_true h
  change 0<e.rootFloor ∧ e.rootFloor^2 ≤ m*rootScale^2 ∧
    m*rootScale^2 ≤ (e.rootFloor+1)^2 ∧ 0 ≤ e.expLower ∧
    EntropyTail.ExpCertificate.entryCheck e.expEntry = true ∧ _ at hc
  have hr := root_bounds h
  have hm0 : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hlo : (0:ℝ) ≤ (e.rootLo:ℝ) := by simp [EnergyEntry.rootLo, rootScale]; positivity
  have hhi : (0:ℝ) < (e.rootHi:ℝ) := by simp [EnergyEntry.rootHi, rootScale]; positivity
  have hzlo : (e.zLo:ℝ) ≤ 2*Real.pi*Real.sqrt (m:ℝ)/5 := by
    simp only [EnergyEntry.zLo, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    gcongr
    · exact pi_fine_bounds.1.le
    · exact hr.1
  have hz0 : (0:ℝ) ≤ (e.zLo:ℝ) := by
    simp only [EnergyEntry.zLo, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    positivity
  have hex := (EntropyTail.ExpCertificate.entryCheck_sound e.expEntry hc.2.2.2.2.1).1
  have harg : 2*(2*Real.pi*Real.sqrt (m:ℝ)/5) ≤
      (e.expEntry.numerator:ℝ)/e.expEntry.denominator := by
    simp only [EnergyEntry.expEntry]
    push_cast
    have hp : 2*(2*Real.pi*Real.sqrt (m:ℝ)/5) ≤
        4*((104348:ℝ)/33215)*(e.rootHi:ℝ)/5 := by
      calc
        _ = 4*Real.pi*Real.sqrt (m:ℝ)/5 := by ring
        _ ≤ _ := by
          gcongr
          · exact pi_fine_bounds.2.le
          · exact hr.2
    convert hp using 1
    simp only [EnergyEntry.rootHi, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    ring
  have hex' : (e.expLower:ℝ)/10^60 ≤ Real.exp (-2*(2*Real.pi*Real.sqrt (m:ℝ)/5)) :=
    hex.trans (Real.exp_le_exp.mpr (by linarith [harg]))
  have hrec : 1/((m:ℝ)^5*(e.rootHi:ℝ)) ≤ 1/((m:ℝ)^5*Real.sqrt (m:ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hr.2 (by positivity))
  have hpoly : polynomialRat e.zLo = (e.zLo)^5+15*(e.zLo)^4+105*(e.zLo)^3+420*(e.zLo)^2+945*e.zLo+945 := rfl
  have hpoly' : (polynomialRat e.zLo:ℝ) = fourierPolynomial (e.zLo:ℝ) := by
    simp [polynomialRat, fourierPolynomial]
  rw [EnergyEntry.lower]
  push_cast
  rw [hpoly', weight_eq]
  have hel : (0:ℝ) ≤ e.expLower := by exact_mod_cast hc.2.2.2.1
  have hpl : 0 ≤ fourierPolynomial (e.zLo:ℝ) := by unfold fourierPolynomial; positivity
  have hpm := fourierPolynomial_mono hz0 hzlo
  calc
    _ ≤ ((stage11[m]!:ℝ)/2) * (1/((m:ℝ)^5*Real.sqrt (m:ℝ))) *
        fourierPolynomial (2*Real.pi*Real.sqrt (m:ℝ)/5)^2 *
          Real.exp (-2*(2*Real.pi*Real.sqrt (m:ℝ)/5))/945^2 := by gcongr
    _ = _ := by ring

#print axioms entry_lower_le_shell
end
end DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell
