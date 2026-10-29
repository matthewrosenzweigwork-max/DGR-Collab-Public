import DGRHS.Gaussian.PeriodicSupercriticalPressure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Exact Gamma recurrence and rational pi bounds certify the dimension range
where the stability threshold lies strictly below the collision threshold. -/
noncomputable section
open MeasureTheory Set Filter Real
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic

lemma periodicStabilityThreshold_succ_two (d : ℕ) (hd : 1≤d) :
    periodicStabilityThreshold (Fin (d+2))=
      (2*Real.pi/(d:ℝ))*periodicStabilityThreshold (Fin d) := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hg : Real.Gamma ((d:ℝ)/2)≠0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hr : (4*Real.pi)^((d:ℝ)/2)≠0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  unfold periodicStabilityThreshold periodicLogConstant
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
  rw [show ((d:ℝ)+2)/2=(d:ℝ)/2+1 by ring,Real.Gamma_add_one (by positivity : (d:ℝ)/2≠0),
    Real.rpow_add (by positivity : (0:ℝ)<4*Real.pi),Real.rpow_one,pow_add]
  field_simp [hg,hr,hd0.ne',Real.pi_ne_zero]
  <;> ring

lemma periodicStabilityThreshold_one : periodicStabilityThreshold (Fin 1)=2 := by
  unfold periodicStabilityThreshold periodicLogConstant
  simp only [Fintype.card_fin,Nat.cast_one,pow_one]
  rw [Real.Gamma_one_half_eq,← Real.sqrt_eq_rpow,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  norm_num [Real.sq_sqrt Real.pi_pos.le]
  field_simp
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

lemma periodicStabilityThreshold_two : periodicStabilityThreshold (Fin 2)=2*Real.pi := by
  unfold periodicStabilityThreshold periodicLogConstant
  norm_num [Real.Gamma_one,Real.pi_ne_zero]
  field_simp
  <;> ring

lemma periodicStabilityThreshold_eleven : periodicStabilityThreshold (Fin 11)=64*Real.pi^5/945 := by
  rw [periodicStabilityThreshold_succ_two 9 (by omega),periodicStabilityThreshold_succ_two 7 (by omega),
    periodicStabilityThreshold_succ_two 5 (by omega),periodicStabilityThreshold_succ_two 3 (by omega),
    periodicStabilityThreshold_succ_two 1 (by omega),periodicStabilityThreshold_one]
  norm_num
  ring

lemma periodicStabilityThreshold_twelve : periodicStabilityThreshold (Fin 12)=Real.pi^6/60 := by
  rw [periodicStabilityThreshold_succ_two 10 (by omega),periodicStabilityThreshold_succ_two 8 (by omega),
    periodicStabilityThreshold_succ_two 6 (by omega),periodicStabilityThreshold_succ_two 4 (by omega),
    periodicStabilityThreshold_succ_two 2 (by omega),periodicStabilityThreshold_two]
  norm_num
  ring

lemma periodicStabilityThreshold_eleven_lt : periodicStabilityThreshold (Fin 11)<22 := by
  rw [periodicStabilityThreshold_eleven]
  calc
    _ ≤ 64*(3.15:ℝ)^5/945 := by gcongr;exact Real.pi_lt_d2.le
    _ < 22 := by norm_num

lemma periodicStabilityThreshold_twelve_lt : periodicStabilityThreshold (Fin 12)<24 := by
  rw [periodicStabilityThreshold_twelve]
  calc
    _ ≤ (3.15:ℝ)^6/60 := by gcongr;exact Real.pi_lt_d2.le
    _ < 24 := by norm_num

/-- Every dimension in the manuscript's high-dimensional regime has a
nonempty interval between stability and collision. -/
theorem periodicStabilityThreshold_lt_collision (d : ℕ) (hd : 11≤d) :
    periodicStabilityThreshold (Fin d)<2*(d:ℝ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases h11 : d=11
    · subst d;convert periodicStabilityThreshold_eleven_lt using 1 <;> norm_num
    by_cases h12 : d=12
    · subst d;convert periodicStabilityThreshold_twelve_lt using 1 <;> norm_num
    have hd13 : 13≤d := by omega
    have hp : 11≤d-2 := by omega
    have hind := ih (d-2) (by omega) hp
    have he : d=d-2+2 := by omega
    have hpos : (0:ℝ)<(d-2:ℕ) := by exact_mod_cast (by omega : 0<d-2)
    have hlarge : (11:ℝ)≤(d-2:ℕ) := by exact_mod_cast hp
    have hf : 2*Real.pi/((d-2:ℕ):ℝ)≤1 := by
      apply (div_le_iff₀ hpos).mpr
      linarith [Real.pi_lt_d2]
    letI : NeZero (d-2) := ⟨by omega⟩
    have hs := (periodicStabilityThreshold_pos (ι := Fin (d-2))).le
    calc
      _ = (2*Real.pi/((d-2:ℕ):ℝ))*periodicStabilityThreshold (Fin (d-2)) := by
        conv_lhs => rw [he]
        exact periodicStabilityThreshold_succ_two (d-2) (by omega)
      _ ≤ periodicStabilityThreshold (Fin (d-2)) := by simpa using mul_le_mul_of_nonneg_right hf hs
      _ < 2*(d:ℝ) := by
        have hle : ((d-2:ℕ):ℝ)≤d := by exact_mod_cast Nat.sub_le d 2
        linarith

/-- The complementary finite list of positive dimensions is certified by the
same recurrence and the native bound pi>3, without numerical oracles. -/
lemma periodicStabilityThreshold_ge_collision_low (d : ℕ) (hd : 1≤d) (h10 : d≤10) :
    2*(d:ℝ)≤periodicStabilityThreshold (Fin d) := by
  have hpi : (3:ℝ)≤Real.pi := by linarith [Real.pi_gt_d2]
  have hp2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hpi 2
  have hp3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hpi 3
  have hp4 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hpi 4
  have hp5 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hpi 5
  norm_num at hp2 hp3 hp4 hp5
  interval_cases d
  all_goals simp only [periodicStabilityThreshold_succ_two 8 (by omega),periodicStabilityThreshold_succ_two 7 (by omega),periodicStabilityThreshold_succ_two 6 (by omega),periodicStabilityThreshold_succ_two 5 (by omega),periodicStabilityThreshold_succ_two 4 (by omega),periodicStabilityThreshold_succ_two 3 (by omega),periodicStabilityThreshold_succ_two 2 (by omega),periodicStabilityThreshold_succ_two 1 (by omega),
    periodicStabilityThreshold_one,periodicStabilityThreshold_two]
  all_goals norm_num
  all_goals nlinarith

/-- Exact positive-integer dimensional threshold stated in the manuscript. -/
theorem periodicStabilityThreshold_lt_collision_iff (d : ℕ) (hd : 1≤d) :
    periodicStabilityThreshold (Fin d)<2*(d:ℝ) ↔ 11≤d := by
  constructor
  · intro h
    by_contra hn
    have hlo := periodicStabilityThreshold_ge_collision_low d hd (by omega)
    linarith
  · exact periodicStabilityThreshold_lt_collision d

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicStabilityThreshold_lt_collision
#check @DGRHS.Periodic.periodicStabilityThreshold_lt_collision
#print axioms DGRHS.Periodic.periodicStabilityThreshold_ge_collision_low
#print axioms DGRHS.Periodic.periodicStabilityThreshold_lt_collision_iff
#check @DGRHS.Periodic.periodicStabilityThreshold_lt_collision_iff
