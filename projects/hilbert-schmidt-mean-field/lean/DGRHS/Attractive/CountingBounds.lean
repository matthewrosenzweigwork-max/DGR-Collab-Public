/- Development counting candidate. It bounds actual cardinalities,
with explicit particle and moment endpoints. -/
import DGRHS.Attractive.CountingEvaluation
import Mathlib.Data.Nat.Factorial.Basic
noncomputable section
open scoped BigOperators
namespace DGRHS.Attractive

lemma card_noSingletonWords_le_all (N m : ℕ) :
    (noSingletonWords (α:=Fin N) m).card≤N^m := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin m→Fin N))
    (fun w => ∀ a,wordMultiplicity w a≠1)
  simpa [noSingletonWords] using h

lemma half_pow_two_mul (k : ℕ) : (1/2:ℝ)^(2*k)=(4^k:ℝ)⁻¹ := by
  calc
    _=((1/2:ℝ)^2)^k := pow_mul _ _ _
    _=((4:ℝ)⁻¹)^k := by congr 1; norm_num
    _=_ := inv_pow _ _

lemma small_particle_vector_count (N k : ℕ) (hk : 1≤k) (hN : N≤4*k) :
    ((noSingletonVectors (α:=Fin N) (2*k)).card:ℝ)≤(4*Real.exp 2)^k := by
  have h := vector_count_scaled_bound (α:=Fin N) (2*k) (by omega) (1/2) (by norm_num) (by norm_num)
  rw [half_pow_two_mul] at h
  simp only [Fintype.card_fin] at h
  have hn : (N:ℝ)≤4*k := by exact_mod_cast hN
  have he : 2*(N:ℝ)*(1/2:ℝ)^2≤(k:ℝ)*2 := by nlinarith
  have hp : (0:ℝ)<4^k := by positivity
  have hv := mul_le_mul_of_nonneg_right (h.trans (Real.exp_le_exp.mpr he)) hp.le
  have hc : ((noSingletonVectors (α:=Fin N) (2*k)).card:ℝ)≤Real.exp ((k:ℝ)*2)*4^k := by
    simpa only [Fintype.card_fin,mul_assoc,inv_mul_cancel₀ hp.ne',mul_one] using hv
  simpa only [Real.exp_nat_mul,mul_pow,mul_comm] using hc

lemma factorial_two_mul_le (k : ℕ) :
    ((2*k).factorial:ℝ)≤4^k*(k:ℝ)^(2*k) := by
  have h : ((2*k).factorial:ℝ)≤(2*(k:ℝ))^(2*k) := by
    exact_mod_cast Nat.factorial_le_pow (2*k)
  calc
    _≤_ := h
    _=_ := by
      rw [mul_pow,pow_mul]
      norm_num only [pow_two]

lemma large_particle_surviving_counts (N k : ℕ) (hk : 1≤k) (hN : 4*k≤N) :
    ((noSingletonVectors (α:=Fin N) (2*k)).card:ℝ)*
      ((noSingletonWords (α:=Fin N) (2*k)).card:ℝ)≤
      (4*Real.exp 3)^k*(N:ℝ)^(2*k) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNk : 4*(k:ℝ)≤N := by exact_mod_cast hN
  let t := Real.sqrt ((k:ℝ)/(N:ℝ))
  have ht : 0≤t := Real.sqrt_nonneg _
  have ht2 : t^2=(k:ℝ)/(N:ℝ) := Real.sq_sqrt (div_nonneg hk0.le hN0.le)
  have hhalf : t≤1/2 := Real.sqrt_le_iff.mpr ⟨by norm_num,
    (div_le_iff₀ hN0).mpr (by nlinarith)⟩
  have hV := vector_count_scaled_bound (α:=Fin N) (2*k) (by omega) t ht hhalf
  have hW := word_count_scaled_bound (α:=Fin N) (2*k) (by omega) t ht (by linarith)
  simp only [Fintype.card_fin] at hV hW
  have hNt : (N:ℝ)*t^2=(k:ℝ) := by rw [ht2];field_simp
  have htwoNt : 2*(N:ℝ)*t^2=2*(k:ℝ) := by nlinarith [hNt]
  rw [htwoNt] at hV
  rw [hNt] at hW
  have hT : t^(2*k)*((N:ℝ)/(k:ℝ))^k=1 := by
    rw [pow_mul,ht2,←mul_pow]
    have he : ((k:ℝ)/(N:ℝ))*((N:ℝ)/(k:ℝ))=1 := by field_simp
    rw [he,one_pow]
  have hT2 : (t^(2*k)*t^(2*k))*((N:ℝ)/(k:ℝ))^(2*k)=1 := by
    have hR : ((N:ℝ)/(k:ℝ))^(2*k)=(((N:ℝ)/(k:ℝ))^k)^2 := by
      rw [Nat.mul_comm 2 k,pow_mul]
    rw [hR]
    calc
      _=(t^(2*k)*((N:ℝ)/(k:ℝ))^k)^2 := by ring
      _=1 := by rw [hT];norm_num
  have hscaled := mul_le_mul hV hW
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht _)) (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hscaled
    (pow_nonneg (div_nonneg hN0.le hk0.le) (2*k))
  have hVW : ((noSingletonVectors (α:=Fin N) (2*k)).card:ℝ)*
      ((noSingletonWords (α:=Fin N) (2*k)).card:ℝ)≤
      ((2*k).factorial:ℝ)*Real.exp (3*(k:ℝ))*((N:ℝ)/(k:ℝ))^(2*k) := by
    calc
      _=(((noSingletonVectors (α:=Fin N) (2*k)).card:ℝ)*
          ((noSingletonWords (α:=Fin N) (2*k)).card:ℝ))*
          ((t^(2*k)*t^(2*k))*((N:ℝ)/(k:ℝ))^(2*k)) := by rw [hT2,mul_one]
      _≤(Real.exp (2*(k:ℝ))*(((2*k).factorial:ℝ)*Real.exp (k:ℝ)))*
          ((N:ℝ)/(k:ℝ))^(2*k) := by simpa only [mul_assoc,mul_comm,mul_left_comm] using hmul
      _=((2*k).factorial:ℝ)*(Real.exp (2*(k:ℝ))*Real.exp (k:ℝ))*((N:ℝ)/(k:ℝ))^(2*k) := by ring
      _=_ := by rw [←Real.exp_add];congr 2 <;>ring
  have hkp : (0:ℝ)<(k:ℝ)^(2*k) := pow_pos hk0 _
  have hf : ((2*k).factorial:ℝ)/(k:ℝ)^(2*k)≤4^k := by
    apply (div_le_iff₀ hkp).mpr
    exact factorial_two_mul_le k
  calc
    _≤_ := hVW
    _=(((2*k).factorial:ℝ)/(k:ℝ)^(2*k))*(N:ℝ)^(2*k)*Real.exp (3*(k:ℝ)) := by rw [div_pow];ring
    _≤4^k*(N:ℝ)^(2*k)*Real.exp (3*(k:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf (pow_nonneg hN0.le _)) (Real.exp_pos _).le
    _=_ := by rw [mul_comm 3,Real.exp_nat_mul,mul_pow];ring

lemma surviving_counts_bound (N k : ℕ) (hk : 1≤k) :
    ((noSingletonVectors (α:=Fin N) (2*k)).card:ℝ)*
      ((noSingletonWords (α:=Fin N) (2*k)).card:ℝ)≤
      (4*Real.exp 3)^k*(N:ℝ)^(2*k) := by
  rcases le_total N (4*k) with hN | hN
  · have hV := small_particle_vector_count N k hk hN
    have he : (4*Real.exp 2)^k≤(4*Real.exp 3)^k :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by norm_num)) (by norm_num)) _
    have hW : ((noSingletonWords (α:=Fin N) (2*k)).card:ℝ)≤(N:ℝ)^(2*k) := by
      exact_mod_cast card_noSingletonWords_le_all N (2*k)
    exact mul_le_mul (hV.trans he) hW (Nat.cast_nonneg _) (by positivity)
  · exact large_particle_surviving_counts N k hk hN

/-- Numeric completion of the weighted count in the original factorial moment
proof. No count, kernel, partition or moment conclusion is a premise. -/
theorem surviving_pair_factorial_bound (N k : ℕ) (hk : 1≤k) :
    ((∑ i∈noSingletonWords (α:=Fin N) (2*k),∑ _j∈noSingletonWords (α:=Fin N) (2*k),
      ∏ a : Fin N,(wordMultiplicity i a).factorial):ℝ)≤
      ((2*k).factorial:ℝ)*(4*Real.exp 3)^k*(N:ℝ)^(2*k) := by
  have he : (∑ i∈noSingletonWords (α:=Fin N) (2*k),∑ _j∈noSingletonWords (α:=Fin N) (2*k),
      ∏ a : Fin N,((wordMultiplicity i a).factorial:ℝ))=
      ((2*k).factorial:ℝ)*((noSingletonVectors (α:=Fin N) (2*k)).card:ℝ)*
        ((noSingletonWords (α:=Fin N) (2*k)).card:ℝ) := by
    exact_mod_cast surviving_pair_factorial_count (α:=Fin N) (2*k)
  rw [he]
  have h := mul_le_mul_of_nonneg_left (surviving_counts_bound N k hk)
    (Nat.cast_nonneg (2*k).factorial)
  simpa only [mul_assoc] using h

end DGRHS.Attractive
#print axioms DGRHS.Attractive.small_particle_vector_count
#print axioms DGRHS.Attractive.factorial_two_mul_le
#print axioms DGRHS.Attractive.large_particle_surviving_counts
#print axioms DGRHS.Attractive.surviving_pair_factorial_bound
#check @DGRHS.Attractive.surviving_pair_factorial_bound
