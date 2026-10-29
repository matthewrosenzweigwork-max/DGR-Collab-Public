import DGRHS.Concentration.RowMoment

noncomputable section
open MeasureTheory
namespace DGRHS.Concentration

lemma nat_cast_le_two_pow (m : ℕ) : (m : ℝ) ≤ 2^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.cast_succ,pow_succ]
    have hp : (1 : ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
    nlinarith

lemma two_high_monomial_le (x y T : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxT : x ≤ T) (hyT : y ≤ T) (m : ℕ) (hm : 2 ≤ m) :
    x^2*y^(m-2) ≤ T^m := by
  calc
    _ ≤ T^2*T^(m-2) := mul_le_mul
      (pow_le_pow_left₀ hx hxT 2) (pow_le_pow_left₀ hy hyT _) (pow_nonneg hy _) (sq_nonneg T)
    _ = T^m := by rw [← pow_add]; congr 1; omega

lemma mixed_B_power_identity (a s B C : ℝ) (hs : s^2 = a) (m : ℕ) (hm : 2 ≤ m) :
    (6*a)^m*(6*s)^m*B^(m-2)*C^2 =
      36^m*a^2*(s*C)^2*(a*s*B)^(m-2) := by
  have hp (x : ℝ) : x^m = x^(m-2)*x^2 := by rw [← pow_add]; congr 1; omega
  have h36 : (36 : ℝ)^m = 6^m*6^m := by rw [← mul_pow]; norm_num
  rw [h36]
  simp only [mul_pow]
  rw [hp a,hp s,hs]
  ring

lemma mixed_A_power_identity (a s A C : ℝ) (hs : s^2 = a) (m : ℕ) (hm : 2 ≤ m) :
    (6*a)^m*(6*a)^m*A^(m-2)*C^2 =
      36^m*a^3*(s*C)^2*(a^2*A)^(m-2) := by
  have hp (x : ℝ) : x^m = x^(m-2)*x^2 := by rw [← pow_add]; congr 1; omega
  have h36 : (36 : ℝ)^m = 6^m*6^m := by rw [← mul_pow]; norm_num
  have hswap : (a^2)^(m-2) = (a^(m-2))^2 := by
    rw [← pow_mul,← pow_mul]; congr 1; omega
  rw [h36]
  simp only [mul_pow]
  rw [hp a,hs,hswap]
  ring

/-- A coarse universal constant; exact source scale dependence is retained.
The elementary integer power bound avoids asymptotic or positive-scale division. -/
lemma four_scale_power_bound (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (m : ℕ) (hm : 2 ≤ m) :
    let a := (m : ℝ)
    let s := Real.sqrt a
    let T := s*C+a*D+a*s*B+a^2*A
    (6*s)^m*(12*(C+s*D+a*B))^m+
      (6*a)^m*((6*s)^m*B^(m-2)*C^2+(6*a)^m*A^(m-2)*C^2) ≤ (864*T)^m := by
  dsimp only
  let a := (m : ℝ)
  let s := Real.sqrt a
  let T := s*C+a*D+a*s*B+a^2*A
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s^2 = a := Real.sq_sqrt ha
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hSC : 0 ≤ s*C := mul_nonneg hs hC
  have hAD : 0 ≤ a*D := mul_nonneg ha hD
  have hASB : 0 ≤ a*s*B := mul_nonneg (mul_nonneg ha hs) hB
  have hAA : 0 ≤ a^2*A := mul_nonneg (sq_nonneg a) hA
  have hx : s*C ≤ T := by dsimp [T]; linarith
  have hyB : a*s*B ≤ T := by dsimp [T]; linarith
  have hyA : a^2*A ≤ T := by dsimp [T]; linarith
  have hp2 : a^2 ≤ (8 : ℝ)^m := by
    have ht := pow_le_pow_left₀ ha (nat_cast_le_two_pow m) 2
    have hh : ((2 : ℝ)^m)^2 = (4 : ℝ)^m := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    rw [hh] at ht
    exact ht.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
  have hp3 : a^3 ≤ (8 : ℝ)^m := by
    have ht := pow_le_pow_left₀ ha (nat_cast_le_two_pow m) 3
    have hh : ((2 : ℝ)^m)^3 = (8 : ℝ)^m := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    rwa [hh] at ht
  have ht0 : (6*s)^m*(12*(C+s*D+a*B))^m ≤ (288*T)^m := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have he : 6*s*(12*(C+s*D+a*B)) = 72*(s*C+a*D+a*s*B) := by nlinarith [hss]
    rw [he]
    dsimp [T]
    nlinarith [mul_nonneg ha hD,mul_nonneg (mul_nonneg ha hs) hB,mul_nonneg (sq_nonneg a) hA,mul_nonneg hs hC]
  have htB : (6*a)^m*(6*s)^m*B^(m-2)*C^2 ≤ (288*T)^m := by
    rw [mixed_B_power_identity a s B C hss m hm]
    have hxy := two_high_monomial_le (s*C) (a*s*B) T (by positivity) (by positivity) hx hyB m hm
    calc
      _ = 36^m*a^2*((s*C)^2*(a*s*B)^(m-2)) := by ring
      _ ≤ 36^m*8^m*T^m := by gcongr
      _ = (288*T)^m := by rw [← mul_pow,← mul_pow]; congr 1; ring
  have htA : (6*a)^m*(6*a)^m*A^(m-2)*C^2 ≤ (288*T)^m := by
    rw [mixed_A_power_identity a s A C hss m hm]
    have hxy := two_high_monomial_le (s*C) (a^2*A) T (by positivity) (by positivity) hx hyA m hm
    calc
      _ = 36^m*a^3*((s*C)^2*(a^2*A)^(m-2)) := by ring
      _ ≤ 36^m*8^m*T^m := by gcongr
      _ = (288*T)^m := by rw [← mul_pow,← mul_pow]; congr 1; ring
  have hthree : (3 : ℝ) ≤ 3^m := by
    calc
      (3 : ℝ) = 3^1 := by norm_num
      _ ≤ 3^m := pow_le_pow_right₀ (by norm_num) (by omega)
  change _ ≤ (864*T)^m
  calc
    _ = (6*s)^m*(12*(C+s*D+a*B))^m+
      (6*a)^m*(6*s)^m*B^(m-2)*C^2+(6*a)^m*(6*a)^m*A^(m-2)*C^2 := by ring
    _ ≤ 3*(288*T)^m := by linarith
    _ ≤ 3^m*(288*T)^m := mul_le_mul_of_nonneg_right hthree (pow_nonneg (by positivity) _)
    _ = (864*T)^m := by rw [← mul_pow]; congr 1; ring

#print axioms DGRHS.Concentration.four_scale_power_bound
end DGRHS.Concentration
