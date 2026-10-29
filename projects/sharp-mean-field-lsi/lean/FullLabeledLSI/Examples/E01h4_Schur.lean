import FullLabeledLSI.Examples.E01h0_Seq

/-!
# Lane D, Task B4: row-sum (Schur) bounds for the Fourier concavity estimate (Lemma 9.11)

Pure real analysis on sequences.  Statement skeleton (to be proved).
-/

open scoped BigOperators

namespace SharpLSI.FL.Ex.LaneD

lemma sq_le_of_abs_le' {z K : ℝ} (h : |z| ≤ K) : z ^ 2 ≤ K ^ 2 := by
  have h0 : 0 ≤ |z| := abs_nonneg z
  have := pow_le_pow_left₀ h0 h 2
  rwa [sq_abs] at this

lemma geom_pair_summable {α β : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) (hβ0 : 0 ≤ β) (hβ : β < 1) :
    Summable (fun p : ℕ × ℕ => α ^ p.1 * β ^ p.2) := by
  have h1 : Summable (fun a : ℕ => ‖α ^ a‖) := by
    simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg hα0] using summable_geometric_of_lt_one hα0 hα
  have h2 : Summable (fun a : ℕ => ‖β ^ a‖) := by
    simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg hβ0] using summable_geometric_of_lt_one hβ0 hβ
  exact summable_mul_of_summable_norm (f := fun a : ℕ => α ^ a) (g := fun a : ℕ => β ^ a) h1 h2

lemma summable_of_geom (f : ℕ × ℕ → ℝ) (C α β : ℝ) (hα0 : 0 ≤ α) (hα : α < 1) (hβ0 : 0 ≤ β)
    (hβ : β < 1) (h0 : ∀ p, 0 ≤ f p) (h : ∀ p, f p ≤ C * (α ^ p.1 * β ^ p.2)) : Summable f :=
  Summable.of_nonneg_of_le h0 h ((geom_pair_summable hα0 hα hβ0 hβ).mul_left C)

lemma summable_wgt : Summable (fun p : ℕ × ℕ => wgt p) := by
  have h1 : Summable (fun j : ℕ => (j : ℝ) * (1 / 100 : ℝ) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 100 : ℝ)) (by norm_num)
  have h2 : Summable (fun j : ℕ => ‖(j : ℝ) * (1 / 100 : ℝ) ^ j‖) := by
    simpa [Real.norm_eq_abs] using h1.abs
  have := summable_mul_of_summable_norm (f := fun j : ℕ => (j : ℝ) * (1 / 100 : ℝ) ^ j)
    (g := fun j : ℕ => (j : ℝ) * (1 / 100 : ℝ) ^ j) h2 h2
  convert this using 2 with p
  simp only [wgt, pow_add]; ring

lemma wgt_nonneg (p : ℕ × ℕ) : 0 ≤ wgt p := by
  unfold wgt; positivity

theorem summable_Ncos_terms (x : ℕ → ℝ) (hb : ∃ K, ∀ j, |x j| ≤ K) :
    Summable (fun j : ℕ => (j : ℝ) ^ 2 * (1 / 100 : ℝ) ^ j * x j ^ 2) := by
  obtain ⟨K, hK⟩ := hb
  have hs := summable_pow_mul_geometric_of_norm_lt_one 2 (r := (1 / 100 : ℝ)) (by norm_num)
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hs.mul_left (K ^ 2))
  have := sq_le_of_abs_le' (hK j)
  have hp : 0 ≤ (j : ℝ) ^ 2 * (1 / 100 : ℝ) ^ j := by positivity
  nlinarith

theorem summable_lin_terms (y : ℕ → ℝ) (hb : ∃ K, ∀ j, |y j| ≤ K) :
    Summable (fun j : ℕ => (j : ℝ) * (1 / 100 : ℝ) ^ j * y j) := by
  obtain ⟨K, hK⟩ := hb
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 100 : ℝ)) (by norm_num)
  refine Summable.of_norm_bounded (hs.mul_left K) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hp : |(j : ℝ)| * |(1 / 100 : ℝ) ^ j| = (j : ℝ) ^ 1 * (1 / 100 : ℝ) ^ j := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; ring
  rw [hp]
  have := hK j
  have hp0 : 0 ≤ (j : ℝ) ^ 1 * (1 / 100 : ℝ) ^ j := by positivity
  nlinarith

lemma sgnk_abs_le (j k : ℕ) : |sgnk j k| ≤ 1 := by
  unfold sgnk; split_ifs <;> simp

theorem summable_Tcos_terms (x : ℕ → ℝ) (hb : ∃ K, ∀ j, |x j| ≤ K) :
    Summable (fun p : ℕ × ℕ => wgt p * x p.1 * (x (Nat.dist p.1 p.2) - x (p.1 + p.2))) := by
  obtain ⟨K, hK⟩ := hb
  refine Summable.of_norm_bounded ((summable_wgt).mul_left (2 * K ^ 2)) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (wgt_nonneg p)]
  have h1 := hK p.1
  have h2 : |x (Nat.dist p.1 p.2) - x (p.1 + p.2)| ≤ 2 * K := by
    calc _ ≤ |x (Nat.dist p.1 p.2)| + |x (p.1 + p.2)| := abs_sub _ _
      _ ≤ K + K := add_le_add (hK _) (hK _)
      _ = 2 * K := by ring
  have h0 := wgt_nonneg p
  have := mul_le_mul h1 h2 (abs_nonneg _) (by linarith [abs_nonneg (x p.1)])
  nlinarith

theorem summable_Tsin_terms (y : ℕ → ℝ) (hb : ∃ K, ∀ j, |y j| ≤ K) :
    Summable (fun p : ℕ × ℕ =>
      wgt p * y p.1 * (y (p.1 + p.2) + sgnk p.1 p.2 * y (Nat.dist p.1 p.2))) := by
  obtain ⟨K, hK⟩ := hb
  refine Summable.of_norm_bounded ((summable_wgt).mul_left (2 * K ^ 2)) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (wgt_nonneg p)]
  have h1 := hK p.1
  have h2 : |y (p.1 + p.2) + sgnk p.1 p.2 * y (Nat.dist p.1 p.2)| ≤ 2 * K := by
    calc _ ≤ |y (p.1 + p.2)| + |sgnk p.1 p.2 * y (Nat.dist p.1 p.2)| := abs_add_le _ _
      _ ≤ K + K := by
        refine add_le_add (hK _) ?_
        rw [abs_mul]
        have := sgnk_abs_le p.1 p.2
        have := hK (Nat.dist p.1 p.2)
        have : 0 ≤ K := le_trans (abs_nonneg _) this
        nlinarith [abs_nonneg (y (Nat.dist p.1 p.2)), abs_nonneg (sgnk p.1 p.2)]
      _ = 2 * K := by ring
  have h0 := wgt_nonneg p
  have := mul_le_mul h1 h2 (abs_nonneg _) (by linarith [abs_nonneg (y p.1)])
  nlinarith

noncomputable def uu (x : ℕ → ℝ) (a : ℕ) : ℝ := (a : ℝ) * (1 / 10 : ℝ) ^ a * |x a|

lemma uu_nonneg (x : ℕ → ℝ) (a : ℕ) : 0 ≤ uu x a := by unfold uu; positivity

lemma uu_zero (x : ℕ → ℝ) : uu x 0 = 0 := by simp [uu]

lemma uu_sq (x : ℕ → ℝ) (a : ℕ) : uu x a ^ 2 = (a : ℝ) ^ 2 * (1 / 100 : ℝ) ^ a * x a ^ 2 := by
  unfold uu
  have : ((1 / 10 : ℝ) ^ a) ^ 2 = (1 / 100 : ℝ) ^ a := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [mul_pow, mul_pow, sq_abs, this]

lemma cast_succ_le_two_pow (a : ℕ) : (a : ℝ) + 1 ≤ 2 ^ a := by
  have : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  exact_mod_cast this

lemma cast_le_two_pow (a : ℕ) : (a : ℝ) ≤ 2 ^ a := by linarith [cast_succ_le_two_pow a]

lemma nat_geom10 (a : ℕ) : (a : ℝ) * (1 / 10 : ℝ) ^ a ≤ (1 / 5 : ℝ) ^ a := by
  have : (1 / 5 : ℝ) ^ a = 2 ^ a * (1 / 10 : ℝ) ^ a := by rw [← mul_pow]; norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_right (cast_le_two_pow a) (by positivity)

lemma nat_geom1000 (a : ℕ) : (a : ℝ) * (1 / 1000 : ℝ) ^ a ≤ (1 / 500 : ℝ) ^ a := by
  have : (1 / 500 : ℝ) ^ a = 2 ^ a * (1 / 1000 : ℝ) ^ a := by rw [← mul_pow]; norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_right (cast_le_two_pow a) (by positivity)

lemma succ_geom1000 (a : ℕ) : ((a : ℝ) + 1) * (1 / 1000 : ℝ) ^ a ≤ (1 / 500 : ℝ) ^ a := by
  have : (1 / 500 : ℝ) ^ a = 2 ^ a * (1 / 1000 : ℝ) ^ a := by rw [← mul_pow]; norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_right (cast_succ_le_two_pow a) (by positivity)

lemma uu_le (x : ℕ → ℝ) {K : ℝ} (hK : ∀ j, |x j| ≤ K) (a : ℕ) : uu x a ≤ K * (1 / 5 : ℝ) ^ a := by
  unfold uu
  have h1 := nat_geom10 a
  have h2 := hK a
  have h3 : 0 ≤ |x a| := abs_nonneg _
  have h4 : 0 ≤ (a : ℝ) * (1 / 10 : ℝ) ^ a := by positivity
  calc (a : ℝ) * (1 / 10 : ℝ) ^ a * |x a| ≤ (1 / 5 : ℝ) ^ a * K :=
        mul_le_mul h1 h2 h3 (by positivity)
    _ = K * (1 / 5 : ℝ) ^ a := by ring

lemma uu_sq_le (x : ℕ → ℝ) {K : ℝ} (hK : ∀ j, |x j| ≤ K) (a : ℕ) :
    uu x a ^ 2 ≤ K ^ 2 * (1 / 25 : ℝ) ^ a := by
  have h := pow_le_pow_left₀ (uu_nonneg x a) (uu_le x hK a) 2
  have e : (K * (1 / 5 : ℝ) ^ a) ^ 2 = K ^ 2 * (1 / 25 : ℝ) ^ a := by
    rw [mul_pow, ← pow_mul, mul_comm a 2, pow_mul]; norm_num
  linarith

/-- kernels -/
noncomputable def c1 (p : ℕ × ℕ) : ℝ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else ((p.1 : ℝ) + p.2) / p.2 * (1 / 10 : ℝ) ^ (3 * p.1 + p.2)
noncomputable def c2 (p : ℕ × ℕ) : ℝ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else (p.2 : ℝ) / p.1 * (1 / 10 : ℝ) ^ (3 * p.2)
noncomputable def c3 (p : ℕ × ℕ) : ℝ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else (p.2 : ℝ) / ((p.1 : ℝ) + p.2) * (1 / 10 : ℝ) ^ p.2
noncomputable def c23 (p : ℕ × ℕ) : ℝ := c2 p + c3 p

lemma c1_nonneg (p : ℕ × ℕ) : 0 ≤ c1 p := by unfold c1; split_ifs <;> positivity
lemma c2_nonneg (p : ℕ × ℕ) : 0 ≤ c2 p := by unfold c2; split_ifs <;> positivity
lemma c3_nonneg (p : ℕ × ℕ) : 0 ≤ c3 p := by unfold c3; split_ifs <;> positivity
lemma c23_nonneg (p : ℕ × ℕ) : 0 ≤ c23 p := add_nonneg (c2_nonneg p) (c3_nonneg p)

lemma pow3 (a n : ℕ) : (1 / 10 : ℝ) ^ (3 * a + n) = (1 / 1000 : ℝ) ^ a * (1 / 10 : ℝ) ^ n := by
  rw [pow_add, pow_mul]; norm_num

lemma c1_le (p : ℕ × ℕ) : c1 p ≤ (1 / 500 : ℝ) ^ p.1 * (1 / 10 : ℝ) ^ p.2 := by
  unfold c1
  split_ifs with h
  · positivity
  · rw [not_or] at h
    obtain ⟨ha, hn⟩ := h
    have hn' : (0 : ℝ) < p.2 := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hq : ((p.1 : ℝ) + p.2) / p.2 ≤ (p.1 : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have : (1 : ℝ) ≤ p.2 := by exact_mod_cast Nat.pos_of_ne_zero hn
      nlinarith [(Nat.cast_nonneg p.1 : (0:ℝ) ≤ p.1)]
    rw [pow3]
    have h2 := succ_geom1000 p.1
    calc ((p.1 : ℝ) + p.2) / p.2 * ((1 / 1000 : ℝ) ^ p.1 * (1 / 10 : ℝ) ^ p.2)
        ≤ ((p.1 : ℝ) + 1) * ((1 / 1000 : ℝ) ^ p.1 * (1 / 10 : ℝ) ^ p.2) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = (((p.1 : ℝ) + 1) * (1 / 1000 : ℝ) ^ p.1) * (1 / 10 : ℝ) ^ p.2 := by ring
      _ ≤ (1 / 500 : ℝ) ^ p.1 * (1 / 10 : ℝ) ^ p.2 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)

lemma c2_le (p : ℕ × ℕ) : c2 p ≤ (p.2 : ℝ) * (1 / 1000 : ℝ) ^ p.2 := by
  unfold c2
  split_ifs with h
  · positivity
  · rw [not_or] at h
    obtain ⟨ha, hn⟩ := h
    have ha' : (1 : ℝ) ≤ p.1 := by exact_mod_cast Nat.pos_of_ne_zero ha
    have e : (1 / 10 : ℝ) ^ (3 * p.2) = (1 / 1000 : ℝ) ^ p.2 := by rw [pow_mul]; norm_num
    rw [e]
    have : (p.2 : ℝ) / p.1 ≤ p.2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [(Nat.cast_nonneg p.2 : (0:ℝ) ≤ p.2)]
    exact mul_le_mul_of_nonneg_right this (by positivity)

lemma c3_le (p : ℕ × ℕ) : c3 p ≤ (p.2 : ℝ) / ((p.1 : ℝ) + p.2) * (1 / 10 : ℝ) ^ p.2 := by
  unfold c3
  split_ifs with h
  · positivity
  · exact le_rfl

lemma c3_le_one (p : ℕ × ℕ) : c3 p ≤ (1 / 10 : ℝ) ^ p.2 := by
  unfold c3
  split_ifs with h
  · positivity
  · rw [not_or] at h
    obtain ⟨ha, hn⟩ := h
    have ha' : (1 : ℝ) ≤ p.1 := by exact_mod_cast Nat.pos_of_ne_zero ha
    have : (p.2 : ℝ) / ((p.1 : ℝ) + p.2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc _ ≤ 1 * (1 / 10 : ℝ) ^ p.2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := one_mul _

lemma c3_le_row (p : ℕ × ℕ) : c3 p ≤ (p.2 : ℝ) / ((p.1 : ℝ) + 1) * (1 / 10 : ℝ) ^ p.2 := by
  unfold c3
  split_ifs with h
  · positivity
  · rw [not_or] at h
    obtain ⟨ha, hn⟩ := h
    have hn' : (1 : ℝ) ≤ p.2 := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : (p.2 : ℝ) / ((p.1 : ℝ) + p.2) ≤ (p.2 : ℝ) / ((p.1 : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)

lemma c23_le_five (p : ℕ × ℕ) : c23 p ≤ 2 * (1 / 5 : ℝ) ^ p.2 := by
  unfold c23
  have h2 := c2_le p
  have h3 := c3_le_one p
  have e1 : (p.2 : ℝ) * (1 / 1000 : ℝ) ^ p.2 ≤ (1 / 5 : ℝ) ^ p.2 := by
    have := nat_geom10 p.2
    have : (1 / 1000 : ℝ) ^ p.2 ≤ (1 / 10 : ℝ) ^ p.2 :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc (p.2 : ℝ) * (1 / 1000 : ℝ) ^ p.2 ≤ (p.2 : ℝ) * (1 / 10 : ℝ) ^ p.2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := nat_geom10 p.2
  have e2 : (1 / 10 : ℝ) ^ p.2 ≤ (1 / 5 : ℝ) ^ p.2 :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  linarith

/-! pointwise identities -/

noncomputable def F1 (x : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := wgt p * |x p.1| * |x (Nat.dist p.1 p.2)|
noncomputable def F2 (x : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := wgt p * |x p.1| * |x (p.1 + p.2)|
noncomputable def F1a (x : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := if p.1 < p.2 then F1 x p else 0
noncomputable def F1b (x : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := if p.2 < p.1 then F1 x p else 0

lemma F1_split (x : ℕ → ℝ) (h0 : x 0 = 0) (p : ℕ × ℕ) : F1 x p = F1a x p + F1b x p := by
  unfold F1a F1b
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · simp [h, not_lt.mpr h.le]
  · have : F1 x p = 0 := by simp [F1, h, h0, Nat.dist_self]
    simp [this, h]
  · simp [h, not_lt.mpr h.le]

lemma F1a_eq (x : ℕ → ℝ) (a n : ℕ) : F1a x (a, a + n) = c1 (a, n) * uu x a * uu x n := by
  by_cases ha : a = 0
  · simp [F1a, F1, c1, uu, wgt, ha]
  by_cases hn : n = 0
  · simp [F1a, c1, hn]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hlt : a < a + n := by omega
  have hd : Nat.dist a (a + n) = n := by
    rw [Nat.dist_eq_sub_of_le (Nat.le_add_right a n)]; omega
  simp only [F1a, F1, c1, uu, wgt, hlt, ite_true, hd, ha, hn, or_self, ite_false]
  have e : (1 / 100 : ℝ) ^ (a + (a + n)) = ((1 / 10 : ℝ) ^ a) ^ 4 * ((1 / 10 : ℝ) ^ n) ^ 2 := by
    rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num]
    generalize (1 / 10 : ℝ) = t
    ring
  rw [e, pow3]
  push_cast
  field_simp
  have e2 : (1 / 1000 : ℝ) ^ a = ((1 / 10 : ℝ) ^ a) ^ 3 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e2]
  ring

lemma F1b_eq (x : ℕ → ℝ) (a n : ℕ) : F1b x (a + n, n) = c2 (a, n) * uu x a * uu x (a + n) := by
  by_cases ha : a = 0
  · simp [F1b, c2, ha]
  by_cases hn : n = 0
  · simp [F1b, F1, c2, uu, wgt, hn]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hlt : n < a + n := by omega
  have hd : Nat.dist (a + n) n = a := by
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_add_left n a)]; omega
  simp only [F1b, F1, c2, uu, wgt, hlt, ite_true, hd, ha, hn, or_self, ite_false]
  have e : (1 / 100 : ℝ) ^ (a + n + n) = ((1 / 10 : ℝ) ^ a) ^ 2 * ((1 / 10 : ℝ) ^ n) ^ 4 := by
    rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num]
    generalize (1 / 10 : ℝ) = t
    ring
  have e2 : (1 / 10 : ℝ) ^ (3 * n) = ((1 / 10 : ℝ) ^ n) ^ 3 := by
    rw [← pow_mul, mul_comm]
  rw [e, e2, pow_add]
  push_cast
  field_simp
  try ring

lemma F2_eq (x : ℕ → ℝ) (a n : ℕ) : F2 x (a, n) = c3 (a, n) * uu x a * uu x (a + n) := by
  by_cases ha : a = 0
  · simp [F2, c3, wgt, ha]
  by_cases hn : n = 0
  · simp [F2, c3, wgt, hn]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hs : ((a : ℝ) + n) ≠ 0 := by positivity
  simp only [F2, c3, uu, wgt, ha, hn, or_self, ite_false]
  have e : (1 / 100 : ℝ) ^ (a + n) = ((1 / 10 : ℝ) ^ a) ^ 2 * ((1 / 10 : ℝ) ^ n) ^ 2 := by
    rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num]
    generalize (1 / 10 : ℝ) = t
    ring
  rw [e, pow_add]
  push_cast
  field_simp
  try ring

lemma amgm_tsum {ι : Type*} (c f g : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i)
    (h1 : Summable (fun i => c i * f i ^ 2)) (h2 : Summable (fun i => c i * g i ^ 2)) :
    Summable (fun i => c i * f i * g i) ∧
    ∑' i, c i * f i * g i ≤ (1 / 2) * (∑' i, c i * f i ^ 2 + ∑' i, c i * g i ^ 2) := by
  have hle : ∀ i, c i * f i * g i ≤ (1 / 2) * (c i * f i ^ 2 + c i * g i ^ 2) := by
    intro i; nlinarith [mul_nonneg (hc i) (sq_nonneg (f i - g i))]
  have hsum : Summable (fun i => (1 / 2) * (c i * f i ^ 2 + c i * g i ^ 2)) :=
    (h1.add h2).mul_left _
  have hs : Summable (fun i => c i * f i * g i) :=
    Summable.of_nonneg_of_le (fun i => by have := hc i; have := hf i; have := hg i; positivity)
      hle hsum
  refine ⟨hs, ?_⟩
  calc ∑' i, c i * f i * g i ≤ ∑' i, (1 / 2) * (c i * f i ^ 2 + c i * g i ^ 2) :=
        hs.tsum_le_tsum hle hsum
    _ = _ := by rw [tsum_mul_left, h1.tsum_add h2]

lemma tsum_row (c : ℕ × ℕ → ℝ) (v : ℕ → ℝ) (hs : Summable (fun p : ℕ × ℕ => c p * v p.1)) :
    ∑' p : ℕ × ℕ, c p * v p.1 = ∑' a : ℕ, (∑' n : ℕ, c (a, n)) * v a ∧
    Summable (fun a : ℕ => (∑' n : ℕ, c (a, n)) * v a) := by
  have h := hs.prod
  simp only [tsum_mul_right] at h
  refine ⟨?_, h⟩
  rw [hs.tsum_prod]
  simp only [tsum_mul_right]

lemma tsum_col (c : ℕ × ℕ → ℝ) (v : ℕ → ℝ) (hs : Summable (fun p : ℕ × ℕ => c p * v p.2)) :
    ∑' p : ℕ × ℕ, c p * v p.2 = ∑' n : ℕ, (∑' a : ℕ, c (a, n)) * v n ∧
    Summable (fun n : ℕ => (∑' a : ℕ, c (a, n)) * v n) := by
  have hs' : Summable (fun p : ℕ × ℕ => c p.swap * v p.1) := hs.prod_symm
  obtain ⟨h1, h2⟩ := tsum_row (fun p => c p.swap) v hs'
  refine ⟨?_, h2⟩
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ => c p * v p.2)]
  exact h1

lemma tsum_antidiag (G : ℕ × ℕ → ℝ) (hG : Summable G) :
    ∑' p, G p = ∑' m : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, G x ∧
    Summable (fun m : ℕ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, G x) := by
  have e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hs : Summable (fun σ => G (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ) σ)) :=
    (Equiv.summable_iff _).mpr hG
  have key : ∀ m : ℕ, ∑' c : (Finset.HasAntidiagonal.antidiagonal m : Finset (ℕ × ℕ)),
      G (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ) ⟨m, c⟩)
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, G x := by
    intro m
    rw [tsum_fintype]
    simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    exact Finset.sum_coe_sort _ G
  have h1 := hs.tsum_sigma
  have h2 := hs.sigma
  simp only [key] at h1 h2
  refine ⟨?_, h2⟩
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq G]
  exact h1

lemma geom10_tsum : ∑' n : ℕ, (1 / 10 : ℝ) ^ n = 10 / 9 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

lemma summable_geom10 : Summable (fun n : ℕ => (1 / 10 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma summable_nat_geom (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)

lemma tsum_nat_geom (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∑' n : ℕ, (n : ℝ) * r ^ n = r / (1 - r) ^ 2 :=
  tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)

lemma tsum_nat_geom_tenth : ∑' n : ℕ, (n : ℝ) * (1 / 10 : ℝ) ^ n = 10 / 81 := by
  rw [tsum_nat_geom _ (by norm_num) (by norm_num)]; norm_num

lemma tsum_nat_geom_milli : ∑' n : ℕ, (n : ℝ) * (1 / 1000 : ℝ) ^ n = 1000 / 998001 := by
  rw [tsum_nat_geom _ (by norm_num) (by norm_num)]; norm_num

/-- rows of `c1` -/
lemma c1_row_summable (a : ℕ) : Summable (fun n : ℕ => c1 (a, n)) :=
  Summable.of_nonneg_of_le (fun n => c1_nonneg _) (fun n => c1_le (a, n))
    (summable_geom10.mul_left ((1 / 500 : ℝ) ^ a))

lemma c1_row_le (a : ℕ) (ha : 1 ≤ a) : ∑' n : ℕ, c1 (a, n) ≤ 1 / 450 := by
  calc ∑' n : ℕ, c1 (a, n) ≤ ∑' n : ℕ, (1 / 500 : ℝ) ^ a * (1 / 10 : ℝ) ^ n :=
        (c1_row_summable a).tsum_le_tsum (fun n => c1_le (a, n))
          (summable_geom10.mul_left ((1 / 500 : ℝ) ^ a))
    _ = (1 / 500 : ℝ) ^ a * (10 / 9) := by rw [tsum_mul_left, geom10_tsum]
    _ ≤ (1 / 500 : ℝ) * (10 / 9) :=
        mul_le_mul_of_nonneg_right (pow_le_of_le_one (by norm_num) (by norm_num) (by omega))
          (by norm_num)
    _ = 1 / 450 := by norm_num

/-- columns of `c1` -/
lemma c1_col_summable (n : ℕ) : Summable (fun a : ℕ => c1 (a, n)) :=
  Summable.of_nonneg_of_le (fun a => c1_nonneg _) (fun a => c1_le (a, n))
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right ((1 / 10 : ℝ) ^ n))

lemma c1_col_le (n : ℕ) (hn : 1 ≤ n) : ∑' a : ℕ, c1 (a, n) ≤ 1 / 4990 := by
  rw [(c1_col_summable n).tsum_eq_zero_add]
  have h0 : c1 (0, n) = 0 := by simp [c1]
  rw [h0, zero_add]
  have hs : Summable (fun a : ℕ => c1 (a + 1, n)) :=
    (summable_nat_add_iff 1).mpr (c1_col_summable n)
  have hg0 : Summable (fun a : ℕ => (1 / 500 : ℝ) ^ a) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg : Summable (fun a : ℕ => (1 / 500 : ℝ) ^ (a + 1) * (1 / 10 : ℝ) ^ n) := by
    simp_rw [pow_succ]
    exact (hg0.mul_right _).mul_right _
  have hsum : ∑' a : ℕ, (1 / 500 : ℝ) ^ (a + 1) = 1 / 499 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  calc ∑' a : ℕ, c1 (a + 1, n) ≤ ∑' a : ℕ, (1 / 500 : ℝ) ^ (a + 1) * (1 / 10 : ℝ) ^ n :=
        hs.tsum_le_tsum (fun a => c1_le (a + 1, n)) hg
    _ = (1 / 499) * (1 / 10 : ℝ) ^ n := by rw [tsum_mul_right, hsum]
    _ ≤ (1 / 499) * (1 / 10) :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one (by norm_num) (by norm_num) (by omega))
          (by norm_num)
    _ = 1 / 4990 := by norm_num

/-- rows of `c23` -/
lemma c23_row_pt (a n : ℕ) : c23 (a, n) ≤
    (n : ℝ) * (1 / 1000 : ℝ) ^ n + (1 / ((a : ℝ) + 1)) * ((n : ℝ) * (1 / 10 : ℝ) ^ n) := by
  have h2 := c2_le (a, n)
  have h3 := c3_le_row (a, n)
  unfold c23
  have : (n : ℝ) / ((a : ℝ) + 1) * (1 / 10 : ℝ) ^ n
      = (1 / ((a : ℝ) + 1)) * ((n : ℝ) * (1 / 10 : ℝ) ^ n) := by ring
  simp only at h2 h3
  linarith

lemma c23_row_summable (a : ℕ) : Summable (fun n : ℕ => c23 (a, n)) :=
  Summable.of_nonneg_of_le (fun n => c23_nonneg _) (fun n => c23_row_pt a n)
    ((summable_nat_geom _ (by norm_num) (by norm_num)).add
      ((summable_nat_geom _ (by norm_num) (by norm_num)).mul_left _))

lemma c23_row_le (a : ℕ) :
    ∑' n : ℕ, c23 (a, n) ≤ 1000 / 998001 + (10 / 81) / ((a : ℝ) + 1) := by
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * (1 / 1000 : ℝ) ^ n) :=
    summable_nat_geom _ (by norm_num) (by norm_num)
  have hs2 : Summable (fun n : ℕ => (1 / ((a : ℝ) + 1)) * ((n : ℝ) * (1 / 10 : ℝ) ^ n)) :=
    (summable_nat_geom _ (by norm_num) (by norm_num)).mul_left _
  calc ∑' n : ℕ, c23 (a, n)
      ≤ ∑' n : ℕ, ((n : ℝ) * (1 / 1000 : ℝ) ^ n
          + (1 / ((a : ℝ) + 1)) * ((n : ℝ) * (1 / 10 : ℝ) ^ n)) :=
        (c23_row_summable a).tsum_le_tsum (fun n => c23_row_pt a n) (hs1.add hs2)
    _ = 1000 / 998001 + (10 / 81) / ((a : ℝ) + 1) := by
        rw [hs1.tsum_add hs2, tsum_mul_left, tsum_nat_geom_tenth, tsum_nat_geom_milli]
        ring

/-- antidiagonals -/
lemma sum_antidiag_snd (F : ℕ → ℝ) (m : ℕ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, F x.2 = ∑ k ∈ Finset.range (m + 1), F k := by
  have h := Finset.Nat.sum_antidiagonal_swap (n := m) (f := fun x : ℕ × ℕ => F x.1)
  simp only [Prod.fst_swap] at h
  rw [h]
  have := Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => F i) m
  simpa using this

lemma c23_col_gen (m : ℕ) (hm : 1 ≤ m) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, c23 x ≤ 1000 / 998001 + (10 / 81) / (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal m, c23 x ≤
      (fun k : ℕ => (k : ℝ) * (1 / 1000 : ℝ) ^ k + (1 / (m : ℝ)) * ((k : ℝ) * (1 / 10 : ℝ) ^ k)) x.2 := by
    intro x hx
    have hxm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hxm' : (x.1 : ℝ) + x.2 = m := by exact_mod_cast hxm
    have h2 := c2_le x
    have h3 := c3_le x
    rw [hxm'] at h3
    have : (x.2 : ℝ) / m * (1 / 10 : ℝ) ^ x.2 = (1 / (m : ℝ)) * ((x.2 : ℝ) * (1 / 10 : ℝ) ^ x.2) := by
      ring
    unfold c23
    simp only []
    linarith
  refine (Finset.sum_le_sum step).trans ?_
  rw [sum_antidiag_snd (fun k : ℕ => (k : ℝ) * (1 / 1000 : ℝ) ^ k
    + (1 / (m : ℝ)) * ((k : ℝ) * (1 / 10 : ℝ) ^ k)) m]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * (1 / 1000 : ℝ) ^ n) :=
    summable_nat_geom _ (by norm_num) (by norm_num)
  have hs2 : Summable (fun n : ℕ => (n : ℝ) * (1 / 10 : ℝ) ^ n) :=
    summable_nat_geom _ (by norm_num) (by norm_num)
  have e1 := hs1.sum_le_tsum (Finset.range (m + 1)) (fun i _ => by positivity)
  have e2 := hs2.sum_le_tsum (Finset.range (m + 1)) (fun i _ => by positivity)
  rw [tsum_nat_geom_milli] at e1
  rw [tsum_nat_geom_tenth] at e2
  have : (1 / (m : ℝ)) * (∑ k ∈ Finset.range (m + 1), (k : ℝ) * (1 / 10 : ℝ) ^ k)
      ≤ (1 / (m : ℝ)) * (10 / 81) := mul_le_mul_of_nonneg_left e2 (by positivity)
  calc _ ≤ 1000 / 998001 + (1 / (m : ℝ)) * (10 / 81) := by linarith
    _ = _ := by ring

lemma c23_col_one : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal 1, c23 x = 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, c23, c2, c3]

lemma c23_col_two : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal 2, c23 x = 51 / 1000 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, c23, c2, c3]
  norm_num

noncomputable def R1 (a : ℕ) : ℝ := ∑' n : ℕ, c1 (a, n)
noncomputable def C1 (a : ℕ) : ℝ := ∑' b : ℕ, c1 (b, a)
noncomputable def R23 (a : ℕ) : ℝ := ∑' n : ℕ, c23 (a, n)
noncomputable def C23 (a : ℕ) : ℝ := ∑ x ∈ Finset.HasAntidiagonal.antidiagonal a, c23 x

section
variable (x : ℕ → ℝ) {K : ℝ}

lemma F1_nonneg (p : ℕ × ℕ) : 0 ≤ F1 x p := by unfold F1; have := wgt_nonneg p; positivity
lemma F2_nonneg (p : ℕ × ℕ) : 0 ≤ F2 x p := by unfold F2; have := wgt_nonneg p; positivity

lemma F1_le (hK : ∀ j, |x j| ≤ K) (p : ℕ × ℕ) : F1 x p ≤ K ^ 2 * wgt p := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have h := mul_le_mul (hK p.1) (hK (Nat.dist p.1 p.2)) (abs_nonneg _) hK0
  have hw := wgt_nonneg p
  unfold F1
  calc wgt p * |x p.1| * |x (Nat.dist p.1 p.2)| = wgt p * (|x p.1| * |x (Nat.dist p.1 p.2)|) := by ring
    _ ≤ wgt p * (K * K) := mul_le_mul_of_nonneg_left h hw
    _ = K ^ 2 * wgt p := by ring

lemma F2_le (hK : ∀ j, |x j| ≤ K) (p : ℕ × ℕ) : F2 x p ≤ K ^ 2 * wgt p := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have h := mul_le_mul (hK p.1) (hK (p.1 + p.2)) (abs_nonneg _) hK0
  have hw := wgt_nonneg p
  unfold F2
  calc wgt p * |x p.1| * |x (p.1 + p.2)| = wgt p * (|x p.1| * |x (p.1 + p.2)|) := by ring
    _ ≤ wgt p * (K * K) := mul_le_mul_of_nonneg_left h hw
    _ = K ^ 2 * wgt p := by ring

lemma summable_F1 (hK : ∀ j, |x j| ≤ K) : Summable (F1 x) :=
  Summable.of_nonneg_of_le (F1_nonneg x) (F1_le x hK) (summable_wgt.mul_left _)

lemma summable_F2 (hK : ∀ j, |x j| ≤ K) : Summable (F2 x) :=
  Summable.of_nonneg_of_le (F2_nonneg x) (F2_le x hK) (summable_wgt.mul_left _)

lemma F1a_nonneg (p : ℕ × ℕ) : 0 ≤ F1a x p := by
  unfold F1a; split_ifs
  · exact F1_nonneg x p
  · exact le_rfl
lemma F1b_nonneg (p : ℕ × ℕ) : 0 ≤ F1b x p := by
  unfold F1b; split_ifs
  · exact F1_nonneg x p
  · exact le_rfl

lemma summable_F1a (hK : ∀ j, |x j| ≤ K) : Summable (F1a x) :=
  Summable.of_nonneg_of_le (F1a_nonneg x) (fun p => by
    unfold F1a; split_ifs
    · exact le_rfl
    · exact F1_nonneg x p) (summable_F1 x hK)

lemma summable_F1b (hK : ∀ j, |x j| ≤ K) : Summable (F1b x) :=
  Summable.of_nonneg_of_le (F1b_nonneg x) (fun p => by
    unfold F1b; split_ifs
    · exact le_rfl
    · exact F1_nonneg x p) (summable_F1 x hK)

lemma inj_phi1 : Function.Injective (fun q : ℕ × ℕ => (q.1, q.1 + q.2)) := by
  intro q r h
  simp only [Prod.mk.injEq] at h
  ext <;> omega

lemma inj_phi2 : Function.Injective (fun q : ℕ × ℕ => (q.1 + q.2, q.2)) := by
  intro q r h
  simp only [Prod.mk.injEq] at h
  ext <;> omega

lemma S_eq (hK : ∀ j, |x j| ≤ K) (h0 : x 0 = 0) :
    ∑' p : ℕ × ℕ, (F1 x p + F2 x p) =
      ∑' q : ℕ × ℕ, c1 q * uu x q.1 * uu x q.2 +
      ∑' q : ℕ × ℕ, c23 q * uu x q.1 * uu x (q.1 + q.2) := by
  have e1 : ∑' q : ℕ × ℕ, F1a x (q.1, q.1 + q.2) = ∑' p, F1a x p := by
    refine inj_phi1.tsum_eq (f := F1a x) ?_
    intro p hp
    have hp' : F1a x p ≠ 0 := hp
    have hlt : p.1 < p.2 := by
      by_contra hn
      apply hp'
      simp [F1a, hn]
    exact ⟨(p.1, p.2 - p.1), by ext <;> simp <;> omega⟩
  have e2 : ∑' q : ℕ × ℕ, F1b x (q.1 + q.2, q.2) = ∑' p, F1b x p := by
    refine inj_phi2.tsum_eq (f := F1b x) ?_
    intro p hp
    have hp' : F1b x p ≠ 0 := hp
    have hlt : p.2 < p.1 := by
      by_contra hn
      apply hp'
      simp [F1b, hn]
    exact ⟨(p.1 - p.2, p.2), by ext <;> simp <;> omega⟩
  have hs1 : Summable (fun q : ℕ × ℕ => c1 q * uu x q.1 * uu x q.2) := by
    have := (summable_F1a x hK).comp_injective inj_phi1
    convert this using 1
    funext q; exact (F1a_eq x q.1 q.2).symm
  have hs2 : Summable (fun q : ℕ × ℕ => c2 q * uu x q.1 * uu x (q.1 + q.2)) := by
    have := (summable_F1b x hK).comp_injective inj_phi2
    convert this using 1
    funext q; exact (F1b_eq x q.1 q.2).symm
  have hs3 : Summable (fun q : ℕ × ℕ => c3 q * uu x q.1 * uu x (q.1 + q.2)) := by
    convert summable_F2 x hK using 1
    funext q; exact (F2_eq x q.1 q.2).symm
  have hsplit : ∀ p, F1 x p + F2 x p = F1a x p + F1b x p + F2 x p := by
    intro p; rw [F1_split x h0 p]
  calc ∑' p : ℕ × ℕ, (F1 x p + F2 x p)
      = ∑' p : ℕ × ℕ, ((F1a x p + F1b x p) + F2 x p) := by
        congr 1; funext p; exact hsplit p
    _ = ∑' p, F1a x p + ∑' p, F1b x p + ∑' p, F2 x p := by
        rw [((summable_F1a x hK).add (summable_F1b x hK)).tsum_add (summable_F2 x hK),
          (summable_F1a x hK).tsum_add (summable_F1b x hK)]
    _ = ∑' q : ℕ × ℕ, c1 q * uu x q.1 * uu x q.2 +
        (∑' q : ℕ × ℕ, c2 q * uu x q.1 * uu x (q.1 + q.2) +
          ∑' q : ℕ × ℕ, c3 q * uu x q.1 * uu x (q.1 + q.2)) := by
        rw [← e1, ← e2]
        have a1 : ∑' q : ℕ × ℕ, F1a x (q.1, q.1 + q.2)
            = ∑' q : ℕ × ℕ, c1 q * uu x q.1 * uu x q.2 := by
          congr 1; funext q; exact F1a_eq x q.1 q.2
        have a2 : ∑' q : ℕ × ℕ, F1b x (q.1 + q.2, q.2)
            = ∑' q : ℕ × ℕ, c2 q * uu x q.1 * uu x (q.1 + q.2) := by
          congr 1; funext q; exact F1b_eq x q.1 q.2
        have a3 : ∑' p : ℕ × ℕ, F2 x p
            = ∑' q : ℕ × ℕ, c3 q * uu x q.1 * uu x (q.1 + q.2) := by
          congr 1; funext q; exact F2_eq x q.1 q.2
        rw [a1, a2, a3]; ring
    _ = _ := by
        rw [← hs2.tsum_add hs3]
        congr 2
        funext q
        unfold c23; ring

end

section
variable (x : ℕ → ℝ) {K : ℝ}

lemma c1_le_tenth (p : ℕ × ℕ) : c1 p ≤ (1 / 10 : ℝ) ^ p.2 := by
  have h1 : (1 / 500 : ℝ) ^ p.1 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc c1 p ≤ (1 / 500 : ℝ) ^ p.1 * (1 / 10 : ℝ) ^ p.2 := c1_le p
    _ ≤ 1 * (1 / 10 : ℝ) ^ p.2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := one_mul _

lemma S1 (hK : ∀ j, |x j| ≤ K) : Summable (fun q : ℕ × ℕ => c1 q * uu x q.1 ^ 2) := by
  refine summable_of_geom _ (K ^ 2) (1 / 25) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun q => by have := c1_nonneg q; positivity) (fun q => ?_)
  have h := mul_le_mul (c1_le_tenth q) (uu_sq_le x hK q.1) (sq_nonneg _) (by positivity)
  calc c1 q * uu x q.1 ^ 2 ≤ (1 / 10 : ℝ) ^ q.2 * (K ^ 2 * (1 / 25 : ℝ) ^ q.1) := h
    _ = K ^ 2 * ((1 / 25 : ℝ) ^ q.1 * (1 / 10 : ℝ) ^ q.2) := by ring

lemma S2 (hK : ∀ j, |x j| ≤ K) : Summable (fun q : ℕ × ℕ => c1 q * uu x q.2 ^ 2) := by
  refine summable_of_geom _ (K ^ 2) (1 / 500) (1 / 250) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun q => by have := c1_nonneg q; positivity) (fun q => ?_)
  have h := mul_le_mul (c1_le q) (uu_sq_le x hK q.2) (sq_nonneg _) (by positivity)
  have e : (1 / 10 : ℝ) ^ q.2 * (1 / 25 : ℝ) ^ q.2 = (1 / 250 : ℝ) ^ q.2 := by
    rw [← mul_pow]; norm_num
  calc c1 q * uu x q.2 ^ 2 ≤ ((1 / 500 : ℝ) ^ q.1 * (1 / 10 : ℝ) ^ q.2) * (K ^ 2 * (1 / 25 : ℝ) ^ q.2) := h
    _ = K ^ 2 * ((1 / 500 : ℝ) ^ q.1 * ((1 / 10 : ℝ) ^ q.2 * (1 / 25 : ℝ) ^ q.2)) := by ring
    _ = K ^ 2 * ((1 / 500 : ℝ) ^ q.1 * (1 / 250 : ℝ) ^ q.2) := by rw [e]

lemma S3 (hK : ∀ j, |x j| ≤ K) : Summable (fun q : ℕ × ℕ => c23 q * uu x q.1 ^ 2) := by
  refine summable_of_geom _ (2 * K ^ 2) (1 / 25) (1 / 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun q => by have := c23_nonneg q; positivity) (fun q => ?_)
  have h := mul_le_mul (c23_le_five q) (uu_sq_le x hK q.1) (sq_nonneg _) (by positivity)
  calc c23 q * uu x q.1 ^ 2 ≤ (2 * (1 / 5 : ℝ) ^ q.2) * (K ^ 2 * (1 / 25 : ℝ) ^ q.1) := by
        rw [mul_comm (c23 q)]; rw [mul_comm (uu x q.1 ^ 2)]
        simpa [mul_comm] using h
    _ = (2 * K ^ 2) * ((1 / 25 : ℝ) ^ q.1 * (1 / 5 : ℝ) ^ q.2) := by ring

lemma S4 (hK : ∀ j, |x j| ≤ K) :
    Summable (fun q : ℕ × ℕ => c23 q * uu x (q.1 + q.2) ^ 2) := by
  refine summable_of_geom _ (2 * K ^ 2) (1 / 25) (1 / 125) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun q => by have := c23_nonneg q; positivity) (fun q => ?_)
  have h := mul_le_mul (c23_le_five q) (uu_sq_le x hK (q.1 + q.2)) (sq_nonneg _) (by positivity)
  have e : (1 / 5 : ℝ) ^ q.2 * (1 / 25 : ℝ) ^ q.2 = (1 / 125 : ℝ) ^ q.2 := by
    rw [← mul_pow]; norm_num
  calc c23 q * uu x (q.1 + q.2) ^ 2
      ≤ (2 * (1 / 5 : ℝ) ^ q.2) * (K ^ 2 * (1 / 25 : ℝ) ^ (q.1 + q.2)) := h
    _ = (2 * K ^ 2) * ((1 / 25 : ℝ) ^ q.1 * ((1 / 5 : ℝ) ^ q.2 * (1 / 25 : ℝ) ^ q.2)) := by
        rw [pow_add]; ring
    _ = (2 * K ^ 2) * ((1 / 25 : ℝ) ^ q.1 * (1 / 125 : ℝ) ^ q.2) := by rw [e]

lemma S_half (hK : ∀ j, |x j| ≤ K) (h0 : x 0 = 0) :
    ∑' p : ℕ × ℕ, (F1 x p + F2 x p) ≤
      (1 / 2) * (∑' q : ℕ × ℕ, c1 q * uu x q.1 ^ 2 + ∑' q : ℕ × ℕ, c1 q * uu x q.2 ^ 2) +
      (1 / 2) * (∑' q : ℕ × ℕ, c23 q * uu x q.1 ^ 2 +
        ∑' q : ℕ × ℕ, c23 q * uu x (q.1 + q.2) ^ 2) := by
  rw [S_eq x hK h0]
  have a1 := amgm_tsum c1 (fun q : ℕ × ℕ => uu x q.1) (fun q : ℕ × ℕ => uu x q.2) c1_nonneg
    (fun q => uu_nonneg x _) (fun q => uu_nonneg x _) (S1 x hK) (S2 x hK)
  have a2 := amgm_tsum c23 (fun q : ℕ × ℕ => uu x q.1) (fun q : ℕ × ℕ => uu x (q.1 + q.2))
    c23_nonneg (fun q => uu_nonneg x _) (fun q => uu_nonneg x _) (S3 x hK) (S4 x hK)
  linarith [a1.2, a2.2]

lemma S_core (hK : ∀ j, |x j| ≤ K) (h0 : x 0 = 0) :
    ∑' p : ℕ × ℕ, (F1 x p + F2 x p) ≤
      ∑' a : ℕ, ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 ∧
    Summable (fun a : ℕ => ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2) := by
  have r1 := tsum_row c1 (fun a => uu x a ^ 2) (S1 x hK)
  have k1 := tsum_col c1 (fun a => uu x a ^ 2) (S2 x hK)
  have r2 := tsum_row c23 (fun a => uu x a ^ 2) (S3 x hK)
  have k2 := tsum_antidiag (fun q : ℕ × ℕ => c23 q * uu x (q.1 + q.2) ^ 2) (S4 x hK)
  have k2' : ∀ m : ℕ, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal m, c23 y * uu x (y.1 + y.2) ^ 2
      = C23 m * uu x m ^ 2 := by
    intro m
    unfold C23
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hy]
  simp only [k2'] at k2
  have s1 : Summable (fun a : ℕ => R1 a * uu x a ^ 2) := r1.2
  have s2 : Summable (fun a : ℕ => C1 a * uu x a ^ 2) := k1.2
  have s3 : Summable (fun a : ℕ => R23 a * uu x a ^ 2) := r2.2
  have s4 : Summable (fun a : ℕ => C23 a * uu x a ^ 2) := k2.2
  have hsumm : Summable (fun a : ℕ => ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2) := by
    have := (((s1.add s2).add s3).add s4).mul_left (1 / 2)
    convert this using 1
    funext a; ring
  refine ⟨?_, hsumm⟩
  have heq : ∑' a : ℕ, ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 =
      (1 / 2) * (∑' a, R1 a * uu x a ^ 2 + ∑' a, C1 a * uu x a ^ 2 +
        ∑' a, R23 a * uu x a ^ 2 + ∑' a, C23 a * uu x a ^ 2) := by
    have : ∀ a : ℕ, ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 =
        (1 / 2) * (R1 a * uu x a ^ 2 + C1 a * uu x a ^ 2 + R23 a * uu x a ^ 2
          + C23 a * uu x a ^ 2) := fun a => by ring
    simp_rw [this]
    rw [tsum_mul_left, ((s1.add s2).add s3).tsum_add s4, (s1.add s2).tsum_add s3,
      s1.tsum_add s2]
  rw [heq]
  have h := S_half x hK h0
  have e1 : ∑' q : ℕ × ℕ, c1 q * uu x q.1 ^ 2 = ∑' a, R1 a * uu x a ^ 2 := r1.1
  have e2 : ∑' q : ℕ × ℕ, c1 q * uu x q.2 ^ 2 = ∑' a, C1 a * uu x a ^ 2 := k1.1
  have e3 : ∑' q : ℕ × ℕ, c23 q * uu x q.1 ^ 2 = ∑' a, R23 a * uu x a ^ 2 := r2.1
  have e4 : ∑' q : ℕ × ℕ, c23 q * uu x (q.1 + q.2) ^ 2 = ∑' a, C23 a * uu x a ^ 2 := k2.1
  rw [e1, e2, e3, e4] at h
  linarith

end

lemma tot_bound (a : ℕ) (ha : 1 ≤ a) :
    (1 / 2) * (R1 a + C1 a + R23 a + C23 a) + (1 / 10 : ℝ) ^ a / 9 ≤ 107 / 2000 := by
  have h1 : R1 a ≤ 1 / 450 := c1_row_le a ha
  have h2 : C1 a ≤ 1 / 4990 := c1_col_le a ha
  have h3 : R23 a ≤ 1000 / 998001 + (10 / 81) / ((a : ℝ) + 1) := c23_row_le a
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | h
  · have h4 : C23 1 = 0 := c23_col_one
    rw [h4]
    norm_num at h3 ⊢
    linarith
  · have h4 : C23 2 = 51 / 1000 := c23_col_two
    rw [h4]
    norm_num at h3 ⊢
    linarith
  · have hm : (3 : ℝ) ≤ a := by exact_mod_cast h
    have h4 : C23 a ≤ 1000 / 998001 + (10 / 81) / (a : ℝ) := c23_col_gen a ha
    have h5 : (10 / 81 : ℝ) / (a : ℝ) ≤ (10 / 81) / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
    have h6 : (10 / 81 : ℝ) / ((a : ℝ) + 1) ≤ (10 / 81) / 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h7 : (1 / 10 : ℝ) ^ a ≤ 1 / 10 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have h8 : C23 a ≤ 1000 / 998001 + (10 / 81) / 3 := by linarith
    have h9 : R23 a ≤ 1000 / 998001 + (10 / 81) / 4 := by linarith
    norm_num at h8 h9 ⊢
    linarith

noncomputable def c0 (p : ℕ × ℕ) : ℝ := if p.1 = 0 ∨ p.2 = 0 then 0 else (1 / 10 : ℝ) ^ (p.1 + p.2)

lemma c0_nonneg (p : ℕ × ℕ) : 0 ≤ c0 p := by unfold c0; split_ifs <;> positivity

lemma c0_le (p : ℕ × ℕ) : c0 p ≤ (1 / 10 : ℝ) ^ p.1 * (1 / 10 : ℝ) ^ p.2 := by
  unfold c0; split_ifs
  · positivity
  · rw [pow_add]

lemma c0_comm (a n : ℕ) : c0 (a, n) = c0 (n, a) := by
  unfold c0; simp only [or_comm, add_comm]

lemma c0_row (a : ℕ) (ha : a ≠ 0) : ∑' n : ℕ, c0 (a, n) = (1 / 10 : ℝ) ^ a / 9 := by
  have hs : Summable (fun n : ℕ => c0 (a, n)) :=
    Summable.of_nonneg_of_le (fun n => c0_nonneg _) (fun n => c0_le (a, n))
      (summable_geom10.mul_left ((1 / 10 : ℝ) ^ a))
  rw [hs.tsum_eq_zero_add]
  have h0 : c0 (a, 0) = 0 := by simp [c0]
  rw [h0, zero_add]
  have : ∀ n : ℕ, c0 (a, n + 1) = (1 / 10 : ℝ) ^ a * (1 / 10 : ℝ) * (1 / 10 : ℝ) ^ n := by
    intro n
    simp [c0, ha, pow_add]
    ring
  simp_rw [this]
  rw [tsum_mul_left, geom10_tsum]
  ring

lemma c0_col (n : ℕ) (hn : n ≠ 0) : ∑' a : ℕ, c0 (a, n) = (1 / 10 : ℝ) ^ n / 9 := by
  simp_rw [c0_comm]
  exact c0_row n hn

lemma abs_tsum_le_of_le {ι : Type*} (f g : ι → ℝ) (hf : Summable f) (hg : Summable g)
    (h : ∀ i, |f i| ≤ g i) : |∑' i, f i| ≤ ∑' i, g i := by
  have hf' : Summable (fun i => ‖f i‖) := by simpa [Real.norm_eq_abs] using hf.abs
  calc |∑' i, f i| = ‖∑' i, f i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm hf'
    _ ≤ ∑' i, g i := hf'.tsum_le_tsum (fun i => by simpa [Real.norm_eq_abs] using h i) hg

section
variable (y : ℕ → ℝ) {K : ℝ}

lemma summable_sU (hK : ∀ j, |y j| ≤ K) : Summable (fun j : ℕ => (1 / 10 : ℝ) ^ j * uu y j) := by
  refine Summable.of_nonneg_of_le (fun j => by have := uu_nonneg y j; positivity) (fun j => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 50) (by norm_num)).mul_left K)
  have h := mul_le_mul_of_nonneg_left (uu_le y hK j) (by positivity : (0 : ℝ) ≤ (1 / 10 : ℝ) ^ j)
  have e : (1 / 10 : ℝ) ^ j * (1 / 5 : ℝ) ^ j = (1 / 50 : ℝ) ^ j := by rw [← mul_pow]; norm_num
  calc (1 / 10 : ℝ) ^ j * uu y j ≤ (1 / 10 : ℝ) ^ j * (K * (1 / 5 : ℝ) ^ j) := h
    _ = K * ((1 / 10 : ℝ) ^ j * (1 / 5 : ℝ) ^ j) := by ring
    _ = K * (1 / 50 : ℝ) ^ j := by rw [e]

lemma rank1_bound (hK : ∀ j, |y j| ≤ K) (hy0 : y 0 = 0) :
    (∑' j : ℕ, (1 / 10 : ℝ) ^ j * uu y j) ^ 2 ≤ ∑' a : ℕ, ((1 / 10 : ℝ) ^ a / 9) * uu y a ^ 2 ∧
    Summable (fun a : ℕ => ((1 / 10 : ℝ) ^ a / 9) * uu y a ^ 2) := by
  have sU := summable_sU y hK
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  have T1 : Summable (fun q : ℕ × ℕ => c0 q * uu y q.1 ^ 2) := by
    refine summable_of_geom _ (K ^ 2) (1 / 250) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (fun q => by have := c0_nonneg q; positivity) (fun q => ?_)
    have h := mul_le_mul (c0_le q) (uu_sq_le y hK q.1) (sq_nonneg _) (by positivity)
    have e : (1 / 10 : ℝ) ^ q.1 * (1 / 25 : ℝ) ^ q.1 = (1 / 250 : ℝ) ^ q.1 := by
      rw [← mul_pow]; norm_num
    calc c0 q * uu y q.1 ^ 2 ≤ ((1 / 10 : ℝ) ^ q.1 * (1 / 10 : ℝ) ^ q.2) *
          (K ^ 2 * (1 / 25 : ℝ) ^ q.1) := h
      _ = K ^ 2 * (((1 / 10 : ℝ) ^ q.1 * (1 / 25 : ℝ) ^ q.1) * (1 / 10 : ℝ) ^ q.2) := by ring
      _ = K ^ 2 * ((1 / 250 : ℝ) ^ q.1 * (1 / 10 : ℝ) ^ q.2) := by rw [e]
  have T2 : Summable (fun q : ℕ × ℕ => c0 q * uu y q.2 ^ 2) := by
    refine summable_of_geom _ (K ^ 2) (1 / 10) (1 / 250) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (fun q => by have := c0_nonneg q; positivity) (fun q => ?_)
    have h := mul_le_mul (c0_le q) (uu_sq_le y hK q.2) (sq_nonneg _) (by positivity)
    have e : (1 / 10 : ℝ) ^ q.2 * (1 / 25 : ℝ) ^ q.2 = (1 / 250 : ℝ) ^ q.2 := by
      rw [← mul_pow]; norm_num
    calc c0 q * uu y q.2 ^ 2 ≤ ((1 / 10 : ℝ) ^ q.1 * (1 / 10 : ℝ) ^ q.2) *
          (K ^ 2 * (1 / 25 : ℝ) ^ q.2) := h
      _ = K ^ 2 * ((1 / 10 : ℝ) ^ q.1 * ((1 / 10 : ℝ) ^ q.2 * (1 / 25 : ℝ) ^ q.2)) := by ring
      _ = K ^ 2 * ((1 / 10 : ℝ) ^ q.1 * (1 / 250 : ℝ) ^ q.2) := by rw [e]
  have a1 := amgm_tsum c0 (fun q : ℕ × ℕ => uu y q.1) (fun q : ℕ × ℕ => uu y q.2) c0_nonneg
    (fun q => uu_nonneg y _) (fun q => uu_nonneg y _) T1 T2
  have r1 := tsum_row c0 (fun a => uu y a ^ 2) T1
  have k1 := tsum_col c0 (fun a => uu y a ^ 2) T2
  have g1 : ∀ a : ℕ, (∑' n : ℕ, c0 (a, n)) * uu y a ^ 2 = ((1 / 10 : ℝ) ^ a / 9) * uu y a ^ 2 := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [uu_zero]
    · rw [c0_row a ha]
  have g2 : ∀ a : ℕ, (∑' n : ℕ, c0 (n, a)) * uu y a ^ 2 = ((1 / 10 : ℝ) ^ a / 9) * uu y a ^ 2 := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [uu_zero]
    · rw [c0_col a ha]
  simp only [g1] at r1
  simp only [g2] at k1
  -- product formula
  have hprod : Summable (fun p : ℕ × ℕ => ((1 / 10 : ℝ) ^ p.1 * uu y p.1) *
      ((1 / 10 : ℝ) ^ p.2 * uu y p.2)) := by
    have h2 : Summable (fun a : ℕ => ‖(1 / 10 : ℝ) ^ a * uu y a‖) := by
      simpa [Real.norm_eq_abs] using sU.abs
    exact summable_mul_of_summable_norm (f := fun a : ℕ => (1 / 10 : ℝ) ^ a * uu y a)
      (g := fun a : ℕ => (1 / 10 : ℝ) ^ a * uu y a) h2 h2
  have hsq : (∑' j : ℕ, (1 / 10 : ℝ) ^ j * uu y j) ^ 2 =
      ∑' q : ℕ × ℕ, c0 q * uu y q.1 * uu y q.2 := by
    rw [sq, sU.tsum_mul_tsum sU hprod]
    congr 1; funext q
    unfold c0
    by_cases h1 : q.1 = 0
    · simp [h1, uu_zero]
    by_cases h2 : q.2 = 0
    · simp [h2, uu_zero]
    simp only [h1, h2, or_self, ite_false, pow_add]
    ring
  refine ⟨?_, r1.2⟩
  rw [hsq]
  have := a1.2
  rw [r1.1, k1.1] at this
  linarith

end

lemma norm_sum_le (y : ℕ → ℝ) {K : ℝ} (hK : ∀ j, |y j| ≤ K) :
    (∑' j : ℕ, (j : ℝ) * (1 / 100 : ℝ) ^ j * y j) ^ 2 ≤
      (∑' j : ℕ, (1 / 10 : ℝ) ^ j * uu y j) ^ 2 := by
  have hsum := summable_lin_terms y ⟨K, hK⟩
  have hU := summable_sU y hK
  have hle := abs_tsum_le_of_le _ _ hsum hU (fun j => by
    have e : (1 / 100 : ℝ) ^ j = (1 / 10 : ℝ) ^ j * (1 / 10 : ℝ) ^ j := by
      rw [← mul_pow]; norm_num
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j : ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 / 100 : ℝ) ^ j), e]
    unfold uu
    apply le_of_eq; ring)
  have h := pow_le_pow_left₀ (abs_nonneg _) hle 2
  rwa [sq_abs] at h

lemma Ncos_eq (x : ℕ → ℝ) : Ncos x = ∑' a : ℕ, uu x a ^ 2 := by
  unfold Ncos; congr 1; funext a; exact (uu_sq x a).symm

lemma summable_uu_sq (x : ℕ → ℝ) (hb : ∃ K, ∀ j, |x j| ≤ K) :
    Summable (fun a : ℕ => uu x a ^ 2) := by
  have := summable_Ncos_terms x hb
  convert this using 1
  funext a; exact uu_sq x a

lemma pt_bound (a : ℕ) (ha : 1 ≤ a) : 
    ((1 / 2) * (R1 a + C1 a + R23 a + C23 a) + (1 / 10 : ℝ) ^ a / 9) ≤ 107 / 2000 := tot_bound a ha

lemma S_le_cos (x : ℕ → ℝ) {K : ℝ} (hK : ∀ j, |x j| ≤ K) (h0 : x 0 = 0) :
    ∑' p : ℕ × ℕ, (F1 x p + F2 x p) ≤ 107 / 2000 * Ncos x := by
  obtain ⟨h1, h2⟩ := S_core x hK h0
  have hu := summable_uu_sq x ⟨K, hK⟩
  have hW : ∀ a : ℕ, ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 ≤
      107 / 2000 * uu x a ^ 2 := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [uu_zero]
    · have := pt_bound a (Nat.pos_of_ne_zero ha)
      have hp : (0 : ℝ) ≤ (1 / 10 : ℝ) ^ a / 9 := by positivity
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  calc _ ≤ ∑' a : ℕ, ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 := h1
    _ ≤ ∑' a : ℕ, 107 / 2000 * uu x a ^ 2 := h2.tsum_le_tsum hW (hu.mul_left _)
    _ = _ := by rw [tsum_mul_left, Ncos_eq]

lemma S_le_sin (x : ℕ → ℝ) {K : ℝ} (hK : ∀ j, |x j| ≤ K) (h0 : x 0 = 0) :
    ∑' p : ℕ × ℕ, (F1 x p + F2 x p) + (∑' j : ℕ, (1 / 10 : ℝ) ^ j * uu x j) ^ 2 ≤
      107 / 2000 * Ncos x := by
  obtain ⟨h1, h2⟩ := S_core x hK h0
  obtain ⟨r1, r2⟩ := rank1_bound x hK h0
  have hu := summable_uu_sq x ⟨K, hK⟩
  have hW : ∀ a : ℕ, ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 +
      ((1 / 10 : ℝ) ^ a / 9) * uu x a ^ 2 ≤ 107 / 2000 * uu x a ^ 2 := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [uu_zero]
    · have := pt_bound a (Nat.pos_of_ne_zero ha)
      have : ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 +
          ((1 / 10 : ℝ) ^ a / 9) * uu x a ^ 2 =
          ((1 / 2) * (R1 a + C1 a + R23 a + C23 a) + (1 / 10 : ℝ) ^ a / 9) * uu x a ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  calc ∑' p : ℕ × ℕ, (F1 x p + F2 x p) + (∑' j : ℕ, (1 / 10 : ℝ) ^ j * uu x j) ^ 2
      ≤ ∑' a : ℕ, ((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 +
        ∑' a : ℕ, ((1 / 10 : ℝ) ^ a / 9) * uu x a ^ 2 := by linarith
    _ = ∑' a : ℕ, (((1 / 2) * (R1 a + C1 a + R23 a + C23 a)) * uu x a ^ 2 +
        ((1 / 10 : ℝ) ^ a / 9) * uu x a ^ 2) := (h2.tsum_add r2).symm
    _ ≤ ∑' a : ℕ, 107 / 2000 * uu x a ^ 2 := (h2.add r2).tsum_le_tsum hW (hu.mul_left _)
    _ = _ := by rw [tsum_mul_left, Ncos_eq]

theorem Tcos_le (x : ℕ → ℝ) (hb : ∃ K, ∀ j, |x j| ≤ K) (h0 : x 0 = 0) :
    Tcos x ≤ 107 / 2000 * Ncos x := by
  obtain ⟨K, hK⟩ := hb
  have hbd : |Tcos x| ≤ ∑' p : ℕ × ℕ, (F1 x p + F2 x p) := by
    unfold Tcos
    refine abs_tsum_le_of_le _ _ (summable_Tcos_terms x ⟨K, hK⟩)
      ((summable_F1 x hK).add (summable_F2 x hK)) (fun p => ?_)
    have hw := wgt_nonneg p
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    have h2 : |x (Nat.dist p.1 p.2) - x (p.1 + p.2)| ≤ |x (Nat.dist p.1 p.2)| + |x (p.1 + p.2)| :=
      abs_sub _ _
    unfold F1 F2
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hw (abs_nonneg (x p.1)))
    nlinarith
  exact (le_abs_self _).trans (hbd.trans (S_le_cos x hK h0))

theorem Tsin_le (y : ℕ → ℝ) (hb : ∃ K, ∀ j, |y j| ≤ K) (h0 : y 0 = 0) :
    Tsin y ≤ 107 / 2000 * Ncos y := by
  obtain ⟨K, hK⟩ := hb
  have hbd : |∑' p : ℕ × ℕ, wgt p * y p.1 * (y (p.1 + p.2) + sgnk p.1 p.2 * y (Nat.dist p.1 p.2))|
      ≤ ∑' p : ℕ × ℕ, (F1 y p + F2 y p) := by
    refine abs_tsum_le_of_le _ _ (summable_Tsin_terms y ⟨K, hK⟩)
      ((summable_F1 y hK).add (summable_F2 y hK)) (fun p => ?_)
    have hw := wgt_nonneg p
    rw [abs_mul, abs_mul, abs_of_nonneg hw]
    have hs := sgnk_abs_le p.1 p.2
    have h2 : |y (p.1 + p.2) + sgnk p.1 p.2 * y (Nat.dist p.1 p.2)| ≤
        |y (Nat.dist p.1 p.2)| + |y (p.1 + p.2)| := by
      calc _ ≤ |y (p.1 + p.2)| + |sgnk p.1 p.2 * y (Nat.dist p.1 p.2)| := abs_add_le _ _
        _ ≤ |y (p.1 + p.2)| + |y (Nat.dist p.1 p.2)| := by
          refine add_le_add le_rfl ?_
          rw [abs_mul]
          nlinarith [abs_nonneg (y (Nat.dist p.1 p.2)), abs_nonneg (sgnk p.1 p.2)]
        _ = _ := add_comm _ _
    unfold F1 F2
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hw (abs_nonneg (y p.1)))
    nlinarith
  have h1 := norm_sum_le y hK
  have h2 := S_le_sin y hK h0
  have h3 := neg_abs_le (∑' p : ℕ × ℕ, wgt p * y p.1 * (y (p.1 + p.2) + sgnk p.1 p.2 * y (Nat.dist p.1 p.2)))
  unfold Tsin
  have h4 := abs_nonneg (∑' p : ℕ × ℕ, wgt p * y p.1 * (y (p.1 + p.2) + sgnk p.1 p.2 * y (Nat.dist p.1 p.2)))
  linarith

end SharpLSI.FL.Ex.LaneD
