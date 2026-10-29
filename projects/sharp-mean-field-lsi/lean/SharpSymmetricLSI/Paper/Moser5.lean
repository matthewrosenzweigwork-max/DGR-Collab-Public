import SharpSymmetricLSI.Paper.Moser4

/-!
# The Moser iteration: boundedness of eigenfunctions (Phase 3, lane D)

Along `m_k = 2^{k+1} - 1` the norms `N_k = (∫|e|^{2m_k})^{1/(2m_k)}` satisfy
`N_{k+1} ≤ (A 2^{n(k+1)})^{2^{-(k+1)}} N_k`, hence `N_k ≤ A 4^n N_0` and `|e| ≤ A 4^n N_0` a.e.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI

/-- `m_k = 2^{k+1} - 1`. -/
def mSeq (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

theorem mSeq_succ (k : ℕ) : mSeq (k + 1) = 2 * mSeq k + 1 := by
  unfold mSeq
  have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem one_le_mSeq (k : ℕ) : 1 ≤ mSeq k := by
  unfold mSeq
  have : 2 ≤ 2 ^ (k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem mSeq_add_one (k : ℕ) : (mSeq k : ℝ) + 1 = 2 ^ (k + 1) := by
  unfold mSeq
  have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [Nat.cast_sub this]; push_cast; ring

theorem pow_le_two_mul_mSeq (k : ℕ) : (2 : ℝ) ^ (k + 1) ≤ 2 * mSeq k := by
  have h := mSeq_add_one k
  have h1 : (1 : ℝ) ≤ mSeq k := by exact_mod_cast one_le_mSeq k
  linarith

/-- The constant `A` with `moserK ≤ A (m+1)^n`. -/
def moserA (ι : Type*) [Fintype ι] (a b lam : ℝ) : ℝ :=
  2 * (3 * (2 * a * b * lam + 2)) ^ Fintype.card ι

variable {ι : Type*} [Fintype ι]

theorem one_le_moserA {a b lam : ℝ} (hab : 0 ≤ a * b * lam) : 1 ≤ moserA ι a b lam := by
  unfold moserA
  have : (1 : ℝ) ≤ 3 * (2 * a * b * lam + 2) := by nlinarith
  have := one_le_pow₀ (n := Fintype.card ι) this
  linarith

theorem moserK_le {a b lam : ℝ} (hab : 0 ≤ a * b * lam) (m : ℕ) :
    moserK ι a b lam m ≤ moserA ι a b lam * ((m : ℝ) + 1) ^ Fintype.card ι := by
  unfold moserK moserA moserR
  have hR : (⌈a * b * (1 + 2 * m) * lam⌉₊ : ℝ) ≤ a * b * (1 + 2 * m) * lam + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ a * b * (1 + 2 * m) * lam by
      have : (0 : ℝ) ≤ 1 + 2 * m := by positivity
      nlinarith)
    linarith
  have h1 : ((2 * (⌈a * b * (1 + 2 * m) * lam⌉₊ + 1) + 1 : ℕ) : ℝ) ≤
      3 * (2 * a * b * lam + 2) * ((m : ℝ) + 1) := by
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  calc 2 * ((2 * (⌈a * b * (1 + 2 * m) * lam⌉₊ + 1) + 1 : ℕ) : ℝ) ^ Fintype.card ι
      ≤ 2 * (3 * (2 * a * b * lam + 2) * ((m : ℝ) + 1)) ^ Fintype.card ι := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

section iterate
variable [DecidableEq ι] {P : Measure (UnitAddTorus ι)}
  [IsProbabilityMeasure P] {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
  (ha : (volume : Measure (UnitAddTorus ι)) ≤ ENNReal.ofReal a • P)
  (hb : P ≤ ENNReal.ofReal b • volume) {e : UnitAddTorus ι → ℝ} (he : MemH1 P e) {lam : ℝ}
  (hlam : 0 ≤ lam)
  (heig : ∀ φ, MemH1 P φ → ∫ x, ∑ k, weakGrad e x k * weakGrad φ x k ∂P =
    lam * ∫ x, e x * φ x ∂P)
include ha0 hb0 ha hb he hlam heig

theorem integrable_mSeq (k : ℕ) : Integrable (fun x => |e x| ^ (2 * mSeq k)) volume := by
  induction k with
  | zero =>
    have : mSeq 0 = 1 := by simp [mSeq]
    rw [this]
    exact (memLp_vol ha he).integrable_sq.congr (Eventually.of_forall fun x => by simp)
  | succ k ih =>
    have := (moser_step ha0 hb0 ha hb he hlam heig (one_le_mSeq k) ih).1
    rw [mSeq_succ]
    convert this using 3
    ring

/-- `N_k = (∫|e|^{2m_k})^{1/(2m_k)}`. -/
def moserN (e : UnitAddTorus ι → ℝ) (k : ℕ) : ℝ :=
  (∫ x, |e x| ^ (2 * mSeq k)) ^ ((1 : ℝ) / (2 * mSeq k))

omit ha0 hb0 ha hb he hlam heig in
theorem moserN_nonneg (k : ℕ) : 0 ≤ moserN e k :=
  Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _

theorem moserN_succ_le (k : ℕ) :
    moserN e (k + 1) ≤ moserA ι a b lam ^ ((1 : ℝ) / 2 ^ (k + 1)) *
      (2 : ℝ) ^ ((Fintype.card ι * (k + 1) : ℝ) / 2 ^ (k + 1)) * moserN e k := by
  set m := mSeq k
  have hm := one_le_mSeq k
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hab : 0 ≤ a * b * lam := by positivity
  obtain ⟨-, hstep⟩ := moser_step ha0 hb0 ha hb he hlam heig hm (integrable_mSeq ha0 hb0 ha hb he
    hlam heig k)
  set I := ∫ x, |e x| ^ (2 * m)
  set K := moserK ι a b lam m
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  have hK1 : 1 ≤ K := by
    unfold K moserK
    have := one_le_pow₀ (M₀ := ℝ) (a := ((2 * moserR a b lam m + 1 : ℕ) : ℝ))
      (n := Fintype.card ι) (by exact_mod_cast Nat.le_add_left 1 _)
    linarith
  have h2m : 2 * mSeq (k + 1) = 4 * m + 2 := by rw [mSeq_succ]; ring
  -- `N_{k+1} ≤ K^θ N_k`
  have hθ : moserN e (k + 1) ≤ K ^ (((m : ℝ) + 1) / (m * (4 * m + 2))) * moserN e k := by
    unfold moserN
    rw [h2m]
    have hcast : (2 * (mSeq (k + 1) : ℝ)) = 4 * m + 2 := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h2m
      push_cast at this; exact this
    rw [hcast]
    have hK0 : 0 ≤ K := by linarith
    calc (∫ x, |e x| ^ (4 * m + 2)) ^ ((1 : ℝ) / (4 * m + 2))
        ≤ (K ^ (((m : ℝ) + 1) / m) * I ^ ((2 * m + 1 : ℝ) / m)) ^ ((1 : ℝ) / (4 * m + 2)) :=
          Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) hstep (by positivity)
      _ = K ^ (((m : ℝ) + 1) / m * (1 / (4 * m + 2))) *
            I ^ ((2 * m + 1 : ℝ) / m * (1 / (4 * m + 2))) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK0,
            ← Real.rpow_mul hI0]
      _ = _ := by
          congr 2
          · field_simp
          · field_simp; ring
  -- `K^θ ≤ (A 2^{n(k+1)})^{2^{-(k+1)}}`
  have hθle : ((m : ℝ) + 1) / (m * (4 * m + 2)) ≤ 1 / 2 ^ (k + 1) := by
    have h1 := pow_le_two_mul_mSeq k
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hKle : K ≤ moserA ι a b lam * (2 : ℝ) ^ (Fintype.card ι * (k + 1)) := by
    have := moserK_le (ι := ι) hab m
    rw [mSeq_add_one, ← pow_mul, mul_comm (k + 1)] at this
    exact this
  have hA1 := one_le_moserA (ι := ι) hab
  calc moserN e (k + 1) ≤ K ^ (((m : ℝ) + 1) / (m * (4 * m + 2))) * moserN e k := hθ
    _ ≤ K ^ ((1 : ℝ) / 2 ^ (k + 1)) * moserN e k := by
        gcongr
        · exact moserN_nonneg k
    _ ≤ (moserA ι a b lam * (2 : ℝ) ^ (Fintype.card ι * (k + 1))) ^ ((1 : ℝ) / 2 ^ (k + 1)) *
          moserN e k := by
        gcongr
        · exact moserN_nonneg k
    _ = _ := by
        have h2 : ((2 : ℝ) ^ (Fintype.card ι * (k + 1))) ^ ((1 : ℝ) / 2 ^ (k + 1)) =
            (2 : ℝ) ^ ((Fintype.card ι * (k + 1) : ℝ) / 2 ^ (k + 1)) := by
          rw [← Real.rpow_natCast (2 : ℝ) (Fintype.card ι * (k + 1)), ← Real.rpow_mul (by norm_num)]
          congr 1; push_cast; ring
        rw [Real.mul_rpow (by linarith) (by positivity), h2]

theorem moserN_le_closed (k : ℕ) :
    moserN e k ≤ moserN e 0 * moserA ι a b lam ^ (1 - (1 : ℝ) / 2 ^ k) *
      (2 : ℝ) ^ (Fintype.card ι * (2 - ((k : ℝ) + 2) / 2 ^ k)) := by
  have hab : 0 ≤ a * b * lam := by positivity
  have hA := one_le_moserA (ι := ι) hab
  have hA0 : 0 < moserA ι a b lam := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
    refine (moserN_succ_le ha0 hb0 ha hb he hlam heig k).trans ?_
    calc moserA ι a b lam ^ ((1 : ℝ) / 2 ^ (k + 1)) *
          (2 : ℝ) ^ ((Fintype.card ι * (k + 1) : ℝ) / 2 ^ (k + 1)) * moserN e k
        ≤ moserA ι a b lam ^ ((1 : ℝ) / 2 ^ (k + 1)) *
          (2 : ℝ) ^ ((Fintype.card ι * (k + 1) : ℝ) / 2 ^ (k + 1)) *
          (moserN e 0 * moserA ι a b lam ^ (1 - (1 : ℝ) / 2 ^ k) *
            (2 : ℝ) ^ (Fintype.card ι * (2 - ((k : ℝ) + 2) / 2 ^ k))) := by gcongr
      _ = moserN e 0 * (moserA ι a b lam ^ ((1 : ℝ) / 2 ^ (k + 1)) *
            moserA ι a b lam ^ (1 - (1 : ℝ) / 2 ^ k)) *
          ((2 : ℝ) ^ ((Fintype.card ι * (k + 1) : ℝ) / 2 ^ (k + 1)) *
            (2 : ℝ) ^ (Fintype.card ι * (2 - ((k : ℝ) + 2) / 2 ^ k))) := by ring
      _ = _ := by
          rw [← Real.rpow_add hA0, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          push_cast
          congr 3
          · field_simp; ring
          · field_simp; ring

theorem moserN_le (k : ℕ) :
    moserN e k ≤ moserN e 0 * moserA ι a b lam * 4 ^ Fintype.card ι := by
  have hab : 0 ≤ a * b * lam := by positivity
  have hA := one_le_moserA (ι := ι) hab
  refine (moserN_le_closed ha0 hb0 ha hb he hlam heig k).trans ?_
  have h0 := moserN_nonneg (e := e) 0
  have h1 : moserA ι a b lam ^ (1 - (1 : ℝ) / 2 ^ k) ≤ moserA ι a b lam := by
    calc moserA ι a b lam ^ (1 - (1 : ℝ) / 2 ^ k) ≤ moserA ι a b lam ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA (by have : (0 : ℝ) ≤ 1 / 2 ^ k := by positivity
                                                  linarith)
      _ = _ := Real.rpow_one _
  have h2 : (2 : ℝ) ^ (Fintype.card ι * (2 - ((k : ℝ) + 2) / 2 ^ k)) ≤ 4 ^ Fintype.card ι := by
    calc (2 : ℝ) ^ (Fintype.card ι * (2 - ((k : ℝ) + 2) / 2 ^ k))
        ≤ (2 : ℝ) ^ ((Fintype.card ι : ℝ) * 2) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have : (0 : ℝ) ≤ ((k : ℝ) + 2) / 2 ^ k := by positivity
          have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
          nlinarith
      _ = 4 ^ Fintype.card ι := by
          rw [mul_comm, Real.rpow_mul (by norm_num)]
          norm_num
  calc moserN e 0 * moserA ι a b lam ^ (1 - (1 : ℝ) / 2 ^ k) *
        (2 : ℝ) ^ (Fintype.card ι * (2 - ((k : ℝ) + 2) / 2 ^ k))
      ≤ moserN e 0 * moserA ι a b lam * 4 ^ Fintype.card ι := by
        gcongr

/-- **Moser: eigenfunctions are bounded.** -/
theorem ae_abs_le_moser :
    ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)),
      |e x| ≤ moserN e 0 * moserA ι a b lam * 4 ^ Fintype.card ι := by
  set C := moserN e 0 * moserA ι a b lam * 4 ^ Fintype.card ι
  have hC0 : 0 ≤ C := by
    have hab : 0 ≤ a * b * lam := by positivity
    have := one_le_moserA (ι := ι) hab
    have := moserN_nonneg (e := e) 0
    positivity
  -- for every `t > C`, `{t ≤ |e|}` is null
  have hnull : ∀ t : ℝ, C < t → volume {x : UnitAddTorus ι | t ≤ |e x|} = 0 := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hC0 ht
    have hbound : ∀ k, (volume {x : UnitAddTorus ι | t ≤ |e x|}).toReal ≤ (C / t) ^ (2 * mSeq k) :=
      fun k => by
        set r := 2 * mSeq k
        have hr : 0 < r := by have := one_le_mSeq k; omega
        have hint := integrable_mSeq ha0 hb0 ha hb he hlam heig k
        have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun x => by positivity)
          hint (t ^ r)
        have hsub : {x : UnitAddTorus ι | t ≤ |e x|} ⊆ {x | t ^ r ≤ |e x| ^ r} := fun x hx =>
          pow_le_pow_left₀ ht0.le hx r
        have hN := moserN_le ha0 hb0 ha hb he hlam heig k
        have hI : ∫ x, |e x| ^ r ≤ C ^ r := by
          have hI0 : 0 ≤ ∫ x, |e x| ^ r := integral_nonneg fun _ => by positivity
          have : (∫ x, |e x| ^ r) = moserN e k ^ r := by
            unfold moserN
            rw [← Real.rpow_natCast, ← Real.rpow_mul hI0]
            have : (1 : ℝ) / (2 * mSeq k) * (r : ℕ) = 1 := by
              simp only [r]; push_cast
              have : (0 : ℝ) < mSeq k := by exact_mod_cast one_le_mSeq k
              field_simp
            rw [this, Real.rpow_one]
          rw [this]
          exact pow_le_pow_left₀ (moserN_nonneg k) hN r
        have hmeas : (volume {x : UnitAddTorus ι | t ≤ |e x|}).toReal ≤
            (volume {x : UnitAddTorus ι | t ^ r ≤ |e x| ^ r}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
        rw [div_pow, le_div_iff₀ (by positivity)]
        calc (volume {x : UnitAddTorus ι | t ≤ |e x|}).toReal * t ^ r
            ≤ t ^ r * (volume {x : UnitAddTorus ι | t ^ r ≤ |e x| ^ r}).toReal := by
              rw [mul_comm]; exact mul_le_mul_of_nonneg_left hmeas (by positivity)
          _ ≤ ∫ x, |e x| ^ r := by simpa [Measure.real] using hmk
          _ ≤ C ^ r := hI
    have hlim : Tendsto (fun k => (C / t) ^ (2 * mSeq k)) atTop (𝓝 0) := by
      have hq : C / t < 1 := (div_lt_one ht0).mpr ht
      have h1 : Tendsto (fun n : ℕ => (C / t) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hC0 ht0.le) hq
      refine h1.comp (tendsto_atTop_mono (fun k => ?_) tendsto_id)
      have : k + 1 ≤ 2 ^ (k + 1) := (Nat.lt_two_pow_self).le
      simp only [id, mSeq]; omega
    have h0 : (volume {x : UnitAddTorus ι | t ≤ |e x|}).toReal = 0 :=
      le_antisymm (ge_of_tendsto' hlim hbound) ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have hall : ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), ∀ j : ℕ, |e x| < C + 1 / (j + 1) := by
    rw [ae_all_iff]
    intro j
    have := hnull (C + 1 / (j + 1)) (by have : (0 : ℝ) < 1 / (j + 1) := by positivity
                                        linarith)
    rw [ae_iff]
    simpa [not_lt] using this
  filter_upwards [hall] with x hx
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  exact (hx j).trans (by linarith)

end iterate

end SharpLSI
