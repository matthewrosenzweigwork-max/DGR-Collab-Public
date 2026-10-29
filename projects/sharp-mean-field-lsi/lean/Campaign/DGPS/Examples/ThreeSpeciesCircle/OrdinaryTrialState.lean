import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBootstrap
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryAllOptimizers

open MeasureTheory

namespace DGPS.Examples.ThreeSpeciesCircle.TrialState

noncomputable section

/-- `X(h,c) = O(|h|^k)` uniformly for `|c| ≤ 1` and small `|h|`. -/
def HOrd (k : ℕ) (X : ℝ → ℝ → ℝ) : Prop :=
  ∃ K h0 : ℝ, 0 ≤ K ∧ 0 < h0 ∧ ∀ h c : ℝ, |h| ≤ h0 → |c| ≤ 1 → |X h c| ≤ K * |h| ^ k

theorem HOrd.add {k : ℕ} {X Y : ℝ → ℝ → ℝ} (hX : HOrd k X) (hY : HOrd k Y) :
    HOrd k (fun h c => X h c + Y h c) := by
  obtain ⟨K1, a1, hK1, ha1, H1⟩ := hX
  obtain ⟨K2, a2, hK2, ha2, H2⟩ := hY
  refine ⟨K1 + K2, min a1 a2, by positivity, lt_min ha1 ha2, fun h c hh hc => ?_⟩
  have e1 := H1 h c (hh.trans (min_le_left _ _)) hc
  have e2 := H2 h c (hh.trans (min_le_right _ _)) hc
  calc |X h c + Y h c| ≤ |X h c| + |Y h c| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem HOrd.neg {k : ℕ} {X : ℝ → ℝ → ℝ} (hX : HOrd k X) : HOrd k (fun h c => -X h c) := by
  obtain ⟨K1, a1, hK1, ha1, H1⟩ := hX
  exact ⟨K1, a1, hK1, ha1, fun h c hh hc => by rw [abs_neg]; exact H1 h c hh hc⟩

theorem HOrd.sub {k : ℕ} {X Y : ℝ → ℝ → ℝ} (hX : HOrd k X) (hY : HOrd k Y) :
    HOrd k (fun h c => X h c - Y h c) := by
  have := hX.add hY.neg
  simpa [sub_eq_add_neg] using this

theorem HOrd.mul {k l : ℕ} {X Y : ℝ → ℝ → ℝ} (hX : HOrd k X) (hY : HOrd l Y) :
    HOrd (k + l) (fun h c => X h c * Y h c) := by
  obtain ⟨K1, a1, hK1, ha1, H1⟩ := hX
  obtain ⟨K2, a2, hK2, ha2, H2⟩ := hY
  refine ⟨K1 * K2, min a1 a2, by positivity, lt_min ha1 ha2, fun h c hh hc => ?_⟩
  have e1 := H1 h c (hh.trans (min_le_left _ _)) hc
  have e2 := H2 h c (hh.trans (min_le_right _ _)) hc
  calc |X h c * Y h c| = |X h c| * |Y h c| := abs_mul _ _
    _ ≤ (K1 * |h| ^ k) * (K2 * |h| ^ l) :=
        mul_le_mul e1 e2 (abs_nonneg _) (le_trans (abs_nonneg _) e1)
    _ = _ := by ring

theorem HOrd.mono {k l : ℕ} {X : ℝ → ℝ → ℝ} (hX : HOrd k X) (hl : l ≤ k) : HOrd l X := by
  obtain ⟨K1, a1, hK1, ha1, H1⟩ := hX
  refine ⟨K1, min a1 1, hK1, lt_min ha1 one_pos, fun h c hh hc => ?_⟩
  have e1 := H1 h c (hh.trans (min_le_left _ _)) hc
  have h1 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  have : |h| ^ k ≤ |h| ^ l := pow_le_pow_of_le_one (abs_nonneg _) h1 hl
  calc |X h c| ≤ K1 * |h| ^ k := e1
    _ ≤ K1 * |h| ^ l := mul_le_mul_of_nonneg_left this hK1

theorem HOrd.congr {k : ℕ} {X Y : ℝ → ℝ → ℝ} (hX : HOrd k X)
    (heq : ∃ h1 : ℝ, 0 < h1 ∧ ∀ h c : ℝ, |h| ≤ h1 → |c| ≤ 1 → X h c = Y h c) : HOrd k Y := by
  obtain ⟨K1, a1, hK1, ha1, H1⟩ := hX
  obtain ⟨b1, hb1, E⟩ := heq
  refine ⟨K1, min a1 b1, hK1, lt_min ha1 hb1, fun h c hh hc => ?_⟩
  rw [← E h c (hh.trans (min_le_right _ _)) hc]
  exact H1 h c (hh.trans (min_le_left _ _)) hc

theorem HOrd.of_cont {k : ℕ} {Y : ℝ → ℝ → ℝ} (hY : Continuous (fun p : ℝ × ℝ => Y p.1 p.2)) :
    HOrd k (fun h c => h ^ k * Y h c) := by
  have hc : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hY.continuousOn
  refine ⟨max C 0, 1, le_max_right _ _, one_pos, fun h c hh hc' => ?_⟩
  have hmem : (h, c) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 :=
    ⟨abs_le.1 hh, abs_le.1 hc'⟩
  have := hC (h, c) hmem
  simp only [Real.norm_eq_abs] at this
  rw [abs_mul, abs_pow, mul_comm]
  exact mul_le_mul (this.trans (le_max_left _ _)) le_rfl (by positivity) (le_max_right _ _) |>.trans_eq' rfl

theorem HOrd.zero_of_cont {Y : ℝ → ℝ → ℝ} (hY : Continuous (fun p : ℝ × ℝ => Y p.1 p.2)) :
    HOrd 0 Y := by
  have := HOrd.of_cont (k := 0) hY
  simpa using this


theorem HOrd.of_eq {k : ℕ} {X Y : ℝ → ℝ → ℝ}
    (hY : Continuous (fun p : ℝ × ℝ => Y p.1 p.2)) (hX : ∀ h c, X h c = h ^ k * Y h c) :
    HOrd k X := by
  have := HOrd.of_cont (k := k) hY
  exact HOrd.congr this ⟨1, one_pos, fun h c _ _ => (hX h c).symm⟩

/-- first-order trial profile `u` as a function of `c = cos θ`. -/
def uP (h c : ℝ) : ℝ := h * (2 * c + h * (-8 / 5 * c ^ 4 + 74 / 15 * c ^ 2 - 28 / 15))
/-- derivative of `u` with respect to `c`. -/
def VP (h c : ℝ) : ℝ := h * (2 + h * (-32 / 5 * c ^ 3 + 148 / 15 * c))
/-- `cos 3θ` as a polynomial in `c = cos θ`. -/
def c3P (c : ℝ) : ℝ := 4 * c ^ 3 - 3 * c
def eP (h c : ℝ) : ℝ := Real.exp (h * c3P c)
def E2 (h c : ℝ) : ℝ := 1 + h * c3P c + (h * c3P c) ^ 2 / 2
def WP (h c : ℝ) : ℝ := (1 - c ^ 2) * VP h c ^ 2
def AIP (h c : ℝ) : ℝ := eP h c * (WP h c / (1 + uP h c))
def BIP (h c : ℝ) : ℝ := eP h c * ((1 + uP h c) * Real.log (1 + uP h c) - uP h c)
def qP (h c : ℝ) : ℝ := 1 - uP h c + uP h c ^ 2
def Q4P (h c : ℝ) : ℝ := uP h c ^ 2 / 2 - uP h c ^ 3 / 6 + uP h c ^ 4 / 12
def FaP (h c : ℝ) : ℝ := E2 h c * (WP h c * qP h c)
def FbP (h c : ℝ) : ℝ := E2 h c * Q4P h c
def GP (h c : ℝ) : ℝ := FaP h c - 2 * (1 - 16 / 15 * h ^ 2) * FbP h c

theorem hord_u : HOrd 1 uP :=
  HOrd.of_eq (Y := fun h c => 2 * c + h * (-8 / 5 * c ^ 4 + 74 / 15 * c ^ 2 - 28 / 15))
    (by fun_prop) (fun h c => by simp [uP])

theorem hord_V : HOrd 1 VP :=
  HOrd.of_eq (Y := fun h c => 2 + h * (-32 / 5 * c ^ 3 + 148 / 15 * c))
    (by fun_prop) (fun h c => by simp [VP])

theorem hord_c3 : HOrd 0 (fun _ c => c3P c) :=
  HOrd.zero_of_cont (by unfold c3P; fun_prop)

theorem hord_e : HOrd 0 eP :=
  HOrd.zero_of_cont (by unfold eP c3P; fun_prop)

theorem hord_E2 : HOrd 0 E2 :=
  HOrd.zero_of_cont (by unfold E2 c3P; fun_prop)

theorem hord_W : HOrd 2 WP := by
  have := (hord_V.mul hord_V).mul (HOrd.zero_of_cont (Y := fun _ c => 1 - c ^ 2) (by fun_prop))
  refine HOrd.congr this ⟨1, one_pos, fun h c _ _ => ?_⟩
  simp only [WP]; ring

theorem hord_q : HOrd 0 qP := by
  have h1 := hord_u.mono (Nat.zero_le 1)
  have := ((HOrd.zero_of_cont (Y := fun _ _ => (1 : ℝ)) (by fun_prop)).sub h1).add
    (h1.mul h1 |>.mono (Nat.zero_le _))
  exact HOrd.congr this ⟨1, one_pos, fun h c _ _ => by simp [qP]; ring⟩

theorem u_small : ∃ h1 : ℝ, 0 < h1 ∧ ∀ h c : ℝ, |h| ≤ h1 → |c| ≤ 1 → |uP h c| ≤ 1 / 2 := by
  obtain ⟨K, a, hK, ha, H⟩ := hord_u
  refine ⟨min a (1 / (2 * K + 2)), lt_min ha (by positivity), fun h c hh hc => ?_⟩
  have e1 := H h c (hh.trans (min_le_left _ _)) hc
  have e2 : |h| ≤ 1 / (2 * K + 2) := hh.trans (min_le_right _ _)
  have e3 : K * |h| ≤ 1 / 2 := by
    have : |h| * (2 * K + 2) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at e2
    nlinarith [abs_nonneg h]
  simpa using e1.trans (by simpa using e3)

theorem hord_inv : HOrd 0 (fun h c => (1 + uP h c)⁻¹) := by
  obtain ⟨h1, hh1, H⟩ := u_small
  refine ⟨2, h1, by norm_num, hh1, fun h c hh hc => ?_⟩
  have := H h c hh hc
  have h2 := (abs_le.1 this).1
  have hpos : 1 / 2 ≤ 1 + uP h c := by linarith
  rw [abs_of_pos (by positivity)]
  simp only [pow_zero, mul_one]
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith


theorem abs_c3P_le {c : ℝ} (hc : |c| ≤ 1) : |c3P c| ≤ 7 := by
  have h1 : |c ^ 3| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
  unfold c3P
  calc |4 * c ^ 3 - 3 * c| ≤ |4 * c ^ 3| + |3 * c| := abs_sub _ _
    _ = 4 * |c ^ 3| + 3 * |c| := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ 7 := by linarith

theorem hord_re : HOrd 3 (fun h c => eP h c - E2 h c) := by
  refine ⟨(2 / 9) * 7 ^ 3, 1 / 7, by norm_num, by norm_num, fun h c hh hc => ?_⟩
  have hx : |h * c3P c| ≤ 1 := by
    rw [abs_mul]
    calc |h| * |c3P c| ≤ (1 / 7) * 7 := mul_le_mul hh (abs_c3P_le hc) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have := Real.exp_bound hx (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  have e : eP h c - E2 h c = Real.exp (h * c3P c) - (1 + h * c3P c + (h * c3P c) ^ 2 / 2) := rfl
  show |eP h c - E2 h c| ≤ _
  rw [e]
  have h3 : |h * c3P c| ^ 3 ≤ 7 ^ 3 * |h| ^ 3 := by
    rw [abs_mul, mul_pow]
    have := pow_le_pow_left₀ (abs_nonneg _) (abs_c3P_le hc) 3
    nlinarith [pow_nonneg (abs_nonneg h) 3]
  calc _ ≤ (|h| * |c3P c|) ^ 3 * (2 / 9) := this
    _ = |h * c3P c| ^ 3 * (2 / 9) := by rw [abs_mul]
    _ ≤ 7 ^ 3 * |h| ^ 3 * (2 / 9) := by linarith
    _ = _ := by ring

theorem hord_upow (n : ℕ) : HOrd n (fun h c => uP h c ^ n) := by
  induction n with
  | zero =>
    have h0 := HOrd.zero_of_cont (Y := fun _ _ => (1 : ℝ)) (by fun_prop)
    exact HOrd.congr h0 ⟨1, one_pos, fun h c _ _ => by simp⟩
  | succ n ih =>
    have := ih.mul hord_u
    exact HOrd.congr this ⟨1, one_pos, fun h c _ _ => by simp only [pow_succ]⟩

/-- the log remainder. -/
def lrP (h c : ℝ) : ℝ :=
  Real.log (1 + uP h c) - (uP h c - uP h c ^ 2 / 2 + uP h c ^ 3 / 3 - uP h c ^ 4 / 4)

theorem hord_lr : HOrd 5 lrP := by
  obtain ⟨K, a, hK, ha, H⟩ := hord_u
  obtain ⟨h1, hh1, H1⟩ := u_small
  refine ⟨2 * K ^ 5, min a h1, by positivity, lt_min ha hh1, fun h c hh hc => ?_⟩
  have e1 := H h c (hh.trans (min_le_left _ _)) hc
  have e2 := H1 h c (hh.trans (min_le_right _ _)) hc
  have hlt : |-uP h c| < 1 := by rw [abs_neg]; linarith
  have := Real.abs_log_sub_add_sum_range_le hlt 4
  have e : |lrP h c| = |(∑ i ∈ Finset.range 4, (-uP h c) ^ (i + 1) / ((i : ℝ) + 1))
      + Real.log (1 - -uP h c)| := by
    congr 1
    simp only [lrP, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast; ring_nf
  show |lrP h c| ≤ _
  rw [e]
  refine this.trans ?_
  rw [abs_neg]
  have hu : |uP h c| ^ 5 ≤ K ^ 5 * |h| ^ 5 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using e1) 5
  have hpos : 0 < 1 - |uP h c| := by linarith
  rw [div_le_iff₀ hpos]
  have hk : 0 ≤ K ^ 5 * |h| ^ 5 := by positivity
  have hpow : |uP h c| ^ (4 + 1) = |uP h c| ^ 5 := rfl
  rw [hpow]
  nlinarith [mul_nonneg hk hpos.le]


theorem hord_one_add_u : HOrd 0 (fun h c => 1 + uP h c) :=
  HOrd.zero_of_cont (by unfold uP; fun_prop)

theorem alg_A (e E u W : ℝ) (hne : 1 + u ≠ 0) :
    e * (W / (1 + u)) - E * (W * (1 - u + u ^ 2)) =
      (e - E) * W * (1 - u + u ^ 2) - e * W * u ^ 3 * (1 + u)⁻¹ := by
  field_simp
  ring

theorem hord_remA : HOrd 5 (fun h c => AIP h c - FaP h c) := by
  obtain ⟨h1, hh1, H1⟩ := u_small
  have a1 := ((hord_re.mul hord_W).mul hord_q).sub
    (((hord_e.mul hord_W).mul (hord_upow 3)).mul hord_inv)
  refine HOrd.congr a1 ⟨h1, hh1, fun h c hh hc => ?_⟩
  have hne : 1 + uP h c ≠ 0 := by
    have := (abs_le.1 (H1 h c hh hc)).1
    linarith
  simp only [AIP, FaP, qP, E2, eP]
  have := alg_A (Real.exp (h * c3P c)) (E2 h c) (uP h c) (WP h c) hne
  simp only [E2] at this
  simp only [eP, E2, WP, qP] at *
  linarith

theorem alg_g (u L lr : ℝ) (hL : L = u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + lr) :
    (1 + u) * L - u = (u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 12) + (-(u ^ 5 / 4) + (1 + u) * lr) := by
  subst hL; ring

theorem hord_remB : HOrd 5 (fun h c => BIP h c - FbP h c) := by
  have hl := hord_lr
  have hq : HOrd 2 Q4P := by
    have := (((hord_upow 2).mul (HOrd.zero_of_cont (Y := fun _ _ => (1 : ℝ) / 2) (by fun_prop))).add
      (((hord_upow 3).mul (HOrd.zero_of_cont (Y := fun _ _ => -(1 : ℝ) / 6) (by fun_prop))).mono
        (by norm_num : 2 ≤ 3 + 0))).add
      (((hord_upow 4).mul (HOrd.zero_of_cont (Y := fun _ _ => (1 : ℝ) / 12) (by fun_prop))).mono
        (by norm_num : 2 ≤ 4 + 0))
    have := this.mono (le_refl 2)
    refine HOrd.congr this ⟨1, one_pos, fun h c _ _ => ?_⟩
    simp only [Q4P]; ring
  have hr : HOrd 5 (fun h c => -(uP h c ^ 5 / 4) + (1 + uP h c) * lrP h c) := by
    have a1 := ((hord_upow 5).mul (HOrd.zero_of_cont (Y := fun _ _ => -(1 : ℝ) / 4) (by fun_prop))).add
      ((hord_one_add_u.mul hl))
    refine HOrd.congr a1 ⟨1, one_pos, fun h c _ _ => ?_⟩
    ring
  have hg : HOrd 2 (fun h c => (1 + uP h c) * Real.log (1 + uP h c) - uP h c) := by
    have a1 := hq.add (hr.mono (by norm_num : 2 ≤ 5))
    refine HOrd.congr a1 ⟨1, one_pos, fun h c _ _ => ?_⟩
    have := alg_g (uP h c) (Real.log (1 + uP h c)) (lrP h c) (by simp only [lrP]; ring)
    simp only [Q4P] at *
    linarith
  have a2 := (hord_re.mul hg).add (hord_E2.mul hr)
  refine HOrd.congr a2 ⟨1, one_pos, fun h c _ _ => ?_⟩
  have := alg_g (uP h c) (Real.log (1 + uP h c)) (lrP h c) (by simp only [lrP]; ring)
  simp only [BIP, FbP, Q4P, eP, E2] at *
  rw [this]; ring


def g2P (c : ℝ) : ℝ := 4 - 8*c^2
def g3P (c : ℝ) : ℝ := -512*c^3/15 + 404*c/15
def g4P (c : ℝ) : ℝ := 512*c^8/25 - 10912*c^6/75 + 8888*c^4/45 - 17182*c^2/225 + 896/225
def SP (h c : ℝ) : ℝ := 262144*c^22*h^7/28125 - 1589248*c^22*h^5/1875 - 10878976*c^20*h^7/84375 + 56123392*c^20*h^5/5625 - 131072*c^19*h^6/3125 + 1400832*c^19*h^4/625 + 63520768*c^18*h^7/84375 - 55911424*c^18*h^5/1125 - 200704*c^18*h^3/375 + 37126144*c^17*h^6/84375 - 108709888*c^17*h^4/5625 - 367935488*c^16*h^7/151875 + 34762130432*c^16*h^5/253125 + 5817344*c^16*h^3/1875 - 51593216*c^15*h^6/28125 + 41901056*c^15*h^4/625 + 283648*c^15*h^2/375 + 10765155328*c^14*h^7/2278125 - 176131415744*c^14*h^5/759375 - 47292928*c^14*h^3/5625 - 8704*c^14*h/25 + 984543232*c^13*h^6/253125 - 2037914368*c^13*h^4/16875 - 518144*c^13*h^2/125 - 13268066816*c^12*h^7/2278125 + 188483321504*c^12*h^5/759375 + 167361664*c^12*h^3/10125 + 719872*c^12*h/375 - 2049430016*c^11*h^6/455625 + 18327599776*c^11*h^4/151875 + 10389632*c^11*h^2/1125 + 2048*c^11/25 + 3503738048*c^10*h^7/759375 - 127613716948*c^10*h^5/759375 - 1244755568*c^10*h^3/50625 - 5047808*c^10*h/1125 + 6493995392*c^9*h^6/2278125 - 9871074616*c^9*h^4/151875 - 100776832*c^9*h^2/10125 - 18176*c^9/75 - 1065283072*c^8*h^7/455625 + 157715601152*c^8*h^5/2278125 + 3433385284*c^8*h^3/151875 + 731104*c^8*h/125 - 674211328*c^7*h^6/759375 + 2377461632*c^7*h^4/151875 + 41044444*c^7*h^2/10125 + 6368*c^7/45 + 1666319872*c^6*h^7/2278125 - 35657163808*c^6*h^5/2278125 - 322545584*c^6*h^3/30375 - 46641118*c^6*h/10125 + 128049152*c^5*h^6/2278125 - 20085632*c^5*h^4/151875 + 2668096*c^5*h^2/3375 + 5432*c^5/45 - 97642496*c^4*h^7/759375 + 121877504*c^4*h^5/84375 + 96302192*c^4*h^3/50625 + 49276*c^4*h/25 + 16156672*c^3*h^6/455625 - 11314688*c^3*h^4/30375 - 8494864*c^3*h^2/10125 - 29036*c^3/225 + 2458624*c^2*h^7/253125 + 14202944*c^2*h^5/2278125 + 1602496*c^2*h^3/151875 - 1078336*c^2*h/3375 - 4917248*c*h^6/759375 - 307328*c*h^4/30375 + 934528*c*h^2/10125 + 6944*c/225 + 4917248*h^5/2278125 + 43904*h^3/151875 + 6272*h/405
def SBP (h c : ℝ) : ℝ := 8192*c^22*h^7/1875 - 339968*c^20*h^7/5625 - 12288*c^19*h^6/625 + 1985024*c^18*h^7/5625 + 2048*c^18*h^5/375 + 1160192*c^17*h^6/5625 - 11497984*c^16*h^7/10125 - 52736*c^16*h^5/1875 - 1612288*c^15*h^6/1875 - 6656*c^15*h^4/375 + 336411104*c^14*h^7/151875 + 26368*c^14*h^5/625 + 256*c^14*h^3/25 + 30766976*c^13*h^6/16875 + 42496*c^13*h^4/375 - 414627088*c^12*h^7/151875 - 3727168*c^12*h^5/50625 - 7808*c^12*h^3/125 - 64044688*c^11*h^6/30375 - 334144*c^11*h^4/1125 - 512*c^11*h^2/25 + 109491814*c^10*h^7/50625 + 14465176*c^10*h^5/50625 + 188576*c^10*h^3/1125 + 202937356*c^9*h^6/151875 + 831136*c^9*h^4/2025 + 6112*c^9*h^2/75 - 33290096*c^8*h^7/30375 - 69717974*c^8*h^5/151875 - 289448*c^8*h^3/1125 + 112*c^8*h/25 - 21069104*c^7*h^6/50625 - 2534654*c^7*h^4/10125 - 4256*c^7*h^2/45 + 52072496*c^6*h^7/151875 + 48376636*c^6*h^5/151875 + 2435549*c^6*h^3/10125 + 376*c^6*h/25 + 4001536*c^5*h^6/151875 + 3472*c^5*h^4/125 + 5462*c^5*h^2/225 + 24*c^5/5 - 3051328*c^4*h^7/50625 - 1602104*c^4*h^5/16875 - 375088*c^4*h^3/3375 - 1121*c^4*h/45 + 504896*c^3*h^6/30375 + 282632*c^3*h^4/10125 + 4508*c^3*h^2/225 + 38*c^3/15 + 76832*c^2*h^7/16875 + 1092112*c^2*h^5/151875 + 56252*c^2*h^3/3375 + 1288*c^2*h/225 - 153664*c*h^6/50625 - 76832*c*h^4/10125 - 392*c*h^2/45 - 56*c/15 + 153664*h^5/151875 + 10976*h^3/10125 + 392*h/225

theorem GP_eq (h c : ℝ) : GP h c = h ^ 2 * g2P c + h ^ 3 * g3P c + h ^ 4 * g4P c + h ^ 5 * SP h c := by
  simp only [GP, FaP, FbP, E2, WP, VP, qP, Q4P, uP, c3P, g2P, g3P, g4P, SP]
  ring

theorem FbP_eq (h c : ℝ) : FbP h c = h ^ 2 * (2 * c ^ 2) + h ^ 3 * SBP h c := by
  simp only [FbP, E2, Q4P, uP, c3P, SBP]
  ring

/-! ### Moments of `cos (2π t)` -/

/-- `∫₀¹ cos(2πt)^n dt`. -/
def mom (n : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * t) ^ n

theorem mom_eq (n : ℕ) : mom n = (2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos x ^ n := by
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun x => Real.cos x ^ n) h2
  simp only [mul_zero, mul_one, smul_eq_mul] at this
  exact this

theorem mom_zero : mom 0 = 1 := by simp [mom]

theorem mom_one : mom 1 = 0 := by
  rw [mom_eq]; simp

theorem mom_succ_succ (n : ℕ) : mom (n + 2) = ((n : ℝ) + 1) / ((n : ℝ) + 2) * mom n := by
  rw [mom_eq, mom_eq, integral_cos_pow]
  simp only [Real.cos_two_pi, Real.sin_two_pi, mul_zero, Real.cos_zero, Real.sin_zero, sub_zero,
    zero_div, zero_add]
  ring

theorem mom_odd (n : ℕ) : mom (2 * n + 1) = 0 := by
  induction n with
  | zero => simpa using mom_one
  | succ n ih =>
    have : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [this, mom_succ_succ, ih, mul_zero]

theorem mom_two : mom 2 = 1 / 2 := by
  have := mom_succ_succ 0
  simp only [zero_add, Nat.cast_zero, mom_zero] at this
  norm_num at this ⊢; linarith

theorem mom_four : mom 4 = 3 / 8 := by
  have := mom_succ_succ 2
  norm_num [mom_two] at this ⊢; linarith

theorem mom_six : mom 6 = 5 / 16 := by
  have := mom_succ_succ 4
  norm_num [mom_four] at this ⊢; linarith

theorem mom_eight : mom 8 = 35 / 128 := by
  have := mom_succ_succ 6
  norm_num [mom_six] at this ⊢; linarith

theorem mom_three : mom 3 = 0 := by simpa using mom_odd 1
theorem mom_five : mom 5 = 0 := by simpa using mom_odd 2
theorem mom_seven : mom 7 = 0 := by simpa using mom_odd 3

/-- polynomial with monomial coefficients `l`, starting at exponent `n`. -/
noncomputable def pev : ℕ → List ℝ → ℝ → ℝ
  | _, [], _ => 0
  | n, a :: l, c => a * c ^ n + pev (n + 1) l c

/-- the corresponding moment sum. -/
noncomputable def lint : ℕ → List ℝ → ℝ
  | _, [] => 0
  | n, a :: l => a * mom n + lint (n + 1) l

theorem integral_pev (n : ℕ) (l : List ℝ) :
    ∫ t in (0 : ℝ)..1, pev n l (Real.cos (2 * Real.pi * t)) = lint n l := by
  induction l generalizing n with
  | nil => simp [pev, lint]
  | cons a l ih =>
    simp only [pev, lint]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, ih (n + 1)]
    · rfl
    · exact (by fun_prop : Continuous fun t : ℝ => a * Real.cos (2 * Real.pi * t) ^ n)
        |>.intervalIntegrable _ _
    · have : Continuous fun t : ℝ => pev (n + 1) l (Real.cos (2 * Real.pi * t)) := by
        clear ih
        induction l generalizing n with
        | nil => simp only [pev]; fun_prop
        | cons b l ih2 =>
          simp only [pev]
          exact (by fun_prop : Continuous fun t : ℝ => b * Real.cos (2 * Real.pi * t) ^ (n + 1)).add
            (ih2 (n + 1))
      exact this.intervalIntegrable _ _

theorem int_HOrd {k : ℕ} {X : ℝ → ℝ → ℝ} (hX : HOrd k X) :
    ∃ K h0 : ℝ, 0 ≤ K ∧ 0 < h0 ∧ ∀ h : ℝ, |h| ≤ h0 →
      |∫ t in (0 : ℝ)..1, X h (Real.cos (2 * Real.pi * t))| ≤ K * |h| ^ k := by
  obtain ⟨K, h0, hK, hh0, H⟩ := hX
  refine ⟨K, h0, hK, hh0, fun h hh => ?_⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t => X h (Real.cos (2 * Real.pi * t))) (C := K * |h| ^ k)
    (fun t _ => by
      simpa using H h _ hh (Real.abs_cos_le_one _))
  simpa using this

/-! ### Integrals of the polynomial coefficients -/

theorem g2P_eq (c : ℝ) : g2P c = pev 0 [4, 0, -8] c := by simp [pev, g2P]; ring
theorem g3P_eq (c : ℝ) : g3P c = pev 0 [0, 404 / 15, 0, -512 / 15] c := by simp [pev, g3P]; ring
theorem g4P_eq (c : ℝ) :
    g4P c = pev 0 [896 / 225, 0, -17182 / 225, 0, 8888 / 45, 0, -10912 / 75, 0, 512 / 25] c := by
  simp [pev, g4P]; ring
theorem two_c_sq_eq (c : ℝ) : 2 * c ^ 2 = pev 0 [0, 0, 2] c := by simp [pev]

theorem int_g2 : ∫ t in (0 : ℝ)..1, g2P (Real.cos (2 * Real.pi * t)) = 0 := by
  simp only [g2P_eq]; rw [integral_pev]
  simp [lint, mom_zero, mom_two]; norm_num

theorem int_g3 : ∫ t in (0 : ℝ)..1, g3P (Real.cos (2 * Real.pi * t)) = 0 := by
  simp only [g3P_eq]; rw [integral_pev]
  simp [lint, mom_one, mom_three, mom_zero]

theorem int_g4 : ∫ t in (0 : ℝ)..1, g4P (Real.cos (2 * Real.pi * t)) = 0 := by
  simp only [g4P_eq]; rw [integral_pev]
  simp [lint, mom_zero, mom_two, mom_four, mom_six, mom_eight, mom_one, mom_three, mom_five,
    mom_seven]
  norm_num

theorem int_two_c_sq : ∫ t in (0 : ℝ)..1, 2 * Real.cos (2 * Real.pi * t) ^ 2 = 1 := by
  have := integral_pev 0 [0, 0, 2]
  simp only [pev, lint] at this
  simp [mom_two] at this
  simpa using this

theorem cont_t (f : ℝ → ℝ → ℝ) (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) (h : ℝ) :
    Continuous fun t : ℝ => f h (Real.cos (2 * Real.pi * t)) := by
  have : Continuous fun t : ℝ => (h, Real.cos (2 * Real.pi * t)) := by fun_prop
  exact hf.comp this

theorem cont_uP : Continuous fun p : ℝ × ℝ => uP p.1 p.2 := by unfold uP; fun_prop
theorem cont_eP : Continuous fun p : ℝ × ℝ => eP p.1 p.2 := by unfold eP c3P; fun_prop
theorem cont_WP : Continuous fun p : ℝ × ℝ => WP p.1 p.2 := by unfold WP VP; fun_prop
theorem cont_FaP : Continuous fun p : ℝ × ℝ => FaP p.1 p.2 := by
  unfold FaP E2 WP VP qP uP c3P; fun_prop
theorem cont_FbP : Continuous fun p : ℝ × ℝ => FbP p.1 p.2 := by
  unfold FbP E2 Q4P uP c3P; fun_prop
theorem cont_GP : Continuous fun p : ℝ × ℝ => GP p.1 p.2 := by
  have h2 : Continuous fun p : ℝ × ℝ => 2 * (1 - 16 / 15 * p.1 ^ 2) := by fun_prop
  unfold GP
  exact cont_FaP.sub (h2.mul cont_FbP)
theorem cont_SP : Continuous fun p : ℝ × ℝ => SP p.1 p.2 := by unfold SP; fun_prop
theorem cont_SBP : Continuous fun p : ℝ × ℝ => SBP p.1 p.2 := by unfold SBP; fun_prop

theorem cont_AIP (h : ℝ) (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) :
    Continuous fun t : ℝ => AIP h (Real.cos (2 * Real.pi * t)) := by
  have hu := cont_t _ cont_uP h
  exact (cont_t _ cont_eP h).mul ((cont_t _ cont_WP h).div (continuous_const.add hu)
    (fun t => (hpos t).ne'))

theorem cont_BIP (h : ℝ) (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) :
    Continuous fun t : ℝ => BIP h (Real.cos (2 * Real.pi * t)) := by
  have hu := cont_t _ cont_uP h
  have h1 : Continuous fun t : ℝ => 1 + uP h (Real.cos (2 * Real.pi * t)) :=
    continuous_const.add hu
  exact (cont_t _ cont_eP h).mul ((h1.mul (h1.log (fun t => (hpos t).ne'))).sub hu)

/-! ### The real-analysis core -/

theorem hord_SP : HOrd 0 SP := HOrd.zero_of_cont cont_SP
theorem hord_SBP3 : HOrd 3 (fun h c => h ^ 3 * SBP h c) := HOrd.of_cont cont_SBP

theorem core_trial :
    ∃ K h0 : ℝ, 0 ≤ K ∧ 0 < h0 ∧ ∀ h : ℝ, 0 < |h| → |h| ≤ h0 →
      (∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) ∧
      h ^ 2 / 2 ≤ ∫ t in (0 : ℝ)..1, BIP h (Real.cos (2 * Real.pi * t)) ∧
      ∫ t in (0 : ℝ)..1, AIP h (Real.cos (2 * Real.pi * t)) ≤
        2 * (1 - 16 / 15 * h ^ 2 + K * |h| ^ 3) * ∫ t in (0 : ℝ)..1, BIP h (Real.cos (2 * Real.pi * t)) := by
  obtain ⟨h1, hh1, H1⟩ := u_small
  obtain ⟨KA, hA0, hKA, hhA, HA⟩ := int_HOrd hord_remA
  obtain ⟨KB, hB0, hKB, hhB, HB⟩ := int_HOrd hord_remB
  obtain ⟨KS, hS0, hKS, hhS, HS⟩ := int_HOrd hord_SP
  obtain ⟨KT, hT0, hKT, hhT, HT⟩ := int_HOrd hord_SBP3
  refine ⟨KA + 2 * KB + KS, min (min (min hA0 hB0) (min hS0 hT0)) (min (min h1 1)
    (1 / (2 * (KT + KB) + 2))), by positivity, ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hhA hhB) (lt_min hhS hhT)) (lt_min (lt_min hh1 one_pos)
      (by positivity))
  intro h hP0 hh
  have hhA' : |h| ≤ hA0 := hh.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhB' : |h| ≤ hB0 := hh.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhS' : |h| ≤ hS0 := hh.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhT' : |h| ≤ hT0 := hh.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hh1' : |h| ≤ h1 := hh.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hh2' : |h| ≤ 1 := hh.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hh3' : |h| ≤ 1 / (2 * (KT + KB) + 2) := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t)) := by
    intro t
    have := (abs_le.1 (H1 h _ hh1' (Real.abs_cos_le_one (2 * Real.pi * t)))).1
    linarith
  refine ⟨hpos, ?_⟩
  -- notation
  have cA := cont_AIP h hpos
  have cB := cont_BIP h hpos
  have cFa := cont_t _ cont_FaP h
  have cFb := cont_t _ cont_FbP h
  have cG := cont_t _ cont_GP h
  have cS := cont_t _ cont_SP h
  have cT : Continuous fun t : ℝ => h ^ 3 * SBP h (Real.cos (2 * Real.pi * t)) :=
    continuous_const.mul (cont_t _ cont_SBP h)
  have cg2 : Continuous fun t : ℝ => g2P (Real.cos (2 * Real.pi * t)) := by unfold g2P; fun_prop
  have cg3 : Continuous fun t : ℝ => g3P (Real.cos (2 * Real.pi * t)) := by unfold g3P; fun_prop
  have cg4 : Continuous fun t : ℝ => g4P (Real.cos (2 * Real.pi * t)) := by unfold g4P; fun_prop
  have c2c : Continuous fun t : ℝ => 2 * Real.cos (2 * Real.pi * t) ^ 2 := by fun_prop
  have e1 : ∫ t in (0 : ℝ)..1, (AIP h (Real.cos (2 * Real.pi * t)) - FaP h (Real.cos (2 * Real.pi * t)))
      = (∫ t in (0 : ℝ)..1, AIP h (Real.cos (2 * Real.pi * t))) -
        ∫ t in (0 : ℝ)..1, FaP h (Real.cos (2 * Real.pi * t)) :=
    intervalIntegral.integral_sub (cA.intervalIntegrable _ _) (cFa.intervalIntegrable _ _)
  have e2 : ∫ t in (0 : ℝ)..1, (BIP h (Real.cos (2 * Real.pi * t)) - FbP h (Real.cos (2 * Real.pi * t)))
      = (∫ t in (0 : ℝ)..1, BIP h (Real.cos (2 * Real.pi * t))) -
        ∫ t in (0 : ℝ)..1, FbP h (Real.cos (2 * Real.pi * t)) :=
    intervalIntegral.integral_sub (cB.intervalIntegrable _ _) (cFb.intervalIntegrable _ _)
  have e3 : ∫ t in (0 : ℝ)..1, GP h (Real.cos (2 * Real.pi * t))
      = (∫ t in (0 : ℝ)..1, FaP h (Real.cos (2 * Real.pi * t))) -
        2 * (1 - 16 / 15 * h ^ 2) * ∫ t in (0 : ℝ)..1, FbP h (Real.cos (2 * Real.pi * t)) := by
    simp only [GP]
    rw [intervalIntegral.integral_sub (cFa.intervalIntegrable _ _)
      ((by exact continuous_const.mul cFb : Continuous fun t : ℝ =>
        2 * (1 - 16 / 15 * h ^ 2) * FbP h (Real.cos (2 * Real.pi * t))).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
  have e4 : ∫ t in (0 : ℝ)..1, GP h (Real.cos (2 * Real.pi * t))
      = h ^ 5 * ∫ t in (0 : ℝ)..1, SP h (Real.cos (2 * Real.pi * t)) := by
    simp only [GP_eq]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      int_g2, int_g3, int_g4]
    · ring
    all_goals first
      | exact ((continuous_const.mul cg2).add (continuous_const.mul cg3)).add
          (continuous_const.mul cg4) |>.intervalIntegrable _ _
      | exact ((continuous_const.mul cg2).add (continuous_const.mul cg3)).intervalIntegrable _ _
      | exact (continuous_const.mul cg2).intervalIntegrable _ _
      | exact (continuous_const.mul cg3).intervalIntegrable _ _
      | exact (continuous_const.mul cg4).intervalIntegrable _ _
      | exact (continuous_const.mul cS).intervalIntegrable _ _
  have e5 : ∫ t in (0 : ℝ)..1, FbP h (Real.cos (2 * Real.pi * t))
      = h ^ 2 + ∫ t in (0 : ℝ)..1, h ^ 3 * SBP h (Real.cos (2 * Real.pi * t)) := by
    simp only [FbP_eq]
    rw [intervalIntegral.integral_add ((by exact continuous_const.mul c2c : Continuous fun t : ℝ =>
        h ^ 2 * (2 * Real.cos (2 * Real.pi * t) ^ 2)).intervalIntegrable _ _)
      (cT.intervalIntegrable _ _), intervalIntegral.integral_const_mul, int_two_c_sq, mul_one]
  have bA := HA h hhA'
  have bB := HB h hhB'
  have bS := HS h hhS'
  have bT := HT h hhT'
  rw [e1] at bA
  rw [e2] at bB
  simp only [pow_zero, mul_one] at bS
  generalize (∫ t in (0 : ℝ)..1, AIP h (Real.cos (2 * Real.pi * t))) = a at *
  generalize (∫ t in (0 : ℝ)..1, BIP h (Real.cos (2 * Real.pi * t))) = b at *
  generalize (∫ t in (0 : ℝ)..1, FaP h (Real.cos (2 * Real.pi * t))) = fa at *
  generalize (∫ t in (0 : ℝ)..1, FbP h (Real.cos (2 * Real.pi * t))) = fb at *
  generalize (∫ t in (0 : ℝ)..1, GP h (Real.cos (2 * Real.pi * t))) = g at *
  generalize (∫ t in (0 : ℝ)..1, SP h (Real.cos (2 * Real.pi * t))) = IS at *
  generalize (∫ t in (0 : ℝ)..1, h ^ 3 * SBP h (Real.cos (2 * Real.pi * t))) = T at *
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have hpow5 : |h ^ 5 * IS| ≤ KS * |h| ^ 5 := by
    rw [abs_mul, abs_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right bS (by positivity)
  have hgb : |g| ≤ KS * |h| ^ 5 := by rw [e4]; exact hpow5
  have hKP : (KT + KB) * |h| ≤ 1 / 2 := by
    have : |h| * (2 * (KT + KB) + 2) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hh3'
    nlinarith [abs_nonneg h]
  have hP2 : |h| ^ 5 ≤ |h| ^ 3 := pow_le_pow_of_le_one (abs_nonneg _) hh2' (by norm_num)
  have hP3 : 0 ≤ |h| ^ 3 := by positivity
  have hb : h ^ 2 / 2 ≤ b := by
    have h1' := (abs_le.1 bT).1
    have h2' := (abs_le.1 bB).1
    have h3' : (KT + KB) * |h| ^ 3 ≤ |h| ^ 2 / 2 := by
      have : (KT + KB) * |h| ^ 3 = ((KT + KB) * |h|) * |h| ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg |h|]
    have h4 : KB * |h| ^ 5 ≤ KB * |h| ^ 3 := mul_le_mul_of_nonneg_left hP2 hKB
    linarith
  refine ⟨hb, ?_⟩
  have hk1 : |2 * (1 - 16 / 15 * h ^ 2)| ≤ 2 := by
    have h2s : h ^ 2 ≤ 1 := by
      rw [hsq]; nlinarith [abs_nonneg h]
    have h2n : 0 ≤ h ^ 2 := sq_nonneg h
    rw [abs_le]; constructor <;> linarith
  have hrA := (abs_le.1 bA).2
  have hrB : |b - fb| ≤ KB * |h| ^ 5 := bB
  have hmain : a - 2 * (1 - 16 / 15 * h ^ 2) * b ≤ (KA + 2 * KB + KS) * |h| ^ 5 := by
    have e6 : a - 2 * (1 - 16 / 15 * h ^ 2) * b
        = (a - fa) + g - 2 * (1 - 16 / 15 * h ^ 2) * (b - fb) := by
      linear_combination (-1 : ℝ) * e3
    have h7 : |2 * (1 - 16 / 15 * h ^ 2) * (b - fb)| ≤ 2 * (KB * |h| ^ 5) := by
      rw [abs_mul]
      exact mul_le_mul hk1 hrB (abs_nonneg _) (by norm_num)
    have := (abs_le.1 h7).1
    have := (abs_le.1 hgb).2
    rw [e6]
    linarith
  have hP5 : |h| ^ 5 = |h| ^ 3 * h ^ 2 := by rw [hsq]; ring
  have hKt : 0 ≤ KA + 2 * KB + KS := by positivity
  have : (KA + 2 * KB + KS) * |h| ^ 5 ≤ (KA + 2 * KB + KS) * |h| ^ 3 * (2 * b) := by
    rw [hP5]
    have : h ^ 2 ≤ 2 * b := by linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hKt hP3)
    linarith
  linarith


/-! ### Harmonic cancellation against the von Mises weight -/

theorem harm_key (h : ℝ) (T : ℝ → ℝ) (hT : Continuous T) (hTp : Function.Periodic T 1)
    (hsum : ∀ u, T u + T (u + 1 / 3) + T (u + 2 / 3) = 0) :
    ∫ t in (0 : ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T t = 0 := by
  set φ : ℝ → ℝ := fun t => Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T t with hφ
  have hφc : Continuous φ := by simp only [hφ]; fun_prop
  have hφp : Function.Periodic φ 1 := by
    intro t
    simp only [hφ]
    have : 2 * Real.pi * 3 * (t + 1) = 2 * Real.pi * 3 * t + (3 : ℕ) * (2 * Real.pi) := by
      push_cast; ring
    rw [this, Real.cos_add_nat_mul_two_pi, hTp t]
  have e1 : ∀ t, φ (t + 1 / 3) = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T (t + 1 / 3) := by
    intro t; simp only [hφ]
    have : 2 * Real.pi * 3 * (t + 1 / 3) = 2 * Real.pi * 3 * t + 2 * Real.pi := by ring
    rw [this, Real.cos_add_two_pi]
  have e2 : ∀ t, φ (t + 2 / 3) = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * T (t + 2 / 3) := by
    intro t; simp only [hφ]
    have : 2 * Real.pi * 3 * (t + 2 / 3) = 2 * Real.pi * 3 * t + (2 : ℕ) * (2 * Real.pi) := by
      push_cast; ring
    rw [this, Real.cos_add_nat_mul_two_pi]
  have s1 := integral_shift_unit hφp (1 / 3)
  have s2 := integral_shift_unit hφp (2 / 3)
  have hsum' : ∫ t in (0 : ℝ)..1, (φ t + φ (t + 1 / 3) + φ (t + 2 / 3)) = 0 := by
    have : ∀ t, φ t + φ (t + 1 / 3) + φ (t + 2 / 3)
        = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * (T t + T (t + 1 / 3) + T (t + 2 / 3)) := by
      intro t; rw [e1, e2]; simp only [hφ]; ring
    simp only [this, hsum, mul_zero]; simp
  have hi : ∀ a, IntervalIntegrable (fun t => φ (t + a)) MeasureSpace.volume 0 1 := by
    intro a
    exact (hφc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hi0 : IntervalIntegrable φ MeasureSpace.volume 0 1 := hφc.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi0.add (hi (1 / 3))) (hi (2 / 3)),
    intervalIntegral.integral_add hi0 (hi (1 / 3)), s1, s2] at hsum'
  simp only [hφ] at hsum' ⊢
  linarith

theorem cos2_three_sum (θ : ℝ) :
    Real.cos (2 * θ) + Real.cos (2 * (θ + 2 * Real.pi / 3)) +
      Real.cos (2 * (θ + 4 * Real.pi / 3)) = 0 := by
  have a1 : 2 * (θ + 2 * Real.pi / 3) = 2 * θ + 4 * Real.pi / 3 := by ring
  have a2 : 2 * (θ + 4 * Real.pi / 3) = (2 * θ + 2 * Real.pi / 3) + 2 * Real.pi := by ring
  rw [a1, a2, Real.cos_add_two_pi]
  have := cos_three_sum (2 * θ)
  linarith

theorem cos4_three_sum (θ : ℝ) :
    Real.cos (4 * θ) + Real.cos (4 * (θ + 2 * Real.pi / 3)) +
      Real.cos (4 * (θ + 4 * Real.pi / 3)) = 0 := by
  have a1 : 4 * (θ + 2 * Real.pi / 3) = (4 * θ + 2 * Real.pi / 3) + 2 * Real.pi := by ring
  have a2 : 4 * (θ + 4 * Real.pi / 3) = (4 * θ + 4 * Real.pi / 3) + (2 : ℕ) * (2 * Real.pi) := by
    push_cast; ring
  rw [a1, a2, Real.cos_add_two_pi, Real.cos_add_nat_mul_two_pi]
  exact cos_three_sum (4 * θ)

/-- `u` as a trigonometric polynomial (harmonics 1, 2, 4). -/
theorem uP_cos_form (h θ : ℝ) :
    uP h (Real.cos θ) = 2 * h * Real.cos θ +
      h ^ 2 * (5 / 3 * Real.cos (2 * θ) - 1 / 5 * Real.cos (4 * θ)) := by
  have h4 : 4 * θ = 2 * (2 * θ) := by ring
  rw [h4, Real.cos_two_mul (2 * θ), Real.cos_two_mul θ]
  unfold uP
  ring

/-- `u` has mean zero against the von Mises weight. -/
theorem integral_exp_uP (h : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
      uP h (Real.cos (2 * Real.pi * t)) = 0 := by
  refine harm_key h (fun t => uP h (Real.cos (2 * Real.pi * t))) ?_ ?_ ?_
  · unfold uP; fun_prop
  · intro t
    have : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
    simp only [this, Real.cos_add_two_pi]
  · intro u
    have e1 : 2 * Real.pi * (u + 1 / 3) = 2 * Real.pi * u + 2 * Real.pi / 3 := by ring
    have e2 : 2 * Real.pi * (u + 2 / 3) = 2 * Real.pi * u + 4 * Real.pi / 3 := by ring
    simp only [e1, e2, uP_cos_form]
    have c1 := cos_three_sum (2 * Real.pi * u)
    have c2 := cos2_three_sum (2 * Real.pi * u)
    have c4 := cos4_three_sum (2 * Real.pi * u)
    linear_combination (2 * h) * c1 + (h ^ 2 * (5 / 3)) * c2 - (h ^ 2 / 5) * c4

/-! ### The trial density -/

/-- The positive factor `1 + u` of the trial density, on the circle. -/
def Fd (h : ℝ) (x : Torus 1) : ℝ := 1 + uP h (cosHarm 1 x)

/-- The trial density `ρ = μ_h (1 + u)`. -/
def Phi (h : ℝ) (x : Torus 1) : ℝ := referenceDensity h x * Fd h x

/-- The square root of the trial density. -/
def sT (h : ℝ) (x : Torus 1) : ℝ := Real.sqrt (Phi h x)

theorem Phi_lift (h : ℝ) (y : Fin 1 → ℝ) :
    Phi h (torusLift y) = Real.exp (h * Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) * y 0)) / besselI 0 h *
      (1 + uP h (Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * y 0))) := by
  simp only [Phi, Fd, referenceDensity, cosHarm_lift]

theorem contDiff_Phi (h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Phi h ∘ torusLift) := by
  have : (Phi h ∘ torusLift) = fun y : Fin 1 → ℝ =>
      Real.exp (h * Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) * y 0)) / besselI 0 h *
        (1 + uP h (Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * y 0))) := by
    funext y; exact Phi_lift h y
  rw [this]
  unfold uP
  fun_prop

theorem Fd_pt (h t : ℝ) : Fd h (pt t) = 1 + uP h (Real.cos (2 * Real.pi * t)) := by
  simp [Fd, cosHarm_pt]

theorem Phi_pt (h t : ℝ) : Phi h (pt t) = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h *
    (1 + uP h (Real.cos (2 * Real.pi * t))) := by
  rw [Phi, referenceDensity_pt, Fd_pt]

theorem isSmoothPeriodic_Phi (h : ℝ) : IsSmoothPeriodic (Phi h) := contDiff_Phi h

theorem Phi_pos {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) (x : Torus 1) :
    0 < Phi h x := by
  obtain ⟨t, rfl⟩ := bs_exists_pt x
  rw [Phi, referenceDensity_pt, Fd_pt]
  exact mul_pos (div_pos (Real.exp_pos _) besselI_zero_pos) (hpos t)

theorem isSmoothPeriodic_sT {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) :
    IsSmoothPeriodic (sT h) := by
  have hc := contDiff_Phi h
  unfold IsSmoothPeriodic
  exact ContDiff.sqrt hc fun z => (Phi_pos hpos _).ne'

theorem sT_sq {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) (x : Torus 1) :
    sT h x ^ 2 = Phi h x := by
  unfold sT; exact Real.sq_sqrt (Phi_pos hpos x).le

theorem continuous_Phi (h : ℝ) : Continuous (Phi h) := (isSmoothPeriodic_Phi h).continuous_torus

/-- The mean of the weight is `1`, on the interval. -/
theorem integral_E_interval (h : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h = 1 := by
  have := integral_referenceDensity_eq_one h
  rw [integral_haar_one _ (continuous_referenceDensity h)] at this
  simpa only [referenceDensity_pt] using this

theorem integral_Phi (h : ℝ) :
    ∫ x, Phi h x ∂haar 1 = 1 := by
  rw [integral_haar_one _ (continuous_Phi h)]
  simp only [Phi_pt]
  have hc : Continuous fun t : ℝ => Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h := by
    fun_prop
  have hu : Continuous fun t : ℝ => uP h (Real.cos (2 * Real.pi * t)) := by unfold uP; fun_prop
  have e : ∀ t : ℝ, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h *
      (1 + uP h (Real.cos (2 * Real.pi * t))) =
      Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h +
        (besselI 0 h)⁻¹ * (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
          uP h (Real.cos (2 * Real.pi * t))) := by
    intro t; ring
  simp only [e]
  have hm : Continuous fun t : ℝ => (besselI 0 h)⁻¹ * (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
      uP h (Real.cos (2 * Real.pi * t))) := by unfold uP; fun_prop
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hm.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_exp_uP, integral_E_interval]
  ring

/-- The trial state as an absolute-admissible density. -/
def trialDensity {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) :
    AbsoluteDensity 1 where
  sqrt := sT h
  sqrt_mem := ⟨_, (isSmoothPeriodic_sT hpos).isWeakGradient⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  mass_one := by
    simp only [sT_sq hpos]
    exact integral_Phi h

theorem c3P_cos (θ : ℝ) : c3P (Real.cos θ) = Real.cos (2 * Real.pi * 3 * (θ / (2 * Real.pi))) := by
  have : 2 * Real.pi * 3 * (θ / (2 * Real.pi)) = 3 * θ := by
    field_simp
  rw [this, Real.cos_three_mul]; unfold c3P; ring

theorem eP_cos (h t : ℝ) :
    eP h (Real.cos (2 * Real.pi * t)) = Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) := by
  have := c3P_cos (2 * Real.pi * t)
  have e : 2 * Real.pi * t / (2 * Real.pi) = t := by field_simp
  rw [e] at this
  unfold eP
  rw [this]

theorem continuous_pt' : Continuous fun t : ℝ => pt t :=
  SharpLSI.continuous_liftT.comp (continuous_pi fun _ => continuous_id)

theorem continuous_BIP_cos {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) :
    Continuous fun t : ℝ => BIP h (Real.cos (2 * Real.pi * t)) := by
  have := cont_BIP h hpos
  exact this

theorem entropy_trial {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) :
    ordinaryEntropy h (trialDensity hpos) = ENNReal.ofReal
      ((besselI 0 h)⁻¹ * ∫ t in (0 : ℝ)..1, BIP h (Real.cos (2 * Real.pi * t))) := by
  rw [ordinaryEntropy_eq, circleEntropy_eq]
  have hd : ∀ x, (trialDensity hpos).density x = Phi h x := fun x => sT_sq hpos x
  simp only [hd]
  have c1 : Continuous fun x => Phi h x * Real.log (Phi h x) :=
    (continuous_Phi h).mul ((continuous_Phi h).log fun x => (Phi_pos hpos x).ne')
  have c2 : Continuous fun x => Phi h x * Real.log (referenceDensity h x) :=
    (continuous_Phi h).mul ((continuous_referenceDensity h).log fun x =>
      (referenceDensity_pos (h := h) x).ne')
  rw [integral_haar_one _ c1, integral_haar_one _ c2]
  congr 1
  have hI0 := besselI_zero_pos (h := h)
  have hcE : Continuous fun t : ℝ => Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) := by fun_prop
  have hcu : Continuous fun t : ℝ => uP h (Real.cos (2 * Real.pi * t)) := by unfold uP; fun_prop
  have hcF : Continuous fun t : ℝ => 1 + uP h (Real.cos (2 * Real.pi * t)) := by
    unfold uP; fun_prop
  have hlogF : Continuous fun t : ℝ => Real.log (1 + uP h (Real.cos (2 * Real.pi * t))) :=
    hcF.log fun t => (hpos t).ne'
  have hint1 : ∫ t in (0 : ℝ)..1, (Phi h (pt t) * Real.log (Phi h (pt t)) -
      Phi h (pt t) * Real.log (referenceDensity h (pt t))) =
      ∫ t in (0 : ℝ)..1, (besselI 0 h)⁻¹ * (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
        ((1 + uP h (Real.cos (2 * Real.pi * t))) * Real.log (1 + uP h (Real.cos (2 * Real.pi * t))))) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Phi_pt, referenceDensity_pt]
    have hE : 0 < Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h :=
      div_pos (Real.exp_pos _) hI0
    rw [Real.log_mul hE.ne' (hpos t).ne']
    field_simp
    ring
  have hB : ∫ t in (0 : ℝ)..1, BIP h (Real.cos (2 * Real.pi * t)) =
      ∫ t in (0 : ℝ)..1, Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
        ((1 + uP h (Real.cos (2 * Real.pi * t))) * Real.log (1 + uP h (Real.cos (2 * Real.pi * t)))) := by
    have e : ∀ t : ℝ, BIP h (Real.cos (2 * Real.pi * t)) =
        Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
          ((1 + uP h (Real.cos (2 * Real.pi * t))) * Real.log (1 + uP h (Real.cos (2 * Real.pi * t)))) -
        Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) * uP h (Real.cos (2 * Real.pi * t)) := by
      intro t; unfold BIP; rw [eP_cos]; ring
    simp only [e]
    have i1 : IntervalIntegrable (fun t : ℝ => Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
        ((1 + uP h (Real.cos (2 * Real.pi * t))) * Real.log (1 + uP h (Real.cos (2 * Real.pi * t)))))
        MeasureSpace.volume 0 1 := (hcE.mul (hcF.mul hlogF)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t : ℝ => Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) *
        uP h (Real.cos (2 * Real.pi * t))) MeasureSpace.volume 0 1 :=
      (hcE.mul hcu).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 i2, integral_exp_uP, sub_zero]
  rw [hB, ← intervalIntegral.integral_const_mul, ← hint1, intervalIntegral.integral_sub]
  · exact (c1.comp continuous_pt').intervalIntegrable _ _
  · exact (c2.comp continuous_pt').intervalIntegrable _ _

/-! ### The Fisher information of the trial state -/

theorem fisher_alg (E F l F' s : ℝ) (hE : 0 < E) (hF : 0 < F) (hs : 0 < s) (hs2 : s ^ 2 = E * F) :
    (2 * ((E * l * F + E * F') / (2 * s)) - s * l) ^ 2 = E * F' ^ 2 / F := by
  have h1 : 2 * ((E * l * F + E * F') / (2 * s)) - s * l = E * F' / s := by
    field_simp
    linear_combination (-l) * hs2
  rw [h1, div_pow, mul_pow, hs2]
  field_simp

theorem hasDerivAt_uP (h c : ℝ) : HasDerivAt (fun c => uP h c) (VP h c) c := by
  have h4 := (hasDerivAt_pow 4 c).const_mul (-8 / 5 : ℝ)
  have h2 := (hasDerivAt_pow 2 c).const_mul (74 / 15 : ℝ)
  have hin := (h4.add h2).sub_const (28 / 15 : ℝ)
  have hmid := ((hasDerivAt_id c).const_mul (2 : ℝ)).add (hin.const_mul h)
  have h1 := hmid.const_mul h
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [VP]
    push_cast
    ring
  · exact Filter.Eventually.of_forall fun x => by simp [uP]

theorem hasDerivAt_Eh (h t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h)
      (Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h * sg0 h t) t := by
  have h1 := ((((hasDerivAt_id t).const_mul (2 * Real.pi * 3)).cos.const_mul h).exp).div_const (besselI 0 h)
  refine h1.congr_deriv ?_
  simp only [id_eq, mul_one, sg0]
  have : 6 * Real.pi * t = 2 * Real.pi * 3 * t := by ring
  rw [this]
  ring

theorem hasDerivAt_Fh (h t : ℝ) :
    HasDerivAt (fun t : ℝ => 1 + uP h (Real.cos (2 * Real.pi * t)))
      (VP h (Real.cos (2 * Real.pi * t)) * (-(2 * Real.pi) * Real.sin (2 * Real.pi * t))) t := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * Real.pi * t))
      (-Real.sin (2 * Real.pi * t) * (2 * Real.pi)) t := by
    have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).cos
    simpa using this
  have := ((hasDerivAt_uP h (Real.cos (2 * Real.pi * t))).comp t hc).const_add 1
  exact this.congr_deriv (by ring)

theorem fisher_pointwise {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) (t : ℝ) :
    (2 * coordPartial 0 (sT h) (pt t) - sT h (pt t) * sigT h (pt t)) ^ 2 =
      4 * Real.pi ^ 2 / besselI 0 h * AIP h (Real.cos (2 * Real.pi * t)) := by
  have hI0 := besselI_zero_pos (h := h)
  set E : ℝ := Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h with hE
  set F : ℝ := 1 + uP h (Real.cos (2 * Real.pi * t)) with hF
  have hE0 : 0 < E := div_pos (Real.exp_pos _) hI0
  have hF0 : 0 < F := hpos t
  have hsfun : (fun t : ℝ => sT h (pt t)) = fun t : ℝ =>
      Real.sqrt ((Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h) *
        (1 + uP h (Real.cos (2 * Real.pi * t)))) := by
    funext t
    show Real.sqrt (Phi h (pt t)) = _
    rw [Phi_pt]
  have hP : 0 < E * F := mul_pos hE0 hF0
  have hd1 : HasDerivAt (fun t : ℝ => sT h (pt t))
      ((Real.exp (h * Real.cos (2 * Real.pi * 3 * t)) / besselI 0 h * sg0 h t * F +
        E * (VP h (Real.cos (2 * Real.pi * t)) * (-(2 * Real.pi) * Real.sin (2 * Real.pi * t)))) /
        (2 * Real.sqrt (E * F))) t := by
    rw [hsfun]
    exact ((hasDerivAt_Eh h t).mul (hasDerivAt_Fh h t)).sqrt hP.ne'
  have hd2 := hasDerivAt_smooth_one (isSmoothPeriodic_sT hpos) t
  have hcp := hd2.unique hd1
  have hs : 0 < Real.sqrt (E * F) := Real.sqrt_pos.mpr hP
  have hs2 : Real.sqrt (E * F) ^ 2 = E * F := Real.sq_sqrt hP.le
  have hsT : sT h (pt t) = Real.sqrt (E * F) := by
    show Real.sqrt (Phi h (pt t)) = _
    rw [Phi_pt]
  have hsig : sigT h (pt t) = sg0 h t := sigT_lift h t
  rw [hcp, hsT, hsig]
  have := fisher_alg E F (sg0 h t) (VP h (Real.cos (2 * Real.pi * t)) *
    (-(2 * Real.pi) * Real.sin (2 * Real.pi * t))) _ hE0 hF0 hs hs2
  rw [this]
  have hsin : Real.sin (2 * Real.pi * t) ^ 2 = 1 - Real.cos (2 * Real.pi * t) ^ 2 := by
    rw [Real.sin_sq]
  unfold AIP WP
  rw [eP_cos, ← hF]
  have : (VP h (Real.cos (2 * Real.pi * t)) * (-(2 * Real.pi) * Real.sin (2 * Real.pi * t))) ^ 2 =
      4 * Real.pi ^ 2 * (1 - Real.cos (2 * Real.pi * t) ^ 2) * VP h (Real.cos (2 * Real.pi * t)) ^ 2 := by
    rw [mul_pow, mul_pow, neg_sq, mul_pow, hsin]; ring
  rw [this, hE]
  field_simp

theorem fisher_trial {h : ℝ} (hpos : ∀ t : ℝ, 0 < 1 + uP h (Real.cos (2 * Real.pi * t))) :
    ordinaryFisher h (trialDensity hpos) = ENNReal.ofReal
      (4 * Real.pi ^ 2 / besselI 0 h * ∫ t in (0 : ℝ)..1, AIP h (Real.cos (2 * Real.pi * t))) := by
  rw [ordinaryFisher_eq]
  congr 1
  have hs := isSmoothPeriodic_sT hpos
  have hg := (isWeakGradient_weakGradient (trialDensity hpos).sqrt_mem).ae_eq hs.isWeakGradient
  have hl := logScore_ae_eq h
  have hae : (fun x => (2 * weakGradient (trialDensity hpos).sqrt (trialDensity hpos).sqrt_mem x 0 -
      (trialDensity hpos).sqrt x * logScore h x) ^ 2) =ᵐ[haar 1]
      fun x => (2 * coordPartial 0 (sT h) x - sT h x * sigT h x) ^ 2 := by
    filter_upwards [hg, hl] with x hx1 hx2
    have e1 : weakGradient (trialDensity hpos).sqrt (trialDensity hpos).sqrt_mem x 0 =
        coordPartial 0 (sT h) x := congrArg (fun v => v 0) hx1
    show (2 * _ - sT h x * _) ^ 2 = _
    rw [e1, hx2]
  rw [integral_congr_ae hae]
  have hc : Continuous fun x => (2 * coordPartial 0 (sT h) x - sT h x * sigT h x) ^ 2 :=
    (((continuous_const.mul (hs.continuous_coordPartial 0)).sub
      (hs.continuous_torus.mul (continuous_sigT h)))).pow 2
  rw [integral_haar_one _ hc]
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => fisher_pointwise hpos t

theorem trial_quotient :
    ∃ K1 h0 : ℝ, 0 ≤ K1 ∧ 0 < h0 ∧ ∀ h : ℝ, 0 < |h| → |h| ≤ h0 →
      ∃ ρ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ ∧
        (str025_quot h ρ).toReal ≤ 4 * Real.pi ^ 2 * (1 - 16 / 15 * h ^ 2 + K1 * |h| ^ 3) := by
  obtain ⟨K, h0, hK, hh0, H⟩ := core_trial
  refine ⟨K, h0, hK, hh0, fun h hh hh1 => ?_⟩
  obtain ⟨hpos, hB, hA⟩ := H h hh hh1
  have hI0 := besselI_zero_pos (h := h)
  have hh2 : 0 < h ^ 2 := by
    have : h ≠ 0 := abs_pos.mp hh
    positivity
  set A := ∫ t in (0 : ℝ)..1, AIP h (Real.cos (2 * Real.pi * t)) with hAdef
  set B := ∫ t in (0 : ℝ)..1, BIP h (Real.cos (2 * Real.pi * t)) with hBdef
  have hB0 : 0 < B := lt_of_lt_of_le (half_pos hh2) hB
  have hent : 0 < (besselI 0 h)⁻¹ * B := mul_pos (inv_pos.mpr hI0) hB0
  have hA0 : 0 ≤ A := by
    refine intervalIntegral.integral_nonneg zero_le_one fun t _ => ?_
    have hc1 : Real.cos (2 * Real.pi * t) ^ 2 ≤ 1 := Real.cos_sq_le_one _
    unfold AIP WP eP
    have := hpos t
    have h3 : 0 ≤ 1 - Real.cos (2 * Real.pi * t) ^ 2 := by linarith
    positivity
  have hfpos : 0 ≤ 4 * Real.pi ^ 2 / besselI 0 h * A :=
    mul_nonneg (div_nonneg (by positivity) hI0.le) hA0
  refine ⟨trialDensity hpos, ?_, ?_⟩
  · rw [entropy_trial hpos]
    exact ENNReal.ofReal_pos.mpr hent
  · unfold str025_quot
    rw [entropy_trial hpos, fisher_trial hpos]
    have e2 : (2 : ENNReal) * ENNReal.ofReal ((besselI 0 h)⁻¹ * B) =
        ENNReal.ofReal (2 * ((besselI 0 h)⁻¹ * B)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    rw [e2, ENNReal.toReal_div, ENNReal.toReal_ofReal hfpos,
      ENNReal.toReal_ofReal (mul_nonneg two_pos.le hent.le)]
    rw [div_le_iff₀ (mul_pos two_pos hent)]
    have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hA (div_nonneg hpi hI0.le)
    calc 4 * Real.pi ^ 2 / besselI 0 h * A
        ≤ 4 * Real.pi ^ 2 / besselI 0 h * (2 * (1 - 16 / 15 * h ^ 2 + K * |h| ^ 3) * B) := this
      _ = _ := by field_simp

theorem optimizer_trial_bound {h K1 : ℝ} (ρ : AbsoluteDensity 1)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' → str025_quot h ρ ≤ str025_quot h ρ')
    (ρ₁ : AbsoluteDensity 1) (h1 : 0 < ordinaryEntropy h ρ₁)
    (hq : (str025_quot h ρ₁).toReal ≤ 4 * Real.pi ^ 2 * (1 - 16 / 15 * h ^ 2 + K1 * |h| ^ 3)) :
    (str025_quot h ρ).toReal / (4 * Real.pi ^ 2) - 1 ≤ -16 / 15 * h ^ 2 + K1 * |h| ^ 3 := by
  have hne : str025_quot h ρ₁ ≠ ⊤ := by
    unfold str025_quot
    refine ENNReal.div_ne_top (str025_fisher_ne_top h ρ₁) ?_
    exact mul_ne_zero two_ne_zero h1.ne'
  have h2 := ENNReal.toReal_mono hne (hmin ρ₁ h1)
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  rw [sub_le_iff_le_add, div_le_iff₀ hpi]
  nlinarith

theorem allOptimizers_trial (K : ℝ) (hK : 0 ≤ K) (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a b h γ E : ℝ) (ρ : AbsoluteDensity 1), 0 < |h| → |h| ≤ ε →
      a ^ 2 + b ^ 2 ≤ ε ^ 2 → |γ| ≤ ε → 0 < a ^ 2 + b ^ 2 →
      γ = (str025_quot h ρ).toReal / (4 * Real.pi ^ 2) - 1 →
      0 < ordinaryEntropy h ρ →
      (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
        str025_quot h ρ ≤ str025_quot h ρ') →
      -γ / 2 - 9 / 20 * h ^ 2 - h * ((a ^ 3 - 3 * a * b ^ 2) / (a ^ 2 + b ^ 2)) / 12 +
        (a ^ 2 + b ^ 2) / 48 + E = 0 →
      |E| ≤ K * ((|h| + Real.sqrt (a ^ 2 + b ^ 2)) ^ 3 + |γ| * (|h| + Real.sqrt (a ^ 2 + b ^ 2)) +
        γ ^ 2) →
      |γ| + (a ^ 2 + b ^ 2) ≤ 192 * h ^ 2 ∧ |h| / 2 < Real.sqrt (a ^ 2 + b ^ 2) ∧
      ((a / h - 2) ^ 2 + (b / h) ^ 2 < η ^ 2 ∨
        (a / h + 1) ^ 2 + (b / h - Real.sqrt 3) ^ 2 < η ^ 2 ∨
        (a / h + 1) ^ 2 + (b / h + Real.sqrt 3) ^ 2 < η ^ 2) := by
  obtain ⟨K1, h0, hK1, hh0, Ht⟩ := trial_quotient
  obtain ⟨ε1, hε1, Hc⟩ := allOptimizers_core K K1 hK hK1 η hη
  refine ⟨min ε1 h0, lt_min hε1 hh0, ?_⟩
  intro a b h γ E ρ hh hhε hab hγ hab0 hγdef _ hmin heq hE
  have hε : min ε1 h0 ≤ ε1 := min_le_left _ _
  have hh1 : |h| ≤ h0 := hhε.trans (min_le_right _ _)
  obtain ⟨ρ₁, h1, hq⟩ := Ht h hh hh1
  have htrial := optimizer_trial_bound ρ hmin ρ₁ h1 hq
  rw [← hγdef] at htrial
  have hε2 : (min ε1 h0) ^ 2 ≤ ε1 ^ 2 :=
    pow_le_pow_left₀ (lt_min hε1 hh0).le hε 2
  exact Hc a b h γ E hh (hhε.trans hε) (hab.trans hε2) (hγ.trans hε) hab0 heq hE htrial

end

end DGPS.Examples.ThreeSpeciesCircle.TrialState
