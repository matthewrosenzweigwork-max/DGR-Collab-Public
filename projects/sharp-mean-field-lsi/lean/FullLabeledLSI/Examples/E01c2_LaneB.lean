import FullLabeledLSI.Examples.E01c_LaneB
import FullLabeledLSI.Examples.Paper.Sec9Prop97A

/-!
# E01c2: Lane B, Proposition 9.4 (`second_harmonic_small`)

Split from `E01c_LaneB` (Lemma 9.3) because it reuses the Lane C/D modules `Sec9Prop97A`, `Sec9DeficitReal`
and the proved `LaneD.lamG_formula`.  Everything is proved; no stub is used.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.LaneBb

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Def

/-- Lemma 9.3 in real form: `J(ρ) ≥ (48π²/11) |ρ̂(2)|²`. -/
theorem Jfun_ge {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    48 * π ^ 2 / 11 * (mcos 2 ρ ^ 2 + msin 2 ρ ^ 2) ≤ Def.Jfun aCos ρ := by
  have hmain := second_mode_remainder_proved ρ h0 h1 hH
  have hρi : Integrable ρ (haar 1) := integrable_of_integral_eq_one' h1
  have hq := circle_quantitative_lsi_aux h0 h1 hH
  have hKtop := hq.1
  have hItop := hq.2.1
  have hz : Complex.normSq (∫ x, fourier 2 (x 0) * (ρ x : ℂ) ∂haar 1) = mcos 2 ρ ^ 2 + msin 2 ρ ^ 2 := by
    have := normSq_fourier hρi 2
    simpa using this
  rw [hz] at hmain
  have haCos : aCos = 4 * π ^ 2 := rfl
  have hnn : 0 ≤ mcos 2 ρ ^ 2 + msin 2 ρ ^ 2 := by positivity
  have hfin1 : ENNReal.ofReal (2 * aCos) * klDiv (densMeasure ρ) (haar 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
  have := ENNReal.toReal_mono hItop hmain
  rw [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by rw [haCos]; positivity),
    ENNReal.toReal_ofReal (by rw [haCos]; positivity)] at this
  unfold Def.Jfun
  rw [haCos] at this ⊢
  nlinarith [this]


theorem mom_sq_le_one {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1) (k : ℕ) :
    mcos k ρ ^ 2 + msin k ρ ^ 2 ≤ 1 := by
  have hρi : Integrable ρ (haar 1) := integrable_of_integral_eq_one' h1
  rw [← normSq_fourier hρi k, Complex.normSq_eq_norm_sq]
  have hle : ‖∫ x, fourier (k : ℤ) (x 0) * (ρ x : ℂ) ∂haar 1‖ ≤ 1 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ x : Torus 1, ‖fourier (k : ℤ) (x 0) * (ρ x : ℂ)‖ ≤ ρ x := fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
      refine mul_le_of_le_one_left (h0 x) ?_
      exact ((fourier (k : ℤ)).norm_coe_le_norm (x 0)).trans (fourier_norm _).le
    calc ∫ x, ‖fourier (k : ℤ) (x 0) * (ρ x : ℂ)‖ ∂haar 1 ≤ ∫ x, ρ x ∂haar 1 :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hρi
            (Eventually.of_forall this)
      _ = 1 := h1
  nlinarith [norm_nonneg (∫ x, fourier (k : ℤ) (x 0) * (ρ x : ℂ) ∂haar 1)]


theorem mcos_bar (F : Family 1) (hF : F.Admissible) (j : ℤ) :
    mcos j F.bar = ∑ i, F.θ i * mcos j (F.ρ i) := by
  have hi : ∀ i, Integrable (F.ρ i) (haar 1) := fun i =>
    integrable_of_integral_eq_one' (hF.2.2 i).2.1
  unfold mcos Family.bar
  have : ∀ y, Reg.cosK j y * ∑ i, F.θ i * F.ρ i y = ∑ i, F.θ i * (Reg.cosK j y * F.ρ i y) := fun y => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ fun i _ => ((integrable_cosK_mul (hi i) j).const_mul (F.θ i))]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem msin_bar (F : Family 1) (hF : F.Admissible) (j : ℤ) :
    msin j F.bar = ∑ i, F.θ i * msin j (F.ρ i) := by
  have hi : ∀ i, Integrable (F.ρ i) (haar 1) := fun i =>
    integrable_of_integral_eq_one' (hF.2.2 i).2.1
  unfold msin Family.bar
  have : ∀ y, sinK j y * ∑ i, F.θ i * F.ρ i y = ∑ i, F.θ i * (sinK j y * F.ρ i y) := fun y => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ fun i _ => ((integrable_sinK_mul (hi i) j).const_mul (F.θ i))]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem jensen_sq (F : Family 1) (hF : F.Admissible) (x : Fin F.q → ℝ) :
    (∑ i, F.θ i * x i) ^ 2 ≤ ∑ i, F.θ i * x i ^ 2 := by
  set m := ∑ i, F.θ i * x i with hm
  have h1 : ∑ i, F.θ i * (x i - m) ^ 2 = ∑ i, F.θ i * x i ^ 2 - m ^ 2 := by
    have : ∀ i, F.θ i * (x i - m) ^ 2 = F.θ i * x i ^ 2 - 2 * m * (F.θ i * x i) + m ^ 2 * F.θ i := fun i => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hF.2.1, ← hm]
    ring
  have h2 : 0 ≤ ∑ i, F.θ i * (x i - m) ^ 2 := Finset.sum_nonneg fun i _ => mul_nonneg (hF.1 i).le (sq_nonneg _)
  linarith


theorem bracket_nonneg {c1 s1 c2 s2 : ℝ} (h : c2 ^ 2 + s2 ^ 2 ≤ 1) :
    0 ≤ c1 ^ 2 * (1 - c2) - 2 * c1 * s1 * s2 + s1 ^ 2 * (1 + c2) := by
  set N := c1 ^ 2 + s1 ^ 2 with hN
  set u := c1 ^ 2 - s1 ^ 2 with hu
  set v := 2 * c1 * s1 with hv
  have hNn : 0 ≤ N := by positivity
  have huv : u ^ 2 + v ^ 2 = N ^ 2 := by simp only [hN, hu, hv]; ring
  have hcs : (c2 * u + s2 * v) ^ 2 ≤ N ^ 2 := by
    nlinarith [sq_nonneg (c2 * v - s2 * u), sq_nonneg u, sq_nonneg v, mul_nonneg (sub_nonneg.2 h) (sq_nonneg u),
      mul_nonneg (sub_nonneg.2 h) (sq_nonneg v)]
  have habs := abs_le_of_sq_le_sq' hcs hNn
  have : c1 ^ 2 * (1 - c2) - 2 * c1 * s1 * s2 + s1 ^ 2 * (1 + c2) = N - (c2 * u + s2 * v) := by
    simp only [hN, hu, hv]; ring
  rw [this]
  linarith [habs.2]

theorem deficit_nonneg_k2 {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 6 / 77) (F : Family 1) (hF : F.Admissible) :
    0 ≤ deficit (attrW (harmKernel 2 a)) aCos F := by
  have hk : 1 ≤ 2 := by norm_num
  have ha1' : a ≤ 1 := by linarith
  have hde := deficit_eq hk ha0 ha1' aCos F hF
  have hb0 := bar_nonneg' F hF
  have hb1 := bar_integral' F hF
  have e2 : ((2 : ℕ) : ℤ) = 2 := by norm_num
  have e4 : (2 * ((2 : ℕ) : ℤ)) = ((4 : ℕ) : ℤ) := by norm_num
  rw [e2] at hde
  rw [show (2 * (2 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num] at hde
  rw [hde]
  set c1 := mcos 2 F.bar with hc1
  set s1 := msin 2 F.bar with hs1
  set c2 := mcos ((4 : ℕ) : ℤ) F.bar with hc2
  set s2 := msin ((4 : ℕ) : ℤ) F.bar with hs2
  have hmom := mom_sq_le_one hb0 hb1 4
  have hmom' : c2 ^ 2 + s2 ^ 2 ≤ 1 := hmom
  have hB := bracket_nonneg (c1 := c1) (s1 := s1) hmom'
  -- species part
  have hspec : ∀ i, 48 * π ^ 2 / 11 * (mcos 2 (F.ρ i) ^ 2 + msin 2 (F.ρ i) ^ 2) ≤ Def.Jfun aCos (F.ρ i) :=
    fun i => Jfun_ge (hF.2.2 i).1 (hF.2.2 i).2.1 (hF.2.2 i).2.2
  have hJ : 48 * π ^ 2 / 11 * (c1 ^ 2 + s1 ^ 2) ≤ ∑ i, F.θ i * Def.Jfun aCos (F.ρ i) := by
    have hj1 := jensen_sq F hF (fun i => mcos 2 (F.ρ i))
    have hj2 := jensen_sq F hF (fun i => msin 2 (F.ρ i))
    rw [← mcos_bar F hF] at hj1
    rw [← msin_bar F hF] at hj2
    calc 48 * π ^ 2 / 11 * (c1 ^ 2 + s1 ^ 2)
        ≤ 48 * π ^ 2 / 11 * (∑ i, F.θ i * mcos 2 (F.ρ i) ^ 2 + ∑ i, F.θ i * msin 2 (F.ρ i) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = ∑ i, F.θ i * (48 * π ^ 2 / 11 * (mcos 2 (F.ρ i) ^ 2 + msin 2 (F.ρ i) ^ 2)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, F.θ i * Def.Jfun aCos (F.ρ i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hspec i) (hF.1 i).le
  -- the interaction part
  have hpsi : Def.Psi 2 a aCos c1 s1 c2 s2 ≥ -(56 * π ^ 2 * a) * (c1 ^ 2 + s1 ^ 2) := by
    unfold Def.Psi Def.omg
    have haCos : aCos = 4 * π ^ 2 := rfl
    rw [haCos]
    push_cast
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg π)) hB]
  have hN : 0 ≤ c1 ^ 2 + s1 ^ 2 := by positivity
  have hπ : 0 < π ^ 2 := by positivity
  nlinarith [mul_nonneg hN hπ.le, mul_nonneg (mul_nonneg hN hπ.le) (sub_nonneg.2 ha1)]


theorem second_harmonic_small_proved {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 6 / 77) :
    HaarUniqueMinimizer (attrW (harmKernel 2 a)) ∧ AgreementAt (attrW (harmKernel 2 a)) aCos := by
  have hk : 1 ≤ 2 := by norm_num
  have ha1' : a < 1 := by linarith
  have hC := Def.goodKernel_harmKernel hk a
  have hmin := Def.harmKernel_isMinimizer hk ha0 ha1'.le
  refine ⟨P97.harmKernel_haarUnique hk ha0 ha1', ?_⟩
  have hℓ : 0 < aCos := by unfold aCos; positivity
  have hlow : ENNReal.ofReal aCos ≤ rMs zeroV (attrW (harmKernel 2 a)) :=
    P97.rMs_ge_of_deficit_nonneg hk hℓ.le (fun F hF => deficit_nonneg_k2 ha0 ha1 F hF)
  refine agreement_of_bounds_proved hC hmin (hyp_attr_aux hC) hℓ hlow ?_
  intro e lam Cm he hCm
  have hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat (harmKernel 2 a) n ≤ 1 - δ :=
    ⟨1 - a, by linarith, fun n _ => by have := P97.chat_harm_le_k hk ha0 n; linarith⟩
  rw [LaneD.lamG_formula hC hmin (hyp_attr_aux hC) hsup e lam Cm he hCm]
  refine (iInf_le _ 0).trans (le_of_eq ?_)
  have h1 : chat (harmKernel 2 a) (((0 : ℕ) : ℤ) + 1) = 0 := by
    rw [P97.chat_harm_k hk]; simp
  rw [h1]
  congr 1
  simp

/-! ### Statement-identity check -/

example : (type_of% @second_harmonic_small) = (type_of% @second_harmonic_small_proved) := rfl

end SharpLSI.FL.Ex.LaneBb

