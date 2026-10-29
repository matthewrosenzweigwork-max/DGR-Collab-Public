import FullLabeledLSI.Nonvacuity.Prop82.B1Convergence

/-!
# Lane B, module 3: the quotient near the Haar density

For admissible `ρ` with small Fisher information the quotient `D / (2G)` is
at least `3a/2 - η`.  This is the only place where the threshold `3a/2` is
sharp: for `ρ = 1 + δ cos` the quotient is exactly `3a/2`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Prop82

attribute [local fun_prop] SharpLSI.continuous_sCos

/-! ### The sup-norm radius in terms of the Fisher information -/

noncomputable def epsOf (I : Real) : Real :=
  (Real.sqrt (I / 4) + I / 4) * (2 + (Real.sqrt (I / 4) + I / 4))

theorem epsOf_nonneg {I : Real} (hI : 0 ≤ I) : 0 ≤ epsOf I := by
  unfold epsOf
  have := Real.sqrt_nonneg (I / 4)
  have : 0 ≤ I / 4 := by positivity
  positivity

theorem continuous_epsOf : Continuous epsOf := by
  unfold epsOf
  fun_prop

theorem epsOf_zero : epsOf 0 = 0 := by simp [epsOf]

theorem ae_abs_sub_one_le_eps {rho : Torus 1 → Real} (h : Admissible cosV (cosW 1) rho) :
    ∀ᵐ x ∂haar 1, |rho x - 1| ≤ epsOf (fisher rho) := by
  filter_upwards [ae_abs_sub_one_le h.1 h.2.1 h.2.2.1] with x hx
  have hf : (∫ y, weakGrad (fun x => Real.sqrt (rho x)) y 0 ^ 2 ∂haar 1) = fisher rho / 4 := by
    rw [fisher_eq_sqrt_energy h]; ring
  rw [hf] at hx
  exact hx

/-! ### The force energy near the Haar density -/

theorem integral_Gp_sq (C S : Real) :
    ∫ x, (2 * π * (-C * sCos x + S * gCos x)) ^ 2 ∂haar 1 = aCos * (C ^ 2 / 2 + S ^ 2 / 2) := by
  have i1 : Integrable (fun x => sCos x ^ 2) (haar 1) := SharpLSI.integrable_of_continuous (by fun_prop)
  have i2 : Integrable (fun x => sCos x * gCos x) (haar 1) := SharpLSI.integrable_of_continuous (by fun_prop)
  have i3 : Integrable (fun x => gCos x ^ 2) (haar 1) := SharpLSI.integrable_of_continuous (by fun_prop)
  have e : ∀ x, (2 * π * (-C * sCos x + S * gCos x)) ^ 2 =
      aCos * (C ^ 2 * sCos x ^ 2 - 2 * (C * S) * (sCos x * gCos x) + S ^ 2 * gCos x ^ 2) :=
    fun x => by unfold aCos; ring
  simp_rw [e]
  rw [integral_const_mul,
    integral_add (f := fun x => C ^ 2 * sCos x ^ 2 - 2 * (C * S) * (sCos x * gCos x))
      (g := fun x => S ^ 2 * gCos x ^ 2) ((i1.const_mul _).sub (i2.const_mul _))
      (i3.const_mul _),
    integral_sub (f := fun x => C ^ 2 * sCos x ^ 2) (g := fun x => 2 * (C * S) * (sCos x * gCos x))
      (i1.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_sCos_sq,
    integral_sCos_gCos, integral_gCos_sq]
  ring

theorem forceEnergy_ge {rho : Torus 1 → Real} (h : Admissible cosV (cosW 1) rho) {ε : Real}
    (hε : ∀ᵐ x ∂haar 1, |rho x - 1| ≤ ε) :
    (1 - ε) * (aCos * firstMode rho / 2) ≤ forceEnergy rho := by
  have h1 := h.2.1
  have hi := integrable_of_integral_eq_one h1
  set C := mom gCos rho with hC
  set S := mom sCos rho with hS
  set Gp : Torus 1 → Real := fun x => 2 * π * (-C * sCos x + S * gCos x) with hGp
  have hGc : Continuous Gp := by rw [hGp]; fun_prop
  have hb : ∀ x, |Gp x ^ 2| ≤ (2 * π * (|C| + |S|)) ^ 2 := by
    intro x
    have hin : |-C * sCos x + S * gCos x| ≤ |C| + |S| := by
      calc |-C * sCos x + S * gCos x| ≤ |-C * sCos x| + |S * gCos x| := abs_add_le _ _
        _ = |C| * |sCos x| + |S| * |gCos x| := by rw [abs_mul, abs_mul, abs_neg]
        _ ≤ |C| * 1 + |S| * 1 := by
            gcongr
            · exact abs_sCos_le x
            · exact abs_gCos_le x
        _ = |C| + |S| := by ring
    rw [abs_pow, hGp]
    simp only
    rw [abs_mul, abs_of_pos (by positivity : (0 : Real) < 2 * π)]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hin (by positivity)) 2
  have iGp : Integrable (fun x => Gp x ^ 2 * rho x) (haar 1) :=
    integrable_mom hi (hGc.pow 2) hb
  have hP : forceEnergy rho = ∫ x, rho x * Gp x ^ 2 ∂haar 1 := by
    unfold forceEnergy
    refine integral_congr_ae ?_
    filter_upwards [weakGrad_gConv_ae h1] with x hx
    rw [hx]
  have hconst : Integrable (fun x => (1 - ε) * Gp x ^ 2) (haar 1) :=
    ((SharpLSI.integrable_of_continuous (hGc.pow 2)).const_mul _)
  have hmono : ∫ x, (1 - ε) * Gp x ^ 2 ∂haar 1 ≤ ∫ x, rho x * Gp x ^ 2 ∂haar 1 := by
    refine integral_mono_ae hconst (by simpa [mul_comm] using iGp) ?_
    filter_upwards [hε] with x hx
    have : 1 - ε ≤ rho x := by linarith [(abs_le.mp hx).1]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  rw [hP]
  refine le_trans (le_of_eq ?_) hmono
  rw [integral_const_mul, hGp, integral_Gp_sq, firstMode_eq_mom hi]
  ring

/-! ### Near-equilibrium bounds -/

theorem near_bounds {rho : Torus 1 → Real} (h : Admissible cosV (cosW 1) rho) {ε : Real}
    (hε1 : ε < 1) (hε : ∀ᵐ x ∂haar 1, |rho x - 1| ≤ ε) :
    2 * firstMode rho ≤ ∫ x, (rho x - 1) ^ 2 ∂haar 1 ∧
    aCos * (4 * ∫ x, (rho x - 1) ^ 2 ∂haar 1 - 6 * firstMode rho) ≤ (1 + ε) * fisher rho ∧
    entropy rho ≤ (∫ x, (rho x - 1) ^ 2 ∂haar 1) / (2 * (1 - ε)) ∧
    (1 - ε) * (aCos * firstMode rho / 2) ≤ forceEnergy rho := by
  obtain ⟨hf1, hf2⟩ := fourier_near_bounds h.1 h.2.1 h.2.2.1 hε
  have hρ2 := memLp_two_of_sqrt_memH1 h.1 h.2.1 h.2.2.1
  refine ⟨hf1, ?_, ?_, forceEnergy_ge h hε⟩
  · rw [fisher_eq_sqrt_energy h]
    exact hf2
  · exact (klDiv_near_bounds h.1 h.2.1 hρ2 hε1 hε).2

/-! ### The real-algebra lemma -/

theorem algebra_bound {a S q ε κ D G : Real} (_ha : 0 < a) (hq : 0 ≤ q) (hS : 2 * q ≤ S)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hG0 : 0 < G)
    (hD : a * (4 * S - 6 * q) / (1 + ε) + 2 * a * q + (1 - ε) * (a * q / 2) ≤ D)
    (hG : 2 * G ≤ S / (1 - ε) + q) (hκ : 0 ≤ κ)
    (hα : κ / (1 - ε) ≤ 4 * a / (1 + ε))
    (hγ : κ * (2 / (1 - ε) + 1) ≤ a * (2 / (1 + ε) + 5 / 2 - ε / 2)) :
    κ ≤ D / (2 * G) := by
  rw [le_div_iff₀ (by positivity)]
  have h1ε : 0 < 1 - ε := by linarith
  have h1ε' : 0 < 1 + ε := by linarith
  set x := 1 / (1 + ε) with hx
  set y := 1 / (1 - ε) with hy
  have hD' : a * (4 * S - 6 * q) * x + 2 * a * q + (1 - ε) * (a * q / 2) ≤ D := by
    have : a * (4 * S - 6 * q) / (1 + ε) = a * (4 * S - 6 * q) * x := by rw [hx]; ring
    linarith
  have hG' : 2 * G ≤ S * y + q := by
    have : S / (1 - ε) = S * y := by rw [hy]; ring
    linarith
  have hα' : κ * y ≤ 4 * a * x := by
    have e1 : κ / (1 - ε) = κ * y := by rw [hy]; ring
    have e2 : 4 * a / (1 + ε) = 4 * a * x := by rw [hx]; ring
    linarith
  have hγ' : κ * (2 * y + 1) ≤ a * (2 * x + 5 / 2 - ε / 2) := by
    have e1 : 2 / (1 - ε) = 2 * y := by rw [hy]; ring
    have e2 : 2 / (1 + ε) = 2 * x := by rw [hx]; ring
    rw [e1, e2] at hγ
    exact hγ
  have hu : 0 ≤ S - 2 * q := by linarith
  have hαn : 0 ≤ 4 * a * x - κ * y := by linarith
  have hγn : 0 ≤ a * (2 * x + 5 / 2 - ε / 2) - κ * (2 * y + 1) := by linarith
  have key : κ * (S * y + q) ≤ D := by
    nlinarith [mul_nonneg hαn hu, mul_nonneg hγn hq]
  nlinarith [mul_le_mul_of_nonneg_left hG' hκ]

/-! ### The quotient bound -/

theorem quotient_ge_of_eps {rho : Torus 1 → Real} (h : Admissible cosV (cosW 1) rho)
    {ε κ : Real} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hεa : ∀ᵐ x ∂haar 1, |rho x - 1| ≤ ε)
    (hκ : 0 ≤ κ) (hα : κ / (1 - ε) ≤ 4 * aCos / (1 + ε))
    (hγ : κ * (2 / (1 - ε) + 1) ≤ aCos * (2 / (1 + ε) + 5 / 2 - ε / 2)) :
    κ ≤ realDiss rho / (2 * realGap rho) := by
  obtain ⟨n1, n2, n3, n4⟩ := near_bounds h hε1 hεa
  set S := ∫ x, (rho x - 1) ^ 2 ∂haar 1
  have hq := firstMode_nonneg rho
  have h1ε : 0 < 1 - ε := by linarith
  have h1ε' : 0 < 1 + ε := by linarith
  refine algebra_bound a_pos hq n1 hε0 hε1 (realGap_pos h) ?_ ?_ hκ hα hγ
  · have hI : aCos * (4 * S - 6 * firstMode rho) / (1 + ε) ≤ fisher rho :=
      (div_le_iff₀ h1ε').mpr (by linarith)
    unfold realDiss
    linarith
  · have : 2 * entropy rho ≤ S / (1 - ε) := by
      have := mul_le_mul_of_nonneg_left n3 (by norm_num : (0 : Real) ≤ 2)
      calc 2 * entropy rho ≤ 2 * (S / (2 * (1 - ε))) := this
        _ = S / (1 - ε) := by field_simp
    unfold realGap
    linarith

theorem eventually_quotient_ge {rho : ℕ → Torus 1 → Real}
    (ha : ∀ n, Admissible cosV (cosW 1) (rho n))
    (hI : Tendsto (fun n => fisher (rho n)) atTop (𝓝 0)) {η : Real} (hη : 0 < η) :
    ∀ᶠ n in atTop, 3 * aCos / 2 - η ≤ realDiss (rho n) / (2 * realGap (rho n)) := by
  have ha0 := a_pos
  set η' := min η aCos with hη'
  have hη'0 : 0 < η' := lt_min hη ha0
  have hη'a : η' ≤ aCos := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  set κ := 3 * aCos / 2 - η' with hκ
  have hκ0 : 0 ≤ κ := by linarith
  set e : ℕ → Real := fun n => epsOf (fisher (rho n)) with he
  have hε : Tendsto e atTop (𝓝 0) := by
    have := (continuous_epsOf.tendsto 0).comp hI
    rwa [epsOf_zero] at this
  have h1 : Tendsto (fun n => 1 + e n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).add hε
  have h2 : Tendsto (fun n => 1 - e n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hε
  have hα : Tendsto (fun n => 4 * aCos / (1 + e n) - κ / (1 - e n)) atTop
      (𝓝 (4 * aCos / 1 - κ / 1)) :=
    (tendsto_const_nhds.div h1 one_ne_zero).sub (tendsto_const_nhds.div h2 one_ne_zero)
  have hγ : Tendsto (fun n => aCos * (2 / (1 + e n) + 5 / 2 - e n / 2) -
      κ * (2 / (1 - e n) + 1)) atTop
      (𝓝 (aCos * (2 / 1 + 5 / 2 - 0 / 2) - κ * (2 / 1 + 1))) :=
    (((tendsto_const_nhds.div h1 one_ne_zero).add tendsto_const_nhds).sub
      (hε.div_const 2)).const_mul aCos |>.sub
      ((((tendsto_const_nhds.div h2 one_ne_zero).add tendsto_const_nhds)).const_mul κ)
  have hαpos := hα.eventually (lt_mem_nhds (by linarith : (0 : Real) < 4 * aCos / 1 - κ / 1))
  have hγpos := hγ.eventually (lt_mem_nhds
    (by rw [hκ]; linarith : (0 : Real) < aCos * (2 / 1 + 5 / 2 - 0 / 2) - κ * (2 / 1 + 1)))
  have hlt1 := hε.eventually (gt_mem_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hαpos, hγpos, hlt1] with n hαn hγn hlt
  have hen0 : 0 ≤ e n := epsOf_nonneg (fisher_nonneg _)
  have := quotient_ge_of_eps (ha n) hen0 hlt (ae_abs_sub_one_le_eps (ha n)) hκ0
    (by linarith) (by linarith)
  linarith

end SharpLSI.FL.Prop82
