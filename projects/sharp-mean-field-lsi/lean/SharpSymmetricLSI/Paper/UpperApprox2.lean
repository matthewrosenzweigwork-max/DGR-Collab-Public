import SharpSymmetricLSI.Paper.UpperApprox

/-!
# Smooth approximation of admissible densities, part 2 (Phase 3, lane D; R6)
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

theorem memLp_two_lintegral_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (two_ne_zero) ENNReal.ofNat_ne_top
    h.eLpNorm_lt_top
  simpa using this.ne

/-- `s ↦ √(s² + t)` for `t > 0`. -/
noncomputable def sqrtShift (t : ℝ) (s : ℝ) : ℝ := Real.sqrt (s ^ 2 + t)

theorem hasDerivAt_sqrtShift {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt (sqrtShift t) (s / Real.sqrt (s ^ 2 + t)) s := by
  have h1 : HasDerivAt (fun s => s ^ 2 + t) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const t
  have h2 := h1.sqrt (by positivity)
  rw [show sqrtShift t = fun y => Real.sqrt (y ^ 2 + t) from rfl]
  convert h2 using 1
  have : 0 < Real.sqrt (s ^ 2 + t) := Real.sqrt_pos.mpr (by positivity)
  field_simp

theorem deriv_sqrtShift {t : ℝ} (ht : 0 < t) :
    deriv (sqrtShift t) = fun s => s / Real.sqrt (s ^ 2 + t) :=
  funext fun s => (hasDerivAt_sqrtShift ht s).deriv

theorem abs_div_sqrtShift_le {t : ℝ} (ht : 0 < t) (s : ℝ) : |s / Real.sqrt (s ^ 2 + t)| ≤ 1 := by
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (by positivity)), div_le_one (Real.sqrt_pos.mpr
    (by positivity))]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

theorem contDiff_sqrtShift {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (sqrtShift t) := by
  unfold sqrtShift
  exact ((contDiff_id.pow 2).add contDiff_const).sqrt fun s => by positivity

theorem continuous_sqrtShift (t : ℝ) : Continuous (sqrtShift t) := by
  unfold sqrtShift; fun_prop

theorem abs_sqrtShift_sub_abs {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    abs (sqrtShift t s - abs s) ≤ Real.sqrt t := by
  unfold sqrtShift
  have h1 : |s| ≤ Real.sqrt (s ^ 2 + t) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (s ^ 2 + t) ≤ |s| + Real.sqrt t := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt ht
    nlinarith [abs_nonneg s, Real.sqrt_nonneg t, sq_abs s]
  rw [abs_of_nonneg (by linarith)]
  linarith

section Abstract

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

theorem L2Tendsto.of_lintegral_le {f : ℕ → α → ℝ} {g : α → ℝ} {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) (hle : ∀ n, ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ ≤ e n) :
    L2Tendsto μ f g :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ => zero_le) hle

/-- Lemma A: `√((vⱼ² + tⱼ)/cⱼ) → u` in `L²`. -/
theorem L2Tendsto_sqrt_approx {v : ℕ → α → ℝ} {u : α → ℝ} {c t : ℕ → ℝ} (hu0 : ∀ x, 0 ≤ u x)
    (hc : ∀ j, 1 / 2 ≤ c j) (ht : ∀ j, 0 ≤ t j) (htl : Tendsto t atTop (𝓝 0))
    (hcl : Tendsto c atTop (𝓝 1)) (hv : L2Tendsto μ v u) (hvm : ∀ j, AEMeasurable (v j) μ)
    (hum : AEMeasurable u μ) (hu2 : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    L2Tendsto μ (fun j x => sqrtShift (t j) (v j x) / Real.sqrt (c j)) u := by
  have hcpos : ∀ j, 0 < c j := fun j => lt_of_lt_of_le (by norm_num) (hc j)
  set a : ℕ → ℝ := fun j => 1 / Real.sqrt (c j) with ha
  have ha_le : ∀ j, |a j| ≤ 2 := fun j => by
    have h1 : Real.sqrt (1 / 2) ≤ Real.sqrt (c j) := Real.sqrt_le_sqrt (hc j)
    have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [abs_of_pos (div_pos one_pos (Real.sqrt_pos.mpr (hcpos j)))]
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (hcpos j))]; linarith
  have hal : Tendsto a atTop (𝓝 1) := by
    have := ((Real.continuous_sqrt.tendsto 1).comp hcl).inv₀ (by simp)
    simpa [ha, Real.sqrt_one] using this
  -- three pieces
  set T1 : ℕ → α → ℝ := fun j x => a j * (sqrtShift (t j) (v j x) - |v j x|)
  set T2 : ℕ → α → ℝ := fun j x => a j * (|v j x| - u x)
  set T3 : ℕ → α → ℝ := fun j x => (a j - 1) * u x
  have h1 : L2Tendsto μ T1 (fun _ => 0) := by
    refine L2Tendsto.of_lintegral_le (e := fun j => ENNReal.ofReal (4 * t j)) ?_ fun j => ?_
    · have := ENNReal.tendsto_ofReal (htl.const_mul 4)
      simpa using this
    · calc ∫⁻ x, ‖T1 j x - 0‖ₑ ^ 2 ∂μ ≤ ∫⁻ _, ENNReal.ofReal (4 * t j) ∂μ := by
            refine lintegral_mono fun x => ?_
            rw [sub_zero, ← ofReal_sq_eq_enorm_sq]
            refine ENNReal.ofReal_le_ofReal ?_
            have hb := abs_sqrtShift_sub_abs (ht j) (v j x)
            have hs := Real.sq_sqrt (ht j)
            calc T1 j x ^ 2 = a j ^ 2 * (sqrtShift (t j) (v j x) - |v j x|) ^ 2 := by ring
              _ ≤ 2 ^ 2 * Real.sqrt (t j) ^ 2 := by
                  have ha2 : a j ^ 2 ≤ 2 ^ 2 := by
                    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (ha_le j) 2
                  have hb2 : (sqrtShift (t j) (v j x) - |v j x|) ^ 2 ≤ Real.sqrt (t j) ^ 2 := by
                    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
                  exact mul_le_mul ha2 hb2 (sq_nonneg _) (by positivity)
              _ = 4 * t j := by rw [hs]; ring
        _ = ENNReal.ofReal (4 * t j) := by simp
  have h2 : L2Tendsto μ T2 (fun _ => 0) := by
    refine (hv.const_mul 2).of_le fun j x => ?_
    rw [sub_zero, ← ofReal_sq_eq_enorm_sq, ← ofReal_sq_eq_enorm_sq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hvu : |(|v j x| - u x)| ≤ |v j x - u x| := by
      have := abs_abs_sub_abs_le_abs_sub (v j x) (u x)
      rwa [abs_of_nonneg (hu0 x)] at this
    calc T2 j x ^ 2 = a j ^ 2 * (|v j x| - u x) ^ 2 := by ring
      _ ≤ 2 ^ 2 * (v j x - u x) ^ 2 := by
          have ha2 : a j ^ 2 ≤ 2 ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (ha_le j) 2
          have hb2 : (|v j x| - u x) ^ 2 ≤ (v j x - u x) ^ 2 := by
            rw [← sq_abs, ← sq_abs (v j x - u x)]
            exact pow_le_pow_left₀ (abs_nonneg _) hvu 2
          exact mul_le_mul ha2 hb2 (sq_nonneg _) (by positivity)
      _ = (2 * v j x - 2 * u x) ^ 2 := by ring
  have h3 : L2Tendsto μ T3 (fun _ => 0) := by
    have e : ∀ j, ∫⁻ x, ‖T3 j x - 0‖ₑ ^ 2 ∂μ = ‖a j - 1‖ₑ ^ 2 * ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := fun j => by
      rw [← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr fun x => ?_
      rw [sub_zero, enorm_mul, mul_pow]
    unfold L2Tendsto
    simp_rw [e]
    have hz : Tendsto (fun j => ‖a j - 1‖ₑ ^ 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun j => a j - 1) atTop (𝓝 0) := by simpa using hal.sub_const 1
      have h1' := (continuous_enorm.tendsto (0 : ℝ)).comp h0
      rw [enorm_zero] at h1'
      have h2' := ((ENNReal.continuous_pow 2).tendsto 0).comp h1'
      rw [zero_pow two_ne_zero] at h2'
      exact h2'
    have := ENNReal.Tendsto.mul_const hz (Or.inr hu2)
    simpa using this
  have hm1 : ∀ j, AEMeasurable (fun x => T1 j x - 0) μ := fun j => by
    simp only [sub_zero, T1]
    exact (((continuous_sqrtShift (t j)).measurable.comp_aemeasurable (hvm j)).sub
      (hvm j).abs).const_mul _
  have hm2 : ∀ j, AEMeasurable (fun x => (T1 j x + T2 j x) - (0 + 0)) μ := fun j => by
    simp only [add_zero, sub_zero, T1, T2]
    exact ((((continuous_sqrtShift (t j)).measurable.comp_aemeasurable (hvm j)).sub
      (hvm j).abs).const_mul _).add (((hvm j).abs.sub hum).const_mul _)
  have h123 := (h1.add h2 hm1).add h3 hm2
  refine h123.of_le fun j x => le_of_eq ?_
  congr 2
  simp only [T1, T2, T3, ha]
  field_simp
  ring

/-- Lemma B: `L²` convergence gives `L¹` convergence of the squares. -/
theorem tendsto_lintegral_sq_sub {f : ℕ → α → ℝ} {g : α → ℝ} (h : L2Tendsto μ f g) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hfB : ∀ j, ∫⁻ x, ‖f j x‖ₑ ^ 2 ∂μ ≤ B) (hgB : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≤ B)
    (hfm : ∀ j, AEMeasurable (f j) μ) (hgm : AEMeasurable g μ) :
    Tendsto (fun j => ∫⁻ x, ‖f j x ^ 2 - g x ^ 2‖ₑ ∂μ) atTop (𝓝 0) := by
  have h22 : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hb : ∀ j, ∫⁻ x, ‖f j x ^ 2 - g x ^ 2‖ₑ ∂μ ≤
      (∫⁻ x, ‖f j x - g x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (4 * B) ^ (1 / (2 : ℝ)) := fun j => by
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ h22
      (f := fun x => ‖f j x - g x‖ₑ) (g := fun x => ‖f j x + g x‖ₑ)
      ((hfm j).sub hgm).enorm ((hfm j).add hgm).enorm
    simp only [Pi.mul_apply, ENNReal.rpow_two] at hH
    have e : ∀ x, ‖f j x ^ 2 - g x ^ 2‖ₑ = ‖f j x - g x‖ₑ * ‖f j x + g x‖ₑ := fun x => by
      rw [← enorm_mul]; congr 1; ring
    simp_rw [e]
    refine hH.trans (mul_le_mul_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) _)
    calc ∫⁻ x, ‖f j x + g x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, (2 * ‖f j x‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2) ∂μ :=
          lintegral_mono fun x => enorm_add_sq_le _ _
      _ = 2 * ∫⁻ x, ‖f j x‖ₑ ^ 2 ∂μ + 2 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
          rw [lintegral_add_left' (((hfm j).enorm.pow_const 2).const_mul 2),
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * B + 2 * B := by gcongr; exact hfB j
      _ = 4 * B := by ring
  have hlim : Tendsto (fun j => (∫⁻ x, ‖f j x - g x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
      (4 * B) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (∫⁻ x, ‖f j x - g x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      exact this
    have := ENNReal.Tendsto.mul_const (b := (4 * B) ^ (1 / (2 : ℝ))) h1
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top (by norm_num) hB)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

theorem abs_inv_sqrt_le_two {c : ℝ} (hc : 1 / 2 ≤ c) : |1 / Real.sqrt c| ≤ 2 := by
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have h1 : Real.sqrt (1 / 2) ≤ Real.sqrt c := Real.sqrt_le_sqrt hc
  have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [abs_of_pos (div_pos one_pos (Real.sqrt_pos.mpr hcpos)),
    div_le_iff₀ (Real.sqrt_pos.mpr hcpos)]; linarith

/-- Lemma C: the gradient factor `cⱼ^{-1/2} vⱼ/√(vⱼ²+tⱼ) wⱼ → g` in `L²`. -/
theorem L2Tendsto_grad_approx {v w : ℕ → α → ℝ} {u gk : α → ℝ} {c t : ℕ → ℝ}
    (hc : ∀ j, 1 / 2 ≤ c j) (ht : ∀ j, 0 < t j) (htl : Tendsto t atTop (𝓝 0))
    (hcl : Tendsto c atTop (𝓝 1)) (hu0 : ∀ x, 0 ≤ u x)
    (hvae : ∀ᵐ x ∂μ, Tendsto (fun j => v j x) atTop (𝓝 (u x)))
    (hgz : ∀ᵐ x ∂μ, u x = 0 → gk x = 0) (hw : L2Tendsto μ w gk)
    (hvm : ∀ j, AEMeasurable (v j) μ) (hwm : ∀ j, AEMeasurable (w j) μ) (hgm : AEMeasurable gk μ)
    (hg2 : ∫⁻ x, ‖gk x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    L2Tendsto μ (fun j x => (1 / Real.sqrt (c j) * (v j x / Real.sqrt (v j x ^ 2 + t j))) * w j x)
      gk := by
  set m : ℕ → α → ℝ := fun j x => 1 / Real.sqrt (c j) * (v j x / Real.sqrt (v j x ^ 2 + t j))
  have hmb : ∀ j x, |m j x| ≤ 2 := fun j x => by
    simp only [m, abs_mul]
    calc |1 / Real.sqrt (c j)| * |v j x / Real.sqrt (v j x ^ 2 + t j)| ≤ 2 * 1 :=
          mul_le_mul (abs_inv_sqrt_le_two (hc j)) (abs_div_sqrtShift_le (ht j) _) (abs_nonneg _)
            (by norm_num)
      _ = 2 := mul_one 2
  have hmm : ∀ j, AEMeasurable (m j) μ := fun j =>
    aemeasurable_const.mul ((hvm j).div (((hvm j).pow_const 2).add_const _).sqrt)
  have h := L2Tendsto.mul_bdd (m := m) (m₀ := fun _ => 1) (M := 2) hw hmb (fun _ => by norm_num)
    (fun j => (hmm j).mul ((hwm j).sub hgm)) (fun j => ((hmm j).sub_const 1).mul hgm) ?_ hg2
  · exact h.of_le fun j x => by simp [m]
  · filter_upwards [hvae, hgz] with x hx hz
    by_cases hux : u x = 0
    · simp [hz hux]
    · have hup : 0 < u x := lt_of_le_of_ne (hu0 x) (Ne.symm hux)
      have hs : Tendsto (fun j => Real.sqrt (v j x ^ 2 + t j)) atTop (𝓝 (Real.sqrt (u x ^ 2 + 0))) :=
        (Real.continuous_sqrt.tendsto _).comp ((hx.pow 2).add htl)
      have hsu : Real.sqrt (u x ^ 2 + 0) = u x := by rw [add_zero, Real.sqrt_sq hup.le]
      rw [hsu] at hs
      have hc' : Tendsto (fun j => 1 / Real.sqrt (c j)) atTop (𝓝 (1 / Real.sqrt 1)) :=
        tendsto_const_nhds.div ((Real.continuous_sqrt.tendsto 1).comp hcl) (by simp)
      have hm1 : Tendsto (fun j => m j x) atTop (𝓝 (1 / Real.sqrt 1 * (u x / u x))) :=
        hc'.mul (hx.div hs hup.ne')
      rw [Real.sqrt_one, div_self hup.ne', div_one, one_mul] at hm1
      simpa using (hm1.sub_const 1).mul_const (gk x)

end Abstract

end SharpLSI
