import SharpSymmetricLSI.Infra.SobolevTorus

/-!
# `L²` convergence from a.e. convergence and an `L²` contraction bound (Phase 3, lane D)

If `fₙ → g` a.e. and `‖fₙ‖₂ ≤ ‖g‖₂ < ∞`, then `fₙ → g` in `L²` (Fatou applied to
`2|fₙ|² + 2|g|² - |fₙ - g|²`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

theorem enorm_sub_sq_le (a b : ℝ) : ‖a - b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  rw [← ofReal_sq_eq_enorm_sq a, ← ofReal_sq_eq_enorm_sq b, ← ofReal_sq_eq_enorm_sq (a - b),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a + b)])

theorem tendsto_L2_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ}
    {g : α → ℝ} (hfm : ∀ n, AEMeasurable (f n) μ) (hgm : AEMeasurable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hle : ∀ n, ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ)
    (hfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  set G := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ with hG
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ with ha
  have hgm2 : AEMeasurable (fun x => ‖g x‖ₑ ^ 2) μ := hgm.enorm.pow_const 2
  have hfm2 : ∀ n, AEMeasurable (fun x => ‖f n x‖ₑ ^ 2) μ := fun n => (hfm n).enorm.pow_const 2
  have hdm : ∀ n, AEMeasurable (fun x => ‖f n x - g x‖ₑ ^ 2) μ := fun n =>
    ((hfm n).sub hgm).enorm.pow_const 2
  have hsum : ∀ n, ∫⁻ x, (2 * ‖f n x‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2) ∂μ ≤ 4 * G := fun n => by
    rw [lintegral_add_left' ((hfm2 n).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
    calc 2 * ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ + 2 * G ≤ 2 * G + 2 * G := by gcongr; exact hle n
      _ = 4 * G := by ring
  have ha_le : ∀ n, a n ≤ 4 * G := fun n =>
    (lintegral_mono fun x => enorm_sub_sq_le _ _).trans (hsum n)
  have h4G : 4 * G ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hfin
  set h : ℕ → α → ℝ≥0∞ := fun n x =>
    (2 * ‖f n x‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2) - ‖f n x - g x‖ₑ ^ 2 with hh
  have hhm : ∀ n, AEMeasurable (h n) μ := fun n =>
    (((hfm2 n).const_mul 2).add (hgm2.const_mul 2)).sub (hdm n)
  -- pointwise limit
  have hlim : ∀ᵐ x ∂μ, liminf (fun n => h n x) atTop = 4 * ‖g x‖ₑ ^ 2 := by
    filter_upwards [hae] with x hx
    have h1 : Tendsto (fun n => ‖f n x‖ₑ ^ 2) atTop (𝓝 (‖g x‖ₑ ^ 2)) :=
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp (continuous_enorm.tendsto _ |>.comp hx)
    have h2 : Tendsto (fun n => ‖f n x - g x‖ₑ ^ 2) atTop (𝓝 0) := by
      have : Tendsto (fun n => f n x - g x) atTop (𝓝 0) := by
        simpa using hx.sub_const (g x)
      have := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp
        ((continuous_enorm.tendsto _).comp this)
      simp only [enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
      exact this
    have h3 : Tendsto (fun n => 2 * ‖f n x‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2) atTop
        (𝓝 (2 * ‖g x‖ₑ ^ 2 + 2 * ‖g x‖ₑ ^ 2)) :=
      (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num))).add_const _
    have h4 := ENNReal.Tendsto.sub h3 h2 (Or.inr ENNReal.zero_ne_top)
    rw [tsub_zero] at h4
    rw [h4.liminf_eq]; ring
  -- Fatou
  have hF := lintegral_liminf_le' hhm (μ := μ) (u := atTop)
  rw [lintegral_congr_ae hlim, lintegral_const_mul' _ _ (by norm_num)] at hF
  have hint : ∀ n, ∫⁻ x, h n x ∂μ ≤ 4 * G - a n := fun n => by
    simp only [hh]
    rw [lintegral_sub' (hdm n) ((ha_le n).trans_lt h4G.lt_top).ne
      (Eventually.of_forall fun x => enorm_sub_sq_le _ _)]
    exact tsub_le_tsub_right (hsum n) _
  have hF2 : 4 * G ≤ 4 * G - limsup a atTop := by
    calc 4 * G ≤ liminf (fun n => ∫⁻ x, h n x ∂μ) atTop := hF
      _ ≤ liminf (fun n => 4 * G - a n) atTop := liminf_le_liminf (Eventually.of_forall hint)
      _ = 4 * G - limsup a atTop := ENNReal.liminf_const_sub _ _ h4G
  have hL : limsup a atTop = 0 := by
    by_contra hne
    rcases eq_or_ne G 0 with hG0 | hG0
    · have : limsup a atTop ≤ 0 := by
        refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
        have := ha_le n; rw [hG0, mul_zero] at this; exact this
      exact hne (le_antisymm this zero_le)
    · have hpos : 0 < 4 * G := by positivity
      have := ENNReal.sub_lt_self h4G hpos.ne' hne
      exact absurd hF2 (not_le.mpr this)
  exact tendsto_of_le_liminf_of_limsup_le zero_le hL.le

end SharpLSI

namespace SharpLSI

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `L²` convergence `fₙ → f`. -/
def L2Tendsto (μ : Measure α) (f : ℕ → α → ℝ) (g : α → ℝ) : Prop :=
  Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)

theorem enorm_add_sq_le (a b : ℝ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have := enorm_sub_sq_le a (-b)
  simpa using this

theorem L2Tendsto.of_le {f f' : ℕ → α → ℝ} {g g' : α → ℝ} (h : L2Tendsto μ f g)
    (hle : ∀ n x, ‖f' n x - g' x‖ₑ ^ 2 ≤ ‖f n x - g x‖ₑ ^ 2) : L2Tendsto μ f' g' :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun n => lintegral_mono fun x => hle n x)

theorem L2Tendsto.add {f f' : ℕ → α → ℝ} {g g' : α → ℝ} (h : L2Tendsto μ f g)
    (h' : L2Tendsto μ f' g') (hm : ∀ n, AEMeasurable (fun x => f n x - g x) μ) :
    L2Tendsto μ (fun n x => f n x + f' n x) (fun x => g x + g' x) := by
  have hb : ∀ n, ∫⁻ x, ‖(f n x + f' n x) - (g x + g' x)‖ₑ ^ 2 ∂μ ≤
      2 * ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ + 2 * ∫⁻ x, ‖f' n x - g' x‖ₑ ^ 2 ∂μ := fun n => by
    rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ (by norm_num),
      ← lintegral_add_left' (((hm n).enorm.pow_const 2).const_mul 2)]
    refine lintegral_mono fun x => ?_
    have := enorm_add_sq_le (f n x - g x) (f' n x - g' x)
    rw [show f n x - g x + (f' n x - g' x) = (f n x + f' n x) - (g x + g' x) by ring] at this
    exact this
  have hlim : Tendsto (fun n => 2 * ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ +
      2 * ∫⁻ x, ‖f' n x - g' x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
    have := (ENNReal.Tendsto.const_mul (a := 2) h (Or.inr (by norm_num))).add
      (ENNReal.Tendsto.const_mul (a := 2) h' (Or.inr (by norm_num)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

theorem L2Tendsto.const_mul {f : ℕ → α → ℝ} {g : α → ℝ} (h : L2Tendsto μ f g) (c : ℝ) :
    L2Tendsto μ (fun n x => c * f n x) (fun x => c * g x) := by
  have e : ∀ n, ∫⁻ x, ‖c * f n x - c * g x‖ₑ ^ 2 ∂μ = ‖c‖ₑ ^ 2 * ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ :=
    fun n => by
      rw [← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr fun x => ?_
      rw [← mul_sub, enorm_mul, mul_pow]
  unfold L2Tendsto
  simp_rw [e]
  have := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ ^ 2) h (Or.inr (by simp))
  simpa using this

/-- Dominated convergence in `L²`: `cₙ f → c f` if `cₙ → c` a.e. boundedly and `f ∈ L²`. -/
theorem L2Tendsto.dominated {c : ℕ → α → ℝ} {c₀ f : α → ℝ} {C : ℝ}
    (hcm : ∀ n, AEMeasurable (fun x => (c n x - c₀ x) * f x) μ)
    (hC : ∀ n x, |c n x - c₀ x| ≤ C)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => (c n x - c₀ x) * f x) atTop (𝓝 0))
    (hf : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    L2Tendsto μ (fun n x => c n x * f x) (fun x => c₀ x * f x) := by
  unfold L2Tendsto
  have e : ∀ n x, c n x * f x - c₀ x * f x = (c n x - c₀ x) * f x := fun n x => by ring
  simp_rw [e]
  have hlim := tendsto_lintegral_of_dominated_convergence' (fun x => ‖C‖ₑ ^ 2 * ‖f x‖ₑ ^ 2)
    (F := fun n x => ‖(c n x - c₀ x) * f x‖ₑ ^ 2) (f := fun _ => 0)
    (fun n => (hcm n).enorm.pow_const 2)
    (fun n => Eventually.of_forall fun x => by
      show ‖(c n x - c₀ x) * f x‖ₑ ^ 2 ≤ ‖C‖ₑ ^ 2 * ‖f x‖ₑ ^ 2
      rw [enorm_mul, mul_pow]
      gcongr
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal ((hC n x).trans (le_abs_self C)))
    (by rw [lintegral_const_mul' _ _ (by simp)]; exact ENNReal.mul_ne_top (by simp) hf)
    (by filter_upwards [hc] with x h0
        have h1 := (continuous_enorm.tendsto (0 : ℝ)).comp h0
        rw [enorm_zero] at h1
        have h2 := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
        rw [zero_pow two_ne_zero] at h2
        exact h2)
  simpa using hlim

/-- Bounded multipliers: `mₙ fₙ → m f` in `L²`. -/
theorem L2Tendsto.mul_bdd {m f : ℕ → α → ℝ} {m₀ f₀ : α → ℝ} {M : ℝ} (h : L2Tendsto μ f f₀)
    (hM : ∀ n x, |m n x| ≤ M) (hM₀ : ∀ x, |m₀ x| ≤ M)
    (hmm : ∀ n, AEMeasurable (fun x => m n x * (f n x - f₀ x)) μ)
    (hmm' : ∀ n, AEMeasurable (fun x => (m n x - m₀ x) * f₀ x) μ)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => (m n x - m₀ x) * f₀ x) atTop (𝓝 0))
    (hf : ∫⁻ x, ‖f₀ x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    L2Tendsto μ (fun n x => m n x * f n x) (fun x => m₀ x * f₀ x) := by
  have h1 : L2Tendsto μ (fun n x => m n x * (f n x - f₀ x)) (fun _ => 0) := by
    refine (h.const_mul M).of_le fun n x => ?_
    rw [sub_zero, ← mul_sub, enorm_mul, enorm_mul, mul_pow, mul_pow]
    gcongr
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ((hM n x).trans (le_abs_self M))
  have h2 := L2Tendsto.dominated (c := m) (c₀ := m₀) (f := f₀) (C := 2 * M) hmm'
    (fun n x => (abs_sub _ _).trans (by linarith [hM n x, hM₀ x])) hc hf
  have h3 := h1.add h2 (fun n => by simpa using hmm n)
  refine h3.of_le fun n x => le_of_eq ?_
  congr 2; ring

/-- Young: `a² ≤ (1+ε) b² + (1 + 1/ε)(a - b)²`. -/
theorem sq_le_young (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    a ^ 2 ≤ (1 + ε) * b ^ 2 + (1 + 1 / ε) * (a - b) ^ 2 := by
  have h : 0 ≤ (ε * b - (a - b)) ^ 2 / ε := by positivity
  have e : (1 + ε) * b ^ 2 + (1 + 1 / ε) * (a - b) ^ 2 - a ^ 2 = (ε * b - (a - b)) ^ 2 / ε := by
    field_simp; ring
  linarith

/-- `L²` convergence gives `limsup ∫ fₙ² ≤ ∫ f²`. -/
theorem L2Tendsto.limsup_le {f : ℕ → α → ℝ} {g : α → ℝ} (h : L2Tendsto μ f g)
    (hgm : AEMeasurable g μ) (hg : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    limsup (fun n => ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ) atTop ≤ ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  set G := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hGt => ?_
  -- choose `δ` with `δ G ≤ ε/2`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ * G ≤ ε := by
    rcases eq_or_ne G 0 with h0 | h0
    · exact ⟨1, one_pos, by rw [h0, mul_zero]; exact zero_le⟩
    · have hGr : 0 < G.toReal := ENNReal.toReal_pos h0 hg
      refine ⟨(ε : ℝ) / G.toReal, div_pos (by exact_mod_cast hε) hGr, ?_⟩
      calc ENNReal.ofReal ((ε : ℝ) / G.toReal) * G =
          ENNReal.ofReal ((ε : ℝ) / G.toReal) * ENNReal.ofReal G.toReal := by
            rw [ENNReal.ofReal_toReal hg]
        _ = ENNReal.ofReal ((ε : ℝ) / G.toReal * G.toReal) :=
            (ENNReal.ofReal_mul (div_pos (by exact_mod_cast hε) hGr).le).symm
        _ = ε := by rw [div_mul_cancel₀ _ hGr.ne']; simp
        _ ≤ ε := le_rfl
  have hpt : ∀ n, ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (1 + δ) * G +
      ENNReal.ofReal (1 + 1 / δ) * ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ := fun n => by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left' ((hgm.enorm.pow_const 2).const_mul _)]
    refine lintegral_mono fun x => ?_
    rw [← ofReal_sq_eq_enorm_sq, ← ofReal_sq_eq_enorm_sq, ← ofReal_sq_eq_enorm_sq,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (sq_le_young _ _ hδ0)
  have hlim : Tendsto (fun n => ENNReal.ofReal (1 + δ) * G +
      ENNReal.ofReal (1 + 1 / δ) * ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ) atTop
      (𝓝 (ENNReal.ofReal (1 + δ) * G)) := by
    have := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (1 + 1 / δ)) h
      (Or.inr ENNReal.ofReal_ne_top)).const_add
      (ENNReal.ofReal (1 + δ) * G)
    simpa using this
  calc limsup (fun n => ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ) atTop
      ≤ limsup (fun n => ENNReal.ofReal (1 + δ) * G +
          ENNReal.ofReal (1 + 1 / δ) * ∫⁻ x, ‖f n x - g x‖ₑ ^ 2 ∂μ) atTop :=
        limsup_le_limsup (Eventually.of_forall hpt)
    _ = ENNReal.ofReal (1 + δ) * G := hlim.limsup_eq
    _ = G + ENNReal.ofReal δ * G := by
        rw [ENNReal.ofReal_add (by norm_num) hδ0.le, ENNReal.ofReal_one, add_mul, one_mul]
    _ ≤ G + ε := add_le_add le_rfl hδ

/-- Finite-sum version of `L2Tendsto.limsup_le`. -/
theorem L2Tendsto.limsup_le_sum {κ : Type*} (s : Finset κ) {f : κ → ℕ → α → ℝ} {g : κ → α → ℝ}
    (h : ∀ k ∈ s, L2Tendsto μ (f k) (g k)) (hgm : ∀ k ∈ s, AEMeasurable (g k) μ)
    (hg : ∀ k ∈ s, ∫⁻ x, ‖g k x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    limsup (fun n => ∑ k ∈ s, ∫⁻ x, ‖f k n x‖ₑ ^ 2 ∂μ) atTop ≤
      ∑ k ∈ s, ∫⁻ x, ‖g k x‖ₑ ^ 2 ∂μ := by
  set G := ∑ k ∈ s, ∫⁻ x, ‖g k x‖ₑ ^ 2 ∂μ
  have hGt : G ≠ ⊤ := ENNReal.sum_ne_top.mpr hg
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ * G ≤ ε := by
    rcases eq_or_ne G 0 with h0 | h0
    · exact ⟨1, one_pos, by rw [h0, mul_zero]; exact zero_le⟩
    · have hGr : 0 < G.toReal := ENNReal.toReal_pos h0 hGt
      refine ⟨(ε : ℝ) / G.toReal, div_pos (by exact_mod_cast hε) hGr, ?_⟩
      calc ENNReal.ofReal ((ε : ℝ) / G.toReal) * G =
          ENNReal.ofReal ((ε : ℝ) / G.toReal) * ENNReal.ofReal G.toReal := by
            rw [ENNReal.ofReal_toReal hGt]
        _ = ENNReal.ofReal ((ε : ℝ) / G.toReal * G.toReal) :=
            (ENNReal.ofReal_mul (div_pos (by exact_mod_cast hε) hGr).le).symm
        _ = ε := by rw [div_mul_cancel₀ _ hGr.ne']; simp
        _ ≤ ε := le_rfl
  have hpt : ∀ n, ∑ k ∈ s, ∫⁻ x, ‖f k n x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (1 + δ) * G +
      ENNReal.ofReal (1 + 1 / δ) * ∑ k ∈ s, ∫⁻ x, ‖f k n x - g k x‖ₑ ^ 2 ∂μ := fun n => by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left' (((hgm k hk).enorm.pow_const 2).const_mul _)]
    refine lintegral_mono fun x => ?_
    rw [← ofReal_sq_eq_enorm_sq, ← ofReal_sq_eq_enorm_sq, ← ofReal_sq_eq_enorm_sq,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (sq_le_young _ _ hδ0)
  have hsum : Tendsto (fun n => ∑ k ∈ s, ∫⁻ x, ‖f k n x - g k x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
    have := tendsto_finsetSum s fun k hk => h k hk
    simpa using this
  have hlim : Tendsto (fun n => ENNReal.ofReal (1 + δ) * G +
      ENNReal.ofReal (1 + 1 / δ) * ∑ k ∈ s, ∫⁻ x, ‖f k n x - g k x‖ₑ ^ 2 ∂μ) atTop
      (𝓝 (ENNReal.ofReal (1 + δ) * G)) := by
    have := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (1 + 1 / δ)) hsum
      (Or.inr ENNReal.ofReal_ne_top)).const_add (ENNReal.ofReal (1 + δ) * G)
    simpa using this
  calc limsup (fun n => ∑ k ∈ s, ∫⁻ x, ‖f k n x‖ₑ ^ 2 ∂μ) atTop
      ≤ limsup (fun n => ENNReal.ofReal (1 + δ) * G +
          ENNReal.ofReal (1 + 1 / δ) * ∑ k ∈ s, ∫⁻ x, ‖f k n x - g k x‖ₑ ^ 2 ∂μ) atTop :=
        limsup_le_limsup (Eventually.of_forall hpt)
    _ = ENNReal.ofReal (1 + δ) * G := hlim.limsup_eq
    _ = G + ENNReal.ofReal δ * G := by
        rw [ENNReal.ofReal_add (by norm_num) hδ0.le, ENNReal.ofReal_one, add_mul, one_mul]
    _ ≤ G + ε := add_le_add le_rfl hδ

end SharpLSI
