import DGPS.Basic.Tightening
import DGPS.Basic.DefectRemoval

/-!
# Positive entropy tightening by finitely many dyadic cutoffs (LIP081)

Under the abstract tightening hypotheses (`TighteningHyp`), no violating normalized
sequence can have entropies `h_k` converging to a positive limit.  The proof selects, by a
pigeonhole argument over the dyadic levels `s_j = 2^j L`, a cutoff `M_j = 2 exp (s_j / 2)`,
splits `f = min f M + (f - M)^+`, and applies the scalar tail entropy inequality and the
small-mass entropy bound (LIP080) together with bounded comparison (LIP079).

Design note: the statement carries the additional hypothesis `hsplit` (energy splitting
`E (min f c) + E ((f - c)^+) ≤ E f` on the admissible class), exactly as in the
vanishing-entropy statement (LIP083).  The conclusion is `False`, for a sequence with
`h_k → hinf > 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Analysis

theorem dyadic_geom_sum_lip081 (K : ℕ) : ∑ j ∈ Finset.range K, (2 : ℝ) ^ j = 2 ^ K - 1 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; ring

/-- For `u ≥ 0` the dyadic levels `s_j = 2^j L` below `u` have `∑ s_j / 2 ≤ u`. -/
theorem dyadic_sum_le_lip081 {L : ℝ} (hL : 0 ≤ L) {u : ℝ} (hu : 0 ≤ u) (K : ℕ) :
    ∑ j ∈ Finset.range K, (if 2 ^ j * L < u then 2 ^ j * L / 2 else 0) ≤ u := by
  induction K with
  | zero => simpa using hu
  | succ K ih =>
    rw [Finset.sum_range_succ]
    by_cases hK : 2 ^ K * L < u
    · have hall : ∀ j ∈ Finset.range K,
          (if 2 ^ j * L < u then 2 ^ j * L / 2 else 0) = 2 ^ j * L / 2 := by
        intro j hj
        have : (2:ℝ) ^ j * L ≤ 2 ^ K * L :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hj).le) hL
        simp only [lt_of_le_of_lt this hK, ↓reduceIte]
      rw [Finset.sum_congr rfl hall]
      simp only [hK, ↓reduceIte]
      have hg : ∑ j ∈ Finset.range K, (2:ℝ) ^ j * L / 2 = (2 ^ K - 1) * L / 2 := by
        rw [← Finset.sum_div, ← Finset.sum_mul, dyadic_geom_sum_lip081]
      rw [hg]
      nlinarith
    · simp only [hK, ↓reduceIte, add_zero]; exact ih

/-- Choice of a good cutoff among finitely many dyadic levels. -/
theorem exists_good_cutoff_lip081 {L A : ℝ} (hL : 0 < L) (hA : 0 ≤ A) {K : ℕ} (hK : 1 ≤ K)
    (ψ : ℕ → ℝ) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hsum : ∑ j ∈ Finset.range K, (2 ^ j * L / 2) * ψ j ≤ A) :
    ∃ j < K, (2 ^ j * L / 2) * ψ j ≤ A / K ∧ ψ j ≤ 2 * A / L := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hne : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.2 hK⟩
  obtain ⟨j, hj, hjle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun j => (2 ^ j * L / 2) * ψ j) (g := fun _ => A / K)
    (by simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hKpos.ne'] using hsum)
  refine ⟨j, Finset.mem_range.1 hj, hjle, ?_⟩
  have h2j : 1 ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h1 : L / 2 * ψ j ≤ (2 ^ j * L / 2) * ψ j := by
    apply mul_le_mul_of_nonneg_right _ (hψ0 j); nlinarith
  have h2 : A / K ≤ A := div_le_self hA (by exact_mod_cast hK)
  rw [le_div_iff₀ hL]
  nlinarith

/-- A mass-one test of finite entropy: `f² log f²` is integrable with integral `Ent(f²)`. -/
theorem sq_mul_log_of_entropy_lip081 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {h : ℝ} (hm : Measurable f)
    (hsi : Integrable (fun x => f x ^ 2) P) (hmass : ∫ x, f x ^ 2 ∂P = 1) (hh : 0 ≤ h)
    (hent : DGPS.homogeneousEntropy P (fun x => f x ^ 2) = ENNReal.ofReal h) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P ∧
      ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P = h := by
  have hΦ0 : ∀ x, 0 ≤ f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 + 1 := fun x =>
    DGPS.self_mul_log_sub_add_one_nonneg (sq_nonneg _)
  have hΦm : Measurable fun x => f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 + 1 := by fun_prop
  rw [DGPS.entropy_mass_one hmass] at hent
  have hΦi : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 + 1) P := by
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hΦ0), hent]
    exact ENNReal.ofReal_lt_top
  have hΦint : ∫ x, (f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 + 1) ∂P = h := by
    have := ofReal_integral_eq_lintegral_ofReal hΦi (Filter.Eventually.of_forall hΦ0)
    rw [hent] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hΦ0) hh).1 this
  have hli : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P := by
    have := (hΦi.add hsi).sub (integrable_const (1 : ℝ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  refine ⟨hli, ?_⟩
  have e : (fun x => f x ^ 2 * Real.log (f x ^ 2))
      = fun x => ((f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 + 1) + f x ^ 2) - 1 := by
    funext x; ring
  have h1 : Integrable (fun x => (f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 + 1) + f x ^ 2) P :=
    hΦi.add hsi
  have h2 := integral_sub h1 (integrable_const (1 : ℝ))
  have h3 := integral_add hΦi hsi
  rw [e, h2, h3, hΦint, hmass]
  simp

/-- Pointwise splitting of `s² log s²` at the cutoff `M` (scalar tail inequality). -/
theorem sq_log_split_pointwise_lip081 {η Cη M : ℝ}
    (hsc : ∀ s : ℝ, M < s →
      s ^ 2 * Real.log (s ^ 2) - M ^ 2 * Real.log (M ^ 2)
        ≤ (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) + Cη * s ^ 2 * Real.log (M ^ 2))
    {s : ℝ} :
    s ^ 2 * Real.log (s ^ 2) ≤ (min s M) ^ 2 * Real.log ((min s M) ^ 2)
      + (1 + η) * ((max (s - M) 0) ^ 2 * Real.posLog ((max (s - M) 0) ^ 2))
      + Cη * Real.log (M ^ 2) * (if M < s then s ^ 2 else 0) := by
  by_cases hs : M < s
  · have h1 : min s M = M := min_eq_right hs.le
    have h2 : max (s - M) 0 = s - M := max_eq_left (by linarith)
    rw [h1, h2]
    simp only [hs, ↓reduceIte]
    have := hsc s hs
    nlinarith
  · push Not at hs
    have h1 : min s M = s := min_eq_left hs
    have h2 : max (s - M) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]
    simp [not_lt.2 hs]

/-- A bounded measurable truncation: `∫ g² log g² ≤ Ent(g²)` when `∫ g² ≤ 1`. -/
theorem trunc_sq_log_le_entropy_lip081 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : Ω → ℝ} {M : ℝ} (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgM : ∀ x, g x ≤ M) (hmass : ∫ x, g x ^ 2 ∂P ≤ 1) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) P ∧
      ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂P
        ≤ (DGPS.homogeneousEntropy P (fun x => g x ^ 2)).toReal := by
  have hsq : Integrable (fun x => g x ^ 2) P :=
    Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable (M ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hg0 x) (hgM x) 2)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := M ^ 2)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.continuousOn)
  have hli : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) P := by
    refine Integrable.of_bound (by fun_prop : Measurable fun x => g x ^ 2 * Real.log (g x ^ 2)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => ?_)
    exact hB (g x ^ 2) ⟨sq_nonneg _, pow_le_pow_left₀ (hg0 x) (hgM x) 2⟩
  refine ⟨hli, ?_⟩
  have hform := DGPS.homogeneousEntropy_eq_formula (P := P) (v := fun x => g x ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg _) hsq hli
  rw [hform, ENNReal.toReal_ofReal']
  refine le_trans ?_ (le_max_left _ _)
  have hm0 : 0 ≤ ∫ x, g x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have : (∫ x, g x ^ 2 ∂P) * Real.log (∫ x, g x ^ 2 ∂P) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm0 (Real.log_nonpos hm0 hmass)
  linarith

/-- The tail piece: small mass bound plus the defective inequality. -/
theorem tail_posLog_integral_le_lip081 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {t : Ω → ℝ} {r0 C Et : ℝ} (htm : Measurable t)
    (ht0 : ∀ x, 0 ≤ t x) (hti2 : Integrable (fun x => t x ^ 2) P)
    (hsmall : ∫ x, t x ^ 2 ∂P ≤ Real.exp (-1)) (hr0 : 0 < r0) (hEt : 0 ≤ Et)
    (hdef : DGPS.homogeneousEntropy P (fun x => t x ^ 2)
      ≤ ENNReal.ofReal (2 * Et / r0 + C * ∫ x, t x ^ 2 ∂P)) :
    Integrable (fun x => t x ^ 2 * Real.posLog (t x ^ 2)) P ∧
      ∫ x, t x ^ 2 * Real.posLog (t x ^ 2) ∂P ≤ 2 * Et / r0 + |C| * ∫ x, t x ^ 2 ∂P := by
  have hsm := small_mass_posLog_le_entropy P t ht0 hti2 hsmall
  set u : Ω → ℝ := fun x => t x ^ 2 * Real.posLog (t x ^ 2) with hu
  have hum : Measurable u := by
    refine (htm.pow_const 2).mul ?_
    exact Real.continuous_posLog.measurable.comp (htm.pow_const 2)
  have hu0 : ∀ x, 0 ≤ u x := fun x => mul_nonneg (sq_nonneg _) Real.posLog_nonneg
  have hX : 0 ≤ 2 * Et / r0 + |C| * ∫ x, t x ^ 2 ∂P := by
    have : 0 ≤ ∫ x, t x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
    positivity
  have hle : ∫⁻ x, ENNReal.ofReal (u x) ∂P
      ≤ ENNReal.ofReal (2 * Et / r0 + |C| * ∫ x, t x ^ 2 ∂P) := by
    refine hsm.trans (hdef.trans (ENNReal.ofReal_le_ofReal ?_))
    have : C * ∫ x, t x ^ 2 ∂P ≤ |C| * ∫ x, t x ^ 2 ∂P :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (integral_nonneg fun x => sq_nonneg _)
    linarith
  have hui : Integrable u P := by
    refine ⟨hum.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hu0)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  refine ⟨hui, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hX, ofReal_integral_eq_lintegral_ofReal hui
    (Filter.Eventually.of_forall hu0)]
  exact hle

/-- Integrability of a truncated square `f² 1_{s < log⁺ f²}`. -/
theorem integrable_cutoff_sq_lip081 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hm : Measurable f) (hsi : Integrable (fun x => f x ^ 2) P) (s : ℝ) :
    Integrable (fun x => if s < Real.posLog (f x ^ 2) then f x ^ 2 else 0) P := by
  refine hsi.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (Measurable.ite (measurableSet_lt measurable_const
      (Real.continuous_posLog.measurable.comp (hm.pow_const 2))) (hm.pow_const 2)
      measurable_const).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    split_ifs
    · rw [abs_of_nonneg (sq_nonneg _)]
    · simp only [abs_zero]; exact sq_nonneg _

/-- Dyadic selection of a good cutoff level at the level of integrals. -/
theorem exists_dyadic_cutoff_integral_lip081 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {L A : ℝ} (hL : 0 < L) (hA : 0 ≤ A) {K : ℕ} (hK : 1 ≤ K)
    (hm : Measurable f) (hsi : Integrable (fun x => f x ^ 2) P)
    (hΦ : Integrable (fun x => f x ^ 2 * Real.posLog (f x ^ 2)) P)
    (hA' : ∫ x, f x ^ 2 * Real.posLog (f x ^ 2) ∂P ≤ A) :
    ∃ j < K, (2 ^ j * L / 2) *
        (∫ x, (if 2 ^ j * L < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P) ≤ A / K ∧
      (∫ x, (if 2 ^ j * L < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P) ≤ 2 * A / L := by
  have hind := fun j : ℕ => integrable_cutoff_sq_lip081 (P := P) hm hsi (2 ^ j * L)
  refine exists_good_cutoff_lip081 hL hA hK
    (fun j => ∫ x, (if 2 ^ j * L < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P)
    (fun j => integral_nonneg fun x => by split_ifs <;> positivity) ?_
  have h1 : ∑ j ∈ Finset.range K, (2 ^ j * L / 2) *
      (∫ x, (if 2 ^ j * L < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P)
      = ∫ x, ∑ j ∈ Finset.range K, (2 ^ j * L / 2) *
          (if 2 ^ j * L < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P := by
    rw [integral_finsetSum _ (fun j _ => (hind j).const_mul _)]
    simp_rw [integral_const_mul]
  rw [h1]
  refine le_trans (integral_mono (integrable_finsetSum _ fun j _ => (hind j).const_mul _) hΦ
    fun x => ?_) hA'
  have h2 : ∑ j ∈ Finset.range K, (2 ^ j * L / 2) *
      (if 2 ^ j * L < Real.posLog (f x ^ 2) then f x ^ 2 else 0)
      = f x ^ 2 * ∑ j ∈ Finset.range K,
          (if 2 ^ j * L < Real.posLog (f x ^ 2) then 2 ^ j * L / 2 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left (dyadic_sum_le_lip081 hL.le Real.posLog_nonneg K) (sq_nonneg _)

/-- A value above the cutoff `2 exp (s/2)` has `log⁺ x² > s`. -/
theorem cutoff_implies_posLog_lip081 {s x : ℝ} (hx : 2 * Real.exp (s / 2) < x) :
    s < Real.posLog (x ^ 2) := by
  have hE : 0 < Real.exp (s / 2) := Real.exp_pos _
  have he : Real.exp s = Real.exp (s / 2) * Real.exp (s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : Real.exp s < x ^ 2 := by nlinarith
  have h2 := Real.log_lt_log (Real.exp_pos s) h1
  rw [Real.log_exp] at h2
  exact lt_of_lt_of_le h2 (le_max_right _ _)

/-- The tail pieces `t = (f - M)⁺` and `f 1_{f>M}` are controlled by the cutoff mass `ψ`. -/
theorem tail_pieces_lip081 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    (hm : Measurable f) (hsi : Integrable (fun x => f x ^ 2) P) {s : ℝ} :
    (Integrable (fun x => (max (f x - 2 * Real.exp (s / 2)) 0) ^ 2) P ∧
      ∫ x, (max (f x - 2 * Real.exp (s / 2)) 0) ^ 2 ∂P
        ≤ ∫ x, (if s < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P) ∧
    (Integrable (fun x => if 2 * Real.exp (s / 2) < f x then f x ^ 2 else 0) P ∧
      ∫ x, (if 2 * Real.exp (s / 2) < f x then f x ^ 2 else 0) ∂P
        ≤ ∫ x, (if s < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P) := by
  have hψ := integrable_cutoff_sq_lip081 (P := P) hm hsi s
  have hM0 : 0 ≤ 2 * Real.exp (s / 2) := by positivity
  have hp1 : ∀ x, (max (f x - 2 * Real.exp (s / 2)) 0) ^ 2
      ≤ (if s < Real.posLog (f x ^ 2) then f x ^ 2 else 0) := by
    intro x
    by_cases hx : 2 * Real.exp (s / 2) < f x
    · have hc := cutoff_implies_posLog_lip081 hx
      simp only [hc, ↓reduceIte, max_eq_left (sub_nonneg.2 hx.le)]
      nlinarith [hM0, hx]
    · rw [max_eq_right (by linarith [not_lt.1 hx])]
      split_ifs <;> simp [sq_nonneg]
  have hp2 : ∀ x, (if 2 * Real.exp (s / 2) < f x then f x ^ 2 else 0)
      ≤ (if s < Real.posLog (f x ^ 2) then f x ^ 2 else 0) := by
    intro x
    by_cases hx : 2 * Real.exp (s / 2) < f x
    · simp only [hx, cutoff_implies_posLog_lip081 hx, ↓reduceIte, le_refl]
    · simp only [hx, ↓reduceIte]
      split_ifs <;> simp [sq_nonneg]
  have hI1 : Integrable (fun x => (max (f x - 2 * Real.exp (s / 2)) 0) ^ 2) P := by
    refine hψ.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (((hm.sub_const _).max measurable_const).pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp1 x
  have hI2 : Integrable (fun x => if 2 * Real.exp (s / 2) < f x then f x ^ 2 else 0) P := by
    refine hψ.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Measurable.ite (measurableSet_lt measurable_const hm) (hm.pow_const 2)
        measurable_const).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]; exact hp2 x
  exact ⟨⟨hI1, integral_mono hI1 hψ hp1⟩, ⟨hI2, integral_mono hI2 hψ hp2⟩⟩

/-- `∫ f² log⁺ f²` is controlled by the entropy. -/
theorem posLog_integral_bound_lip081 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {h : ℝ} (hm : Measurable f)
    (hli : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P)
    (hint : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P = h) :
    Integrable (fun x => f x ^ 2 * Real.posLog (f x ^ 2)) P ∧
      ∫ x, f x ^ 2 * Real.posLog (f x ^ 2) ∂P ≤ h + 1 := by
  have hpt : ∀ x, f x ^ 2 * Real.posLog (f x ^ 2) ≤ f x ^ 2 * Real.log (f x ^ 2) + 1 := by
    intro x
    have h1 := DGPS.self_mul_log_sub_add_one_nonneg (sq_nonneg (f x))
    rcases le_total 0 (Real.log (f x ^ 2)) with hl | hl
    · rw [Real.posLog_apply, max_eq_right hl]; linarith
    · rw [Real.posLog_apply, max_eq_left hl]; nlinarith [sq_nonneg (f x)]
  have hnn : ∀ x, 0 ≤ f x ^ 2 * Real.posLog (f x ^ 2) := fun x =>
    mul_nonneg (sq_nonneg _) Real.posLog_nonneg
  have hi1 : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2) + 1) P :=
    hli.add (integrable_const (1 : ℝ))
  have hi : Integrable (fun x => f x ^ 2 * Real.posLog (f x ^ 2)) P := by
    refine (hli.abs.add (integrable_const (1 : ℝ))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hm.pow_const 2).mul
        (Real.continuous_posLog.measurable.comp (hm.pow_const 2))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
      have := hpt x
      have h2 := le_abs_self (f x ^ 2 * Real.log (f x ^ 2))
      simp only [Pi.add_apply]
      linarith
  refine ⟨hi, ?_⟩
  calc ∫ x, f x ^ 2 * Real.posLog (f x ^ 2) ∂P
      ≤ ∫ x, (f x ^ 2 * Real.log (f x ^ 2) + 1) ∂P := integral_mono hi hi1 hpt
    _ = h + 1 := by
      rw [integral_add hli (integrable_const (1 : ℝ)), hint]; simp

/-- A single truncation level: the entropy of `f` is bounded through the splitting
`f = f ∧ M + (f - M)⁺`, bounded comparison on `f ∧ M`, and the tail estimates on `(f - M)⁺`. -/
theorem single_cutoff_bound_lip081 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R)
    (hsplit : ∀ n, ∀ f ∈ S n, (∀ x, 0 ≤ f x) → ∀ c : ℝ, 0 ≤ c →
      E n (fun x => min (f x) c) + E n (fun x => max (f x - c) 0) ≤ E n f)
    {r0 C η Cη a ε E0 Mmax M τ σ : ℝ} (hr0 : 0 < r0) (hr0a : r0 ≤ a) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hC : ∀ n, ∀ f ∈ S n, homogeneousEntropy (P n) (fun x => f x ^ 2)
      ≤ ENNReal.ofReal (2 * E n f / r0 + C * ∫ x, f x ^ 2 ∂P n))
    (hsc : ∀ s : ℝ, M < s →
      s ^ 2 * Real.log (s ^ 2) - M ^ 2 * Real.log (M ^ 2)
        ≤ (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) + Cη * s ^ 2 * Real.log (M ^ 2))
    (hM0 : 0 ≤ M) (hMM : M ≤ Mmax) (hLM : 0 ≤ Real.log (M ^ 2))
    {n : ℕ}
    (hcmp : ∀ g ∈ S n, (∀ x, |g x| ≤ Mmax) → E n g ≤ E0 →
      ENNReal.ofReal (a / 2) * homogeneousEntropy (P n) (fun x => g x ^ 2)
        ≤ ENNReal.ofReal (E n g + ε))
    {f : Ω n → ℝ} (hf : f ∈ S n) (hf0 : ∀ x, 0 ≤ f x) (hmass : ∫ x, f x ^ 2 ∂P n = 1)
    {h : ℝ} (hh : 0 ≤ h)
    (hent : homogeneousEntropy (P n) (fun x => f x ^ 2) = ENNReal.ofReal h)
    (hE0 : E n f ≤ E0) (hτ : τ ≤ Real.exp (-1))
    (htail : ∫ x, (max (f x - M) 0) ^ 2 ∂P n ≤ τ)
    (hσ : ∫ x, (if M < f x then f x ^ 2 else 0) ∂P n ≤ σ) :
    h ≤ (1 + η) * (2 * E n f / r0) + 2 * ε / r0 + (1 + η) * |C| * τ
      + |Cη| * Real.log (M ^ 2) * σ := by
  have hm : Measurable f := hyp.measurable n f hf
  have hsi : Integrable (fun x => f x ^ 2) (P n) := hyp.sq_integrable n f hf
  obtain ⟨hli, hint⟩ := sq_mul_log_of_entropy_lip081 hm hsi hmass hh hent
  -- the truncation and the tail
  have hgS : (fun x => min (f x) M) ∈ S n := hyp.min_mem n f hf M
  have htS : (fun x => max (f x - M) 0) ∈ S n := by
    have h1 := hyp.max_mem n _ (hyp.affine_mem n f hf 1 (-M)) 0
    have e : (fun x => max (f x - M) 0) = fun x => max ((fun y => 1 * f y + -M) x) 0 := by
      funext x; simp [sub_eq_add_neg]
    rw [e]; exact h1
  have hgm : Measurable fun x => min (f x) M := hm.min measurable_const
  have hg0 : ∀ x, 0 ≤ min (f x) M := fun x => le_min (hf0 x) hM0
  have hgM : ∀ x, min (f x) M ≤ M := fun x => min_le_right _ _
  have hgsq : ∀ x, min (f x) M ^ 2 ≤ f x ^ 2 := fun x =>
    pow_le_pow_left₀ (hg0 x) (min_le_left _ _) 2
  have hg2 : Integrable (fun x => min (f x) M ^ 2) (P n) := by
    refine hsi.mono' (hgm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hgsq x
  have hgmass : ∫ x, min (f x) M ^ 2 ∂P n ≤ 1 := by
    rw [← hmass]; exact integral_mono hg2 hsi hgsq
  obtain ⟨hgli, hgle⟩ := trunc_sq_log_le_entropy_lip081 hgm hg0 hgM hgmass
  -- the tail
  have htm : Measurable fun x => max (f x - M) 0 := (hm.sub_const M).max measurable_const
  have ht0 : ∀ x, 0 ≤ max (f x - M) 0 := fun x => le_max_right _ _
  have htsq : ∀ x, (max (f x - M) 0) ^ 2 ≤ f x ^ 2 := by
    intro x
    have h1 : max (f x - M) 0 ≤ f x := max_le (by linarith) (hf0 x)
    exact pow_le_pow_left₀ (ht0 x) h1 2
  have ht2 : Integrable (fun x => (max (f x - M) 0) ^ 2) (P n) := by
    refine hsi.mono' (htm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact htsq x
  obtain ⟨htli, htle⟩ := tail_posLog_integral_le_lip081 (P := P n) (r0 := r0) (C := C)
    (Et := E n (fun x => max (f x - M) 0)) htm ht0 ht2 (htail.trans hτ) hr0
    (hyp.energy_nonneg n _ htS) (hC n _ htS)
  have hind : Integrable (fun x => if M < f x then f x ^ 2 else 0) (P n) := by
    refine hsi.mono' (Measurable.ite (measurableSet_lt measurable_const hm) (hm.pow_const 2)
      measurable_const).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  -- integrate the pointwise splitting
  have hA1 : Integrable (fun x => min (f x) M ^ 2 * Real.log (min (f x) M ^ 2)) (P n) := hgli
  have hB1 : Integrable (fun x => (1 + η) *
      ((max (f x - M) 0) ^ 2 * Real.posLog ((max (f x - M) 0) ^ 2))) (P n) :=
    htli.const_mul (1 + η)
  have hC1 : Integrable (fun x => Cη * Real.log (M ^ 2) * (if M < f x then f x ^ 2 else 0))
      (P n) := hind.const_mul (Cη * Real.log (M ^ 2))
  have hAB : Integrable (fun x => min (f x) M ^ 2 * Real.log (min (f x) M ^ 2)
      + (1 + η) * ((max (f x - M) 0) ^ 2 * Real.posLog ((max (f x - M) 0) ^ 2))) (P n) :=
    hA1.add hB1
  have hRHS : Integrable (fun x => min (f x) M ^ 2 * Real.log (min (f x) M ^ 2)
      + (1 + η) * ((max (f x - M) 0) ^ 2 * Real.posLog ((max (f x - M) 0) ^ 2))
      + Cη * Real.log (M ^ 2) * (if M < f x then f x ^ 2 else 0)) (P n) := hAB.add hC1
  have hkey : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P n
      ≤ ∫ x, (min (f x) M ^ 2 * Real.log (min (f x) M ^ 2)
      + (1 + η) * ((max (f x - M) 0) ^ 2 * Real.posLog ((max (f x - M) 0) ^ 2))
      + Cη * Real.log (M ^ 2) * (if M < f x then f x ^ 2 else 0)) ∂P n :=
    integral_mono hli hRHS fun x => sq_log_split_pointwise_lip081 hsc
  rw [integral_add hAB hC1, integral_add hA1 hB1, integral_const_mul, integral_const_mul] at hkey
  rw [hint] at hkey
  -- bounded comparison for the truncation
  have hEg : E n (fun x => min (f x) M) ≤ E n f := hyp.energy_min_le n f hf M
  have hEg0 : 0 ≤ E n (fun x => min (f x) M) := hyp.energy_nonneg n _ hgS
  have hEt0 : 0 ≤ E n (fun x => max (f x - M) 0) := hyp.energy_nonneg n _ htS
  have hcm := hcmp _ hgS (fun x => by
    rw [abs_of_nonneg (hg0 x)]; exact (hgM x).trans hMM) (hEg.trans hE0)
  have hapos : 0 < a := lt_of_lt_of_le hr0 hr0a
  have hcm2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by linarith)] at hcm2
  set T : ℝ := (homogeneousEntropy (P n) (fun x => min (f x) M ^ 2)).toReal with hT
  have hT1 : T ≤ 2 * (E n (fun x => min (f x) M) + ε) / a := by
    rw [le_div_iff₀ hapos]; linarith
  have hT2 : 2 * (E n (fun x => min (f x) M) + ε) / a
      ≤ 2 * (E n (fun x => min (f x) M) + ε) / r0 :=
    div_le_div_of_nonneg_left (by linarith) hr0 hr0a
  have hsp := hsplit n f hf hf0 M hM0
  -- tail bounds
  have hCt : (1 + η) * (|C| * ∫ x, (max (f x - M) 0) ^ 2 ∂P n) ≤ (1 + η) * |C| * τ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  have hYt : |Cη| * Real.log (M ^ 2) * ∫ x, (if M < f x then f x ^ 2 else 0) ∂P n
      ≤ |Cη| * Real.log (M ^ 2) * σ :=
    mul_le_mul_of_nonneg_left hσ (by positivity)
  have hCη : Cη * Real.log (M ^ 2) * ∫ x, (if M < f x then f x ^ 2 else 0) ∂P n
      ≤ |Cη| * Real.log (M ^ 2) * ∫ x, (if M < f x then f x ^ 2 else 0) ∂P n := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hLM) ?_
    exact integral_nonneg fun x => by split_ifs <;> positivity
  have hρ : 0 ≤ r0⁻¹ := inv_nonneg.2 hr0.le
  have e1 : ∀ z : ℝ, z / r0 = z * r0⁻¹ := fun z => div_eq_mul_inv z r0
  rw [e1] at hT2 ⊢
  simp only [e1] at hT2 htle ⊢
  have hfin : 2 * (E n (fun x => min (f x) M) + ε) * r0⁻¹
      + (1 + η) * (2 * E n (fun x => max (f x - M) 0) * r0⁻¹)
      ≤ (1 + η) * (2 * E n f * r0⁻¹) + 2 * ε * r0⁻¹ := by
    nlinarith [mul_nonneg hη (mul_nonneg hEg0 hρ), mul_nonneg hEg0 hρ, mul_nonneg hEt0 hρ,
      mul_nonneg hη (mul_nonneg hEt0 hρ), mul_le_mul_of_nonneg_right hsp hρ,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsp hρ) hη]
  nlinarith [mul_nonneg hη (mul_nonneg hEt0 hρ)]

/-- One normalized function, with the dyadic selection of the cutoff level. -/
theorem entropy_cutoff_bound_lip081 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R)
    (hsplit : ∀ n, ∀ f ∈ S n, (∀ x, 0 ≤ f x) → ∀ c : ℝ, 0 ≤ c →
      E n (fun x => min (f x) c) + E n (fun x => max (f x - c) 0) ≤ E n f)
    {r0 C η Cη a ε E0 L A Mmax : ℝ} {K : ℕ} (hr0 : 0 < r0) (hr0a : r0 ≤ a) (hη : 0 ≤ η)
    (hε : 0 ≤ ε)
    (hC : ∀ n, ∀ f ∈ S n, homogeneousEntropy (P n) (fun x => f x ^ 2)
      ≤ ENNReal.ofReal (2 * E n f / r0 + C * ∫ x, f x ^ 2 ∂P n))
    (hsc : ∀ M : ℝ, Real.exp 1 ≤ M → ∀ s : ℝ, M < s →
      s ^ 2 * Real.log (s ^ 2) - M ^ 2 * Real.log (M ^ 2)
        ≤ (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) + Cη * s ^ 2 * Real.log (M ^ 2))
    (hL : 3 ≤ L) (hA0 : 0 ≤ A) (hLA : 6 * A ≤ L) (hK : 1 ≤ K)
    (hMmax : ∀ j < K, 2 * Real.exp (2 ^ j * L / 2) ≤ Mmax)
    {n : ℕ}
    (hcmp : ∀ g ∈ S n, (∀ x, |g x| ≤ Mmax) → E n g ≤ E0 →
      ENNReal.ofReal (a / 2) * homogeneousEntropy (P n) (fun x => g x ^ 2)
        ≤ ENNReal.ofReal (E n g + ε))
    {f : Ω n → ℝ} (hf : f ∈ S n) (hf0 : ∀ x, 0 ≤ f x) (hmass : ∫ x, f x ^ 2 ∂P n = 1)
    {h : ℝ} (hh : 0 ≤ h)
    (hent : homogeneousEntropy (P n) (fun x => f x ^ 2) = ENNReal.ofReal h)
    (hE0 : E n f ≤ E0) (hhA : h + 1 ≤ A) :
    h ≤ (1 + η) * (2 * E n f / r0) + 2 * ε / r0 + 2 * (1 + η) * |C| * A / L
      + 4 * |Cη| * A / K := by
  have hm : Measurable f := hyp.measurable n f hf
  have hsi : Integrable (fun x => f x ^ 2) (P n) := hyp.sq_integrable n f hf
  obtain ⟨hli, hint⟩ := sq_mul_log_of_entropy_lip081 hm hsi hmass hh hent
  obtain ⟨hΦi, hΦle⟩ := posLog_integral_bound_lip081 hm hli hint
  have hLpos : 0 < L := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨j, hjK, hj1, hj2⟩ := exists_dyadic_cutoff_integral_lip081 hLpos hA0 hK hm hsi hΦi
    (hΦle.trans hhA)
  have hs3 : 3 ≤ 2 ^ j * L := by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  obtain ⟨⟨-, htle⟩, ⟨-, hile⟩⟩ := tail_pieces_lip081 (P := P n) hm hsi (s := 2 ^ j * L)
  have hE : 0 < Real.exp (2 ^ j * L / 2) := Real.exp_pos _
  have hMe : Real.exp 1 ≤ 2 * Real.exp (2 ^ j * L / 2) := by
    have : Real.exp 1 ≤ Real.exp (2 ^ j * L / 2) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hM2 : (2 * Real.exp (2 ^ j * L / 2)) ^ 2 = 4 * Real.exp (2 ^ j * L) := by
    have he : Real.exp (2 ^ j * L) = Real.exp (2 ^ j * L / 2) * Real.exp (2 ^ j * L / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]; ring
  have hlog : Real.log ((2 * Real.exp (2 ^ j * L / 2)) ^ 2) = Real.log 4 + 2 ^ j * L := by
    rw [hM2, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hlog40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set ψ : ℝ := ∫ x, (if 2 ^ j * L < Real.posLog (f x ^ 2) then f x ^ 2 else 0) ∂P n with hψ
  have hψ0 : 0 ≤ ψ := integral_nonneg fun x => by split_ifs <;> positivity
  have hτ : ψ ≤ Real.exp (-1) := by
    have h3 : Real.exp 1 < 3 := lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num)
    have h4 : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos 1) h3.le
    have h5 : 2 * A / L ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hLpos (by norm_num)]; linarith
    linarith
  have hbase := single_cutoff_bound_lip081 hyp hsplit (Cη := Cη) (a := a) (ε := ε) (E0 := E0)
    (Mmax := Mmax) (M := 2 * Real.exp (2 ^ j * L / 2)) (τ := ψ) (σ := ψ) hr0 hr0a hη hε hC
    (fun s hs => hsc _ hMe s hs) (by positivity) (hMmax j hjK)
    (by rw [hlog]; linarith) hcmp hf hf0 hmass hh hent hE0 hτ htle hile
  rw [hlog] at hbase
  have hlogψ : (Real.log 4 + 2 ^ j * L) * ψ ≤ 4 * (A / K) := by
    have h1 : (Real.log 4 + 2 ^ j * L) ≤ 2 * (2 ^ j * L) := by linarith
    have := mul_le_mul_of_nonneg_right h1 hψ0
    nlinarith
  have hC1 : (1 + η) * |C| * ψ ≤ 2 * (1 + η) * |C| * A / L := by
    have : ψ ≤ 2 * A / L := hj2
    calc (1 + η) * |C| * ψ ≤ (1 + η) * |C| * (2 * A / L) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * (1 + η) * |C| * A / L := by ring
  have hC2 : |Cη| * (Real.log 4 + 2 ^ j * L) * ψ ≤ 4 * |Cη| * A / K := by
    calc |Cη| * (Real.log 4 + 2 ^ j * L) * ψ = |Cη| * ((Real.log 4 + 2 ^ j * L) * ψ) := by ring
      _ ≤ |Cη| * (4 * (A / K)) := mul_le_mul_of_nonneg_left hlogψ (abs_nonneg _)
      _ = 4 * |Cη| * A / K := by ring
  linarith

/-- LIP081.  Under the abstract tightening hypotheses of LIP079 (and the exact splitting of the
energy at a truncation level), a nonnegative normalized admissible sequence `f_k` with
`n k → ∞`, entropies `h_k = Ent(f_k²)` and `2 E_k < r h_k` cannot have `h_k → h∞ > 0`.

The argument: with `0 < η`, `(1+η) r < r0 < R`, a finite family of dyadic levels
`s_j = 2^j L` (`0 ≤ j < K`) and `ψ_{k,j} = ∫_{f_k² > exp s_j} f_k²`, a pigeonhole choice of `j`
with `(s_j/2) ψ_{k,j} ≤ A/K` and `ψ_{k,j} ≤ 2A/L`; cutting `f_k` at `M_j = 2 exp (s_j/2)` into
`g = f ∧ M_j` and `t = (f - M_j)⁺`, the bounded comparison for `g` (fixed before `k` grows, for
all the levels at once) and the defective inequality and small-mass bound for `t` yield
`h_k ≤ (1+η) 2 E_k / r0 + 2ε/r0 + 2(1+η)|C| A/L + 4|Cη| A/K`. -/
theorem positive_entropy_tightening_by_finitely_many_dyadic_cutoffs
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R)
    (hsplit : ∀ n, ∀ f ∈ S n, (∀ x, 0 ≤ f x) → ∀ c : ℝ, 0 ≤ c →
      E n (fun x => min (f x) c) + E n (fun x => max (f x - c) 0) ≤ E n f)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (f : ∀ k, Ω (n k) → ℝ) (h : ℕ → ℝ)
    (hf : ∀ k, f k ∈ S (n k) ∧ (∀ x, 0 ≤ f k x) ∧ ∫ x, f k x ^ 2 ∂P (n k) = 1 ∧
      homogeneousEntropy (P (n k)) (fun x => f k x ^ 2) = ENNReal.ofReal (h k) ∧ 0 < h k ∧
      2 * E (n k) (f k) < r * h k)
    {hinf : ℝ} (hpos : 0 < hinf) (hh : Tendsto h atTop (𝓝 hinf)) : False := by
  -- constants
  set r0 : ℝ := (r + R) / 2 with hr0def
  have hr0pos : 0 < r0 := by rw [hr0def]; linarith
  have hrr0 : r < r0 := by rw [hr0def]; linarith
  have hr0R : r0 < R := by rw [hr0def]; linarith
  set η : ℝ := (r0 - r) / (2 * r) with hηdef
  have hη : 0 < η := by rw [hηdef]; apply div_pos <;> linarith
  have hηr : (1 + η) * r = (r + r0) / 2 := by rw [hηdef]; field_simp; ring
  set θ : ℝ := (r + r0) / (2 * r0) with hθdef
  have hθ : 0 < 1 - θ := by
    rw [hθdef, sub_pos, div_lt_one (by linarith)]; linarith
  obtain ⟨C, hC⟩ := hyp.defective r0 hr0pos hr0R
  obtain ⟨Cη, hCη⟩ := scalar_tail_entropy_inequality η hη
  obtain ⟨a, hRa, hcomp⟩ := hyp.bounded_comparison
  have hr0a : r0 ≤ a := by linarith
  set A : ℝ := hinf + 2 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  set δ : ℝ := (1 - θ) * hinf / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  set ε : ℝ := r0 * δ / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  set L : ℝ := 3 + 6 * A + 2 * (1 + η) * |C| * A / δ with hLdef
  have hL3 : 3 ≤ L := by
    have : 0 ≤ 2 * (1 + η) * |C| * A / δ := by positivity
    rw [hLdef]; linarith
  have hL6 : 6 * A ≤ L := by
    have : 0 ≤ 2 * (1 + η) * |C| * A / δ := by positivity
    rw [hLdef]; linarith
  have hLC : 2 * (1 + η) * |C| * A / δ ≤ L := by
    have : 0 ≤ 6 * A := by positivity
    rw [hLdef]; linarith
  have hLpos : 0 < L := by linarith
  set K : ℕ := ⌈4 * |Cη| * A / δ⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKC : 4 * |Cη| * A / δ ≤ K := by
    have := Nat.le_ceil (4 * |Cη| * A / δ)
    have h2 : ((⌈4 * |Cη| * A / δ⌉₊ : ℕ) : ℝ) ≤ K := by
      rw [hKdef]; push_cast; linarith
    linarith
  set Mmax : ℝ := 2 * Real.exp (2 ^ K * L / 2) with hMmaxdef
  have hMmax : ∀ j < K, 2 * Real.exp (2 ^ j * L / 2) ≤ Mmax := by
    intro j hj
    rw [hMmaxdef]
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hj.le
    have := mul_le_mul_of_nonneg_right h2 hLpos.le
    have := Real.exp_le_exp.2 (by linarith : 2 ^ j * L / 2 ≤ 2 ^ K * L / 2)
    linarith
  have hMpos : 0 < Mmax := by rw [hMmaxdef]; positivity
  set E0 : ℝ := r * (hinf + 1) / 2 with hE0def
  have hE0pos : 0 < E0 := by rw [hE0def]; positivity
  obtain ⟨N0, hN0⟩ := hcomp Mmax E0 ε hMpos hE0pos hε
  -- a good index
  have hev1 : ∀ᶠ k in atTop, N0 ≤ n k := hn.eventually_ge_atTop N0
  have hev2 : ∀ᶠ k in atTop, h k < hinf + 1 := hh.eventually (gt_mem_nhds (by linarith))
  have hev3 : ∀ᶠ k in atTop, 7 / 8 * hinf < h k :=
    hh.eventually (lt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2, hk3⟩ := (hev1.and (hev2.and hev3)).exists
  obtain ⟨hfS, hf0, hmass, hent, hhpos, hE⟩ := hf k
  have hEk0 : E (n k) (f k) ≤ E0 := by
    rw [hE0def]; nlinarith
  have hstep := entropy_cutoff_bound_lip081 hyp hsplit (Cη := Cη) (L := L) (A := A) (K := K)
    (Mmax := Mmax) hr0pos hr0a hη.le hε.le hC (fun M hM s hs => hCη M hM s hs) hL3 hA0 hL6 hK1
    hMmax (fun g hg hb hEg => hN0 (n k) hk1 g hg hb hEg) hfS hf0 hmass hhpos.le hent hEk0
    (by rw [hAdef]; linarith)
  -- arithmetic
  have hb1 : (1 + η) * (2 * E (n k) (f k) / r0) ≤ θ * h k := by
    have h1 : 2 * E (n k) (f k) / r0 ≤ r * h k / r0 :=
      div_le_div_of_nonneg_right hE.le hr0pos.le
    calc (1 + η) * (2 * E (n k) (f k) / r0) ≤ (1 + η) * (r * h k / r0) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = ((1 + η) * r) * h k / r0 := by ring
      _ = θ * h k := by rw [hηr, hθdef]; field_simp
  have hb2 : 2 * ε / r0 = δ := by rw [hεdef]; field_simp
  have hb3 : 2 * (1 + η) * |C| * A / L ≤ δ := by
    rw [div_le_iff₀ hLpos]
    have := (div_le_iff₀ hδ).1 hLC
    linarith
  have hb4 : 4 * |Cη| * A / K ≤ δ := by
    rw [div_le_iff₀ hKpos]
    have := (div_le_iff₀ hδ).1 hKC
    linarith
  have hfin : (1 - θ) * h k ≤ 3 * δ := by linarith
  have hc : (1 - θ) * (7 / 8 * hinf) < (1 - θ) * h k := mul_lt_mul_of_pos_left hk3 hθ
  have hd : 3 * δ = 3 / 4 * ((1 - θ) * hinf) := by rw [hδdef]; ring
  have hpp : 0 < (1 - θ) * hinf := mul_pos hθ hpos
  nlinarith

end DGPS.Analysis
