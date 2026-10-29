import SharpSymmetricLSI.Infra.Entropy

/-!
# R34: Lemma B.1 (`lem:truncation`), scalar estimates for the entropy truncations

Manuscript Appendix B, Lemma B.1 (i)–(iii), equations (B.1), (B.2), (B.3).
`log⁺ x = max(0, log x)` is Mathlib's `Real.posLog`. `0 log 0 = 0` is automatic
(`Real.log 0 = 0`).
-/

open MeasureTheory Real
open scoped ENNReal

namespace SharpLSI

/-- `Φ(s) = s² log s² - s² + 1` (Lemma B.1). -/
noncomputable def Phi (s : ℝ) : ℝ := s ^ 2 * Real.log (s ^ 2) - s ^ 2 + 1

/-- Lemma B.1 (i), (B.1): for every `η > 0` there is `C_η < ∞` such that for `M ≥ e`, `s > M`,
`s² log s² - M² log M² ≤ (1+η)(s-M)² log⁺(s-M)² + C_η s² log M²`. -/
def TruncationLarge : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ M s : ℝ, Real.exp 1 ≤ M → M < s →
    s ^ 2 * Real.log (s ^ 2) - M ^ 2 * Real.log (M ^ 2) ≤
      (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) + C * s ^ 2 * Real.log (M ^ 2)

/-- Lemma B.1 (ii), (B.2) and the final assertion of (ii): for `b > 1`, `t ≥ 0`,
`Φ(b+t) - Φ(b) - Φ'(b) t ≤ t² log⁺ t² + 2(1 + log(b+1)) t²`; and
`Φ(s) ≤ 2(1 + log b)(s-1)²` for `0 ≤ s ≤ b`. -/
def TruncationSmall : Prop :=
  ∀ b : ℝ, 1 < b →
    (∀ t : ℝ, 0 ≤ t →
      Phi (b + t) - Phi b - deriv Phi b * t ≤
        t ^ 2 * Real.posLog (t ^ 2) + 2 * (1 + Real.log (b + 1)) * t ^ 2) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ b → Phi s ≤ 2 * (1 + Real.log b) * (s - 1) ^ 2)

/-- Lemma B.1 (iii), (B.3): if `h ≥ 0` on a probability space and `∫ h² = c ≤ e^{-1}`, then
`∫ h² log⁺ h² ≤ Ent(h²)`. (`h² ∈ L¹` is part of "`∫ h² = c`".) -/
def TruncationSmallMass : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] (h : α → ℝ),
    (∀ x, 0 ≤ h x) → Integrable (fun x => h x ^ 2) P →
    ∫ x, h x ^ 2 ∂P ≤ Real.exp (-1) →
    ∫⁻ x, ENNReal.ofReal (h x ^ 2 * Real.posLog (h x ^ 2)) ∂P ≤ ent P (fun x => h x ^ 2)

/-- Lemma B.1, all three parts. -/
def TruncationConclusion : Prop := TruncationLarge ∧ TruncationSmall ∧ TruncationSmallMass

/-- Lemma B.1 (i). -/
theorem scalar_large : TruncationLarge := by
  intro η hη
  set R : ℝ := 2 + 2 / η with hRdef
  set q : ℝ := 1 - 1 / R with hqdef
  have hR2 : 2 < R := by have : 0 < 2 / η := by positivity
                         linarith
  have hR0 : 0 < R := by linarith
  have hqR : q = (η + 2) / (2 * η + 2) := by
    rw [hqdef, hRdef]; field_simp; ring
  have hq1 : q ≤ 1 := by
    have : 0 < 1 / R := by positivity
    linarith
  have hqh : 1 / 2 ≤ q := by
    rw [hqR, le_div_iff₀ (by linarith)]; linarith
  have hq0 : 0 < q := by linarith
  have hqη : 1 ≤ (1 + η) * q ^ 2 := by
    rw [hqR, div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg η]
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  refine ⟨Real.log R + 1 + (1 + η) * Real.log 4, fun M s hM hMs => ?_⟩
  have he1 : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  have hM0 : 0 < M := by linarith
  have hs0 : 0 < s := by linarith
  have hlogM : 1 ≤ Real.log M := by
    have := Real.log_le_log (Real.exp_pos 1) hM
    rwa [Real.log_exp] at this
  set L := Real.log (M ^ 2) with hL
  have hL2 : 2 ≤ L := by
    rw [hL, Real.log_pow]; push_cast; linarith
  have hM2 : 0 ≤ M ^ 2 * L := by positivity
  have hls : Real.log (s ^ 2) = 2 * Real.log s := by rw [Real.log_pow]; push_cast; ring
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hsL : 0 ≤ s ^ 2 * L := by positivity
  rcases le_or_gt s (R * M) with hcase | hcase
  · -- `s ≤ R M`
    have h1 : Real.log (s ^ 2) ≤ L * (Real.log R + 1) := by
      have : Real.log (s ^ 2) ≤ Real.log ((R * M) ^ 2) :=
        Real.log_le_log (by positivity) (pow_le_pow_left₀ hs0.le hcase 2)
      have hlR : Real.log (R ^ 2) = 2 * Real.log R := by rw [Real.log_pow]; push_cast; ring
      rw [mul_pow, Real.log_mul (by positivity) (by positivity), hlR, ← hL] at this
      nlinarith only [this, hL2, hlogR, mul_nonneg (sub_nonneg.mpr hL2) hlogR.le]
    have h2 : 0 ≤ (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) := by
      have := Real.posLog_nonneg (x := (s - M) ^ 2); positivity
    have h3 : s ^ 2 * Real.log (s ^ 2) ≤ s ^ 2 * L * (Real.log R + 1) := by
      have := mul_le_mul_of_nonneg_left h1 hs2; linarith
    have h4 : s ^ 2 * L * (Real.log R + 1) ≤
        (Real.log R + 1 + (1 + η) * Real.log 4) * s ^ 2 * L := by
      have : 0 ≤ (1 + η) * Real.log 4 * (s ^ 2 * L) := by positivity
      nlinarith
    nlinarith
  · -- `s > R M`
    have hMs' : M < s / R := by rw [lt_div_iff₀ hR0]; linarith
    have hsM : q * s ≤ s - M := by
      have : s / R = (1 / R) * s := by ring
      rw [hqdef]; nlinarith
    have hqs0 : 0 ≤ q * s := by positivity
    have hqs1 : 1 ≤ q * s := by
      have : 2 * M < s := by nlinarith
      nlinarith
    set A₀ := (q * s) ^ 2 with hA₀
    set A := (s - M) ^ 2 with hA
    have hA₀1 : 1 ≤ A₀ := by rw [hA₀]; nlinarith
    have hAA : A₀ ≤ A := pow_le_pow_left₀ hqs0 hsM 2
    have hlA : Real.log A₀ ≤ Real.log A := Real.log_le_log (by linarith) hAA
    have hlA0 : 0 ≤ Real.log A₀ := Real.log_nonneg hA₀1
    have hpos : Real.log A ≤ Real.posLog A := le_max_right _ _
    have hfirst : A₀ * Real.log A₀ ≤ A * Real.posLog A := by
      apply mul_le_mul hAA (by linarith) hlA0 (by linarith)
    have hlogA₀ : Real.log A₀ = Real.log (q ^ 2) + Real.log (s ^ 2) := by
      rw [hA₀, mul_pow, Real.log_mul (by positivity) (by positivity)]
    have hlq : -Real.log 4 ≤ Real.log (q ^ 2) := by
      have : Real.log (1 / 4) ≤ Real.log (q ^ 2) :=
        Real.log_le_log (by norm_num)
          (by calc (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
                _ ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hqh 2)
      rwa [one_div, Real.log_inv] at this
    have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1
    have hlq0 : Real.log (q ^ 2) ≤ 0 := Real.log_nonpos (sq_nonneg _) hq2
    -- (1+η) A₀ log A₀ ≥ s² log s² - (1+η) log 4 · s²
    have hkey : s ^ 2 * Real.log (s ^ 2) - (1 + η) * Real.log 4 * s ^ 2 ≤
        (1 + η) * (A₀ * Real.log A₀) := by
      rw [hlogA₀, hA₀, mul_pow]
      have hls0 : 0 ≤ Real.log (s ^ 2) := by rw [hls]; linarith
      have e1 : s ^ 2 * Real.log (s ^ 2) ≤ (1 + η) * q ^ 2 * (s ^ 2 * Real.log (s ^ 2)) :=
        le_mul_of_one_le_left (mul_nonneg hs2 hls0) hqη
      have e2 : -(1 + η) * Real.log 4 ≤ (1 + η) * (q ^ 2 * Real.log (q ^ 2)) := by
        have h' : Real.log (q ^ 2) ≤ q ^ 2 * Real.log (q ^ 2) := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr hq2) (neg_nonneg.mpr hlq0)]
        nlinarith only [h', hlq, hη]
      have e3 : -(1 + η) * Real.log 4 * s ^ 2 ≤ (1 + η) * (q ^ 2 * Real.log (q ^ 2)) * s ^ 2 :=
        mul_le_mul_of_nonneg_right e2 hs2
      linarith only [e1, e3]
    have hfirst' : (1 + η) * (A₀ * Real.log A₀) ≤ (1 + η) * A * Real.posLog A := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfirst (by linarith)
    have hsec : (1 + η) * Real.log 4 * s ^ 2 ≤
        (Real.log R + 1 + (1 + η) * Real.log 4) * s ^ 2 * L := by
      have : (1 + η) * Real.log 4 * s ^ 2 ≤ (1 + η) * Real.log 4 * s ^ 2 * L := by
        have h0 : 0 ≤ (1 + η) * Real.log 4 * s ^ 2 := by positivity
        nlinarith only [h0, hL2, mul_nonneg h0 (by linarith : (0:ℝ) ≤ L - 1)]
      have : 0 ≤ (Real.log R + 1) * (s ^ 2 * L) := by positivity
      linarith
    have hMM : 0 ≤ M ^ 2 * Real.log (M ^ 2) := hM2
    linarith only [hkey, hfirst', hsec, hMM]

/-- Lemma B.1 (ii). -/
theorem scalar_small : TruncationSmall := by
  have taylor2 : ∀ {f f' f'' : ℝ → ℝ} {x₀ x K : ℝ},
      (∀ y ∈ Set.uIcc x₀ x, HasDerivAt f (f' y) y) →
      (∀ y ∈ Set.uIcc x₀ x, HasDerivAt f' (f'' y) y) →
      (∀ y ∈ Set.uIcc x₀ x, f'' y ≤ K) →
      f x - f x₀ - f' x₀ * (x - x₀) ≤ K / 2 * (x - x₀) ^ 2 := by
    intro f f' f'' x₀ x K hf hf' hK
    set g : ℝ → ℝ := fun y => f y - f' x₀ * (y - x₀) - K / 2 * (y - x₀) ^ 2 with hg
    set g' : ℝ → ℝ := fun y => f' y - f' x₀ - K * (y - x₀) with hg'
    have hgd : ∀ y ∈ Set.uIcc x₀ x, HasDerivAt g (g' y) y := by
      intro y hy
      have h1 : HasDerivAt (fun y => f' x₀ * (y - x₀)) (f' x₀) y := by
        simpa using ((hasDerivAt_id' y).sub_const x₀).const_mul (f' x₀)
      have h2 : HasDerivAt (fun y => K / 2 * (y - x₀) ^ 2) (K * (y - x₀)) y := by
        have := (((hasDerivAt_id' y).sub_const x₀).pow 2).const_mul (K / 2)
        convert this using 1; push_cast; ring
      exact ((hf y hy).sub h1).sub h2
    have hg'd : ∀ y ∈ Set.uIcc x₀ x, HasDerivAt g' (f'' y - K) y := by
      intro y hy
      have h1 : HasDerivAt (fun y => K * (y - x₀)) K y := by
        simpa using ((hasDerivAt_id' y).sub_const x₀).const_mul K
      exact ((hf' y hy).sub_const (f' x₀)).sub h1
    have key : g x ≤ g x₀ := by
      rcases le_total x₀ x with h | h
      · have hI : Set.uIcc x₀ x = Set.Icc x₀ x := Set.uIcc_of_le h
        rw [hI] at hgd hg'd hK
        have hanti : AntitoneOn g' (Set.Icc x₀ x) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          · exact fun y hy => (hg'd y hy).continuousAt.continuousWithinAt
          · intro y hy; exact (hg'd y (interior_subset hy)).differentiableAt.differentiableWithinAt
          · intro y hy; rw [(hg'd y (interior_subset hy)).deriv]; linarith [hK y (interior_subset hy)]
        have hanti2 : AntitoneOn g (Set.Icc x₀ x) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          · exact fun y hy => (hgd y hy).continuousAt.continuousWithinAt
          · intro y hy; exact (hgd y (interior_subset hy)).differentiableAt.differentiableWithinAt
          · intro y hy
            have hy' := interior_subset hy
            rw [(hgd y hy').deriv]
            have := hanti ⟨le_refl x₀, h⟩ hy' hy'.1
            simpa [hg'] using this
        exact hanti2 ⟨le_refl x₀, h⟩ ⟨h, le_refl x⟩ h
      · have hI : Set.uIcc x₀ x = Set.Icc x x₀ := Set.uIcc_of_ge h
        rw [hI] at hgd hg'd hK
        have hanti : AntitoneOn g' (Set.Icc x x₀) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
          · exact fun y hy => (hg'd y hy).continuousAt.continuousWithinAt
          · intro y hy; exact (hg'd y (interior_subset hy)).differentiableAt.differentiableWithinAt
          · intro y hy; rw [(hg'd y (interior_subset hy)).deriv]; linarith [hK y (interior_subset hy)]
        have hmono : MonotoneOn g (Set.Icc x x₀) := by
          apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
          · exact fun y hy => (hgd y hy).continuousAt.continuousWithinAt
          · intro y hy; exact (hgd y (interior_subset hy)).differentiableAt.differentiableWithinAt
          · intro y hy
            have hy' := interior_subset hy
            rw [(hgd y hy').deriv]
            have := hanti hy' ⟨h, le_refl x₀⟩ hy'.2
            simpa [hg'] using this
        exact hmono ⟨le_refl x, h⟩ ⟨h, le_refl x₀⟩ h
    simp only [hg] at key
    linarith
  have Phi_hasDerivAt : ∀ {y : ℝ}, y ≠ 0 →
      HasDerivAt Phi (2 * y * Real.log (y ^ 2)) y := by
    intro y hy
    have h2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    have := ((((hasDerivAt_pow 2 y).mul ((hasDerivAt_pow 2 y).log h2))).sub (hasDerivAt_pow 2 y)).add_const 1
    refine this.congr_deriv ?_
    field_simp
    ring
  have Phi'_hasDerivAt : ∀ {y : ℝ}, y ≠ 0 →
      HasDerivAt (fun y => 2 * y * Real.log (y ^ 2)) (2 * Real.log (y ^ 2) + 4) y := by
    intro y hy
    have h2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    have := (((hasDerivAt_id' y).const_mul 2).mul ((hasDerivAt_pow 2 y).log h2))
    refine this.congr_deriv ?_
    field_simp
    ring
  intro b hb
  have hb0 : 0 < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hd : deriv Phi b = 2 * b * Real.log (b ^ 2) := (Phi_hasDerivAt hb0.ne').deriv
  refine ⟨fun t ht => ?_, fun s hs0 hsb => ?_⟩
  · have hT := taylor2 (f := Phi) (f' := fun y => 2 * y * Real.log (y ^ 2))
      (f'' := fun y => 2 * Real.log (y ^ 2) + 4) (x₀ := b) (x := b + t)
      (K := 2 * Real.log ((b + t) ^ 2) + 4)
      (fun y hy => by
        rw [Set.uIcc_of_le (by linarith)] at hy
        exact Phi_hasDerivAt (by linarith [hy.1]))
      (fun y hy => by
        rw [Set.uIcc_of_le (by linarith)] at hy
        exact Phi'_hasDerivAt (by linarith [hy.1]))
      (fun y hy => by
        rw [Set.uIcc_of_le (by linarith)] at hy
        have hy0 : 0 < y := by linarith [hy.1]
        have : Real.log (y ^ 2) ≤ Real.log ((b + t) ^ 2) :=
          Real.log_le_log (by positivity) (pow_le_pow_left₀ hy0.le hy.2 2)
        linarith)
    simp only [add_sub_cancel_left] at hT
    rw [hd]
    have hbt : 0 < b + t := by linarith
    have hl : Real.log ((b + t) ^ 2) = 2 * Real.log (b + t) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hl] at hT
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hmain : Real.log (b + t) * t ^ 2 ≤ t ^ 2 * Real.posLog (t ^ 2) / 2 +
        Real.log (b + 1) * t ^ 2 := by
      rcases le_total t 1 with h1 | h1
      · have : Real.log (b + t) ≤ Real.log (b + 1) := Real.log_le_log hbt (by linarith)
        have := mul_le_mul_of_nonneg_right this ht2
        have : 0 ≤ t ^ 2 * Real.posLog (t ^ 2) := mul_nonneg ht2 Real.posLog_nonneg
        linarith
      · have ht0 : 0 < t := by linarith
        have hle : Real.log (b + t) ≤ Real.log (b + 1) + Real.log t := by
          rw [← Real.log_mul (by linarith) ht0.ne']
          exact Real.log_le_log hbt (by nlinarith)
        have hpl : Real.posLog (t ^ 2) = 2 * Real.log t := by
          rw [Real.posLog_eq_log (by rw [abs_of_nonneg ht2]; nlinarith), Real.log_pow]; push_cast; ring
        rw [hpl]
        have := mul_le_mul_of_nonneg_right hle ht2
        nlinarith
    nlinarith
  · have pos : ∀ y ∈ Set.uIcc 1 s, 0 < s → 0 < y := fun y hy h0 => by
      rcases Set.mem_uIcc.mp hy with h | h <;> linarith [h.1]
    rcases hs0.eq_or_lt with h0 | h0
    · subst h0
      simp [Phi]
      linarith
    · have hT := taylor2 (f := Phi) (f' := fun y => 2 * y * Real.log (y ^ 2))
        (f'' := fun y => 2 * Real.log (y ^ 2) + 4) (x₀ := 1) (x := s)
        (K := 4 * (1 + Real.log b))
        (fun y hy => Phi_hasDerivAt (pos y hy h0).ne')
        (fun y hy => Phi'_hasDerivAt (pos y hy h0).ne')
        (fun y hy => by
          · have hy0 : 0 < y := pos y hy h0
            have hyb : y ≤ b := by
              rcases Set.mem_uIcc.mp hy with h | h <;> linarith [h.2]
            have : Real.log (y ^ 2) ≤ Real.log (b ^ 2) :=
              Real.log_le_log (by positivity) (pow_le_pow_left₀ hy0.le hyb 2)
            simp only [Real.log_pow] at this ⊢; push_cast at this ⊢
            linarith)
      have hPhi1 : Phi 1 = 0 := by simp [Phi]
      simp [hPhi1] at hT
      linarith

/-- Lemma B.1 (iii). -/
theorem small_mass_poslog : TruncationSmallMass := by
  intro α _ P _ h hh hint hc
  unfold ent
  simp only [hint, ↓reduceIte]
  set c := ∫ x, h x ^ 2 ∂P with hcdef
  have hc0' : 0 ≤ c := integral_nonneg fun x => sq_nonneg _
  rcases hc0'.eq_or_lt with hc0 | hc0
  · have hz : (fun x => h x ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).mp hc0.symm
    have : (∫⁻ x, ENNReal.ofReal (h x ^ 2 * Real.posLog (h x ^ 2)) ∂P) = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hz] with x hx
        simp only [Pi.zero_apply] at hx
        simp [hx]
    rw [this]; exact zero_le
  · apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    set u := h x ^ 2 with hu
    have hu0 : 0 ≤ u := sq_nonneg _
    rcases le_or_gt u 1 with h1 | h1
    · rw [(Real.posLog_eq_zero_iff u).mpr (by rw [abs_of_nonneg hu0]; exact h1), mul_zero]
      exact mul_nonneg hc0.le (InformationTheory.klFun_nonneg (div_nonneg hu0 hc0.le))
    · have hlc : Real.log c ≤ -1 := by
        have := Real.log_le_log hc0 hc
        rwa [Real.log_exp] at this
      rw [Real.posLog_eq_log (by rw [abs_of_nonneg hu0]; exact h1.le)]
      unfold InformationTheory.klFun
      rw [Real.log_div (by linarith) hc0.ne']
      have : c * (u / c * (Real.log u - Real.log c) + 1 - u / c) =
          u * Real.log u - u * Real.log c + c - u := by
        field_simp
      rw [this]
      nlinarith

/-- Lemma B.1. -/
theorem lemma_B1 : TruncationConclusion := ⟨scalar_large, scalar_small, small_mass_poslog⟩

end SharpLSI
