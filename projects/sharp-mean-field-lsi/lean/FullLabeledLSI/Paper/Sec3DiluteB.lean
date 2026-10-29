import FullLabeledLSI.Paper.Sec3DiluteA

/-!
# Proposition 3.3 (≤), part B: the two-species family and its quotient

The family `θ = (ε, 1-ε)`, `ρ₁ = q u₁²`, `ρ₂ = q u₂²` with `ε u₁² + (1-ε) u₂² = 1` has average `q`;
it is admissible, and its quotient is bounded by `(ε I(ρ₁|q) + (1-ε) I(ρ₂|q)) / (2 ε H(ρ₁|q))`
when `q` is the equilibrium density (`D(q) = 0`, `G(q) = 0`).
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The two-species family `(ε, 1-ε)`, `(q u₁², q u₂²)`. -/
def diluteFam (q u₁ u₂ : Torus d → ℝ) (ε : ℝ) : Family d where
  q := 2
  θ := ![ε, 1 - ε]
  ρ := ![fun x => q x * u₁ x ^ 2, fun x => q x * u₂ x ^ 2]

section
variable (q u₁ u₂ : Torus d → ℝ) (ε : ℝ)

theorem diluteFam_q_pos0 : 0 < (diluteFam q u₁ u₂ ε).q := by show 0 < 2; norm_num
theorem diluteFam_q_pos1 : 1 < (diluteFam q u₁ u₂ ε).q := by show 1 < 2; norm_num

theorem diluteFam_sum {α : Type*} [AddCommMonoid α] (f : Fin (diluteFam q u₁ u₂ ε).q → α) :
    ∑ a, f a = f ⟨0, diluteFam_q_pos0 q u₁ u₂ ε⟩ + f ⟨1, diluteFam_q_pos1 q u₁ u₂ ε⟩ :=
  Fin.sum_univ_two f

theorem diluteFam_forall (P : Fin (diluteFam q u₁ u₂ ε).q → Prop)
    (p0 : P ⟨0, diluteFam_q_pos0 q u₁ u₂ ε⟩) (p1 : P ⟨1, diluteFam_q_pos1 q u₁ u₂ ε⟩) :
    ∀ a, P a := by
  intro a
  obtain ⟨a, ha⟩ := a
  change a < 2 at ha
  interval_cases a
  exacts [p0, p1]

theorem diluteFam_θ0 : (diluteFam q u₁ u₂ ε).θ ⟨0, diluteFam_q_pos0 q u₁ u₂ ε⟩ = ε := rfl
theorem diluteFam_θ1 : (diluteFam q u₁ u₂ ε).θ ⟨1, diluteFam_q_pos1 q u₁ u₂ ε⟩ = 1 - ε := rfl
theorem diluteFam_ρ0 : (diluteFam q u₁ u₂ ε).ρ ⟨0, diluteFam_q_pos0 q u₁ u₂ ε⟩ =
    fun x => q x * u₁ x ^ 2 := rfl
theorem diluteFam_ρ1 : (diluteFam q u₁ u₂ ε).ρ ⟨1, diluteFam_q_pos1 q u₁ u₂ ε⟩ =
    fun x => q x * u₂ x ^ 2 := rfl
end

theorem diluteFam_bar {q u₁ u₂ : Torus d → ℝ} {ε : ℝ}
    (h : ∀ x, ε * u₁ x ^ 2 + (1 - ε) * u₂ x ^ 2 = 1) :
    (diluteFam q u₁ u₂ ε).bar = q := by
  funext x
  unfold Family.bar
  rw [diluteFam_sum, diluteFam_θ0, diluteFam_θ1, diluteFam_ρ0, diluteFam_ρ1]
  linear_combination q x * h x

theorem dilute_quotient_le (hyp : Hyp V W KV KW) {q u₁ u₂ : Torus d → ℝ} {c C B₁ B₂ ε : ℝ}
    {g₁ g₂ : Torus d → Fin d → ℝ}
    (hc : 0 < c) (hbd : ∀ x, c ≤ q x ∧ q x ≤ C) (hqm : Measurable q)
    (hq1 : ∫ x, q x ∂haar d = 1)
    (hqH : MemH1 (haar d) (fun x => Real.sqrt (q x))) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hu₁ : IsWeakGrad u₁ g₁) (hu₁0 : ∀ x, 0 ≤ u₁ x) (hu₁B : ∀ x, u₁ x ≤ B₁)
    (hg₁ : ∀ k, MemLp (fun y => g₁ y k) 2 (haar d))
    (hu₂ : IsWeakGrad u₂ g₂) (hu₂0 : ∀ x, 0 ≤ u₂ x) (hu₂B : ∀ x, u₂ x ≤ B₂)
    (hg₂ : ∀ k, MemLp (fun y => g₂ y k) 2 (haar d))
    (hid : ∀ x, ε * u₁ x ^ 2 + (1 - ε) * u₂ x ^ 2 = 1)
    (hint₁ : ∫ x, q x * u₁ x ^ 2 ∂haar d = 1)
    (hKpos : 0 < klDiv (densMeasure fun x => q x * u₁ x ^ 2) (densMeasure q))
    (hD0 : dissipation V W q = 0) (hG0 : gap V W (densMeasure q) = 0) :
    MsAdmissible V W (diluteFam q u₁ u₂ ε) ∧
      densMeasure (diluteFam q u₁ u₂ ε).bar = densMeasure q ∧
      msDiss V W (diluteFam q u₁ u₂ ε) / (2 * (msGap V W (diluteFam q u₁ u₂ ε)).toENNReal) ≤
        (ENNReal.ofReal ε * relFisher (fun x => q x * u₁ x ^ 2) q +
          ENNReal.ofReal (1 - ε) * relFisher (fun x => q x * u₂ x ^ 2) q) /
        (2 * (ENNReal.ofReal ε * klDiv (densMeasure fun x => q x * u₁ x ^ 2) (densMeasure q))) := by
  set F := diluteFam q u₁ u₂ ε with hF
  have hq0 : ∀ x, 0 < q x := fun x => hc.trans_le (hbd x).1
  have hqC : ∀ x, q x ≤ C := fun x => (hbd x).2
  have hbar : F.bar = q := diluteFam_bar hid
  -- integrability and the second normalization
  have hint : ∀ {u : Torus d → ℝ} {B : ℝ}, (AEStronglyMeasurable u (haar d)) → (∀ x, 0 ≤ u x) →
      (∀ x, u x ≤ B) → Integrable (fun x => q x * u x ^ 2) (haar d) := by
    intro u B hum hu0 huB
    refine Integrable.of_bound (C := C * B ^ 2) (hqm.aestronglyMeasurable.mul (hum.pow 2))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 x).le (sq_nonneg _))]
    exact mul_le_mul (hqC x) (pow_le_pow_left₀ (hu0 x) (huB x) 2) (sq_nonneg _)
      ((hq0 x).le.trans (hqC x))
  have hi1 := hint hu₁.aestronglyMeasurable_fun hu₁0 hu₁B
  have hi2 := hint hu₂.aestronglyMeasurable_fun hu₂0 hu₂B
  have hint₂ : ∫ x, q x * u₂ x ^ 2 ∂haar d = 1 := by
    have h1 : ∫ x, q x ∂haar d = ε * ∫ x, q x * u₁ x ^ 2 ∂haar d +
        (1 - ε) * ∫ x, q x * u₂ x ^ 2 ∂haar d := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hi1.const_mul ε)
        (hi2.const_mul (1 - ε))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      linear_combination (-(q x)) * hid x
    rw [hq1, hint₁] at h1
    have : (1 - ε) * (∫ x, q x * u₂ x ^ 2 ∂haar d - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by linarith)
    · linarith
  -- admissibility
  have hAd : F.Admissible := by
    refine ⟨?_, ?_, ?_⟩
    · refine diluteFam_forall q u₁ u₂ ε _ ?_ ?_
      · rw [diluteFam_θ0]; exact hε0
      · rw [diluteFam_θ1]; linarith
    · rw [diluteFam_sum, diluteFam_θ0, diluteFam_θ1]; ring
    · refine diluteFam_forall q u₁ u₂ ε _ ?_ ?_
      · rw [diluteFam_ρ0]
        exact ⟨fun x => mul_nonneg (hq0 x).le (sq_nonneg _), hint₁,
          memH1_sqrt_mul hqH hqC (fun x => (hq0 x).le) hu₁ hu₁0 hu₁B hg₁⟩
      · rw [diluteFam_ρ1]
        exact ⟨fun x => mul_nonneg (hq0 x).le (sq_nonneg _), hint₂,
          memH1_sqrt_mul hqH hqC (fun x => (hq0 x).le) hu₂ hu₂0 hu₂B hg₂⟩
  -- the gap
  obtain ⟨hmsG, -⟩ := msGap_decomp F hyp hAd
  have hdm : densMeasure F.bar = densMeasure q := by rw [hbar]
  have hmsGq : msGap V W F = ((ENNReal.ofReal ε * klDiv (densMeasure fun x => q x * u₁ x ^ 2)
      (densMeasure q) + ENNReal.ofReal (1 - ε) * klDiv (densMeasure fun x => q x * u₂ x ^ 2)
      (densMeasure q) : ℝ≥0∞) : EReal) := by
    rw [hmsG, hdm, hG0, zero_add]
    congr 1
    rw [diluteFam_sum, diluteFam_θ0, diluteFam_θ1, diluteFam_ρ0, diluteFam_ρ1]
  set S : ℝ≥0∞ := ENNReal.ofReal ε * klDiv (densMeasure fun x => q x * u₁ x ^ 2)
      (densMeasure q) + ENNReal.ofReal (1 - ε) * klDiv (densMeasure fun x => q x * u₂ x ^ 2)
      (densMeasure q) with hS
  have hSge : ENNReal.ofReal ε * klDiv (densMeasure fun x => q x * u₁ x ^ 2) (densMeasure q) ≤ S :=
    le_self_add
  have hSpos : 0 < S := lt_of_lt_of_le
    (ENNReal.mul_pos (by simpa using hε0) hKpos.ne') hSge
  refine ⟨⟨hAd, ?_⟩, hdm, ?_⟩
  · rw [hmsGq]; exact EReal.coe_ennreal_pos.2 hSpos
  · have hG : (msGap V W F).toENNReal = S := by rw [hmsGq, EReal.toENNReal_coe]
    have hDdec := msDiss_decomp F hyp hAd
    rw [hbar, hD0, zero_add] at hDdec
    have hDq : msDiss V W F = ENNReal.ofReal ε * relFisher (fun x => q x * u₁ x ^ 2) q +
        ENNReal.ofReal (1 - ε) * relFisher (fun x => q x * u₂ x ^ 2) q := by
      rw [hDdec, diluteFam_sum, diluteFam_θ0, diluteFam_θ1, diluteFam_ρ0, diluteFam_ρ1]
    rw [hG, hDq]
    exact ENNReal.div_le_div_left (by gcongr) _

end SharpLSI.FL
