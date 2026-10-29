import SharpSymmetricLSI.Paper.CenteredEntropy

/-!
# R19 (Lemma 5.2), part 1: mean-field coercivity in usable form

* `klDiv_haar_ne_top_of_minimizer`: `H(ρ|μ) < ∞ ⇒ H(ρ|m) < ∞` (the minimizer has a density bounded
  above and below), via `m = μ.tilted (-log q)`.
* `mf_coercive_of`: the conclusion of Lemma 4.2 (R16, passed as the hypothesis `hco`) together with
  `G = H(·|μ) + J` (R17) gives `c H(ρ|μ) ≤ H(ρ|μ) + J(ρ)` in `ℝ` for every probability `ρ` with
  `H(ρ|μ) < ∞`.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The conclusion of Lemma 4.2 (R16 `gap_ge_entropy`), used as an explicit hypothesis. -/
def MFCoercive (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : ProbabilityMeasure (Torus d)) :
    Prop :=
  ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ρ : ProbabilityMeasure (Torus d),
    klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
      (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ENNReal) : EReal) ≤
        gap V W ρ

section coerc
variable (hyp : Hyp V W KV KW)
include hyp

theorem tilted_negLog_densMeasure {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ x, 0 < q x)
    (hq1 : ∫ x, q x ∂haar d = 1) :
    (densMeasure q).tilted (fun x => -Real.log (q x)) = haar d := by
  have hZ : ∫ x, exp (-Real.log (q x)) ∂densMeasure q = 1 := by
    rw [integral_densMeasure' (fun x => (hq0 x).le) hq1]
    simp_rw [Real.exp_neg, Real.exp_log (hq0 _)]
    have : ∀ x, q x * (q x)⁻¹ = 1 := fun x => mul_inv_cancel₀ (hq0 x).ne'
    simp [this]
  unfold Measure.tilted
  rw [hZ]
  have hfun : (fun x => ENNReal.ofReal (exp (-Real.log (q x)) / 1)) =
      fun x => (ENNReal.ofReal (q x))⁻¹ := by
    funext x
    rw [div_one, Real.exp_neg, Real.exp_log (hq0 x), ENNReal.ofReal_inv_of_pos (hq0 x)]
  rw [hfun, densMeasure]
  exact withDensity_inv_same (ENNReal.measurable_ofReal.comp hqm)
    (Filter.Eventually.of_forall fun x => by simp [hq0 x])
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_ne_top)

theorem klDiv_haar_ne_top_of_minimizer {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    (h : klDiv ρ (μ : Measure (Torus d)) ≠ ⊤) : klDiv ρ (haar d) ≠ ⊤ := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨c0, C0, L, hc0, hb⟩ := elDensity_bounds hyp
  obtain ⟨hbd, -⟩ := hb μm inferInstance
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp μm
  set q := elDens V W μm
  have hμq : μm = densMeasure q := minimizer_eq_elDensity hyp hμ
  have hfB : ∀ x, |-Real.log (q x)| ≤ |Real.log c0| + |Real.log C0| := by
    intro x
    rw [abs_neg]
    have h1 := Real.log_le_log (hqpos x) (hbd x).2
    have h2 := Real.log_le_log hc0 (hbd x).1
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log c0), neg_abs_le (Real.log c0),
      le_abs_self (Real.log C0), neg_abs_le (Real.log C0)]
  have := (klDiv_tilted (ρ := ρ) (ν := μm) (f := fun x => -Real.log (q x))
    (measurable_log.comp hqm).neg hfB h).1
  rwa [hμq, tilted_negLog_densMeasure hyp hqm hqpos hq1] at this

/-- **Mean-field coercivity** in `ℝ`, from Lemma 4.2 (`hco`) and `G = H(·|μ) + J`. -/
theorem mf_coercive_of {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    (hco : MFCoercive V W μ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ →
      klDiv ρ (μ : Measure (Torus d)) ≠ ⊤ →
        c * (klDiv ρ (μ : Measure (Torus d))).toReal ≤
          (klDiv ρ (μ : Measure (Torus d))).toReal + Jfun W μ ρ := by
  obtain ⟨c, hc0, hc1, hc⟩ := hco
  refine ⟨c, hc0, hc1, fun ρ hρ h => ?_⟩
  set ρ' : ProbabilityMeasure (Torus d) := ⟨ρ, hρ⟩
  have h1 := hc ρ' (klDiv_haar_ne_top_of_minimizer hyp hμ h)
  rw [gap_eq_aux hyp hμ ρ'] at h1
  change (c : EReal) * ((klDiv ρ (μ : Measure (Torus d)) : ENNReal) : EReal) ≤
    ((klDiv ρ (μ : Measure (Torus d)) : ENNReal) : EReal) + ((Jfun W μ ρ : ℝ) : EReal) at h1
  rw [← ENNReal.ofReal_toReal h, EReal.coe_ennreal_ofReal,
    max_eq_left ENNReal.toReal_nonneg, ← EReal.coe_mul, ← EReal.coe_add] at h1
  exact EReal.coe_le_coe_iff.mp h1

end coerc

end SharpLSI
