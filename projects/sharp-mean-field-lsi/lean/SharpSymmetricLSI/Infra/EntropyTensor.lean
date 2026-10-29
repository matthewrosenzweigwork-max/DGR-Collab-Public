import Mathlib

/-!
# Subadditivity of entropy on products (Phase 3, lane C)

For probability measures `μ, ν` and a measurable `F` on `α × β` with `0 < c ≤ F ≤ C`,
`Ent_{μ⊗ν}(F) ≤ ∫ Ent_ν(F(a,·)) dμ(a) + ∫ Ent_μ(F(·,b)) dν(b)`,
where `Ent(F) = ∫ F log F - (∫F) log ∫F`. The first summand is the exact conditional part
`Ent_{μ⊗ν}(F) - Ent_μ(G)`, `G(a) = ∫ F(a,b) dν(b)`; the bound `Ent_μ(G) ≤ ∫ Ent_μ(F(·,b)) dν(b)`
is the Gibbs inequality `∫ f ψ ≤ Ent(f)` for `∫ e^ψ = 1`, with `ψ = log(G/∫G)`.
-/

open MeasureTheory Set Filter

namespace SharpLSI

/-- The real entropy `∫ F log F - (∫F) log ∫F`. -/
noncomputable def entR {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℝ) : ℝ :=
  ∫ x, F x * Real.log (F x) ∂μ - (∫ x, F x ∂μ) * Real.log (∫ x, F x ∂μ)

theorem abs_mul_log_le {c C x : ℝ} (hc : 0 < c) (hx : c ≤ x) (hxC : x ≤ C) :
    |x * Real.log x| ≤ C * (|Real.log c| + |Real.log C|) := by
  have hx0 : 0 < x := lt_of_lt_of_le hc hx
  have h1 : Real.log c ≤ Real.log x := Real.log_le_log hc hx
  have h2 : Real.log x ≤ Real.log C := Real.log_le_log hx0 hxC
  have h3 : |Real.log x| ≤ |Real.log c| + |Real.log C| := by
    rw [abs_le]; constructor
    · have := neg_abs_le (Real.log c); have := abs_nonneg (Real.log C); linarith
    · have := le_abs_self (Real.log C); have := abs_nonneg (Real.log c); linarith
  rw [abs_mul, abs_of_pos hx0]
  exact mul_le_mul hxC h3 (abs_nonneg _) (by linarith)

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem integral_mem_Icc {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ} [IsProbabilityMeasure ρ]
    {f : γ → ℝ} (hf : AEStronglyMeasurable f ρ) {c C : ℝ} (hc : ∀ x, c ≤ f x) (hC : ∀ x, f x ≤ C) :
    c ≤ ∫ x, f x ∂ρ ∧ ∫ x, f x ∂ρ ≤ C := by
  have hi : Integrable f ρ := Integrable.of_bound hf (|c| + |C|) (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_le]; constructor
    · have := hc x; have := neg_abs_le c; have := abs_nonneg C; linarith
    · have := hC x; have := le_abs_self C; have := abs_nonneg c; linarith)
  constructor
  · calc c = ∫ _x, c ∂ρ := by simp
      _ ≤ ∫ x, f x ∂ρ := integral_mono (integrable_const c) hi hc
  · calc ∫ x, f x ∂ρ ≤ ∫ _x, C ∂ρ := integral_mono hi (integrable_const C) hC
      _ = C := by simp

/-- Gibbs inequality: `∫ f ψ ≤ Ent(f)` when `∫ e^ψ = 1`, in the form needed below. -/
theorem integral_mul_log_ratio_le {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    [IsProbabilityMeasure ρ] {f G : γ → ℝ} (hf : Measurable f) (hG : Measurable G) {c C : ℝ}
    (hc : 0 < c) (hfc : ∀ x, c ≤ f x) (hfC : ∀ x, f x ≤ C) (hGc : ∀ x, c ≤ G x)
    (hGC : ∀ x, G x ≤ C) :
    ∫ x, f x * (Real.log (G x) - Real.log (∫ y, G y ∂ρ)) ∂ρ ≤ entR ρ f := by
  set Z := ∫ y, G y ∂ρ
  set m := ∫ y, f y ∂ρ
  obtain ⟨hZc, hZC⟩ := integral_mem_Icc (ρ := ρ) hG.aestronglyMeasurable hGc hGC
  obtain ⟨hmc, hmC⟩ := integral_mem_Icc (ρ := ρ) hf.aestronglyMeasurable hfc hfC
  have hZ : 0 < Z := lt_of_lt_of_le hc hZc
  have hm : 0 < m := lt_of_lt_of_le hc hmc
  have hf0 : ∀ x, 0 < f x := fun x => lt_of_lt_of_le hc (hfc x)
  have hG0 : ∀ x, 0 < G x := fun x => lt_of_lt_of_le hc (hGc x)
  have bdd : ∀ {F : γ → ℝ}, Measurable F → ∀ B, (∀ x, |F x| ≤ B) → Integrable F ρ :=
    fun {F} hF B hB => Integrable.of_bound hF.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hlogG : ∀ x, |Real.log (G x)| ≤ |Real.log c| + |Real.log C| := fun x => by
    have h1 := Real.log_le_log hc (hGc x); have h2 := Real.log_le_log (hG0 x) (hGC x)
    rw [abs_le]; constructor
    · have := neg_abs_le (Real.log c); have := abs_nonneg (Real.log C); linarith
    · have := le_abs_self (Real.log C); have := abs_nonneg (Real.log c); linarith
  have hlogf : ∀ x, |Real.log (f x)| ≤ |Real.log c| + |Real.log C| := fun x => by
    have h1 := Real.log_le_log hc (hfc x); have h2 := Real.log_le_log (hf0 x) (hfC x)
    rw [abs_le]; constructor
    · have := neg_abs_le (Real.log c); have := abs_nonneg (Real.log C); linarith
    · have := le_abs_self (Real.log C); have := abs_nonneg (Real.log c); linarith
  have hfi : Integrable f ρ := bdd hf (|C| + |c|) fun x => by
    rw [abs_of_pos (hf0 x)]; have := hfC x; have := le_abs_self C; have := abs_nonneg c; linarith
  have hGi : Integrable G ρ := bdd hG (|C| + |c|) fun x => by
    rw [abs_of_pos (hG0 x)]; have := hGC x; have := le_abs_self C; have := abs_nonneg c; linarith
  have hflf : Integrable (fun x => f x * Real.log (f x)) ρ :=
    bdd (hf.mul (Real.measurable_log.comp hf)) _ fun x => abs_mul_log_le hc (hfc x) (hfC x)
  have hflG : Integrable (fun x => f x * Real.log (G x)) ρ :=
    bdd (hf.mul (Real.measurable_log.comp hG)) (C * (|Real.log c| + |Real.log C|)) fun x => by
      rw [abs_mul, abs_of_pos (hf0 x)]
      exact mul_le_mul (hfC x) (hlogG x) (abs_nonneg _) (by linarith [hf0 x, hfC x])
  -- pointwise `f (log G - log Z + log m - log f) ≤ m G / Z - f`
  have hpt : ∀ x, f x * (Real.log (G x) - Real.log Z) + f x * Real.log m -
      f x * Real.log (f x) ≤ m * G x / Z - f x := fun x => by
    have hr : 0 < m * G x / (Z * f x) := by have := hf0 x; have := hG0 x; positivity
    have hl := Real.log_le_sub_one_of_pos hr
    rw [Real.log_div (by have := hG0 x; positivity) (by have := hf0 x; positivity),
      Real.log_mul hm.ne' (hG0 x).ne', Real.log_mul hZ.ne' (hf0 x).ne'] at hl
    have := mul_le_mul_of_nonneg_left hl (hf0 x).le
    have e : f x * (m * G x / (Z * f x) - 1) = m * G x / Z - f x := by
      field_simp [(hf0 x).ne']
    nlinarith
  have h2 : Integrable (fun x => f x * (Real.log (G x) - Real.log Z)) ρ :=
    (hflG.sub (hfi.mul_const (Real.log Z))).congr (Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]; ring)
  have h1 : Integrable (fun x => f x * (Real.log (G x) - Real.log Z) + f x * Real.log m) ρ :=
    h2.add (hfi.mul_const _)
  have hψ : Integrable (fun x => m * G x / Z - f x) ρ := ((hGi.const_mul m).div_const Z).sub hfi
  have hint := integral_mono (f := fun x => f x * (Real.log (G x) - Real.log Z) +
    f x * Real.log m - f x * Real.log (f x)) (g := fun x => m * G x / Z - f x) (h1.sub hflf) hψ hpt
  rw [integral_sub (f := fun x => f x * (Real.log (G x) - Real.log Z) + f x * Real.log m)
      (g := fun x => f x * Real.log (f x)) h1 hflf,
    integral_add (f := fun x => f x * (Real.log (G x) - Real.log Z))
      (g := fun x => f x * Real.log m) h2 (hfi.mul_const _),
    integral_sub (f := fun x => m * G x / Z) (g := f) ((hGi.const_mul m).div_const Z) hfi,
    integral_div, integral_const_mul, integral_mul_const] at hint
  unfold entR
  have e2 : m * Z / Z = m := by field_simp
  rw [e2] at hint
  linarith

theorem measurable_integral_right {F : α × β → ℝ} (hF : Measurable F) :
    Measurable fun a => ∫ b, F (a, b) ∂ν :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem measurable_integral_left {F : α × β → ℝ} (hF : Measurable F) :
    Measurable fun b => ∫ a, F (a, b) ∂μ :=
  (hF.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable

/-- **Subadditivity of entropy** on a product of probability spaces. -/
theorem entR_prod_le {F : α × β → ℝ} (hF : Measurable F) {c C : ℝ} (hc : 0 < c)
    (hFc : ∀ z, c ≤ F z) (hFC : ∀ z, F z ≤ C) :
    entR (μ.prod ν) F ≤ ∫ a, entR ν (fun b => F (a, b)) ∂μ + ∫ b, entR μ (fun a => F (a, b)) ∂ν := by
  have hF0 : ∀ z, 0 < F z := fun z => lt_of_lt_of_le hc (hFc z)
  set B := C * (|Real.log c| + |Real.log C|) with hB
  have hL : Measurable fun z => F z * Real.log (F z) := hF.mul (Real.measurable_log.comp hF)
  have hLb : ∀ z, |F z * Real.log (F z)| ≤ B := fun z => abs_mul_log_le hc (hFc z) (hFC z)
  have bddP : ∀ {H : α × β → ℝ}, Measurable H → ∀ D, (∀ z, |H z| ≤ D) → Integrable H (μ.prod ν) :=
    fun {H} hH D hD => Integrable.of_bound hH.aestronglyMeasurable D
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hD z)
  have hFb : ∀ z, |F z| ≤ C := fun z => by rw [abs_of_pos (hF0 z)]; exact hFC z
  have hFi := bddP hF C hFb
  have hLi := bddP hL B hLb
  -- marginals
  set G : α → ℝ := fun a => ∫ b, F (a, b) ∂ν with hGdef
  have hGm : Measurable G := measurable_integral_right hF
  have hGb : ∀ a, c ≤ G a ∧ G a ≤ C := fun a =>
    integral_mem_Icc (ρ := ν) (hF.comp measurable_prodMk_left).aestronglyMeasurable
      (fun b => hFc _) (fun b => hFC _)
  set Z := ∫ a, G a ∂μ with hZdef
  have hZ : ∫ z, F z ∂(μ.prod ν) = Z := integral_prod F hFi
  have hLL : ∫ z, F z * Real.log (F z) ∂(μ.prod ν) =
      ∫ a, ∫ b, F (a, b) * Real.log (F (a, b)) ∂ν ∂μ := integral_prod _ hLi
  -- the conditional part
  have hGlogm : Measurable fun a => G a * Real.log (G a) := hGm.mul (Real.measurable_log.comp hGm)
  have hGlogi : Integrable (fun a => G a * Real.log (G a)) μ :=
    Integrable.of_bound hGlogm.aestronglyMeasurable B (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]; exact abs_mul_log_le hc (hGb a).1 (hGb a).2)
  have hinnerL : Integrable (fun a => ∫ b, F (a, b) * Real.log (F (a, b)) ∂ν) μ :=
    hLi.integral_prod_left
  have hcond : ∫ a, entR ν (fun b => F (a, b)) ∂μ =
      ∫ a, ∫ b, F (a, b) * Real.log (F (a, b)) ∂ν ∂μ - ∫ a, G a * Real.log (G a) ∂μ := by
    unfold entR
    exact integral_sub hinnerL hGlogi
  -- the marginal part, by Fubini and the Gibbs inequality
  have hψ : ∀ a, |Real.log (G a) - Real.log Z| ≤ 2 * (|Real.log c| + |Real.log C|) := fun a => by
    obtain ⟨hZc, hZC⟩ := integral_mem_Icc (ρ := μ) hGm.aestronglyMeasurable (fun a => (hGb a).1)
      (fun a => (hGb a).2)
    have hG0 : 0 < G a := lt_of_lt_of_le hc (hGb a).1
    have hZ0 : 0 < Z := lt_of_lt_of_le hc hZc
    have h1 := Real.log_le_log hc (hGb a).1; have h2 := Real.log_le_log hG0 (hGb a).2
    have h3 := Real.log_le_log hc hZc; have h4 := Real.log_le_log hZ0 hZC
    rw [abs_le]; constructor
    · have := neg_abs_le (Real.log c); have := le_abs_self (Real.log C)
      have := abs_nonneg (Real.log c); have := abs_nonneg (Real.log C); linarith
    · have := neg_abs_le (Real.log c); have := le_abs_self (Real.log C)
      have := abs_nonneg (Real.log c); have := abs_nonneg (Real.log C); linarith
  set Φ : α × β → ℝ := fun z => F z * (Real.log (G z.1) - Real.log Z) with hΦ
  have hΦm : Measurable Φ :=
    hF.mul (((Real.measurable_log.comp hGm).comp measurable_fst).sub measurable_const)
  have hΦi : Integrable Φ (μ.prod ν) := bddP hΦm (C * (2 * (|Real.log c| + |Real.log C|)))
    fun z => by
      rw [hΦ, abs_mul]
      exact mul_le_mul (hFb z) (hψ z.1) (abs_nonneg _) (by linarith [hF0 z, hFC z])
  have hmarg : ∫ a, G a * Real.log (G a) ∂μ - Z * Real.log Z =
      ∫ b, ∫ a, Φ (a, b) ∂μ ∂ν := by
    rw [← integral_prod_symm Φ hΦi, integral_prod Φ hΦi]
    have hin : ∀ a, ∫ b, Φ (a, b) ∂ν = G a * Real.log (G a) - G a * Real.log Z := fun a => by
      simp only [hΦ]
      rw [integral_mul_const, mul_sub]
    simp_rw [hin]
    have hGi : Integrable G μ := Integrable.of_bound hGm.aestronglyMeasurable C
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hc (hGb a).1)]; exact (hGb a).2)
    rw [integral_sub hGlogi (hGi.mul_const _), integral_mul_const]
  have hgibbs : ∀ b, ∫ a, Φ (a, b) ∂μ ≤ entR μ (fun a => F (a, b)) := fun b =>
    integral_mul_log_ratio_le (hF.comp measurable_prodMk_right) hGm hc (fun a => hFc _)
      (fun a => hFC _) (fun a => (hGb a).1) (fun a => (hGb a).2)
  -- integrability of the slice entropies
  have hentm : Measurable fun b => entR μ (fun a => F (a, b)) := by
    unfold entR
    exact (measurable_integral_left hL).sub ((measurable_integral_left hF).mul
      (Real.measurable_log.comp (measurable_integral_left hF)))
  have hentb : ∀ b, |entR μ (fun a => F (a, b))| ≤ 2 * B := fun b => by
    unfold entR
    obtain ⟨h1, h2⟩ := integral_mem_Icc (ρ := μ) (hF.comp measurable_prodMk_right).aestronglyMeasurable
      (fun a => hFc (a, b)) (fun a => hFC (a, b))
    have hA : |∫ a, F (a, b) * Real.log (F (a, b)) ∂μ| ≤ B := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ a, |F (a, b) * Real.log (F (a, b))| ∂μ ≤ ∫ _a, B ∂μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun a => abs_nonneg _)
              (integrable_const B) (Eventually.of_forall fun a => hLb _)
        _ = B := by simp
    simp only [Function.comp_apply] at h1 h2
    have hB' := abs_mul_log_le hc h1 h2
    beta_reduce
    rw [abs_le] at hA hB' ⊢
    constructor <;> linarith [hA.1, hA.2, hB'.1, hB'.2]
  have henti : Integrable (fun b => entR μ (fun a => F (a, b))) ν :=
    Integrable.of_bound hentm.aestronglyMeasurable (2 * B) (Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs]; exact hentb b)
  have hmarg_le : ∫ b, ∫ a, Φ (a, b) ∂μ ∂ν ≤ ∫ b, entR μ (fun a => F (a, b)) ∂ν :=
    integral_mono hΦi.integral_prod_right henti hgibbs
  have htot : entR (μ.prod ν) F = ∫ a, ∫ b, F (a, b) * Real.log (F (a, b)) ∂ν ∂μ -
      Z * Real.log Z := by
    unfold entR; rw [hZ, hLL]
  rw [htot]
  linarith

theorem abs_entR_le {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ} [IsProbabilityMeasure ρ]
    {f : γ → ℝ} (hf : Measurable f) {c C : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x)
    (hfC : ∀ x, f x ≤ C) : |entR ρ f| ≤ 2 * (C * (|Real.log c| + |Real.log C|)) := by
  unfold entR
  obtain ⟨h1, h2⟩ := integral_mem_Icc (ρ := ρ) hf.aestronglyMeasurable hfc hfC
  have hA : |∫ x, f x * Real.log (f x) ∂ρ| ≤ C * (|Real.log c| + |Real.log C|) := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |f x * Real.log (f x)| ∂ρ ≤ ∫ _x, C * (|Real.log c| + |Real.log C|) ∂ρ :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun x => abs_mul_log_le hc (hfc x) (hfC x))
      _ = _ := by simp
  have hB' := abs_mul_log_le hc h1 h2
  rw [abs_le] at hA hB' ⊢
  constructor <;> linarith [hA.1, hA.2, hB'.1, hB'.2]

theorem integrable_entR_left {F : α × β → ℝ} (hF : Measurable F) {c C : ℝ} (hc : 0 < c)
    (hFc : ∀ z, c ≤ F z) (hFC : ∀ z, F z ≤ C) :
    Integrable (fun a => entR ν (fun b => F (a, b))) μ := by
  have hL : Measurable fun z => F z * Real.log (F z) := hF.mul (Real.measurable_log.comp hF)
  have hm : Measurable fun a => entR ν (fun b => F (a, b)) := by
    unfold entR
    exact (measurable_integral_right hL).sub ((measurable_integral_right hF).mul
      (Real.measurable_log.comp (measurable_integral_right hF)))
  exact Integrable.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs]
    exact abs_entR_le (hF.comp measurable_prodMk_left) hc (fun b => hFc _) (fun b => hFC _))

theorem integrable_entR_right {F : α × β → ℝ} (hF : Measurable F) {c C : ℝ} (hc : 0 < c)
    (hFc : ∀ z, c ≤ F z) (hFC : ∀ z, F z ≤ C) :
    Integrable (fun b => entR μ (fun a => F (a, b))) ν := by
  have hL : Measurable fun z => F z * Real.log (F z) := hF.mul (Real.measurable_log.comp hF)
  have hm : Measurable fun b => entR μ (fun a => F (a, b)) := by
    unfold entR
    exact (measurable_integral_left hL).sub ((measurable_integral_left hF).mul
      (Real.measurable_log.comp (measurable_integral_left hF)))
  exact Integrable.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun b => by
    rw [Real.norm_eq_abs]
    exact abs_entR_le (hF.comp measurable_prodMk_right) hc (fun a => hFc _) (fun a => hFC _))

end SharpLSI
