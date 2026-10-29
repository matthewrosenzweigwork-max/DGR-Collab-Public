import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
Extended entropy for the manuscript's nonnegative integrable observables.
Source: eq:entropy and lem:cutoffs, exact snapshot 20260926T153433Z.
The positive part is a Lebesgue integral with values in ENNReal. In particular,
failure of entropy integrability does not use the real integral's default value.
The shift is 1 instead of 1/e; it cancels exactly for every finite measure.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

variable {α : Type*} [MeasurableSpace α]

/-- The continuous, nonnegative (on nonnegative inputs) shifted entropy density. -/
def entropyDensity (t : ℝ) : ℝ := t * Real.log t + 1

theorem entropyDensity_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ entropyDensity t := by
  have h := Real.self_sub_one_le_mul_log ht
  dsimp [entropyDensity]
  linarith

theorem continuous_entropyDensity : Continuous entropyDensity :=
  Real.continuous_mul_log.add continuous_const

/-- Entropy, on nonnegative integrable functions over a finite measure.
For a probability measure this is exactly the source's unnormalised entropy.
The value can be positive infinity. -/
def entropy (μ : Measure α) (F : α → ℝ) : EReal :=
  (∫⁻ x, ENNReal.ofReal (entropyDensity (F x)) ∂μ) -
    ((μ.real Set.univ + (∫ x, F x ∂μ) * Real.log (∫ x, F x ∂μ) : ℝ) : EReal)

theorem entropy_congr_ae {μ : Measure α} {F G : α → ℝ} (h : F =ᵐ[μ] G) :
    entropy μ F = entropy μ G := by
  unfold entropy
  rw [integral_congr_ae h,
    lintegral_congr_ae (h.mono fun _ hx ↦ congrArg (fun t ↦ ENNReal.ofReal (entropyDensity t)) hx)]

theorem entropy_eq_integral {μ : Measure α} [IsFiniteMeasure μ] {F : α → ℝ}
    (hF : 0 ≤ᵐ[μ] F) (hlog : Integrable (fun x ↦ F x * Real.log (F x)) μ) :
    entropy μ F =
      ((∫ x, F x * Real.log (F x) ∂μ) -
        (∫ x, F x ∂μ) * Real.log (∫ x, F x ∂μ) : ℝ) := by
  have hd : Integrable (fun x ↦ entropyDensity (F x)) μ := hlog.add (integrable_const 1)
  have hn : 0 ≤ᵐ[μ] fun x ↦ entropyDensity (F x) :=
    hF.mono fun _ hx ↦ entropyDensity_nonneg hx
  have hi := ofReal_integral_eq_lintegral_ofReal hd hn
  have hp : 0 ≤ ∫ x, entropyDensity (F x) ∂μ := integral_nonneg_of_ae hn
  unfold entropy
  rw [← hi, EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast hp),
    ← EReal.coe_sub]
  congr 1
  simp only [entropyDensity]
  rw [integral_add hlog (integrable_const 1)]
  simp only [integral_const, smul_eq_mul, mul_one]
  ring

theorem entropy_zero (μ : Measure α) [IsFiniteMeasure μ] :
    entropy μ (fun _ ↦ 0) = 0 := by
  rw [entropy_eq_integral (Filter.Eventually.of_forall fun _ ↦ le_refl 0)
    (by simp)]
  simp

theorem entropy_const (μ : Measure α) [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 ≤ c) :
    entropy μ (fun _ ↦ c) = 0 := by
  rw [entropy_eq_integral (Filter.Eventually.of_forall fun _ ↦ hc) (integrable_const _)]
  simp

/-- The real bound is equivalent to a bound on the extended shifted integral.
This equivalence does not assume entropy integrability. -/
theorem entropy_le_iff {μ : Measure α} {F : α → ℝ} {b : ℝ} :
    entropy μ F ≤ (b : EReal) ↔
      ((∫⁻ x, ENNReal.ofReal (entropyDensity (F x)) ∂μ) : EReal) ≤
        ((b + μ.real Set.univ +
          (∫ x, F x ∂μ) * Real.log (∫ x, F x ∂μ) : ℝ) : EReal) := by
  unfold entropy
  rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))]
  rw [← EReal.coe_add]
  rw [add_assoc]

/-- Nonintegrable positive entropy remains infinite, rather than receiving the
default value of a real Bochner integral. -/
theorem entropy_eq_top_of_not_integrable {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℝ} (hF : AEMeasurable F μ) (hn : 0 ≤ᵐ[μ] F)
    (hi : ¬ Integrable (fun x ↦ F x * Real.log (F x)) μ) : entropy μ F = ⊤ := by
  have hd : AEStronglyMeasurable (fun x ↦ entropyDensity (F x)) μ :=
    (continuous_entropyDensity.measurable.comp_aemeasurable hF).aestronglyMeasurable
  have hdn : 0 ≤ᵐ[μ] fun x ↦ entropyDensity (F x) :=
    hn.mono fun _ hx ↦ entropyDensity_nonneg hx
  have hni : ¬ Integrable (fun x ↦ entropyDensity (F x)) μ := by
    simpa only [entropyDensity, integrable_add_const_iff] using hi
  have htop : (∫⁻ x, ENNReal.ofReal (entropyDensity (F x)) ∂μ) = ⊤ := by
    by_contra h
    exact hni ((lintegral_ofReal_ne_top_iff_integrable hd hdn).mp h)
  unfold entropy
  rw [htop, EReal.coe_ennreal_top, EReal.top_sub_coe]

/-- Fatou passes a sequence of finite entropy upper bounds to an almost
everywhere limit, when its masses and the bounds converge. Entropy finiteness
of the limit is a conclusion, never a hypothesis. This is the analytic step
used for the source's ambient-domain extension. -/
theorem entropy_le_of_ae_tendsto {μ : Measure α} {F : ℕ → α → ℝ} {f : α → ℝ}
    {b : ℕ → ℝ} {B : ℝ}
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)))
    (hmass : Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)))
    (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ n, entropy μ (F n) ≤ (b n : EReal)) : entropy μ f ≤ (B : EReal) := by
  let s : ℕ → ℝ := fun n ↦ b n + μ.real Set.univ +
    (∫ x, F n x ∂μ) * Real.log (∫ x, F n x ∂μ)
  let S : ℝ := B + μ.real Set.univ + (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)
  have hs : Tendsto s atTop (𝓝 S) :=
    (hb.add tendsto_const_nhds).add (Real.continuous_mul_log.tendsto _ |>.comp hmass)
  have hi (n : ℕ) :
      ((∫⁻ x, ENNReal.ofReal (entropyDensity (F n x)) ∂μ) : EReal) ≤ (s n : EReal) :=
    entropy_le_iff.mp (hbound n)
  have hn (n : ℕ) : 0 ≤ s n := by
    exact_mod_cast (EReal.coe_ennreal_nonneg _).trans (hi n)
  have hS : 0 ≤ S := ge_of_tendsto' hs hn
  have hle (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (entropyDensity (F n x)) ∂μ) ≤ ENNReal.ofReal (s n) := by
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mp
    simpa only [EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast hn n)] using hi n
  have hm (n : ℕ) : AEMeasurable (fun x ↦ ENNReal.ofReal (entropyDensity (F n x))) μ :=
    (continuous_entropyDensity.measurable.comp_aemeasurable (hF n)).ennreal_ofReal
  have hl : (∫⁻ x, ENNReal.ofReal (entropyDensity (f x)) ∂μ) ≤ ENNReal.ofReal S := by
    calc
      _ = ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (entropyDensity (F n x))) atTop ∂μ := by
        apply lintegral_congr_ae
        exact hlim.mono fun x hx ↦
          ((ENNReal.continuous_ofReal.comp continuous_entropyDensity).tendsto (f x)
            |>.comp hx).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (entropyDensity (F n x)) ∂μ) atTop :=
        lintegral_liminf_le' hm
      _ ≤ liminf (fun n ↦ ENNReal.ofReal (s n)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
      _ = ENNReal.ofReal S := (ENNReal.continuous_ofReal.tendsto S |>.comp hs).liminf_eq
  apply entropy_le_iff.mpr
  simpa only [EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast hS)] using
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hl)

end PeriodicAttractiveLogGas
