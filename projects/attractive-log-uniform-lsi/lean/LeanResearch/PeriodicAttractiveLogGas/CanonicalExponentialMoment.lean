import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The analytic summation step of `thm:canonical-pairs`: factorial even
moments imply exponential integrability. The combinatorial moment bound
is an explicit input; this module does not prove the canonical-pairs theorem. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace PeriodicAttractiveLogGas.CanonicalExponentialMoment

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Nonnegative series may be integrated without assuming integrability
of their sum. Finiteness is obtained from the summable integrals by Tonelli. -/
theorem integrable_integral_of_nonneg_hasSum {F : ℕ → α → ℝ} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hF : ∀ n, Integrable (F n) μ)
    (hpos : ∀ n x, 0 ≤ F n x) (hs : ∀ x, HasSum (fun n => F n x) (f x))
    (hi : Summable (fun n => ∫ x, F n x ∂μ)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = ∑' n, ∫ x, F n x ∂μ := by
  have heq (x : α) : f x = ∑' n, F n x := (hs x).tsum_eq.symm
  have hnonneg : ∀ x, 0 ≤ f x := fun x => heq x ▸ tsum_nonneg (fun n => hpos n x)
  have hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∑' n, ENNReal.ofReal (∫ x, F n x ∂μ) := by
    simp_rw [heq, ENNReal.ofReal_tsum_of_nonneg (fun n => hpos n _) (hs _).summable]
    rw [lintegral_tsum (fun n => (hF n).aemeasurable.ennreal_ofReal)]
    congr 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (hF n)
      (Eventually.of_forall (hpos n))).symm
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf (Eventually.of_forall hnonneg)).mp
      (hlin ▸ hi.tsum_ofReal_ne_top)
  refine ⟨hint, ?_⟩
  have hnorm : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hpos _ _)] using hi
  rw [show f = (fun x => ∑' n, F n x) from funext heq]
  exact (integral_tsum_of_summable_integral_norm hF hnorm).symm

/-- The source comparison retains the linear term, whose expectation vanishes. -/
theorem exp_le_linear_cosh (u : ℝ) : Real.exp u ≤ 2 * Real.cosh u - 1 + u := by
  rw [Real.cosh_eq]
  have h := Real.add_one_le_exp (-u)
  linarith

variable [IsProbabilityMeasure μ]

/-- The nonnegative cosh series is integrable under the even-moment bound. -/
theorem integral_cosh_le_of_even_moments {Y : α → ℝ} (hY : Measurable Y)
    {A : ℝ} (hA : 0 ≤ A)
    (hMom : ∀ k : ℕ, 1 ≤ k → Integrable (fun ω => (Y ω) ^ (2 * k)) μ ∧
      (∫ ω, (Y ω) ^ (2 * k) ∂μ) ≤ A ^ (2 * k) * ((2 * k).factorial : ℝ))
    {t : ℝ} (ht : |t| * A < 1) :
    Integrable (fun ω => Real.cosh (t * Y ω)) μ ∧
      (∫ ω, Real.cosh (t * Y ω) ∂μ) ≤ (1 - (|t| * A) ^ 2)⁻¹ := by
  let F : ℕ → α → ℝ := fun k ω => (t * Y ω) ^ (2 * k) / ((2 * k).factorial : ℝ)
  have hFpos (k : ℕ) (ω : α) : 0 ≤ F k ω := by
    dsimp [F]
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hFint (k : ℕ) : Integrable (F k) μ := by
    by_cases hk : k = 0
    · subst k
      simp [F]
    · simpa only [F, mul_pow] using
        ((hMom k (Nat.one_le_iff_ne_zero.mpr hk)).1.const_mul (t ^ (2 * k))).div_const
          ((2 * k).factorial : ℝ)
  have hFbound (k : ℕ) : (∫ ω, F k ω ∂μ) ≤ ((|t| * A) ^ 2) ^ k := by
    by_cases hk : k = 0
    · subst k
      simp [F]
    · have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
      have hpow : t ^ (2 * k) * A ^ (2 * k) = ((|t| * A) ^ 2) ^ k := by
        simp only [mul_pow, pow_mul, sq_abs]
      rw [show (∫ ω, F k ω ∂μ) =
          t ^ (2 * k) * (∫ ω, (Y ω) ^ (2 * k) ∂μ) / ((2 * k).factorial : ℝ) by
        simp only [F, mul_pow, integral_div, integral_const_mul]]
      apply (div_le_iff₀ hfac).mpr
      calc
        t ^ (2 * k) * (∫ ω, (Y ω) ^ (2 * k) ∂μ) ≤
            t ^ (2 * k) * (A ^ (2 * k) * ((2 * k).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (hMom k (Nat.one_le_iff_ne_zero.mpr hk)).2
            (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
        _ = ((|t| * A) ^ 2) ^ k * ((2 * k).factorial : ℝ) := by rw [← mul_assoc, hpow]
  have hr0 : 0 ≤ |t| * A := mul_nonneg (abs_nonneg _) hA
  have hr2 : (|t| * A) ^ 2 < 1 := by nlinarith
  have hgeo := summable_geometric_of_lt_one (sq_nonneg (|t| * A)) hr2
  have hi : Summable (fun k => ∫ ω, F k ω ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (hFpos k)) hFbound hgeo
  have hs (ω : α) : HasSum (fun k => F k ω) (Real.cosh (t * Y ω)) :=
    Real.hasSum_cosh (t * Y ω)
  have hmeas : AEStronglyMeasurable (fun ω => Real.cosh (t * Y ω)) μ := by
    exact (Real.continuous_cosh.measurable.comp (hY.const_mul t)).aestronglyMeasurable
  obtain ⟨hint, heq⟩ := integrable_integral_of_nonneg_hasSum hmeas hFint hFpos hs hi
  refine ⟨hint, ?_⟩
  rw [heq, ← tsum_geometric_of_lt_one (sq_nonneg (|t| * A)) hr2]
  exact hi.tsum_le_tsum hFbound hgeo

/-- Source exponential bound. Exponential integrability is a conclusion,
and only the even moments and the mean are assumed. -/
theorem integral_exp_le_of_even_moments {Y : α → ℝ} (hY : Measurable Y)
    (h1 : Integrable Y μ) (hmean : (∫ ω, Y ω ∂μ) = 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hMom : ∀ k : ℕ, 1 ≤ k → Integrable (fun ω => (Y ω) ^ (2 * k)) μ ∧
      (∫ ω, (Y ω) ^ (2 * k) ∂μ) ≤ A ^ (2 * k) * ((2 * k).factorial : ℝ))
    {t : ℝ} (ht : |t| * A < 1) :
    Integrable (fun ω => Real.exp (t * Y ω)) μ ∧
      (∫ ω, Real.exp (t * Y ω) ∂μ) ≤
        (1 + (|t| * A) ^ 2) / (1 - (|t| * A) ^ 2) := by
  obtain ⟨hc, hbound⟩ := integral_cosh_le_of_even_moments hY hA hMom ht
  have hu : Integrable (fun ω => 2 * Real.cosh (t * Y ω) - 1) μ :=
    (hc.const_mul 2).sub (integrable_const (1 : ℝ))
  have hv : Integrable (fun ω => t * Y ω) μ := h1.const_mul t
  have hint : Integrable (fun ω => Real.exp (t * Y ω)) μ := by
    apply (hu.add hv).mono'
      ((Real.continuous_exp.measurable.comp (hY.const_mul t)).aestronglyMeasurable)
    exact Eventually.of_forall (fun ω => by
      change ‖Real.exp (t * Y ω)‖ ≤ 2 * Real.cosh (t * Y ω) - 1 + t * Y ω
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact exp_le_linear_cosh _)
  refine ⟨hint, ?_⟩
  have hr0 : 0 ≤ |t| * A := mul_nonneg (abs_nonneg _) hA
  have hr2 : (|t| * A) ^ 2 < 1 := by nlinarith
  calc
    (∫ ω, Real.exp (t * Y ω) ∂μ) ≤
        ∫ ω, (2 * Real.cosh (t * Y ω) - 1 + t * Y ω) ∂μ :=
      integral_mono hint (hu.add hv) (fun ω => exp_le_linear_cosh _)
    _ = 2 * (∫ ω, Real.cosh (t * Y ω) ∂μ) - 1 := by
      rw [integral_add hu hv, integral_sub (hc.const_mul 2) (integrable_const (1 : ℝ)),
        integral_const_mul, integral_const_mul, hmean]
      simp
    _ ≤ 2 * (1 - (|t| * A) ^ 2)⁻¹ - 1 := by linarith
    _ = (1 + (|t| * A) ^ 2) / (1 - (|t| * A) ^ 2) := by
      apply (eq_div_iff (ne_of_gt (sub_pos.mpr hr2))).mpr
      rw [sub_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr hr2))]
      ring

/-- The exact analytic conclusion of the canonical pair-sum estimate,
conditional on its centering and factorial even-moment inputs. -/
theorem integral_exp_normalized_le {S : α → ℝ} (hS : Measurable S)
    (h1 : Integrable S μ) (hmean : (∫ ω, S ω ∂μ) = 0)
    {L : ℝ} (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m)
    (hMom : ∀ k : ℕ, 1 ≤ k → Integrable (fun ω => (S ω) ^ (2 * k)) μ ∧
      (∫ ω, (S ω) ^ (2 * k) ∂μ) ≤
        (8 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
          ((2 * k).factorial : ℝ))
    {τ : ℝ} (hτ : |τ| * (8 * Real.sqrt 2 * Real.exp 1 * L) < 1) :
    Integrable (fun ω => Real.exp (τ * S ω / (m : ℝ))) μ ∧
      (∫ ω, Real.exp (τ * S ω / (m : ℝ)) ∂μ) ≤
        (1 + (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) /
          (1 - (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hscale : |τ / (m : ℝ)| * (8 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) =
      |τ| * (8 * Real.sqrt 2 * Real.exp 1 * L) := by
    rw [abs_div, abs_of_pos hmpos]
    field_simp [ne_of_gt hmpos]
  have h := integral_exp_le_of_even_moments hS h1 hmean
    (A := 8 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) (by positivity) hMom
    (t := τ / (m : ℝ)) (by rwa [hscale])
  simpa only [hscale, div_mul_eq_mul_div] using h

end PeriodicAttractiveLogGas.CanonicalExponentialMoment
