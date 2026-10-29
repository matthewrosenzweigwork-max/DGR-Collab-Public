import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# LIP051.41: Exact scalar Gaussian fourth moment

Task id `LIP051.41`, title "Exact scalar Gaussian fourth moment" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1).

## Provides

* `DGPS.Frontier.LIP051.lip051_41_exact_scalar_gaussian_fourth_moment`: for the standard real
  Gaussian law `gaussianReal 0 1`, `E Z = 0`, `E Z^2 = 1`, `E Z^3 = 0`, `E Z^4 = 3`, and
  `|Z|^k` is integrable for every `k ≤ 4`.
* `DGPS.Frontier.LIP051.lip051_41_exact_scalar_gaussian_fourth_moment_random_variable`: the same
  for any real random variable `Z` on any measure space whose law `P.map Z` is `gaussianReal 0 1`.
* `DGPS.Frontier.LIP051.lip051_41_exact_scalar_gaussian_fourth_moment_abs_integrable`: the
  integrability part alone, `Integrable (fun x => |x| ^ k) (gaussianReal 0 1)` for `k ≤ 4`.

## R5 notes

1. Mode index (DEFECTS.md FD-002). No mode index occurs in this statement: it concerns one scalar
   standard Gaussian. The zero-mode versus positive-mode convention of LIP051 is therefore not
   touched and nothing is chosen here.
2. "Standard real Gaussian variable": read as a real random variable `Z` with law
   `gaussianReal 0 1` (mean `0`, variance `1`). The primary statement is about the law itself
   (moments are integrals against `gaussianReal 0 1`); the random-variable form assumes only
   `P.map Z = gaussianReal 0 1`, with no probability-measure or measurability hypothesis (a
   non-a.e.-measurable `Z` has `P.map Z = 0`, so measurability follows from the law hypothesis).
3. "Every absolute moment of degree at most four is finite": read as integrability of
   `|x| ^ k` for each natural `k ≤ 4` (this includes `k = 0`).
4. Proof route differs mildly from the specification text: the specification integrates
   `x^k * phi` on `[-A, A]` and lets `A` tend to infinity. Here the integration by parts is done
   directly on the whole line with Mathlib's version assuming integrability of all three products,
   so no boundary term or dominated convergence is needed. The derivative of the density is
   `phi' x = -x phi x`; the recursion is `E Z^(k+2) = (k+1) E Z^k` for all `k`, with
   `E Z^0 = 1` and `E Z = 0` (Mathlib's `integral_id_gaussianReal`) as the starting values.
   Fourth moments are computed, not only shown to exist. Integrability of `x^k * phi` is
   obtained from `memLp_id_gaussianReal'` transported along `gaussianReal 0 1 = volume.withDensity phi`.
-/

open MeasureTheory ProbabilityTheory

namespace DGPS.Frontier.LIP051

private lemma integrable_abs_pow_LIP05141 (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) := by
  simpa using (memLp_id_gaussianReal' (μ := 0) (v := 1) (k : ENNReal) (by simp)).integrable_norm_pow'

private lemma integrable_pow_LIP05141 (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  refine (integrable_abs_pow_LIP05141 k).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  simp

private lemma integrable_pdf_pow_LIP05141 (k : ℕ) :
    Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * x ^ k) volume := by
  have h := integrable_pow_LIP05141 k
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero] at h
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
  simpa [gaussianPDF, smul_eq_mul, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)] using h

private lemma moment_eq_LIP05141 (k : ℕ) :
    ∫ x, x ^ k ∂gaussianReal 0 1 = ∫ x : ℝ, gaussianPDFReal 0 1 x * x ^ k := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  rfl

private lemma hasDerivAt_pdf_LIP05141 (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  have h : gaussianPDFReal 0 1 = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
    ext y; simp [gaussianPDFReal_def]
  rw [h]
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
    ring
  have := (h1.exp).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  convert this using 1
  ring

/-- Gaussian moment recursion `E Z^(k+2) = (k+1) E Z^k`, by integration by parts on the line. -/
private lemma moment_succ_succ_LIP05141 (k : ℕ) :
    ∫ x, x ^ (k + 2) ∂gaussianReal 0 1 = (k + 1) * ∫ x, x ^ k ∂gaussianReal 0 1 := by
  simp only [moment_eq_LIP05141]
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ (k + 1)) (u' := fun x : ℝ => ((k : ℝ) + 1) * x ^ k)
    (v := gaussianPDFReal 0 1) (v' := fun x => -(x * gaussianPDFReal 0 1 x))
    (fun x _ => by simpa using hasDerivAt_pow (k + 1) x) (fun x _ => hasDerivAt_pdf_LIP05141 x)
    ?_ ?_ ?_
  · have e : (fun x : ℝ => x ^ (k + 1) * -(x * gaussianPDFReal 0 1 x))
        = fun x => -(gaussianPDFReal 0 1 x * x ^ (k + 2)) := by
      ext x; ring
    have e' : (fun x : ℝ => ((k : ℝ) + 1) * x ^ k * gaussianPDFReal 0 1 x)
        = fun x => ((k : ℝ) + 1) * (gaussianPDFReal 0 1 x * x ^ k) := by
      ext x; ring
    rw [e, e', integral_neg, integral_const_mul] at key
    linarith
  · have e2 : ((fun x : ℝ => x ^ (k + 1)) * fun x => -(x * gaussianPDFReal 0 1 x))
        = fun x => -(gaussianPDFReal 0 1 x * x ^ (k + 2)) := by
      ext x; simp only [Pi.mul_apply]; ring
    rw [e2]
    exact (integrable_pdf_pow_LIP05141 (k + 2)).neg
  · have e2 : ((fun x : ℝ => ((k : ℝ) + 1) * x ^ k) * gaussianPDFReal 0 1)
        = fun x => ((k : ℝ) + 1) * (gaussianPDFReal 0 1 x * x ^ k) := by
      ext x; simp only [Pi.mul_apply]; ring
    rw [e2]
    exact (integrable_pdf_pow_LIP05141 k).const_mul _
  · have e2 : ((fun x : ℝ => x ^ (k + 1)) * gaussianPDFReal 0 1)
        = fun x => gaussianPDFReal 0 1 x * x ^ (k + 1) := by
      ext x; simp only [Pi.mul_apply]; ring
    rw [e2]
    exact integrable_pdf_pow_LIP05141 (k + 1)

/-- Integrability of absolute moments of degree at most four of the standard Gaussian law. -/
theorem lip051_41_exact_scalar_gaussian_fourth_moment_abs_integrable {k : ℕ} (_hk : k ≤ 4) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) :=
  integrable_abs_pow_LIP05141 k

/-- Exact scalar Gaussian fourth moment: for the standard real Gaussian law,
`E Z = E Z^3 = 0`, `E Z^2 = 1`, `E Z^4 = 3`, and all absolute moments of degree at most four
are finite. -/
theorem lip051_41_exact_scalar_gaussian_fourth_moment :
    (∫ x : ℝ, x ∂gaussianReal 0 1 = 0) ∧ (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1) ∧
      (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = 0) ∧ (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3) ∧
      ∀ k : ℕ, k ≤ 4 → Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) := by
  have h0 : ∫ x : ℝ, x ^ 0 ∂gaussianReal 0 1 = 1 := by simp
  have h1 : ∫ x : ℝ, x ^ 1 ∂gaussianReal 0 1 = 0 := by
    simp
  have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have := moment_succ_succ_LIP05141 0
    simp only [zero_add, Nat.cast_zero] at this
    rw [this, h0]; norm_num
  have h3 : ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = 0 := by
    have := moment_succ_succ_LIP05141 1
    rw [h1] at this
    simpa using this
  have h4 : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
    have := moment_succ_succ_LIP05141 2
    rw [h2] at this
    norm_num at this
    exact this
  exact ⟨by simp, h2, h3, h4,
    fun k hk => lip051_41_exact_scalar_gaussian_fourth_moment_abs_integrable hk⟩

/-- The same for a real random variable `Z` with law `gaussianReal 0 1`. -/
theorem lip051_41_exact_scalar_gaussian_fourth_moment_random_variable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : P.map Z = gaussianReal 0 1) :
    (∫ ω, Z ω ∂P = 0) ∧ (∫ ω, Z ω ^ 2 ∂P = 1) ∧ (∫ ω, Z ω ^ 3 ∂P = 0) ∧
      (∫ ω, Z ω ^ 4 ∂P = 3) ∧ ∀ k : ℕ, k ≤ 4 → Integrable (fun ω => |Z ω| ^ k) P := by
  have hmeas : AEMeasurable Z P := by
    by_contra h
    by_cases hP : P = 0
    · subst hP
      have := congrArg (fun m : Measure ℝ => m Set.univ) hZ
      simp at this
    · rw [Measure.map_of_not_aemeasurable_of_ne_zero h hP] at hZ
      have := congrArg (fun m : Measure ℝ => m {Classical.ofNonempty}) hZ
      simp only [Measure.dirac_apply_of_mem (Set.mem_singleton _)] at this
      have hns := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      rw [@measure_singleton _ _ _ hns] at this
      exact one_ne_zero this
  obtain ⟨a, b, c, d, e⟩ := lip051_41_exact_scalar_gaussian_fourth_moment
  have key : ∀ f : ℝ → ℝ, Measurable f → ∫ ω, f (Z ω) ∂P = ∫ x, f x ∂gaussianReal 0 1 := by
    intro f hf
    rw [← hZ, integral_map hmeas hf.aestronglyMeasurable]
  refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · simpa using (key (fun x => x) measurable_id).trans a
  · exact (key (fun x => x ^ 2) (by fun_prop)).trans b
  · exact (key (fun x => x ^ 3) (by fun_prop)).trans c
  · exact (key (fun x => x ^ 4) (by fun_prop)).trans d
  · have := e k hk
    rw [← hZ] at this
    exact (integrable_map_measure (by fun_prop) hmeas).1 this

end DGPS.Frontier.LIP051
