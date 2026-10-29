import DGPS.Lipschitz.KernelDiagonal
import DGPS.Equilibrium.GaussianRate
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite-rank compression estimates for LIP016

This module constructs the actual finite-rank kernel compressions, their coercive inverses,
finite traces, and Wick quadratic forms on one countable Gaussian product. Finite spectral
moment bounds give uniform integrability and the strictly positive limiting normalizer.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction Matrix

namespace DGPS.Lipschitz

open DGPS DGPS.Lipschitz.KernelApproximation

/-- The elementary operator identity underlying positivity of a contraction compression. -/
theorem compression_identity_LIP016 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T S : E →L[ℝ] E) :
    1 + S * T * S = 1 - S * S + S * (1 + T) * S := by
  noncomm_ring

/-- Coercivity survives compression by any symmetric contraction. -/
theorem compression_coercive_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T S : E →L[ℝ] E) {σ : ℝ}
    (hT : ∀ x, σ * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ⟪x, T x⟫_ℝ)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) (hcon : ∀ x, ‖S x‖ ≤ ‖x‖) (x : E) :
    min 1 σ * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ⟪x, (S * T * S) x⟫_ℝ := by
  have hi : ⟪x, (S * T * S) x⟫_ℝ = ⟪S x, T (S x)⟫_ℝ := by
    simpa only [mul_apply_eq_comp] using (hS.apply_clm x (T (S x))).symm
  rw [hi]
  have hc : ‖S x‖ ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hcon x)
  have ht := hT (S x)
  rcases le_total σ 1 with hσ | hσ
  · rw [min_eq_right hσ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr hc)]
  · rw [min_eq_left hσ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sq_nonneg ‖S x‖)]

/-- A strictly coercive quadratic form has an explicit exponent greater than one
with a uniform positive lower bound. -/
theorem compression_exponent_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (hA : ∀ x, a * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ⟪x, A x⟫_ℝ) :
    1 < 1 + a / 2 ∧ 0 < a / 2 ∧
      ∀ x, a / 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + (1 + a / 2) * ⟪x, A x⟫_ℝ := by
  refine ⟨by linarith, by linarith, fun x => ?_⟩
  have h := hA x
  have hn := sq_nonneg ‖x‖
  have hm := mul_nonneg (show 0 ≤ 1 + a / 2 by linarith)
    (sub_nonneg.mpr h)
  have hh := mul_nonneg (sq_nonneg a) hn
  nlinarith

/-- The coefficient array of the smoothed finite-rank kernel, extended by zero. -/
noncomputable def kernelCoefficient_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m i j : ℕ) : ℝ :=
  if i ≤ m ∧ j ≤ m then
    Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j else 0

/-- The ordinary finite trace; no trace of the limiting operator is defined. -/
noncomputable def kernelTrace_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), kernelCoefficient_LIP016 S D t m i i

theorem smoothK_continuous_LIP016 {d : ℕ} (S : Spec d) (D : KData d) (t : ℝ) (m : ℕ) :
    Continuous (fun p : Torus d × Torus d => smoothK S D t m p.1 p.2) := by
  unfold smoothK
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (((S.vc i).comp continuous_fst).mul ((S.vc j).comp continuous_snd))

/-- Orthogonality identifies each finite trace with the integral of the actual kernel diagonal. -/
theorem kernelTrace_integral_LIP016 {d : ℕ} (S : Spec d) (D : KData d) (t : ℝ) (m : ℕ) :
    kernelTrace_LIP016 S D t m = ∫ x, smoothK S D t m x x ∂S.mu := by
  have hint (i j : ℕ) : Integrable
      (fun x => Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j *
        (S.v i x * S.v j x)) S.mu :=
    (continuous_const.mul ((S.vc i).mul (S.vc j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold smoothK
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul, S.orth]
  unfold kernelTrace_LIP016
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
  simp [kernelCoefficient_LIP016, him]

/-- Uniform convergence of bounded smoothed kernels gives convergence of their finite traces. -/
theorem kernelTrace_tendsto_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℕ → ℝ) (m : ℕ → ℕ) {C : ℝ}
    (hbd : ∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C)
    (hU : TendstoUniformly
      (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
      (fun p => D.K p.1 p.2) atTop) :
    Tendsto (fun R => kernelTrace_LIP016 S D (t R) (m R))
      atTop (𝓝 (∫ x, D.K x x ∂S.mu)) := by
  simp_rw [kernelTrace_integral_LIP016]
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun R => ((smoothK_continuous_LIP016 S D (t R) (m R)).comp
      (continuous_id.prodMk continuous_id)).aestronglyMeasurable)
    (integrable_const _) (fun R => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => hU.tendsto_at (x, x))
  simpa only [Real.norm_eq_abs] using hbd R x x

/-- Each compression coefficient tends to its genuine kernel coefficient. -/
theorem kernelCoefficient_tendsto_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : Tendsto t atTop (𝓝 0))
    (hm : StrictMono m) (i j : ℕ) :
    Tendsto (fun R => kernelCoefficient_LIP016 S D (t R) (m R) i j)
      atTop (𝓝 (TK S D.K i j)) := by
  have hm' : Tendsto m atTop atTop := hm.tendsto_atTop
  have hi : ∀ᶠ R in atTop, i ≤ m R := hm'.eventually (eventually_ge_atTop i)
  have hj : ∀ᶠ R in atTop, j ≤ m R := hm'.eventually (eventually_ge_atTop j)
  have he : Tendsto (fun R => Real.exp (-(t R * (S.lam i + S.lam j))) * TK S D.K i j)
      atTop (𝓝 (TK S D.K i j)) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp
      ((ht.mul_const (S.lam i + S.lam j)).neg)
    simpa using he.mul_const (TK S D.K i j)
  apply he.congr'
  filter_upwards [hi, hj] with R hi hj
  simp [kernelCoefficient_LIP016, hi, hj]

/-- Contraction of the smoothing weights bounds every squared coefficient error. -/
theorem kernelCoefficient_error_le_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    {t : ℝ} (ht : 0 ≤ t) (m i j : ℕ) :
    (kernelCoefficient_LIP016 S D t m i j - TK S D.K i j) ^ 2 ≤
      TK S D.K i j ^ 2 := by
  unfold kernelCoefficient_LIP016
  split_ifs
  · have hl : 0 ≤ S.lam i + S.lam j := add_nonneg (S.lam_nonneg i) (S.lam_nonneg j)
    have he0 := (Real.exp_pos (-(t * (S.lam i + S.lam j)))).le
    have he1 : Real.exp (-(t * (S.lam i + S.lam j))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hl))
    have he2 : (Real.exp (-(t * (S.lam i + S.lam j))) - 1) ^ 2 ≤ 1 := by
      nlinarith
    calc _ = (Real.exp (-(t * (S.lam i + S.lam j))) - 1) ^ 2 * TK S D.K i j ^ 2 := by ring
      _ ≤ 1 * TK S D.K i j ^ 2 := mul_le_mul_of_nonneg_right he2 (sq_nonneg _)
      _ = _ := one_mul _
  · simp

/-- Squared Hilbert--Schmidt distance of the actual coefficient arrays tends to zero. -/
theorem kernelCoefficient_hilbertSchmidt_tendsto_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht0 : ∀ R, 0 ≤ t R)
    (ht : Tendsto t atTop (𝓝 0)) (hm : StrictMono m) :
    Tendsto (fun R => ∑' p : ℕ × ℕ,
      (kernelCoefficient_LIP016 S D (t R) (m R) p.1 p.2 - TK S D.K p.1 p.2) ^ 2)
      atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (hasSum_prod_sq S D).summable
    (f := fun R (p : ℕ × ℕ) =>
      (kernelCoefficient_LIP016 S D (t R) (m R) p.1 p.2 - TK S D.K p.1 p.2) ^ 2)
    (g := fun _ => (0 : ℝ))
    (fun p => by simpa using
      ((kernelCoefficient_tendsto_LIP016 S D t m ht hm p.1 p.2).sub_const
        (TK S D.K p.1 p.2)).pow 2)
    (Eventually.of_forall fun R p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact kernelCoefficient_error_le_LIP016 S D (ht0 R) (m R) p.1 p.2)
  simpa using h

/-- Coercivity makes a bounded operator invertible on a real Hilbert space. -/
theorem isUnit_of_coercive_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E)
    {σ : ℝ} (hσ : 0 < σ) (hA : ∀ x, σ * ‖x‖ ^ 2 ≤ ⟪x, A x⟫_ℝ) :
    IsUnit A := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp A
  have hB : IsCoercive B := by
    refine ⟨σ, hσ, fun x => ?_⟩
    change σ * ‖x‖ * ‖x‖ ≤ ⟪A x, x⟫_ℝ
    rw [real_inner_comm]
    simpa only [sq, mul_assoc] using hA x
  have hBA : InnerProductSpace.continuousLinearMapOfBilin B = A := by
    ext x
    apply ext_inner_right ℝ
    intro y
    exact InnerProductSpace.continuousLinearMapOfBilin_apply B x y
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  rw [← hBA]
  exact hB.continuousLinearEquivOfBilin.bijective

/-- Operator-norm convergence to a coercive operator implies operator-norm resolvent
convergence. The inverse is the genuine ring inverse, not supplied as a hypothesis. -/
theorem resolvent_tendsto_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E)
    {σ : ℝ} (hσ : 0 < σ)
    (hT : ∀ x, σ * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ⟪x, T x⟫_ℝ)
    (A : ℕ → E →L[ℝ] E) (hlim : Tendsto A atTop (𝓝 T)) :
    Tendsto (fun R => Ring.inverse (1 + A R)) atTop (𝓝 (Ring.inverse (1 + T))) := by
  have hu : IsUnit (1 + T) := isUnit_of_coercive_LIP016 (1 + T) hσ fun x => by
    simpa only [add_apply, one_apply_eq_self,
      inner_add_right, real_inner_self_eq_norm_sq] using hT x
  have hc := NormedRing.inverse_continuousAt hu.unit
  rw [hu.unit_spec] at hc
  exact hc.tendsto.comp (tendsto_const_nhds.add hlim)

/-- The same LIP011 approximants simultaneously have Hilbert--Schmidt coefficient
convergence and convergence of their finite traces to the diagonal integral. -/
theorem finite_rank_trace_and_hilbertSchmidt_approximation_LIP016 {d : ℕ}
    (S : Spec d) (A : Aux S) (D : KData d) :
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ), (∀ R, 0 < t R) ∧
      Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
      Tendsto (fun R => ∑' p : ℕ × ℕ,
        (kernelCoefficient_LIP016 S D (t R) (m R) p.1 p.2 - TK S D.K p.1 p.2) ^ 2)
        atTop (𝓝 0) ∧
      Tendsto (fun R => kernelTrace_LIP016 S D (t R) (m R))
        atTop (𝓝 (∫ x, D.K x x ∂S.mu)) := by
  obtain ⟨t, m, C, ht, -, hlim, hm, -, hbd, -, -, -, -, hU, -⟩ :=
    smoothed_approximation' S A D
  exact ⟨t, m, ht, hlim, hm,
    kernelCoefficient_hilbertSchmidt_tendsto_LIP016 S D t m (fun R => (ht R).le) hlim hm,
    kernelTrace_tendsto_LIP016 S D t m hbd hU⟩

/-- Positivity for the actual finite coefficient matrix follows from positivity of
the original coefficient quadratic form, by the damping-contraction argument. -/
theorem kernelCoefficient_coercive_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) {σ : ℝ}
    (hT : ∀ u : ℕ → ℝ,
      σ * (∑ i ∈ Finset.range (m + 1), u i ^ 2) ≤
        (∑ i ∈ Finset.range (m + 1), u i ^ 2) +
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          TK S D.K i j * u i * u j) (z : ℕ → ℝ) :
    min 1 σ * (∑ i ∈ Finset.range (m + 1), z i ^ 2) ≤
      (∑ i ∈ Finset.range (m + 1), z i ^ 2) +
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        kernelCoefficient_LIP016 S D t m i j * z i * z j := by
  let u : ℕ → ℝ := fun i => ee S t i * z i
  have hnorm : (∑ i ∈ Finset.range (m + 1), u i ^ 2) ≤
      ∑ i ∈ Finset.range (m + 1), z i ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have he0 := (ee_pos S t i).le
    have he1 := ee_le_one S ht i
    have he2 : ee S t i ^ 2 ≤ 1 := by nlinarith
    calc u i ^ 2 = ee S t i ^ 2 * z i ^ 2 := by dsimp [u]; ring
      _ ≤ 1 * z i ^ 2 := mul_le_mul_of_nonneg_right he2 (sq_nonneg _)
      _ = _ := one_mul _
  have hquad :
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        kernelCoefficient_LIP016 S D t m i j * z i * z j) =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        TK S D.K i j * u i * u j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have hj' : j ≤ m := by have := Finset.mem_range.mp hj; omega
    simp only [kernelCoefficient_LIP016, hi', hj', and_self, ite_true, u, ← ee_mul_ee]
    ring
  rw [hquad]
  have h := hT u
  rcases le_total σ 1 with hσ | hσ
  · rw [min_eq_right hσ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr hnorm)]
  · rw [min_eq_left hσ]
    have hu0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), u i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) hu0]

/-- The fourth moment is computed from the actual standard Gaussian measure. -/
theorem gaussian_fourth_moment_LIP016 :
    ∫ x : ℝ, x ^ 4 ∂ProbabilityTheory.gaussianReal 0 1 = 3 := by
  have hm := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 4
  have h1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := by
    funext t
    convert (((hasDerivAt_pow 2 t).div_const 2).exp).deriv using 1
    all_goals simp
    all_goals ring
  have h2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    funext t
    convert ((hasDerivAt_id t).fun_mul (((hasDerivAt_pow 2 t).div_const 2).exp)).deriv
      using 1
    all_goals simp
    all_goals ring
  have h3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    funext t
    convert (((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_pow 2 t)).fun_mul
      (((hasDerivAt_pow 2 t).div_const 2).exp)).deriv using 1
    all_goals simp
    all_goals ring
  have h4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    funext t
    have hpoly := ((hasDerivAt_const t (3 : ℝ)).fun_mul (hasDerivAt_id t)).fun_add
      (hasDerivAt_pow 3 t)
    have hexp := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert (hpoly.fun_mul hexp).deriv using 1
    all_goals simp
    all_goals ring
  rw [ProbabilityTheory.mgf_fun_id_gaussianReal] at hm
  simp only [NNReal.coe_one, zero_mul, zero_add, one_mul] at hm
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3, h4] at hm
  simpa using hm.symm

/-- The centered square has variance two under the actual standard Gaussian measure. -/
theorem gaussian_wick_square_LIP016 :
    ∫ x : ℝ, (x ^ 2 - 1) ^ 2 ∂ProbabilityTheory.gaussianReal 0 1 = 2 := by
  have h2 : ∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.gaussianReal 0 1 = 1 := by
    have hv := ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    rw [ProbabilityTheory.variance_eq_integral aemeasurable_id] at hv
    simpa [ProbabilityTheory.integral_id_gaussianReal] using hv
  have hi2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
    have h : MemLp id (2 : ℕ) (gaussianReal 0 1) := by
      simpa using memLp_id_gaussianReal (μ := 0) (v := 1) (2 : ℝ≥0)
    exact h.integrable_norm_pow'.congr (Eventually.of_forall fun x => by
      simpa only [id_eq, Real.norm_eq_abs] using (show Even (2 : ℕ) by norm_num).pow_abs x)
  have hi4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
    have h : MemLp id (4 : ℕ) (gaussianReal 0 1) := by
      simpa using memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)
    exact h.integrable_norm_pow'.congr (Eventually.of_forall fun x => by
      simpa only [id_eq, Real.norm_eq_abs] using (show Even (4 : ℕ) by norm_num).pow_abs x)
  have he : (fun x : ℝ => (x ^ 2 - 1) ^ 2) =
      fun x => x ^ 4 - 2 * x ^ 2 + 1 := by funext x; ring
  have hisub : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2) (gaussianReal 0 1) := by
    exact (hi4.sub (hi2.const_mul 2)).congr (Eventually.of_forall fun _ => rfl)
  rw [he, integral_add hisub (integrable_const _),
    integral_sub hi4 (hi2.const_mul 2), integral_const_mul, gaussian_fourth_moment_LIP016, h2]
  norm_num

/-- The exact one-dimensional Gaussian tilt integral, with its precise positivity threshold. -/
theorem gaussian_scalar_normalizer_LIP016 {a : ℝ} (ha : 0 < 1 + a) :
    Integrable (fun x : ℝ => Real.exp (-a * x ^ 2 / 2)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, Real.exp (-a * x ^ 2 / 2) ∂gaussianReal 0 1) =
        Real.sqrt ((1 + a)⁻¹) := by
  let b : ℝ := (1 + a) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hfun (x : ℝ) :
      gaussianPDFReal 0 1 x * Real.exp (-a * x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-b * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [b]
    ring
  have hi : Integrable
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-b * x ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  refine ⟨?_, ?_⟩
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (Eventually.of_forall fun x => (gaussianPDF_lt_top : gaussianPDF 0 1 x < ∞))]
    simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      smul_eq_mul, hfun] using hi
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul, hfun]
    rw [integral_const_mul, integral_gaussian, ← Real.sqrt_inv,
      ← Real.sqrt_mul (by positivity)]
    congr 1
    dsimp [b]
    field_simp

/-- The determinant remainder is controlled uniformly above the precise lower threshold. -/
theorem log_remainder_quadratic_LIP016 {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ 1 + x) :
    x - Real.log (1 + x) ≤ x ^ 2 / δ := by
  have hp : 0 < 1 + x := lt_of_lt_of_le hδ hx
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have he : x ^ 2 / (1 + x) = x - 1 + (1 + x)⁻¹ := by
    field_simp
    ring
  calc x - Real.log (1 + x) ≤ x ^ 2 / (1 + x) := by rw [he]; linarith
    _ ≤ x ^ 2 / δ := div_le_div_of_nonneg_left (sq_nonneg _) hδ hx

/-- The scalar logarithmic estimate sums with a constant independent of the finite dimension. -/
theorem log_remainder_sum_LIP016 {ι : Type*} [Fintype ι] (a : ι → ℝ)
    {p δ : ℝ} (hδ : 0 < δ) (hpos : ∀ i, δ ≤ 1 + p * a i) :
    (∑ i, (p * a i - Real.log (1 + p * a i))) ≤
      p ^ 2 / δ * ∑ i, a i ^ 2 := by
  calc _ ≤ ∑ i, (p * a i) ^ 2 / δ :=
      Finset.sum_le_sum fun i _ => log_remainder_quadratic_LIP016 hδ (hpos i)
    _ = _ := by
      simp_rw [mul_pow]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      ring

/-- Every polynomial moment used below is integrable under the actual Gaussian measure. -/
theorem gaussian_pow_integrable_LIP016 (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have h : MemLp id (n : ℝ≥0∞) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' _ (by simp)
  have hn := h.integrable_norm_pow'
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq, norm_pow] using hn

theorem gaussian_wick_memLp_LIP016 :
    MemLp (fun x : ℝ => x ^ 2 - 1) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := ((gaussian_pow_integrable_LIP016 4).sub
    ((gaussian_pow_integrable_LIP016 2).const_mul 2)).add (integrable_const (1 : ℝ))
  convert h using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The Wick isometry for an arbitrary finite diagonal quadratic under product standard Gaussians. -/
theorem gaussian_diagonal_wick_LIP016 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) :
    (∫ z : ι → ℝ, (∑ i, a i * (z i ^ 2 - 1)) ^ 2
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) = 2 * ∑ i, a i ^ 2 := by
  let γ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let w : ι → (ι → ℝ) → ℝ := fun i z => z i ^ 2 - 1
  have hev (i : ι) (f : ℝ → ℝ) (hf : Continuous f) :
      (∫ z, f (z i) ∂γ) = ∫ x, f x ∂gaussianReal 0 1 := by
    rw [← (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq,
      integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]
  have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    rw [variance_eq_integral aemeasurable_id] at hv
    simpa [integral_id_gaussianReal] using hv
  have hwmean (i : ι) : ∫ z, w i z ∂γ = 0 := by
    change (∫ z, (z i) ^ 2 - 1 ∂γ) = 0
    rw [hev i (fun x : ℝ => x ^ 2 - 1) (by fun_prop), integral_sub (gaussian_pow_integrable_LIP016 2)
      (integrable_const _), h2]
    simp
  have hwLp (i : ι) : MemLp (w i) 2 γ :=
    gaussian_wick_memLp_LIP016.comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)
  have hwprod (i j : ι) : Integrable (fun z => w i z * w j z) γ :=
    (hwLp i).integrable_mul (hwLp j)
  have hcov (i j : ι) : (∫ z, w i z * w j z ∂γ) = if i = j then 2 else 0 := by
    by_cases hij : i = j
    · subst j
      simp only
      change (∫ z, ((z i) ^ 2 - 1) * ((z i) ^ 2 - 1) ∂γ) = 2
      rw [hev i (fun x : ℝ => (x ^ 2 - 1) * (x ^ 2 - 1)) (by fun_prop)]
      simpa only [← sq] using gaussian_wick_square_LIP016
    · rw [ite_eq_right hij]
      have hind := (iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
        (X := fun _ => fun x : ℝ => x ^ 2 - 1) (fun _ => by fun_prop)).indepFun hij
      have heq : (∫ z, w i z * w j z ∂γ) =
          (∫ z, w i z ∂γ) * (∫ z, w j z ∂γ) := by
        simpa only [Pi.mul_apply, w, γ] using
          hind.integral_mul_eq_mul_integral (hwLp i).aestronglyMeasurable
            (hwLp j).aestronglyMeasurable
      rw [heq, hwmean i, hwmean j, zero_mul]
  have he : (fun z : ι → ℝ => (∑ i, a i * w i z) ^ 2) =
      fun z => ∑ i, ∑ j, (a i * a j) * (w i z * w j z) := by
    funext z
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  change (∫ z, (∑ i, a i * w i z) ^ 2 ∂γ) = _
  rw [he, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hwprod i j).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hwprod _ j).const_mul _),
    integral_const_mul, hcov]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Exact normalization for every finite diagonal Gaussian tilt. -/
theorem gaussian_diagonal_normalizer_LIP016 {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < 1 + a i) :
    Integrable (fun z : ι → ℝ => Real.exp (∑ i, -a i * z i ^ 2 / 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
      (∫ z : ι → ℝ, Real.exp (∑ i, -a i * z i ^ 2 / 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∏ i, Real.sqrt ((1 + a i)⁻¹) := by
  have he : (fun z : ι → ℝ => Real.exp (∑ i, -a i * z i ^ 2 / 2)) =
      fun z => ∏ i, Real.exp (-a i * z i ^ 2 / 2) := by
    funext z
    exact Real.exp_sum _ _
  rw [he]
  refine ⟨Integrable.fintype_prod (fun i => (gaussian_scalar_normalizer_LIP016 (ha i)).1), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Real.exp (-a i * x ^ 2 / 2))]
  exact Finset.prod_congr rfl fun i _ => (gaussian_scalar_normalizer_LIP016 (ha i)).2

/-- A genuine eigenbasis turns the operator quadratic form into its coordinate quadratic. -/
theorem eigenbasis_quadratic_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (a : ι → ℝ)
    (hdiag : ∀ i, T (b i) = a i • b i) (z : ι → ℝ) :
    ⟪∑ i, z i • b i, T (∑ i, z i • b i)⟫_ℝ = ∑ i, a i * z i ^ 2 := by
  simp [map_sum, map_smul, hdiag, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, b.inner_eq_ite, sq, mul_left_comm]

/-- Wick variance for a genuine finite-dimensional operator in any orthonormal eigenbasis. -/
theorem gaussian_wick_eigenbasis_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (a : ι → ℝ)
    (hdiag : ∀ i, T (b i) = a i • b i) :
    (∫ z : E, (⟪z, T z⟫_ℝ - ∑ i, a i) ^ 2 ∂stdGaussian E) =
      2 * ∑ i, a i ^ 2 := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map
      (show AEMeasurable (fun x : ι → ℝ => ∑ i, x i • b i)
        (Measure.pi fun _ : ι => gaussianReal 0 1) from
          (show Continuous (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).measurable.aemeasurable)
      (by fun_prop)]
  convert gaussian_diagonal_wick_LIP016 a using 1
  congr 1
  funext z
  rw [eigenbasis_quadratic_LIP016 b T a hdiag]
  congr 1
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]

/-- Exact Gaussian normalization in a genuine finite-dimensional operator eigenbasis. -/
theorem gaussian_normalizer_eigenbasis_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (a : ι → ℝ)
    (hdiag : ∀ i, T (b i) = a i • b i) (ha : ∀ i, 0 < 1 + a i) :
    (∫ z : E, Real.exp (-⟪z, T z⟫_ℝ / 2) ∂stdGaussian E) =
      ∏ i, Real.sqrt ((1 + a i)⁻¹) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map
      (show AEMeasurable (fun x : ι → ℝ => ∑ i, x i • b i)
        (Measure.pi fun _ : ι => gaussianReal 0 1) from
          (show Continuous (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).measurable.aemeasurable)
      (by fun_prop)]
  convert (gaussian_diagonal_normalizer_LIP016 a ha).2 using 1
  congr 1
  funext z
  rw [eigenbasis_quadratic_LIP016 b T a hdiag]
  congr 1
  calc
    -(∑ i, a i * z i ^ 2) / 2 = (∑ i, -(a i * z i ^ 2) / 2) := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ = _ := Finset.sum_congr rfl fun i _ => by ring

/-- The finite Gaussian exponential moment is bounded by the squared spectral
Hilbert--Schmidt norm, with a constant independent of dimension. -/
theorem gaussian_diagonal_exponential_bound_LIP016 {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {p δ : ℝ} (hδ : 0 < δ) (hpos : ∀ i, δ ≤ 1 + p * a i) :
    Integrable (fun z : ι → ℝ => Real.exp (∑ i, -p * a i * (z i ^ 2 - 1) / 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
      (∫ z : ι → ℝ, Real.exp (∑ i, -p * a i * (z i ^ 2 - 1) / 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
      Real.exp (p ^ 2 / (2 * δ) * ∑ i, a i ^ 2) := by
  have hp (i : ι) : 0 < 1 + p * a i := lt_of_lt_of_le hδ (hpos i)
  have hn := gaussian_diagonal_normalizer_LIP016 (fun i => p * a i) hp
  have he : (fun z : ι → ℝ => Real.exp (∑ i, -p * a i * (z i ^ 2 - 1) / 2)) =
      fun z => Real.exp (∑ i, p * a i / 2) *
        Real.exp (∑ i, -(p * a i) * z i ^ 2 / 2) := by
    funext z
    rw [← Real.exp_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he]
  refine ⟨hn.1.const_mul _, ?_⟩
  rw [integral_const_mul, hn.2]
  have hs (i : ι) : Real.sqrt ((1 + p * a i)⁻¹) =
      Real.exp (-Real.log (1 + p * a i) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (inv_pos.mpr (hp i)), Real.log_inv]
    congr 1
    ring
  simp_rw [hs]
  rw [← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsum := log_remainder_sum_LIP016 a hδ hpos
  calc (∑ i, p * a i / 2) + ∑ i, -Real.log (1 + p * a i) / 2 =
      (1 / 2 : ℝ) * ∑ i, (p * a i - Real.log (1 + p * a i)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (1 / 2 : ℝ) * (p ^ 2 / δ * ∑ i, a i ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

/-- Symmetry of the original kernel gives symmetry of its genuine coefficients. -/
theorem TK_symmetric_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (i j : ℕ) :
    TK S D.K i j = TK S D.K j i := by
  have hs : D.swap.K = D.K := by
    funext x y
    exact hK y x
  rw [← TK_swap S D i j, hs]

theorem kernelCoefficient_symmetric_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (t : ℝ) (m i j : ℕ) :
    kernelCoefficient_LIP016 S D t m i j = kernelCoefficient_LIP016 S D t m j i := by
  have hc := TK_symmetric_LIP016 S D hK i j
  by_cases h : i ≤ m ∧ j ≤ m
  · simp only [kernelCoefficient_LIP016, h, hc, add_comm]
  · have h' : ¬ (j ≤ m ∧ i ≤ m) := fun h' => h ⟨h'.2, h'.1⟩
    simp only [kernelCoefficient_LIP016, h, h', ite_false]

theorem kernelCoefficient_zero_left_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (h0 : ∀ x, S.v 0 x = 1) (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0)
    (t : ℝ) (m j : ℕ) : kernelCoefficient_LIP016 S D t m 0 j = 0 := by
  simp only [kernelCoefficient_LIP016, TK_zero_left S D h0 hc j, mul_zero, ite_self]

theorem kernelCoefficient_zero_right_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (h0 : ∀ x, S.v 0 x = 1) (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0)
    (hK : ∀ x y, D.K x y = D.K y x)
    (t : ℝ) (m i : ℕ) : kernelCoefficient_LIP016 S D t m i 0 = 0 := by
  rw [kernelCoefficient_symmetric_LIP016 S D hK]
  exact kernelCoefficient_zero_left_LIP016 S D h0 hc t m i

/-- The actual centered kernel operator kills the constant function. -/
theorem kernelOp_const_one_LIP016 {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    DGPS.kernelOp A μ (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)) = 0 := by
  apply Lp.ext
  filter_upwards [DGPS.kernelOp_ae A μ (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)),
    Lp.coeFn_zero ℝ 2 (μ : Measure (Torus d))] with x hx hz
  rw [hx, hz]
  change (∫ y, DGPS.centeredKernel A μ x y *
    (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)) y ∂(μ : Measure (Torus d))) = 0
  calc
    _ = (∫ y, DGPS.centeredKernel A μ x y ∂(μ : Measure (Torus d))) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const (E := ℝ) (p := 2)
        (μ := (μ : Measure (Torus d))) (1 : ℝ)] with y hy
      rw [hy]
      simp only [Function.const_apply, mul_one]
    _ = 0 := DGPS.integral_centeredKernel_right A μ x

/-- Coercivity on the actual mean-zero space extends to the full probability L² space.
The kernel centering removes the constant and cross terms, rather than adding a hypothesis. -/
theorem centered_coercivity_full_LIP016 {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 μ,
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian A μ g⟫_ℝ)
    (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    min 1 σ * ‖f‖ ^ 2 ≤ ‖f‖ ^ 2 + ⟪f, DGPS.kernelOp A μ f⟫_ℝ := by
  let e : Lp ℝ 2 (μ : Measure (Torus d)) := Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)
  let c : ℝ := ⟪e, f⟫_ℝ
  let g : Lp ℝ 2 (μ : Measure (Torus d)) := f - c • e
  have hee : ⟪e, e⟫_ℝ = 1 := by
    change ⟪Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ),
      Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)⟫_ℝ = 1
    rw [DGPS.inner_const_one]
    rw [integral_congr_ae (Lp.coeFn_const (E := ℝ) (p := 2)
      (μ := (μ : Measure (Torus d))) (1 : ℝ))]
    simp
  have heg : ⟪e, g⟫_ℝ = 0 := by
    dsimp only [g]
    rw [inner_sub_right, inner_smul_right, hee]
    dsimp only [c]
    ring
  have hge : ⟪g, e⟫_ℝ = 0 := by rw [real_inner_comm, heg]
  have hg0 : g ∈ DGPS.centeredL2 μ := by
    rw [DGPS.mem_centeredL2, ← DGPS.inner_const_one]
    exact heg
  have hf : f = g + c • e := by
    dsimp only [g]
    module
  have hTe : DGPS.kernelOp A μ e = 0 := kernelOp_const_one_LIP016 A μ
  have hTf : DGPS.kernelOp A μ f = DGPS.kernelOp A μ g := by
    rw [hf, map_add, map_smul, hTe, smul_zero, add_zero]
  have heTg : ⟪e, DGPS.kernelOp A μ g⟫_ℝ = 0 := by
    change ⟪Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ), DGPS.kernelOp A μ g⟫_ℝ = 0
    rw [DGPS.inner_const_one]
    exact DGPS.kernelOp_mem_centeredL2 A μ hg0
  have hnorm : ‖f‖ ^ 2 = c ^ 2 + ‖g‖ ^ 2 := by
    have hgg : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
    calc
      _ = ⟪f, f⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
      _ = _ := by
        rw [hf, inner_add_left, inner_add_right, inner_add_right]
        simp only [inner_smul_left, inner_smul_right, heg, hge, hee, hgg,
          conj_trivial, mul_zero, mul_one, add_zero, zero_add]
        ring
  have hquad : ⟪f, DGPS.kernelOp A μ f⟫_ℝ = ⟪g, DGPS.kernelOp A μ g⟫_ℝ := by
    rw [hTf, hf, inner_add_left, inner_smul_left, heTg]
    simp
  have hgH : σ * ‖g‖ ^ 2 ≤ ‖g‖ ^ 2 + ⟪g, DGPS.kernelOp A μ g⟫_ℝ := by
    have hh := hH ⟨g, hg0⟩
    change σ * ‖g‖ ^ 2 ≤ ⟪g, g + DGPS.kernelOp A μ g⟫_ℝ at hh
    simpa only [inner_add_right, real_inner_self_eq_norm_sq] using hh
  rw [hnorm, hquad]
  rcases le_total σ 1 with hσ | hσ
  · rw [min_eq_right hσ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sq_nonneg c)]
  · rw [min_eq_left hσ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sq_nonneg ‖g‖)]

/-- Applying the contraction identity to the genuine kernel operator requires only the
original mean-zero Hessian coercivity. -/
theorem kernelOp_compression_coercive_LIP016 {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 μ,
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian A μ g⟫_ℝ)
    (S : Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)))
    (hS : (S : Lp ℝ 2 (μ : Measure (Torus d)) →ₗ[ℝ]
      Lp ℝ 2 (μ : Measure (Torus d))).IsSymmetric)
    (hcon : ∀ f, ‖S f‖ ≤ ‖f‖) (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    min 1 σ * ‖f‖ ^ 2 ≤ ‖f‖ ^ 2 + ⟪f, (S * DGPS.kernelOp A μ * S) f⟫_ℝ := by
  simpa only [← min_assoc, min_self] using
    compression_coercive_LIP016 (DGPS.kernelOp A μ) S
      (centered_coercivity_full_LIP016 A μ hH) hS hcon f

/-- The actual probability measure already supplied by the normalized spectral data. -/
noncomputable def specProbability_LIP016 {d : ℕ} (S : Spec d) :
    ProbabilityMeasure (Torus d) :=
  ⟨S.mu, isProbabilityMeasure_iff_real.mpr S.real_univ⟩

/-- Diagonal subtraction represents a centered kernel by valid zero-diagonal interaction data. -/
noncomputable def kernelInteraction_LIP016 {d : ℕ} (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) : InteractionData d where
  V := fun _ => 0
  W := fun x y => D.K x y - (D.K x x + D.K y y) / 2
  V_continuous := continuous_const
  W_continuous := by
    have hd : Continuous (fun x => D.K x x) :=
      D.Kc.comp (continuous_id.prodMk continuous_id)
    exact D.Kc.sub (((hd.comp continuous_fst).add (hd.comp continuous_snd)).div_const 2)
  W_symm := fun x y => by rw [hK x y]; ring
  W_diag := fun x => by ring

theorem kernelInteraction_convolution_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (x : Torus d) :
    DGPS.interactionConvolution (kernelInteraction_LIP016 D hK) (specProbability_LIP016 S) x =
      -(D.K x x + ∫ y, D.K y y ∂S.mu) / 2 := by
  let _ : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hd : Continuous (fun y => D.K y y) :=
    D.Kc.comp (continuous_id.prodMk continuous_id)
  have hdi : Integrable (fun y => D.K y y) S.mu :=
    hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hki : Integrable (fun y => D.K x y) S.mu :=
    (D.Kc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hci : Integrable (fun y => (D.K x x + D.K y y) / 2) S.mu :=
    ((continuous_const.add hd).div_const 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcol : ∫ y, D.K x y ∂S.mu = 0 := by
    rw [integral_congr_ae (Eventually.of_forall fun y => hK x y)]
    exact hc x
  change (∫ y, D.K x y - (D.K x x + D.K y y) / 2 ∂S.mu) = _
  rw [integral_sub hki hci, integral_div, integral_add (integrable_const _) hdi, hcol]
  simp
  all_goals ring

theorem kernelInteraction_mean_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) :
    DGPS.meanInteraction (kernelInteraction_LIP016 D hK) (specProbability_LIP016 S) =
      -(∫ y, D.K y y ∂S.mu) := by
  let _ : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hdi : Integrable (fun y => D.K y y) S.mu :=
    (D.Kc.comp (continuous_id.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← DGPS.integral_interactionConvolution]
  simp_rw [kernelInteraction_convolution_LIP016 S D hK hc]
  change (∫ x, -(D.K x x + ∫ y, D.K y y ∂S.mu) / 2 ∂S.mu) = _
  rw [integral_div, integral_neg, integral_add hdi (integrable_const _)]
  simp

/-- The representation changes no kernel: double centering recovers the original function. -/
theorem kernelInteraction_centered_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (x y : Torus d) :
    DGPS.centeredKernel (kernelInteraction_LIP016 D hK) (specProbability_LIP016 S) x y =
      D.K x y := by
  unfold DGPS.centeredKernel
  rw [kernelInteraction_convolution_LIP016 S D hK hc x,
    kernelInteraction_convolution_LIP016 S D hK hc y,
    kernelInteraction_mean_LIP016 S D hK hc]
  change D.K x y - (D.K x x + D.K y y) / 2 -
    (-(D.K x x + ∫ z, D.K z z ∂S.mu) / 2) -
    (-(D.K y y + ∫ z, D.K z z ∂S.mu) / 2) +
    (-(∫ z, D.K z z ∂S.mu)) = D.K x y
  ring

/-- The spectral basis with its measure written in the concrete probability-space type. -/
noncomputable def spectralBasis_LIP016 {d : ℕ} (S : Spec d) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) := S.e

theorem spectralBasis_ae_LIP016 {d : ℕ} (S : Spec d) (i : ℕ) :
    (spectralBasis_LIP016 S i : Torus d → ℝ) =ᵐ[S.mu] S.v i := by
  change (S.e i : Torus d → ℝ) =ᵐ[S.mu] S.v i
  exact Filter.EventuallyEq.symm (S.ae_mu (S.ve i))

/-- The genuine integral operator has exactly the previously defined kernel coefficients. -/
theorem kernelOp_basis_coefficient_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (i j : ℕ) :
    ⟪spectralBasis_LIP016 S i, DGPS.kernelOp (kernelInteraction_LIP016 D hK) (specProbability_LIP016 S)
      (spectralBasis_LIP016 S j)⟫_ℝ = TK S D.K i j := by
  rw [DGPS.inner_kernelOp]
  simp_rw [kernelInteraction_centered_LIP016 S D hK hc]
  unfold TK
  apply integral_congr_ae
  filter_upwards [
    (Measure.quasiMeasurePreserving_fst (μ := S.mu) (ν := S.mu)).ae_eq_comp (Filter.EventuallyEq.symm (spectralBasis_ae_LIP016 S i)),
    (Measure.quasiMeasurePreserving_snd (μ := S.mu) (ν := S.mu)).ae_eq_comp (Filter.EventuallyEq.symm (spectralBasis_ae_LIP016 S j))]
    with p hi hj
  change S.v i p.1 = spectralBasis_LIP016 S i p.1 at hi
  change S.v j p.2 = spectralBasis_LIP016 S j p.2 at hj
  rw [← hi, ← hj]

/-- Exact norm of a finite linear combination of the genuine spectral basis. -/
theorem spectral_sum_norm_sq_LIP016 {d : ℕ} (S : Spec d) (n : ℕ) (z : ℕ → ℝ) :
    ‖∑ i ∈ Finset.range n, z i • spectralBasis_LIP016 S i‖ ^ 2 = ∑ i ∈ Finset.range n, z i ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq, conj_trivial, ← sq] using
    (spectralBasis_LIP016 S).orthonormal.inner_sum z z (Finset.range n)

/-- The original coefficient quadratic form is the actual kernel-operator quadratic form. -/
theorem kernelOp_finite_form_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (n : ℕ) (z : ℕ → ℝ) :
    ⟪∑ i ∈ Finset.range n, z i • spectralBasis_LIP016 S i,
      DGPS.kernelOp (kernelInteraction_LIP016 D hK) (specProbability_LIP016 S)
        (∑ i ∈ Finset.range n, z i • spectralBasis_LIP016 S i)⟫_ℝ =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, TK S D.K i j * z i * z j := by
  simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [kernelOp_basis_coefficient_LIP016 S D hK hc i j]
  simp only [conj_trivial]
  ring

/-- The actual source Hessian coercivity discharges the finite-coordinate premise:
no additional positivity assumption on coefficient arrays is used. -/
theorem kernelCoefficient_coercive_from_hessian_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (z : ℕ → ℝ) :
    min 1 σ * (∑ i ∈ Finset.range (m + 1), z i ^ 2) ≤
      (∑ i ∈ Finset.range (m + 1), z i ^ 2) +
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        kernelCoefficient_LIP016 S D t m i j * z i * z j := by
  have hT (u : ℕ → ℝ) :
      min 1 σ * (∑ i ∈ Finset.range (m + 1), u i ^ 2) ≤
        (∑ i ∈ Finset.range (m + 1), u i ^ 2) +
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          TK S D.K i j * u i * u j := by
    have h := centered_coercivity_full_LIP016 (kernelInteraction_LIP016 D hK)
      (specProbability_LIP016 S) hH (∑ i ∈ Finset.range (m + 1), u i • spectralBasis_LIP016 S i)
    rw [spectral_sum_norm_sq_LIP016 S (m + 1) u,
      kernelOp_finite_form_LIP016 S D hK hc (m + 1) u] at h
    exact h
  simpa only [← min_assoc, min_self] using
    kernelCoefficient_coercive_LIP016 S D ht m hT z

/-- The genuine integral operator associated with the original centered kernel. -/
noncomputable def kernelOperator_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) :
    Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →L[ℝ]
      Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) :=
  DGPS.kernelOp (kernelInteraction_LIP016 D hK) (specProbability_LIP016 S)

/-- The actual finite diagonal spectral contraction. -/
noncomputable def spectralDamping_LIP016 {d : ℕ} (S : Spec d) (t : ℝ) (m : ℕ) :
    Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →L[ℝ]
      Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) :=
  ∑ i ∈ Finset.range (m + 1),
    ee S t i • (innerSL ℝ (spectralBasis_LIP016 S i)).smulRight (spectralBasis_LIP016 S i)

theorem spectralDamping_apply_LIP016 {d : ℕ} (S : Spec d) (t : ℝ) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    spectralDamping_LIP016 S t m f =
      ∑ i ∈ Finset.range (m + 1),
        (ee S t i * ⟪spectralBasis_LIP016 S i, f⟫_ℝ) • spectralBasis_LIP016 S i := by
  simp [spectralDamping_LIP016, smul_smul]

theorem spectralDamping_basis_LIP016 {d : ℕ} (S : Spec d) (t : ℝ) (m j : ℕ) :
    spectralDamping_LIP016 S t m (spectralBasis_LIP016 S j) =
      if j ≤ m then ee S t j • spectralBasis_LIP016 S j else 0 := by
  rw [spectralDamping_apply_LIP016]
  simp [orthonormal_iff_ite.mp (spectralBasis_LIP016 S).orthonormal,
    Finset.mem_range]

theorem spectralDamping_symmetric_LIP016 {d : ℕ} (S : Spec d) (t : ℝ) (m : ℕ) :
    (spectralDamping_LIP016 S t m :
      Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →ₗ[ℝ]
        Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))).IsSymmetric := by
  intro f g
  change ⟪spectralDamping_LIP016 S t m f, g⟫_ℝ =
    ⟪f, spectralDamping_LIP016 S t m g⟫_ℝ
  simp only [spectralDamping_apply_LIP016, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm f (spectralBasis_LIP016 S i)]
  simp only [conj_trivial]
  ring

theorem spectralDamping_contraction_LIP016 {d : ℕ} (S : Spec d)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    ‖spectralDamping_LIP016 S t m f‖ ≤ ‖f‖ := by
  have hnorm : ‖spectralDamping_LIP016 S t m f‖ ^ 2 =
      ∑ i ∈ Finset.range (m + 1), (ee S t i * ⟪spectralBasis_LIP016 S i, f⟫_ℝ) ^ 2 := by
    rw [spectralDamping_apply_LIP016]
    exact spectral_sum_norm_sq_LIP016 S (m + 1) _
  have hle : ‖spectralDamping_LIP016 S t m f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [hnorm]
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), ⟪spectralBasis_LIP016 S i, f⟫_ℝ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have he0 := (ee_pos S t i).le
        have he1 := ee_le_one S ht i
        have he2 : ee S t i ^ 2 ≤ 1 := by nlinarith
        rw [mul_pow]
        calc
          _ ≤ 1 * ⟪spectralBasis_LIP016 S i, f⟫_ℝ ^ 2 :=
            mul_le_mul_of_nonneg_right he2 (sq_nonneg _)
          _ = _ := one_mul _
      _ ≤ _ := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          (spectralBasis_LIP016 S).orthonormal.sum_inner_products_le
            (x := f) (s := Finset.range (m + 1))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hle

/-- The coefficient operator is the actual contraction compression, by definition. -/
noncomputable def kernelCompression_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (t : ℝ) (m : ℕ) :
    Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →L[ℝ]
      Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) :=
  spectralDamping_LIP016 S t m * kernelOperator_LIP016 S D hK * spectralDamping_LIP016 S t m

theorem kernelCompression_coercive_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    min 1 σ * ‖f‖ ^ 2 ≤ ‖f‖ ^ 2 + ⟪f, kernelCompression_LIP016 S D hK t m f⟫_ℝ := by
  exact kernelOp_compression_coercive_LIP016 (kernelInteraction_LIP016 D hK)
    (specProbability_LIP016 S) hH (spectralDamping_LIP016 S t m)
      (spectralDamping_symmetric_LIP016 S t m) (spectralDamping_contraction_LIP016 S ht m) f

/-- The concrete compressed operator has the prescribed smoothed finite coefficients. -/
theorem kernelCompression_basis_coefficient_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m i j : ℕ) :
    ⟪spectralBasis_LIP016 S i,
      kernelCompression_LIP016 S D hK t m (spectralBasis_LIP016 S j)⟫_ℝ =
      kernelCoefficient_LIP016 S D t m i j := by
  have hs := spectralDamping_symmetric_LIP016 S t m
  have he :
      ⟪spectralBasis_LIP016 S i,
        kernelCompression_LIP016 S D hK t m (spectralBasis_LIP016 S j)⟫_ℝ =
      ⟪spectralDamping_LIP016 S t m (spectralBasis_LIP016 S i),
        kernelOperator_LIP016 S D hK
          (spectralDamping_LIP016 S t m (spectralBasis_LIP016 S j))⟫_ℝ := by
    simpa only [kernelCompression_LIP016, mul_apply_eq_comp] using
      (hs.apply_clm (spectralBasis_LIP016 S i)
        (kernelOperator_LIP016 S D hK
          (spectralDamping_LIP016 S t m (spectralBasis_LIP016 S j)))).symm
  rw [he, spectralDamping_basis_LIP016, spectralDamping_basis_LIP016]
  by_cases hi : i ≤ m
  · by_cases hj : j ≤ m
    · simp only [hi, hj, and_self, ite_true, kernelOperator_LIP016, map_smul,
        inner_smul_left, inner_smul_right, conj_trivial,
        kernelOp_basis_coefficient_LIP016 S D hK hc, kernelCoefficient_LIP016]
      rw [← ee_mul_ee]
      ring
    · simp [hi, hj, kernelCoefficient_LIP016]
  · simp [hi, kernelCoefficient_LIP016]

/-- A continuous representative of each spectral basis vector. -/
noncomputable def spectralBCF_LIP016 {d : ℕ} (S : Spec d) (i : ℕ) : Torus d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨S.v i, S.vc i⟩

theorem spectralBCF_toLp_LIP016 {d : ℕ} (S : Spec d) (i : ℕ) :
    BoundedContinuousFunction.toLp 2 (specProbability_LIP016 S : Measure (Torus d)) ℝ
      (spectralBCF_LIP016 S i) = spectralBasis_LIP016 S i := by
  apply Lp.ext
  filter_upwards [
    BoundedContinuousFunction.coeFn_toLp 2 (specProbability_LIP016 S : Measure (Torus d)) ℝ
      (spectralBCF_LIP016 S i), spectralBasis_ae_LIP016 S i] with x hx hy
  rw [hx, hy]
  rfl

theorem spectralBasis_inner_integral_LIP016 {d : ℕ} (S : Spec d) (i : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    ⟪spectralBasis_LIP016 S i, f⟫_ℝ =
      ∫ y, S.v i y * f y ∂(specProbability_LIP016 S : Measure (Torus d)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectralBasis_ae_LIP016 S i] with y hy
  rw [hy]
  simp [mul_comm]

/-- The concrete compression written as a finite coefficient operator. -/
theorem kernelCompression_apply_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    kernelCompression_LIP016 S D hK t m f =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (kernelCoefficient_LIP016 S D t m i j *
          ⟪spectralBasis_LIP016 S j, f⟫_ℝ) • spectralBasis_LIP016 S i := by
  unfold kernelCompression_LIP016
  simp only [mul_apply_eq_comp, spectralDamping_apply_LIP016, kernelOperator_LIP016,
    map_sum, map_smul,
    kernelOp_basis_coefficient_LIP016 S D hK hc]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
  have hj' : j ≤ m := by have := Finset.mem_range.mp hj; omega
  simp only [kernelCoefficient_LIP016, hi', hj', and_self, ite_true, ← ee_mul_ee]
  congr 1
  ring

/-- The same finite coefficient operator as a bounded continuous function. -/
noncomputable def finiteKernelBCF_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) : Torus d →ᵇ ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    (kernelCoefficient_LIP016 S D t m i j *
      ⟪spectralBasis_LIP016 S j, f⟫_ℝ) • spectralBCF_LIP016 S i

theorem finiteKernelBCF_toLp_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    BoundedContinuousFunction.toLp 2 (specProbability_LIP016 S : Measure (Torus d)) ℝ
      (finiteKernelBCF_LIP016 S D t m f) = kernelCompression_LIP016 S D hK t m f := by
  rw [kernelCompression_apply_LIP016 S D hK hc]
  unfold finiteKernelBCF_LIP016
  simp only [map_sum, map_smul, spectralBCF_toLp_LIP016]

/-- The actual compressed operator integrates the actual LIP011 finite kernel. -/
theorem finiteKernelBCF_integral_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) (x : Torus d) :
    finiteKernelBCF_LIP016 S D t m f x =
      ∫ y, smoothK S D t m x y * f y
        ∂(specProbability_LIP016 S : Measure (Torus d)) := by
  have hvi (j : ℕ) : Integrable (fun y => S.v j y * f y)
      (specProbability_LIP016 S : Measure (Torus d)) := by
    have hv : MemLp (S.v j) 2 (specProbability_LIP016 S : Measure (Torus d)) :=
      S.memLp_mu (S.vc j)
    exact hv.integrable_mul (Lp.memLp f)
  have he :
      (fun y => smoothK S D t m x y * f y) =
      fun y => ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (kernelCoefficient_LIP016 S D t m i j * S.v i x) * (S.v j y * f y) := by
    funext y
    unfold smoothK
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have hj' : j ≤ m := by have := Finset.mem_range.mp hj; omega
    simp only [kernelCoefficient_LIP016, hi', hj', and_self, ite_true]
    ring
  rw [he, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hvi j).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hvi j).const_mul _), integral_const_mul,
    ← spectralBasis_inner_integral_LIP016]
  unfold finiteKernelBCF_LIP016
  simp [spectralBCF_LIP016, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Supremum kernel control gives an operator-norm bound for the actual compression. -/
theorem kernelCompression_opNorm_sub_le_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbd : ∀ x y, |smoothK S D t m x y - D.K x y| ≤ ε) :
    ‖kernelCompression_LIP016 S D hK t m - kernelOperator_LIP016 S D hK‖ ≤ ε := by
  let μ := specProbability_LIP016 S
  let A := kernelInteraction_LIP016 D hK
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro f
  have he : (kernelCompression_LIP016 S D hK t m - kernelOperator_LIP016 S D hK) f =
      BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ
        (finiteKernelBCF_LIP016 S D t m f - DGPS.kernelBCF A μ f) := by
    rw [map_sub, finiteKernelBCF_toLp_LIP016 S D hK hc]
    rfl
  rw [he]
  refine (DGPS.norm_toLp_le_norm μ _).trans ?_
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε (norm_nonneg f))).mpr
  intro x
  let g : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => smoothK S D t m x y - D.K x y,
      ((smoothK_continuous_LIP016 S D t m).comp (continuous_const.prodMk continuous_id)).sub
        (D.Kc.comp (continuous_const.prodMk continuous_id))⟩
  have hg : ‖g‖ ≤ ε := (BoundedContinuousFunction.norm_le hε).mpr fun y => by
    change |smoothK S D t m x y - D.K x y| ≤ ε
    exact hbd x y
  have hKR : Integrable (fun y => smoothK S D t m x y * f y) (μ : Measure (Torus d)) := by
    have hv : MemLp (fun y => smoothK S D t m x y) 2 (μ : Measure (Torus d)) :=
      (((smoothK_continuous_LIP016 S D t m).comp
        (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
    exact hv.integrable_mul (Lp.memLp f)
  have hKf : Integrable (fun y => D.K x y * f y) (μ : Measure (Torus d)) := by
    have hv : MemLp (fun y => D.K x y) 2 (μ : Measure (Torus d)) :=
      (D.Kc.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact hv.integrable_mul (Lp.memLp f)
  have hx :
      (finiteKernelBCF_LIP016 S D t m f - DGPS.kernelBCF A μ f) x =
      ∫ y, g y * f y ∂(μ : Measure (Torus d)) := by
    rw [BoundedContinuousFunction.sub_apply, finiteKernelBCF_integral_LIP016,
      DGPS.kernelBCF_apply]
    unfold DGPS.kernelTransform
    dsimp only [A, μ]
    simp_rw [kernelInteraction_centered_LIP016 S D hK hc]
    rw [← integral_sub hKR hKf]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by dsimp [g]; ring
  rw [hx, Real.norm_eq_abs]
  exact (DGPS.abs_integral_mul_le μ g f).trans
    (mul_le_mul_of_nonneg_right hg (norm_nonneg f))

/-- The actual finite coefficient operators converge in operator norm by the actual
uniform kernel approximation, using the concrete integral-operator estimate. -/
theorem kernelCompression_tendsto_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℕ → ℝ) (m : ℕ → ℕ)
    (hU : TendstoUniformly
      (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
      (fun p => D.K p.1 p.2) atTop) :
    Tendsto (fun R => kernelCompression_LIP016 S D hK (t R) (m R))
      atTop (𝓝 (kernelOperator_LIP016 S D hK)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hU) (ε / 2) (by linarith)] with R hR
  rw [dist_eq_norm]
  refine (kernelCompression_opNorm_sub_le_LIP016 S D hK hc (t R) (m R)
    (ε := ε / 2) (by linarith) (fun x y => ?_)).trans_lt (by linarith)
  simpa only [Real.dist_eq, abs_sub_comm] using (hR (x, y)).le

/-- Actual covariance inverses exist at every smoothing index. -/
theorem kernelCompression_isUnit_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ) {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    IsUnit (1 + kernelCompression_LIP016 S D hK t m) := by
  apply isUnit_of_coercive_LIP016 _ (show (0 : ℝ) < min 1 σ from lt_min zero_lt_one hσ)
  intro f
  simpa only [add_apply, one_apply_eq_self, inner_add_right, real_inner_self_eq_norm_sq] using
    kernelCompression_coercive_LIP016 S D hK hH ht m f

/-- The genuine covariance inverses converge in operator norm, with no supplied
operator-convergence or covariance premise. -/
theorem kernelCovariance_tendsto_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ) (t : ℕ → ℝ) (m : ℕ → ℕ)
    (hU : TendstoUniformly
      (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
      (fun p => D.K p.1 p.2) atTop) :
    Tendsto (fun R => Ring.inverse (1 + kernelCompression_LIP016 S D hK (t R) (m R)))
      atTop (𝓝 (Ring.inverse (1 + kernelOperator_LIP016 S D hK))) := by
  apply resolvent_tendsto_LIP016 _ (show (0 : ℝ) < min 1 σ from lt_min zero_lt_one hσ)
    (fun f => centered_coercivity_full_LIP016 (kernelInteraction_LIP016 D hK)
      (specProbability_LIP016 S) hH f)
  exact kernelCompression_tendsto_LIP016 S D hK hc t m hU

/-- The squared spectral Hilbert--Schmidt norm equals the squared coefficient norm
for every finite real symmetric matrix, including difference matrices. -/
theorem matrix_eigen_sq_sum_LIP016 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) :
    (∑ i, hB.eigenvalues i ^ 2) = ∑ i, ∑ j, B i j ^ 2 := by
  let D : Matrix ι ι ℝ := Matrix.diagonal hB.eigenvalues
  let U := hB.eigenvectorUnitary
  have hs : B = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U D := by
    exact hB.spectral_theorem
  have hsq : B * B = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U (D * D) := by
    rw [map_mul, ← hs]
  have htr : Matrix.trace (B * B) = ∑ i, hB.eigenvalues i ^ 2 := by
    rw [hsq, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsym (i j : ι) : B j i = B i j := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hB
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  rw [← htr]
  change (∑ i, ∑ j, B i j * B j i) = _
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym i j]
  ring

noncomputable def matrixQuadratic_LIP016 {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, B i j * z i * z j

noncomputable def matrixWick_LIP016 {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ :=
  matrixQuadratic_LIP016 B z - Matrix.trace B

theorem matrixWick_sub_LIP016 {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (z : ι → ℝ) :
    matrixWick_LIP016 (B - C) z = matrixWick_LIP016 B z - matrixWick_LIP016 C z := by
  simp only [matrixWick_LIP016, matrixQuadratic_LIP016, Matrix.sub_apply,
    sub_mul, Finset.sum_sub_distrib, Matrix.trace_sub]
  ring

theorem gaussian_matrix_wick_memLp_LIP016 {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) :
    MemLp (matrixWick_LIP016 B) 2 (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hv (i : ι) : MemLp (fun z : ι → ℝ => z i) 4
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)
  let _ : ENNReal.HolderTriple 4 4 2 := ⟨by
    have h4 : (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    rw [h4, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]⟩
  have hp (i j : ι) : MemLp (fun z : ι → ℝ => B i j * z i * z j) 2
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    have h : MemLp (fun z : ι → ℝ => B i j * (z i * z j)) 2
        (Measure.pi fun _ : ι => gaussianReal 0 1) :=
      ((hv i).mul (hv j)).const_mul (B i j)
    exact MemLp.ae_eq (Eventually.of_forall fun z => by dsimp; ring) h
  have hq : MemLp (matrixQuadratic_LIP016 B) 2
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => hp i j
  exact MemLp.ae_eq (Eventually.of_forall fun _ => rfl) (hq.sub (memLp_const (Matrix.trace B)))

theorem matrixQuadratic_inner_LIP016 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (z : ι → ℝ) :
    ⟪WithLp.toLp 2 z,
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B) (WithLp.toLp 2 z)⟫_ℝ =
      matrixQuadratic_LIP016 B z := by
  change ⟪WithLp.toLp 2 z, WithLp.toLp 2 (B *ᵥ z)⟫_ℝ = _
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change (∑ i, (∑ j, B i j * z j) * z i) = matrixQuadratic_LIP016 B z
  simp only [matrixQuadratic_LIP016, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The Gaussian Wick identity on fixed canonical finite coordinates, for an arbitrary
symmetric matrix. The matrix may in particular be a difference of two compressions. -/
theorem gaussian_matrix_wick_LIP016 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) :
    (∫ z : ι → ℝ, matrixWick_LIP016 B z ^ 2
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) = 2 * ∑ i, ∑ j, B i j ^ 2 := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)
  have heig (i : ι) : T (hB.eigenvectorBasis i) =
      hB.eigenvalues i • hB.eigenvectorBasis i := by
    ext j
    change (B *ᵥ (hB.eigenvectorBasis i : ι → ℝ)) j =
      hB.eigenvalues i * hB.eigenvectorBasis i j
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (hB.mulVec_eigenvectorBasis i) j
  have h := gaussian_wick_eigenbasis_LIP016 hB.eigenvectorBasis T hB.eigenvalues heig
  have htr : Matrix.trace B = ∑ i, hB.eigenvalues i := hB.trace_eq_sum_eigenvalues
  rw [← htr] at h
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)] at h
  simp_rw [T, matrixQuadratic_inner_LIP016] at h
  rw [matrix_eigen_sq_sum_LIP016 B hB] at h
  exact h

/-- One probability space for every finite Gaussian block. -/
noncomputable def gaussianCountable_LIP016 : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance gaussianCountable_probability_LIP016 :
    IsProbabilityMeasure gaussianCountable_LIP016 := by
  unfold gaussianCountable_LIP016
  infer_instance

theorem sum_finset_pair_LIP016 (F : ℕ → ℕ → ℝ) (s : Finset ℕ) :
    (∑ i : s, ∑ j : s, F i j) = ∑ i ∈ s, ∑ j ∈ s, F i j := by
  calc
    _ = ∑ i : s, ∑ j ∈ s, F i j := Finset.sum_congr rfl fun i _ =>
      Finset.sum_coe_sort s (F i)
    _ = _ := Finset.sum_coe_sort s (fun i => ∑ j ∈ s, F i j)

/-- The polynomial uses fixed coordinates of the countable product. -/
noncomputable def finiteWickOn_LIP016 (B : ℕ → ℕ → ℝ) (s : Finset ℕ)
    (z : ℕ → ℝ) : ℝ :=
  matrixWick_LIP016 (Matrix.of fun i j : s => B i j) (s.restrict z)

theorem finiteWickOn_eq_LIP016 (B : ℕ → ℕ → ℝ) (s : Finset ℕ) (z : ℕ → ℝ) :
    finiteWickOn_LIP016 B s z =
      (∑ i ∈ s, ∑ j ∈ s, B i j * z i * z j) - ∑ i ∈ s, B i i := by
  simp only [finiteWickOn_LIP016, matrixWick_LIP016, matrixQuadratic_LIP016,
    Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Finset.restrict]
  rw [sum_finset_pair_LIP016 (fun i j => B i j * z i * z j) s,
    Finset.sum_coe_sort s (fun i => B i i)]

theorem finiteWickOn_memLp_LIP016 (B : ℕ → ℕ → ℝ) (s : Finset ℕ) :
    MemLp (finiteWickOn_LIP016 B s) 2 gaussianCountable_LIP016 := by
  have hp : MeasurePreserving s.restrict gaussianCountable_LIP016
      (Measure.pi fun _ : s => gaussianReal 0 1) :=
    ⟨Finset.measurable_restrict s, Measure.infinitePi_map_restrict _⟩
  exact (gaussian_matrix_wick_memLp_LIP016 (Matrix.of fun i j : s => B i j)).comp_measurePreserving hp

theorem finiteWickOn_isometry_LIP016 (B : ℕ → ℕ → ℝ) (s : Finset ℕ)
    (hB : ∀ i j, B i j = B j i) :
    (∫ z, finiteWickOn_LIP016 B s z ^ 2 ∂gaussianCountable_LIP016) =
      2 * ∑ i ∈ s, ∑ j ∈ s, B i j ^ 2 := by
  have hsym : (Matrix.of fun i j : s => B i j).IsHermitian := by
    ext i j
    exact hB j i
  have h := gaussian_matrix_wick_LIP016 (Matrix.of fun i j : s => B i j) hsym
  rw [← Measure.infinitePi_map_restrict (fun _ : ℕ => gaussianReal 0 1) (I := s),
    integral_map (Finset.measurable_restrict s).aemeasurable
      (show AEStronglyMeasurable
        (fun z : s → ℝ => matrixWick_LIP016 (Matrix.of fun i j : s => B i j) z ^ 2)
        ((gaussianCountable_LIP016).map s.restrict) from
          (show Measurable (fun z : s → ℝ =>
              matrixWick_LIP016 (Matrix.of fun i j : s => B i j) z ^ 2) by
            unfold matrixWick_LIP016 matrixQuadratic_LIP016
            fun_prop).aestronglyMeasurable)] at h
  change (∫ z, finiteWickOn_LIP016 B s z ^ 2 ∂gaussianCountable_LIP016) =
    2 * (∑ i : s, ∑ j : s, B i j ^ 2) at h
  rw [sum_finset_pair_LIP016 (fun i j => B i j ^ 2) s] at h
  exact h

theorem finiteWickOn_sub_LIP016 (B C : ℕ → ℕ → ℝ) (s : Finset ℕ) (z : ℕ → ℝ) :
    finiteWickOn_LIP016 (fun i j => B i j - C i j) s z =
      finiteWickOn_LIP016 B s z - finiteWickOn_LIP016 C s z :=
  matrixWick_sub_LIP016 _ _ _

theorem finiteWickOn_padding_LIP016 (B : ℕ → ℕ → ℝ) (s r : Finset ℕ)
    (hsr : s ⊆ r) (hleft : ∀ i, i ∉ s → ∀ j, B i j = 0)
    (hright : ∀ j, j ∉ s → ∀ i, B i j = 0) (z : ℕ → ℝ) :
    finiteWickOn_LIP016 B r z = finiteWickOn_LIP016 B s z := by
  rw [finiteWickOn_eq_LIP016, finiteWickOn_eq_LIP016]
  have hrow (i : ℕ) :
      (∑ j ∈ r, B i j * z i * z j) = ∑ j ∈ s, B i j * z i * z j := by
    symm
    apply Finset.sum_subset hsr
    intro j _ hj
    rw [hright j hj i, zero_mul, zero_mul]
  simp_rw [hrow]
  congr 1
  · symm
    apply Finset.sum_subset hsr
    intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [hleft i hi j, zero_mul, zero_mul]
  · symm
    apply Finset.sum_subset hsr
    intro i _ hi
    exact hleft i hi i

theorem norm_toLp_sq_LIP016 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

noncomputable def finiteWickLp_LIP016 (B : ℕ → ℕ → ℝ) (s : Finset ℕ) :
    Lp ℝ 2 gaussianCountable_LIP016 :=
  (finiteWickOn_memLp_LIP016 B s).toLp (finiteWickOn_LIP016 B s)

theorem finiteWickLp_sub_LIP016 (B C : ℕ → ℕ → ℝ) (s : Finset ℕ) :
    finiteWickLp_LIP016 (fun i j => B i j - C i j) s =
      finiteWickLp_LIP016 B s - finiteWickLp_LIP016 C s := by
  unfold finiteWickLp_LIP016
  rw [← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  exact Eventually.of_forall (finiteWickOn_sub_LIP016 B C s)

theorem finiteWickLp_padding_LIP016 (B : ℕ → ℕ → ℝ) (s r : Finset ℕ)
    (hsr : s ⊆ r) (hleft : ∀ i, i ∉ s → ∀ j, B i j = 0)
    (hright : ∀ j, j ∉ s → ∀ i, B i j = 0) :
    finiteWickLp_LIP016 B r = finiteWickLp_LIP016 B s := by
  apply MemLp.toLp_congr
  exact Eventually.of_forall (finiteWickOn_padding_LIP016 B s r hsr hleft hright)

theorem finiteWickLp_norm_sq_LIP016 (B : ℕ → ℕ → ℝ) (s : Finset ℕ)
    (hB : ∀ i j, B i j = B j i)
    (hleft : ∀ i, i ∉ s → ∀ j, B i j = 0)
    (hright : ∀ j, j ∉ s → ∀ i, B i j = 0) :
    ‖finiteWickLp_LIP016 B s‖ ^ 2 = 2 * ∑' p : ℕ × ℕ, B p.1 p.2 ^ 2 := by
  rw [finiteWickLp_LIP016, norm_toLp_sq_LIP016, finiteWickOn_isometry_LIP016 B s hB]
  congr 1
  rw [tsum_eq_sum (s := s.product s)]
  · exact (Finset.sum_product s s (fun p : ℕ × ℕ => B p.1 p.2 ^ 2)).symm
  · intro p hp
    by_cases hi : p.1 ∈ s
    · have hj : p.2 ∉ s := fun hj => hp (Finset.mem_product.mpr ⟨hi, hj⟩)
      rw [hright p.2 hj p.1, zero_pow (by decide)]
    · rw [hleft p.1 hi p.2, zero_pow (by decide)]

theorem kernelCoefficient_support_left_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m i : ℕ) (hi : i ∉ Finset.range (m + 1)) (j : ℕ) :
    kernelCoefficient_LIP016 S D t m i j = 0 := by
  have h : ¬ i ≤ m := by
    have hi' : ¬ i < m + 1 := by simpa only [Finset.mem_range] using hi
    omega
  simp only [kernelCoefficient_LIP016, h, false_and, ite_false]

theorem kernelCoefficient_support_right_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m j : ℕ) (hj : j ∉ Finset.range (m + 1)) (i : ℕ) :
    kernelCoefficient_LIP016 S D t m i j = 0 := by
  have h : ¬ j ≤ m := by
    have hj' : ¬ j < m + 1 := by simpa only [Finset.mem_range] using hj
    omega
  simp only [kernelCoefficient_LIP016, h, and_false, ite_false]

noncomputable def kernelWickLp_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) : Lp ℝ 2 gaussianCountable_LIP016 :=
  finiteWickLp_LIP016 (kernelCoefficient_LIP016 S D t m) (Finset.range (m + 1))

theorem kernelWick_difference_sq_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (t u : ℝ) (m n : ℕ) :
    ‖kernelWickLp_LIP016 S D t m - kernelWickLp_LIP016 S D u n‖ ^ 2 =
      2 * ∑' p : ℕ × ℕ,
        (kernelCoefficient_LIP016 S D t m p.1 p.2 -
          kernelCoefficient_LIP016 S D u n p.1 p.2) ^ 2 := by
  let r := Finset.range (max m n + 1)
  have hmr : Finset.range (m + 1) ⊆ r := Finset.range_mono (by omega)
  have hnr : Finset.range (n + 1) ⊆ r := Finset.range_mono (by omega)
  have hp_m := finiteWickLp_padding_LIP016 (kernelCoefficient_LIP016 S D t m)
    (Finset.range (m + 1)) r hmr
    (kernelCoefficient_support_left_LIP016 S D t m)
    (kernelCoefficient_support_right_LIP016 S D t m)
  have hp_n := finiteWickLp_padding_LIP016 (kernelCoefficient_LIP016 S D u n)
    (Finset.range (n + 1)) r hnr
    (kernelCoefficient_support_left_LIP016 S D u n)
    (kernelCoefficient_support_right_LIP016 S D u n)
  unfold kernelWickLp_LIP016
  rw [← hp_m, ← hp_n, ← finiteWickLp_sub_LIP016]
  apply finiteWickLp_norm_sq_LIP016
  · intro i j
    rw [kernelCoefficient_symmetric_LIP016 S D hK t m i j,
      kernelCoefficient_symmetric_LIP016 S D hK u n i j]
  · intro i hi j
    rw [kernelCoefficient_support_left_LIP016 S D t m i (fun h => hi (hmr h)) j,
      kernelCoefficient_support_left_LIP016 S D u n i (fun h => hi (hnr h)) j, sub_self]
  · intro j hj i
    rw [kernelCoefficient_support_right_LIP016 S D t m j (fun h => hj (hmr h)) i,
      kernelCoefficient_support_right_LIP016 S D u n j (fun h => hj (hnr h)) i, sub_self]

/-- Completion of the actual finite quadratic forms on one Gaussian product space.
The error is the exact squared coefficient error, rather than a diagonal-only estimate. -/
theorem kernelWick_completion_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (t : ℕ → ℝ) (m : ℕ → ℕ)
    (ht0 : ∀ R, 0 ≤ t R) (ht : Tendsto t atTop (𝓝 0)) (hm : StrictMono m) :
    ∃ q : Lp ℝ 2 gaussianCountable_LIP016,
      Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R)) atTop (𝓝 q) ∧
      ∀ R, ‖kernelWickLp_LIP016 S D (t R) (m R) - q‖ ^ 2 =
        2 * ∑' p : ℕ × ℕ,
          (kernelCoefficient_LIP016 S D (t R) (m R) p.1 p.2 - TK S D.K p.1 p.2) ^ 2 := by
  let a (R : ℕ) (p : ℕ × ℕ) := kernelCoefficient_LIP016 S D (t R) (m R) p.1 p.2
  let b (p : ℕ × ℕ) := TK S D.K p.1 p.2
  let E (R : ℕ) := ∑' p : ℕ × ℕ, (a R p - b p) ^ 2
  let qR (R : ℕ) := kernelWickLp_LIP016 S D (t R) (m R)
  have hE : Tendsto E atTop (𝓝 0) :=
    kernelCoefficient_hilbertSchmidt_tendsto_LIP016 S D t m ht0 ht hm
  have he (R : ℕ) (p : ℕ × ℕ) : (a R p - b p) ^ 2 ≤ b p ^ 2 :=
    kernelCoefficient_error_le_LIP016 S D (ht0 R) (m R) p.1 p.2
  have hEs (R : ℕ) : Summable (fun p : ℕ × ℕ => (a R p - b p) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (he R) (hasSum_prod_sq S D).summable
  have hd (R U : ℕ) (p : ℕ × ℕ) :
      (a R p - a U p) ^ 2 ≤ 2 * (a R p - b p) ^ 2 + 2 * (a U p - b p) ^ 2 := by
    nlinarith [sq_nonneg (a R p + a U p - 2 * b p)]
  have hds (R U : ℕ) : Summable (fun p : ℕ × ℕ => (a R p - a U p) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (hd R U)
      (((hEs R).mul_left 2).add ((hEs U).mul_left 2))
  have hnorm (R U : ℕ) : ‖qR R - qR U‖ ^ 2 ≤ 4 * (E R + E U) := by
    have hsum := Summable.tsum_le_tsum (hd R U) (hds R U)
      (((hEs R).mul_left 2).add ((hEs U).mul_left 2))
    rw [Summable.tsum_add (((hEs R).mul_left 2)) (((hEs U).mul_left 2)),
      tsum_mul_left, tsum_mul_left] at hsum
    have hid := kernelWick_difference_sq_LIP016 S D hK (t R) (t U) (m R) (m U)
    change ‖qR R - qR U‖ ^ 2 = 2 * ∑' p, (a R p - a U p) ^ 2 at hid
    dsimp only [E]
    nlinarith
  have hC : CauchySeq qR := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hsmall : ∀ᶠ R in atTop, E R < ε ^ 2 / 8 :=
      hE.eventually (gt_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    refine ⟨N, fun R hR U hU => ?_⟩
    rw [dist_eq_norm]
    have h := hnorm R U
    have hR' := hN R hR
    have hU' := hN U hU
    nlinarith [norm_nonneg (qR R - qR U)]
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨q, hq, fun R => ?_⟩
  have hl : Tendsto (fun U => ‖qR R - qR U‖ ^ 2) atTop (𝓝 (‖qR R - q‖ ^ 2)) :=
    (tendsto_const_nhds.sub hq).norm.pow 2
  have hb : Tendsto (fun U => ∑' p : ℕ × ℕ, (a R p - a U p) ^ 2)
      atTop (𝓝 (E R)) := by
    apply tendsto_tsum_of_dominated_convergence
      ((hasSum_prod_sq S D).summable.mul_left 4)
    · intro p
      exact (tendsto_const_nhds.sub
        (kernelCoefficient_tendsto_LIP016 S D t m ht hm p.1 p.2)).pow 2
    · exact Eventually.of_forall fun U p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h := hd R U p
        have hR := he R p
        have hU := he U p
        nlinarith
  have hr : Tendsto (fun U => ‖qR R - qR U‖ ^ 2) atTop (𝓝 (2 * E R)) := by
    convert hb.const_mul 2 using 1
    funext U
    exact kernelWick_difference_sq_LIP016 S D hK (t R) (t U) (m R) (m U)
  exact tendsto_nhds_unique hl hr

/-- A uniform moment of order greater than one gives actual uniform integrability.
The proof supplies the tail estimate required by Mathlib's criterion. -/
theorem uniformIntegrable_of_moment_LIP016 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) {p C : ℝ}
    (hp : 1 < p) (hf0 : ∀ n x, 0 ≤ f n x) (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n) μ)
    (hpi : ∀ n, Integrable (fun x => f n x ^ p) μ)
    (hpC : ∀ n, ∫ x, f n x ^ p ∂μ ≤ C) :
    UniformIntegrable f 1 μ := by
  apply uniformIntegrable_of (by norm_num) (by simp) (fun n => (hfm n).aestronglyMeasurable)
  intro ε hε
  by_cases hεtop : ε = ∞
  · subst ε
    exact ⟨0, fun _ => le_top⟩
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hrpow := tendsto_rpow_atTop (show 0 < p - 1 by linarith)
  obtain ⟨K, hK, hKC⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (hrpow.eventually (eventually_ge_atTop (C / ε.toReal)))).exists
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hPow : 0 < K ^ (p - 1) := Real.rpow_pos_of_pos hK0 _
  have hfac : (K ^ (p - 1))⁻¹ * C ≤ ε.toReal := by
    have h := (div_le_iff₀ hεr).mp hKC
    have hd : C / K ^ (p - 1) ≤ ε.toReal := by
      apply (div_le_iff₀ hPow).mpr
      simpa only [mul_comm] using h
    simpa only [div_eq_mul_inv, mul_comm] using hd
  let cut : ℝ≥0 := ⟨K, hK0.le⟩
  refine ⟨cut, fun n => ?_⟩
  let A : Set Ω := {x | cut ≤ ‖f n x‖₊}
  have hA : MeasurableSet A := measurableSet_le measurable_const (hfm n).nnnorm
  have hTi : Integrable (A.indicator (f n)) μ := (hfi n).indicator hA
  have hpoint (x : Ω) :
      ‖A.indicator (f n) x‖ ≤ (K ^ (p - 1))⁻¹ * f n x ^ p := by
    by_cases hx : x ∈ A
    · have hxK : K ≤ f n x := by
        change K ≤ ‖f n x‖ at hx
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 n x)] using hx
      have hx0 : 0 < f n x := lt_of_lt_of_le hK0 hxK
      have hm := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hK0.le hxK (by linarith : 0 ≤ p - 1)) (hf0 n x)
      have he : f n x ^ (p - 1) * f n x = f n x ^ p := by
        calc
          _ = f n x ^ (p - 1) * f n x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = f n x ^ ((p - 1) + 1) := (Real.rpow_add hx0 _ _).symm
          _ = _ := by congr 1; ring
      rw [he] at hm
      have hd : f n x ≤ f n x ^ p / K ^ (p - 1) := by
        apply (le_div_iff₀ hPow).mpr
        simpa only [mul_comm] using hm
      rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (hf0 n x)]
      simpa only [div_eq_mul_inv, mul_comm] using hd
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hPow.le) (Real.rpow_nonneg (hf0 n x) _)
  have hInt :
      (∫ x, ‖A.indicator (f n) x‖ ∂μ) ≤ (K ^ (p - 1))⁻¹ * C := by
    calc
      _ ≤ ∫ x, (K ^ (p - 1))⁻¹ * f n x ^ p ∂μ :=
        integral_mono hTi.norm ((hpi n).const_mul _) hpoint
      _ = (K ^ (p - 1))⁻¹ * ∫ x, f n x ^ p ∂μ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpC n) (inv_nonneg.mpr hPow.le)
  change eLpNorm (A.indicator (f n)) 1 μ ≤ ε
  rw [eLpNorm_one_eq_lintegral_enorm hTi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hTi]
  simpa only [ENNReal.ofReal_toReal hεtop] using
    ENNReal.ofReal_le_ofReal (hInt.trans hfac)

/-- Continuous exponential composition in measure, including the deterministic trace. -/
theorem exponential_tendstoInMeasure_LIP016 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) (q : Ω → ℝ)
    (tr : ℕ → ℝ) (d : ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hF : ∀ n, AEStronglyMeasurable (fun x => Real.exp (-(f n x + tr n) / 2)) μ)
    (hq : TendstoInMeasure μ f atTop q) (htr : Tendsto tr atTop (𝓝 d)) :
    TendstoInMeasure μ (fun n x => Real.exp (-(f n x + tr n) / 2)) atTop
      (fun x => Real.exp (-(q x + d) / 2)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hF).mpr
  intro ns hns
  obtain ⟨ms, hms, hae⟩ :=
    (exists_seq_tendstoInMeasure_atTop_iff hf).mp hq ns hns
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae] with x hx
  exact Real.continuous_exp.continuousAt.tendsto.comp
    (((hx.add ((htr.comp hns.tendsto_atTop).comp hms.tendsto_atTop)).neg).div_const 2)

/-- Vitali's theorem gives the actual finite positive limiting normalizer. -/
theorem exponential_integral_limit_LIP016 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ]
    (f : ℕ → Ω → ℝ) (q : Ω → ℝ) (tr : ℕ → ℝ) (d : ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hF : ∀ n, AEStronglyMeasurable (fun x => Real.exp (-(f n x + tr n) / 2)) μ)
    (hq : TendstoInMeasure μ f atTop q) (htr : Tendsto tr atTop (𝓝 d))
    (hUI : UniformIntegrable (fun n x => Real.exp (-(f n x + tr n) / 2)) 1 μ) :
    Integrable (fun x => Real.exp (-(q x + d) / 2)) μ ∧
      0 < ∫ x, Real.exp (-(q x + d) / 2) ∂μ ∧
      Tendsto (fun n => ∫ x, Real.exp (-(f n x + tr n) / 2) ∂μ) atTop
        (𝓝 (∫ x, Real.exp (-(q x + d) / 2) ∂μ)) := by
  have hc := exponential_tendstoInMeasure_LIP016 μ f q tr d hf hF hq htr
  have hg := hUI.memLp_of_tendstoInMeasure hc
  have hi : Integrable (fun x => Real.exp (-(q x + d) / 2)) μ :=
    memLp_one_iff_integrable.mp hg
  refine ⟨hi, integral_exp_pos hi, ?_⟩
  apply tendsto_integral_of_L1' (fun x => Real.exp (-(q x + d) / 2))
    (Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hUI.memLp n))
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by simp) hF hg hUI.1 hc

/-- A spectral computation of the higher exponential moment, with integrability. -/
theorem gaussian_exponential_eigenbasis_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (a : ι → ℝ) (hdiag : ∀ i, T (b i) = a i • b i)
    {p δ : ℝ} (hδ : 0 < δ) (hpos : ∀ i, δ ≤ 1 + p * a i) :
    Integrable (fun z : E => Real.exp (-p * (⟪z, T z⟫_ℝ - ∑ i, a i) / 2))
      (stdGaussian E) ∧
      (∫ z : E, Real.exp (-p * (⟪z, T z⟫_ℝ - ∑ i, a i) / 2) ∂stdGaussian E) ≤
        Real.exp (p ^ 2 / (2 * δ) * ∑ i, a i ^ 2) := by
  have he (z : ι → ℝ) :
      -p * (⟪∑ i, z i • b i, T (∑ i, z i • b i)⟫_ℝ - ∑ i, a i) / 2 =
        ∑ i, -p * a i * (z i ^ 2 - 1) / 2 := by
    rw [eigenbasis_quadratic_LIP016 b T a hdiag]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hm : AEMeasurable (fun x : ι → ℝ => ∑ i, x i • b i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    (show Continuous (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).measurable.aemeasurable
  have hd := gaussian_diagonal_exponential_bound_LIP016 a hδ hpos
  constructor
  · rw [stdGaussian_eq_map_pi_orthonormalBasis b]
    apply (integrable_map_measure (by fun_prop) hm).mpr
    exact hd.1.congr (Eventually.of_forall fun z => by
      dsimp only [Function.comp_apply]
      rw [he])
  · rw [stdGaussian_eq_map_pi_orthonormalBasis b, integral_map hm (by fun_prop)]
    simpa only [he] using hd.2

/-- The exponential moment is computed on the fixed canonical finite coordinates,
although the eigenbasis used to calculate it depends on the matrix. -/
theorem gaussian_matrix_exponential_bound_LIP016 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) {p δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ i, δ ≤ 1 + p * hB.eigenvalues i) :
    Integrable (fun z : ι → ℝ => Real.exp (-p * matrixWick_LIP016 B z / 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
      (∫ z : ι → ℝ, Real.exp (-p * matrixWick_LIP016 B z / 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
        Real.exp (p ^ 2 / (2 * δ) * ∑ i, ∑ j, B i j ^ 2) := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)
  have heig (i : ι) : T (hB.eigenvectorBasis i) =
      hB.eigenvalues i • hB.eigenvectorBasis i := by
    ext j
    change (B *ᵥ (hB.eigenvectorBasis i : ι → ℝ)) j =
      hB.eigenvalues i * hB.eigenvectorBasis i j
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (hB.mulVec_eigenvectorBasis i) j
  have h := gaussian_exponential_eigenbasis_LIP016 hB.eigenvectorBasis T
    hB.eigenvalues heig hδ hpos
  have htr : Matrix.trace B = ∑ i, hB.eigenvalues i := hB.trace_eq_sum_eigenvalues
  rw [← htr] at h
  rw [← map_pi_eq_stdGaussian] at h
  have hi := (integrable_map_measure (by fun_prop) (by fun_prop)).mp h.1
  have hb := h.2
  rw [integral_map (by fun_prop) (by fun_prop)] at hb
  have hi' : Integrable (fun z : ι → ℝ => Real.exp (-p * matrixWick_LIP016 B z / 2))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    hi.congr (Eventually.of_forall fun z => by
      dsimp only [Function.comp_apply, T]
      rw [matrixQuadratic_inner_LIP016]
      rfl)
  simp only [T, matrixQuadratic_inner_LIP016] at hb
  rw [matrix_eigen_sq_sum_LIP016 B hB] at hb
  exact ⟨hi', hb⟩

theorem kernelCompression_finiteRank_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ) :
    FiniteDimensional ℝ (LinearMap.range
      (kernelCompression_LIP016 S D hK t m).toLinearMap) := by
  let V := Submodule.span ℝ
    (spectralBasis_LIP016 S '' (Finset.range (m + 1) : Set ℕ))
  let _ : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ ((Finset.range (m + 1)).finite_toSet.image _)
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  rintro _ ⟨f, rfl⟩
  change kernelCompression_LIP016 S D hK t m f ∈ V
  rw [kernelCompression_apply_LIP016 S D hK hc]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, hi, rfl⟩

theorem kernelCoefficient_sq_le_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    {t : ℝ} (ht : 0 ≤ t) (m i j : ℕ) :
    kernelCoefficient_LIP016 S D t m i j ^ 2 ≤ TK S D.K i j ^ 2 := by
  unfold kernelCoefficient_LIP016
  split_ifs
  · have hl : 0 ≤ S.lam i + S.lam j := add_nonneg (S.lam_nonneg i) (S.lam_nonneg j)
    have he0 := (Real.exp_pos (-(t * (S.lam i + S.lam j)))).le
    have he1 : Real.exp (-(t * (S.lam i + S.lam j))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht hl))
    have he2 : Real.exp (-(t * (S.lam i + S.lam j))) ^ 2 ≤ 1 := by nlinarith
    calc _ = Real.exp (-(t * (S.lam i + S.lam j))) ^ 2 * TK S D.K i j ^ 2 := by ring
      _ ≤ 1 * TK S D.K i j ^ 2 := mul_le_mul_of_nonneg_right he2 (sq_nonneg _)
      _ = _ := one_mul _
  · simpa only [zero_pow (show (2 : ℕ) ≠ 0 by decide)] using (sq_nonneg (TK S D.K i j))

theorem matrix_eigenvalue_lower_LIP016 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (a : ℝ)
    (hquad : ∀ z : ι → ℝ, a * (∑ i, z i ^ 2) ≤
      (∑ i, z i ^ 2) + matrixQuadratic_LIP016 B z) :
    ∀ k, a ≤ 1 + hB.eigenvalues k := by
  intro k
  let v := hB.eigenvectorBasis k
  have hn : ‖v‖ = 1 := hB.eigenvectorBasis.orthonormal.1 k
  have hs : (∑ i, v i ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hn, one_pow]
  have he : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B) v =
      hB.eigenvalues k • v := by
    ext j
    change (B *ᵥ (v : ι → ℝ)) j = hB.eigenvalues k * v j
    simpa only [v, Pi.smul_apply, smul_eq_mul] using
      congrFun (hB.mulVec_eigenvectorBasis k) j
  have hq : matrixQuadratic_LIP016 B v = hB.eigenvalues k := by
    rw [← matrixQuadratic_inner_LIP016]
    change ⟪v, LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B) v⟫_ℝ = _
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  have h := hquad v
  rw [hs, hq, mul_one] at h
  exact h

theorem kernelCoefficient_finite_coercive_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (z : (Finset.range (m + 1)) → ℝ) :
    min 1 σ * (∑ i, z i ^ 2) ≤ (∑ i, z i ^ 2) +
      matrixQuadratic_LIP016 (Matrix.of fun i j : Finset.range (m + 1) =>
        kernelCoefficient_LIP016 S D t m i j) z := by
  let u (i : ℕ) : ℝ := if h : i ∈ Finset.range (m + 1) then z ⟨i, h⟩ else 0
  have hu (i : Finset.range (m + 1)) : u i = z i := by simp only [u, dite_eq_left i.property]
  have h := kernelCoefficient_coercive_from_hessian_LIP016 S D hK hc hH ht m u
  have hs (u : ℕ → ℝ) :
      (∑ i ∈ Finset.range (m + 1), u i ^ 2) =
        ∑ i : Finset.range (m + 1), u i ^ 2 := (Finset.sum_coe_sort _ _).symm
  simp only [hs, ← sum_finset_pair_LIP016, hu] at h
  exact h

theorem kernelTrace_abs_le_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) {C : ℝ} (hbd : ∀ x y, |smoothK S D t m x y| ≤ C) :
    |kernelTrace_LIP016 S D t m| ≤ C := by
  let _ : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  rw [kernelTrace_integral_LIP016]
  calc
    _ ≤ ∫ x, |smoothK S D t m x x| ∂S.mu := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Torus d, C ∂S.mu := integral_mono
      ((((smoothK_continuous_LIP016 S D t m).comp
        (continuous_id.prodMk continuous_id)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)).abs)
      (integrable_const _) (fun x => hbd x x)
    _ = C := by simp

theorem kernelCoefficient_finite_sq_sum_le_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    (∑ i : Finset.range (m + 1), ∑ j : Finset.range (m + 1),
      kernelCoefficient_LIP016 S D t m i j ^ 2) ≤
        ∑' p : ℕ × ℕ, TK S D.K p.1 p.2 ^ 2 := by
  rw [sum_finset_pair_LIP016 (fun i j => kernelCoefficient_LIP016 S D t m i j ^ 2)
    (Finset.range (m + 1))]
  apply (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    kernelCoefficient_sq_le_LIP016 S D ht m i j).trans
  rw [← Finset.sum_product (Finset.range (m + 1)) (Finset.range (m + 1))
    (fun ij : ℕ × ℕ => TK S D.K ij.1 ij.2 ^ 2)]
  exact (hasSum_prod_sq S D).summable.sum_le_tsum _ (fun _ _ => sq_nonneg _)

/-- Uniform spectral-gap and coefficient bounds give a dimension-independent moment
on the one fixed countable Gaussian product. -/
theorem kernelWick_exponential_bound_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) {p δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ ell : ℝ, min 1 σ ≤ 1 + ell → δ ≤ 1 + p * ell) :
    Integrable (fun z => Real.exp (-p *
      finiteWickOn_LIP016 (kernelCoefficient_LIP016 S D t m) (Finset.range (m + 1)) z / 2))
      gaussianCountable_LIP016 ∧
      (∫ z, Real.exp (-p *
        finiteWickOn_LIP016 (kernelCoefficient_LIP016 S D t m) (Finset.range (m + 1)) z / 2)
        ∂gaussianCountable_LIP016) ≤
      Real.exp (p ^ 2 / (2 * δ) * ∑' ij : ℕ × ℕ, TK S D.K ij.1 ij.2 ^ 2) := by
  let s := Finset.range (m + 1)
  let B : Matrix s s ℝ := Matrix.of fun i j => kernelCoefficient_LIP016 S D t m i j
  have hB : B.IsHermitian := by
    ext i j
    exact kernelCoefficient_symmetric_LIP016 S D hK t m j i
  have hell := matrix_eigenvalue_lower_LIP016 B hB (min 1 σ)
    (kernelCoefficient_finite_coercive_LIP016 S D hK hc hH ht m)
  have hfin := gaussian_matrix_exponential_bound_LIP016 B hB hδ
    (fun i => hgap _ (hell i))
  have hp : MeasurePreserving s.restrict gaussianCountable_LIP016
      (Measure.pi fun _ : s => gaussianReal 0 1) :=
    ⟨Finset.measurable_restrict s, Measure.infinitePi_map_restrict _⟩
  have hi := hp.integrable_comp_of_integrable hfin.1
  have hb := hfin.2
  have hfm : AEStronglyMeasurable
      (fun z : s → ℝ => Real.exp (-p * matrixWick_LIP016 B z / 2))
      (gaussianCountable_LIP016.map s.restrict) := by
    rw [hp.map_eq]
    exact hfin.1.aestronglyMeasurable
  rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hfm] at hb
  refine ⟨hi, hb.trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (kernelCoefficient_finite_sq_sum_le_LIP016 S D ht m)
    (div_nonneg (sq_nonneg p) (by positivity))

/-- The unnormalized finite Gaussian exponential, including its actual finite trace. -/
noncomputable def kernelRawGaussian_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) (z : ℕ → ℝ) : ℝ :=
  Real.exp (-(finiteWickOn_LIP016 (kernelCoefficient_LIP016 S D t m)
    (Finset.range (m + 1)) z + kernelTrace_LIP016 S D t m) / 2)

theorem kernelRawGaussian_quadratic_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) (z : ℕ → ℝ) :
    kernelRawGaussian_LIP016 S D t m z =
      Real.exp (-(∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        kernelCoefficient_LIP016 S D t m i j * z i * z j) / 2) := by
  unfold kernelRawGaussian_LIP016
  rw [finiteWickOn_eq_LIP016]
  simp only [kernelTrace_LIP016, sub_add_cancel]

theorem kernelRawGaussian_moment_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) {p δ C : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ)
    (hgap : ∀ ell : ℝ, min 1 σ ≤ 1 + ell → δ ≤ 1 + p * ell)
    (htrace : |kernelTrace_LIP016 S D t m| ≤ C) :
    Integrable (fun z => kernelRawGaussian_LIP016 S D t m z ^ p)
      gaussianCountable_LIP016 ∧
      (∫ z, kernelRawGaussian_LIP016 S D t m z ^ p ∂gaussianCountable_LIP016) ≤
        Real.exp (p * C / 2 + p ^ 2 / (2 * δ) *
          ∑' ij : ℕ × ℕ, TK S D.K ij.1 ij.2 ^ 2) := by
  have hw := kernelWick_exponential_bound_LIP016 S D hK hc hH ht m hδ hgap
  have he (z : ℕ → ℝ) :
      kernelRawGaussian_LIP016 S D t m z ^ p =
        Real.exp (-p * kernelTrace_LIP016 S D t m / 2) *
          Real.exp (-p * finiteWickOn_LIP016 (kernelCoefficient_LIP016 S D t m)
            (Finset.range (m + 1)) z / 2) := by
    unfold kernelRawGaussian_LIP016
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hfac : Real.exp (-p * kernelTrace_LIP016 S D t m / 2) ≤ Real.exp (p * C / 2) := by
    apply Real.exp_le_exp.mpr
    have ht' : -kernelTrace_LIP016 S D t m ≤ C := (neg_le_abs _).trans htrace
    nlinarith
  constructor
  · exact (hw.1.const_mul _).congr (Eventually.of_forall fun z => (he z).symm)
  · simp_rw [he]
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (-p * kernelTrace_LIP016 S D t m / 2) *
          Real.exp (p ^ 2 / (2 * δ) * ∑' ij : ℕ × ℕ, TK S D.K ij.1 ij.2 ^ 2) :=
        mul_le_mul_of_nonneg_left hw.2 (Real.exp_pos _).le
      _ ≤ Real.exp (p * C / 2) *
          Real.exp (p ^ 2 / (2 * δ) * ∑' ij : ℕ × ℕ, TK S D.K ij.1 ij.2 ^ 2) :=
        mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm

/-- Uniform integrability is proved from the original Hessian coercivity, the actual
finite Gaussian calculation and the LIP011 uniform kernel bound. -/
theorem kernelRawGaussian_uniformIntegrable_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R) {C : ℝ}
    (hbd : ∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C) :
    UniformIntegrable (fun R => kernelRawGaussian_LIP016 S D (t R) (m R)) 1
      gaussianCountable_LIP016 := by
  let a := min 1 σ
  let p := 1 + a / 2
  let δ := a / 2
  have ha : 0 < a := lt_min zero_lt_one hσ
  have hp : 1 < p := by dsimp [p]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hgap (ell : ℝ) (hell : a ≤ 1 + ell) : δ ≤ 1 + p * ell := by
    have h := mul_nonneg (show 0 ≤ p by linarith) (sub_nonneg.mpr hell)
    dsimp only [p, δ] at h ⊢
    nlinarith [sq_nonneg a]
  have htrace (R : ℕ) := kernelTrace_abs_le_LIP016 S D (t R) (m R) (hbd R)
  have hi (R : ℕ) : Integrable (kernelRawGaussian_LIP016 S D (t R) (m R))
      gaussianCountable_LIP016 := by
    have h := (kernelRawGaussian_moment_LIP016 S D hK hc hH (ht R) (m R)
      (p := 1) (δ := a) zero_le_one ha (fun ell hell => by simpa only [one_mul] using hell)
      (htrace R)).1
    simpa only [Real.rpow_one] using h
  have hmom (R : ℕ) := kernelRawGaussian_moment_LIP016 S D hK hc hH (ht R) (m R)
    (p := p) (δ := δ) (by linarith) hδ hgap (htrace R)
  apply uniformIntegrable_of_moment_LIP016 gaussianCountable_LIP016
    (fun R => kernelRawGaussian_LIP016 S D (t R) (m R)) hp
    (fun R z => (Real.exp_pos _).le)
    (fun R => by
      unfold kernelRawGaussian_LIP016 finiteWickOn_LIP016 matrixWick_LIP016
        matrixQuadratic_LIP016 Finset.restrict
      fun_prop)
    hi (fun R => (hmom R).1)
  exact fun R => (hmom R).2

/-- Integral operators and Hessians depend only on the centered kernel. -/
theorem kernelOp_congr_LIP016 {d : ℕ} (J L : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hK : ∀ x y, DGPS.centeredKernel J μ x y = DGPS.centeredKernel L μ x y) :
    DGPS.kernelOp J μ = DGPS.kernelOp L μ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [DGPS.kernelOp_ae J μ f, DGPS.kernelOp_ae L μ f] with x hJ hL
  rw [hJ, hL]
  unfold DGPS.kernelTransform
  simp_rw [hK]

theorem densityHessian_congr_LIP016 {d : ℕ} (J L : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hK : ∀ x y, DGPS.centeredKernel J μ x y = DGPS.centeredKernel L μ x y) :
    DGPS.densityHessian J μ = DGPS.densityHessian L μ := by
  have hop := kernelOp_congr_LIP016 J L μ hK
  have hc : DGPS.centeredInteraction J μ = DGPS.centeredInteraction L μ := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    change DGPS.kernelOp J μ f = DGPS.kernelOp L μ f
    rw [hop]
  simp only [DGPS.densityHessian, hc]

theorem kernelOperator_original_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y) :
    kernelOperator_LIP016 S D hK = DGPS.kernelOp J (specProbability_LIP016 S) :=
  kernelOp_congr_LIP016 (kernelInteraction_LIP016 D hK) J (specProbability_LIP016 S)
    (fun x y => (kernelInteraction_centered_LIP016 S D hK hc x y).trans (hD x y))

/-- The original Hessian coercivity discharges the reconstructed-kernel helper premise. -/
theorem original_hessian_transport_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y)
    {σ : ℝ}
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J (specProbability_LIP016 S) g⟫_ℝ) :
    ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ := by
  have he := densityHessian_congr_LIP016 (kernelInteraction_LIP016 D hK) J
    (specProbability_LIP016 S) (fun x y =>
      (kernelInteraction_centered_LIP016 S D hK hc x y).trans (hD x y))
  simpa only [he] using hH

/-- The full-space inverse has the original density covariance on the centered subspace.
Its constant block is the identity. -/
theorem kernelCovariance_centered_LIP016 {d : ℕ} (J : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 μ,
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J μ g⟫_ℝ)
    (g : DGPS.centeredL2 μ) :
    Ring.inverse (1 + DGPS.kernelOp J μ) (g : Lp ℝ 2 (μ : Measure (Torus d))) =
      (DGPS.densityCovariance J μ ⟨σ, hσ, hH⟩ g : Lp ℝ 2 (μ : Measure (Torus d))) := by
  have hu : IsUnit (1 + DGPS.kernelOp J μ) := by
    apply isUnit_of_coercive_LIP016 _ (show (0 : ℝ) < min 1 σ from lt_min zero_lt_one hσ)
    intro f
    simpa only [add_apply, one_apply_eq_self, inner_add_right, real_inner_self_eq_norm_sq] using
      centered_coercivity_full_LIP016 J μ hH f
  let v := DGPS.densityCovariance J μ ⟨σ, hσ, hH⟩ g
  have hv : (1 + DGPS.kernelOp J μ) (v : Lp ℝ 2 (μ : Measure (Torus d))) = g := by
    have h := congrArg (fun f : DGPS.centeredL2 μ =>
      (f : Lp ℝ 2 (μ : Measure (Torus d)))) (DGPS.densityHessian_densityCovariance J μ ⟨σ, hσ, hH⟩ g)
    exact h
  calc
    _ = Ring.inverse (1 + DGPS.kernelOp J μ)
        ((1 + DGPS.kernelOp J μ) (v : Lp ℝ 2 (μ : Measure (Torus d)))) :=
      congrArg (fun f : Lp ℝ 2 (μ : Measure (Torus d)) =>
        (Ring.inverse (1 + DGPS.kernelOp J μ)) f) hv.symm
    _ = (v : Lp ℝ 2 (μ : Measure (Torus d))) := by
      rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu, one_apply_eq_self]

theorem kernelCovariance_const_one_LIP016 {d : ℕ} (J : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 μ,
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J μ g⟫_ℝ) :
    Ring.inverse (1 + DGPS.kernelOp J μ)
      (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)) =
        Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ) := by
  have hu : IsUnit (1 + DGPS.kernelOp J μ) := by
    apply isUnit_of_coercive_LIP016 _ (show (0 : ℝ) < min 1 σ from lt_min zero_lt_one hσ)
    intro f
    simpa only [add_apply, one_apply_eq_self, inner_add_right, real_inner_self_eq_norm_sq] using
      centered_coercivity_full_LIP016 J μ hH f
  have he : (1 + DGPS.kernelOp J μ) (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)) =
      Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ) := by
    rw [add_apply, one_apply_eq_self, kernelOp_const_one_LIP016, add_zero]
  calc
    _ = Ring.inverse (1 + DGPS.kernelOp J μ)
        ((1 + DGPS.kernelOp J μ) (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ))) :=
      congrArg (fun f : Lp ℝ 2 (μ : Measure (Torus d)) =>
        (Ring.inverse (1 + DGPS.kernelOp J μ)) f) he.symm
    _ = Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ) := by
      rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu, one_apply_eq_self]

theorem kernelCovariance_original_centered_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J (specProbability_LIP016 S) g⟫_ℝ)
    (g : DGPS.centeredL2 (specProbability_LIP016 S)) :
    Ring.inverse (1 + kernelOperator_LIP016 S D hK)
      (g : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) =
      (DGPS.densityCovariance J (specProbability_LIP016 S) ⟨σ, hσ, hH⟩ g :
        Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) := by
  rw [kernelOperator_original_LIP016 S D hK hc J hD]
  exact kernelCovariance_centered_LIP016 J (specProbability_LIP016 S) hσ hH g

/-- The actual finite-rank kernel compressions satisfy positivity, operator resolvent,
coefficient Hilbert--Schmidt, finite-trace and common-space Wick convergence.
The finite normalizers converge to a finite strictly positive expectation. No trace
of the limiting operator and no limiting tilted-law premise is used. -/
theorem kernel_packet_LIP016 {d : ℕ}
    (S : Spec d) (A : Aux S) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ) :
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (q : Lp ℝ 2 gaussianCountable_LIP016),
      (∀ R, 0 < t R) ∧ Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
      (∀ R, FiniteDimensional ℝ (LinearMap.range
        (kernelCompression_LIP016 S D hK (t R) (m R)).toLinearMap)) ∧
      (∀ R f, min 1 σ * ‖f‖ ^ 2 ≤ ‖f‖ ^ 2 +
        ⟪f, kernelCompression_LIP016 S D hK (t R) (m R) f⟫_ℝ) ∧
      (∀ R i j, ⟪spectralBasis_LIP016 S i,
        kernelCompression_LIP016 S D hK (t R) (m R) (spectralBasis_LIP016 S j)⟫_ℝ =
          kernelCoefficient_LIP016 S D (t R) (m R) i j) ∧
      Tendsto (fun R => ∑' ij : ℕ × ℕ,
        (kernelCoefficient_LIP016 S D (t R) (m R) ij.1 ij.2 - TK S D.K ij.1 ij.2) ^ 2)
          atTop (𝓝 0) ∧
      (∀ R, IsUnit (1 + kernelCompression_LIP016 S D hK (t R) (m R))) ∧
      Tendsto (fun R => Ring.inverse (1 + kernelCompression_LIP016 S D hK (t R) (m R)))
        atTop (𝓝 (Ring.inverse (1 + kernelOperator_LIP016 S D hK))) ∧
      Tendsto (fun R => kernelTrace_LIP016 S D (t R) (m R))
        atTop (𝓝 (∫ x, D.K x x ∂S.mu)) ∧
      Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R)) atTop (𝓝 q) ∧
      (∀ R, ‖kernelWickLp_LIP016 S D (t R) (m R) - q‖ ^ 2 =
        2 * ∑' ij : ℕ × ℕ,
          (kernelCoefficient_LIP016 S D (t R) (m R) ij.1 ij.2 - TK S D.K ij.1 ij.2) ^ 2) ∧
      UniformIntegrable (fun R => kernelRawGaussian_LIP016 S D (t R) (m R)) 1
        gaussianCountable_LIP016 ∧
      Integrable (fun z => Real.exp (-(q z + ∫ x, D.K x x ∂S.mu) / 2))
        gaussianCountable_LIP016 ∧
      0 < ∫ z, Real.exp (-(q z + ∫ x, D.K x x ∂S.mu) / 2) ∂gaussianCountable_LIP016 ∧
      Tendsto (fun R => ∫ z, kernelRawGaussian_LIP016 S D (t R) (m R) z
        ∂gaussianCountable_LIP016) atTop
        (𝓝 (∫ z, Real.exp (-(q z + ∫ x, D.K x x ∂S.mu) / 2) ∂gaussianCountable_LIP016)) := by
  obtain ⟨t, m, C, ht, -, htlim, hm, -, hbd, -, -, -, -, hU, -⟩ :=
    smoothed_approximation' S A D
  have ht0 (R : ℕ) := (ht R).le
  have hHS := kernelCoefficient_hilbertSchmidt_tendsto_LIP016 S D t m ht0 htlim hm
  have htrace := kernelTrace_tendsto_LIP016 S D t m hbd hU
  obtain ⟨q, hq, herr⟩ := kernelWick_completion_LIP016 S D hK t m ht0 htlim hm
  have hUI := kernelRawGaussian_uniformIntegrable_LIP016 S D hK hc hσ hH t m ht0 hbd
  let f (R : ℕ) := finiteWickOn_LIP016 (kernelCoefficient_LIP016 S D (t R) (m R))
    (Finset.range (m R + 1))
  have hf (R : ℕ) : MemLp (f R) 2 gaussianCountable_LIP016 :=
    finiteWickOn_memLp_LIP016 _ _
  have hAE (R : ℕ) :
      (kernelWickLp_LIP016 S D (t R) (m R) : (ℕ → ℝ) → ℝ) =ᵐ[gaussianCountable_LIP016] f R :=
    (hf R).coeFn_toLp
  have hqm : TendstoInMeasure gaussianCountable_LIP016 f atTop q :=
    TendstoInMeasure.congr_left hAE (tendstoInMeasure_of_tendsto_Lp hq)
  have hFm (R : ℕ) : AEStronglyMeasurable
      (fun z => Real.exp (-(f R z + kernelTrace_LIP016 S D (t R) (m R)) / 2))
      gaussianCountable_LIP016 := by
    apply Measurable.aestronglyMeasurable
    unfold f finiteWickOn_LIP016 matrixWick_LIP016 matrixQuadratic_LIP016 Finset.restrict
    fun_prop
  have hlim := exponential_integral_limit_LIP016 gaussianCountable_LIP016 f q
    (fun R => kernelTrace_LIP016 S D (t R) (m R)) (∫ x, D.K x x ∂S.mu)
    (fun R => (hf R).aestronglyMeasurable) hFm hqm htrace hUI
  refine ⟨t, m, q, ht, htlim, hm,
    (fun R => kernelCompression_finiteRank_LIP016 S D hK hc (t R) (m R)),
    (fun R f => kernelCompression_coercive_LIP016 S D hK hH (ht0 R) (m R) f),
    (fun R i j => kernelCompression_basis_coefficient_LIP016 S D hK hc (t R) (m R) i j),
    hHS, (fun R => kernelCompression_isUnit_LIP016 S D hK hσ hH (ht0 R) (m R)),
    kernelCovariance_tendsto_LIP016 S D hK hc hσ hH t m hU, htrace, hq, herr,
    hUI, hlim.1, hlim.2.1, hlim.2.2⟩

theorem spectralBasis_zero_LIP016 {d : ℕ} (S : Spec d) (A : Aux S) :
    spectralBasis_LIP016 S 0 = Lp.const 2 (specProbability_LIP016 S : Measure (Torus d)) (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [spectralBasis_ae_LIP016 S 0,
    Lp.coeFn_const (E := ℝ) (p := 2)
      (μ := (specProbability_LIP016 S : Measure (Torus d))) (1 : ℝ)] with x hx he
  rw [hx, he]
  exact A.v0 x

theorem kernelCompression_mem_centered_LIP016 {d : ℕ} (S : Spec d) (A : Aux S) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    (f : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    kernelCompression_LIP016 S D hK t m f ∈ DGPS.centeredL2 (specProbability_LIP016 S) := by
  rw [DGPS.mem_centeredL2, ← DGPS.inner_const_one, ← spectralBasis_zero_LIP016 S A,
    kernelCompression_apply_LIP016 S D hK hc]
  simp only [inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp (spectralBasis_LIP016 S).orthonormal]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : i = 0
  · subst i
    rw [kernelCoefficient_zero_left_LIP016 S D A.v0 hc, zero_mul, zero_mul]
  · simp only [Ne.symm hi, ite_false, mul_zero]

theorem kernelCovariance_mem_centered_LIP016 {d : ℕ} (S : Spec d) (A : Aux S) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    (hu : IsUnit (1 + kernelCompression_LIP016 S D hK t m))
    (g : DGPS.centeredL2 (specProbability_LIP016 S)) :
    Ring.inverse (1 + kernelCompression_LIP016 S D hK t m)
      (g : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) ∈
        DGPS.centeredL2 (specProbability_LIP016 S) := by
  let T := kernelCompression_LIP016 S D hK t m
  let C := Ring.inverse (1 + T)
  let g0 : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) := g
  have he : C g0 + T (C g0) = g0 := by
    have h := congrArg (fun L => L g0) (Ring.mul_inverse_cancel (1 + T) hu)
    simpa only [mul_apply_eq_comp, add_apply, one_apply_eq_self] using h
  have hf : C g0 = g0 - T (C g0) := eq_sub_of_add_eq he
  change C g0 ∈ DGPS.centeredL2 (specProbability_LIP016 S)
  rw [hf]
  exact (DGPS.centeredL2 (specProbability_LIP016 S)).sub_mem g.property
    (kernelCompression_mem_centered_LIP016 S A D hK hc t m _)

noncomputable def centeredCovarianceApprox_LIP016 {d : ℕ} (S : Spec d) (A : Aux S) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    (hu : IsUnit (1 + kernelCompression_LIP016 S D hK t m)) :
    DGPS.centeredL2 (specProbability_LIP016 S) →L[ℝ]
      DGPS.centeredL2 (specProbability_LIP016 S) :=
  ((Ring.inverse (1 + kernelCompression_LIP016 S D hK t m)).comp
    (DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL).codRestrict
      (DGPS.centeredL2 (specProbability_LIP016 S))
      (fun g => kernelCovariance_mem_centered_LIP016 S A D hK hc t m hu g)

theorem centeredCovarianceApprox_inclusion_LIP016 {d : ℕ} (S : Spec d) (A : Aux S) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    (hu : IsUnit (1 + kernelCompression_LIP016 S D hK t m)) :
    (DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL.comp
      (centeredCovarianceApprox_LIP016 S A D hK hc t m hu) =
        (Ring.inverse (1 + kernelCompression_LIP016 S D hK t m)).comp
          (DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL := by
  apply ContinuousLinearMap.ext
  intro g
  rfl

theorem centeredSubtype_comp_norm_LIP016 {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Submodule ℝ F) (L : E →L[ℝ] V) :
    ‖V.subtypeL.comp L‖ = ‖L‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro f
    change ‖L f‖ ≤ ‖L‖ * ‖f‖
    exact L.le_opNorm f
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (V.subtypeL.comp L))
    intro f
    change ‖(V.subtypeL.comp L) f‖ ≤ ‖V.subtypeL.comp L‖ * ‖f‖
    exact (V.subtypeL.comp L).le_opNorm f

theorem centeredSubtype_tendsto_iff_LIP016 {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Submodule ℝ F) (L : ℕ → E →L[ℝ] V) (M : E →L[ℝ] V) :
    Tendsto L atTop (𝓝 M) ↔
      Tendsto (fun R => V.subtypeL.comp (L R)) atTop (𝓝 (V.subtypeL.comp M)) := by
  have hd (R : ℕ) :
      ‖V.subtypeL.comp (L R) - V.subtypeL.comp M‖ = ‖L R - M‖ := by
    have he : V.subtypeL.comp (L R) - V.subtypeL.comp M = V.subtypeL.comp (L R - M) := by
      ext f
      rfl
    rw [he, centeredSubtype_comp_norm_LIP016]
  constructor
  · intro h
    have hc : Continuous (fun N : E →L[ℝ] V => V.subtypeL.comp N) :=
      continuous_id.const_clm_comp V.subtypeL
    simpa only [Function.comp_def] using (hc.tendsto M).comp h
  · intro h
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    refine (tendsto_iff_norm_sub_tendsto_zero (f := L) (b := M)).mpr ?_
    simpa only [hd] using h

theorem original_kernel_symmetric_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (J : InteractionData d)
    (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y) :
    ∀ x y, D.K x y = D.K y x := fun x y =>
  (hD x y).trans ((DGPS.centeredKernel_symm J (specProbability_LIP016 S) x y).trans
    (hD y x).symm)

theorem original_kernel_centered_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (J : InteractionData d)
    (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y) :
    ∀ y, ∫ x, D.K x y ∂S.mu = 0 := by
  intro y
  simp_rw [hD]
  exact DGPS.integral_centeredKernel_left J (specProbability_LIP016 S) y


/-- The unit-modulus phase used in every finite Gaussian test. -/
noncomputable def gaussianPhase_LIP016 (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))

theorem gaussianPhase_norm_LIP016 (x : ℝ) : ‖gaussianPhase_LIP016 x‖ = 1 := by
  simp only [gaussianPhase_LIP016, Complex.norm_exp, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.exp_zero]

theorem phase_mul_integrable_LIP016 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Measurable g) :
    Integrable (fun x => gaussianPhase_LIP016 (g x) * (f x : ℂ)) μ := by
  apply hf.ofReal.bdd_mul
  · apply Measurable.aestronglyMeasurable
    unfold gaussianPhase_LIP016
    fun_prop
  · exact Eventually.of_forall fun x => (gaussianPhase_norm_LIP016 (g x)).le

/-- The scalar Gaussian quadratic tilt characteristic function. Its common complex
Fourier prefactor is identified at the zero test using the real normalizer. -/
theorem gaussian_scalar_characteristic_LIP016 {a : ℝ} (ha : 0 < 1 + a) (u : ℝ) :
    (∫ x : ℝ, gaussianPhase_LIP016 (u * x) *
      (Real.exp (-a * x ^ 2 / 2) : ℂ) ∂gaussianReal 0 1) =
      (Real.sqrt ((1 + a)⁻¹) : ℂ) *
        Complex.exp ((-(u ^ 2 / (2 * (1 + a))) : ℝ) : ℂ) := by
  let b : ℝ := (1 + a) / 2
  let d : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  let P : ℂ := (d : ℂ) * (Real.pi / (b : ℂ)) ^ (1 / 2 : ℂ)
  have hb : 0 < b := by dsimp only [b]; linarith
  have hfun (x : ℝ) :
      gaussianPDFReal 0 1 x * Real.exp (-a * x ^ 2 / 2) =
        d * Real.exp (-b * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    dsimp only [b]
    ring
  have hcast (x : ℝ) :
      (gaussianPDFReal 0 1 x : ℂ) * (Real.exp (-a * x ^ 2 / 2) : ℂ) =
        (d : ℂ) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
    have h := congrArg Complex.ofReal (hfun x)
    simpa only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_pow, neg_mul] using h
  have hphase (v x : ℝ) : gaussianPhase_LIP016 (v * x) =
      Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) := by
    simp only [gaussianPhase_LIP016, Complex.ofReal_mul, mul_assoc]
  have hcalc (v : ℝ) :
      (∫ x : ℝ, gaussianPhase_LIP016 (v * x) *
        (Real.exp (-a * x ^ 2 / 2) : ℂ) ∂gaussianReal 0 1) =
          P * Complex.exp (-(v : ℂ) ^ 2 / (4 * (b : ℂ))) := by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    have he :
        (fun x : ℝ => gaussianPDFReal 0 1 x •
          (gaussianPhase_LIP016 (v * x) * (Real.exp (-a * x ^ 2 / 2) : ℂ))) =
        fun x : ℝ => (d : ℂ) *
          (Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
            Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)) := by
      funext x
      rw [Complex.real_smul]
      calc
        _ = gaussianPhase_LIP016 (v * x) *
            ((gaussianPDFReal 0 1 x : ℂ) * (Real.exp (-a * x ^ 2 / 2) : ℂ)) := by ring
        _ = _ := by rw [hcast, hphase]; ring
    rw [he, integral_const_mul, fourierIntegral_gaussian (by simpa using hb) (v : ℂ)]
    dsimp only [P]
    ring
  have hP : P = (Real.sqrt ((1 + a)⁻¹) : ℂ) := by
    have hzero := hcalc 0
    simp only [zero_mul, gaussianPhase_LIP016, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul, zero_pow (show (2 : ℕ) ≠ 0 by decide), neg_zero,
      zero_div, mul_one, integral_complex_ofReal,
      (gaussian_scalar_normalizer_LIP016 ha).2] at hzero
    exact hzero.symm
  have hdenom : (4 : ℂ) * (b : ℂ) = ((2 * (1 + a) : ℝ) : ℂ) := by
    dsimp only [b]
    push_cast
    ring
  rw [hcalc u, hP, hdenom]
  congr 2
  push_cast
  ring


theorem gaussian_diagonal_characteristic_LIP016 {ι : Type*} [Fintype ι]
    (a u : ι → ℝ) (ha : ∀ i, 0 < 1 + a i) :
    (∫ z : ι → ℝ, gaussianPhase_LIP016 (∑ i, u i * z i) *
      (Real.exp (∑ i, -(a i * z i ^ 2) / 2) : ℂ)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ((∏ i, Real.sqrt ((1 + a i)⁻¹) : ℝ) : ℂ) *
        Complex.exp ((-(∑ i, u i ^ 2 / (1 + a i)) / 2 : ℝ) : ℂ) := by
  have he (z : ι → ℝ) :
      gaussianPhase_LIP016 (∑ i, u i * z i) *
        (Real.exp (∑ i, -(a i * z i ^ 2) / 2) : ℂ) =
      ∏ i, gaussianPhase_LIP016 (u i * z i) *
        (Real.exp (-(a i * z i ^ 2) / 2) : ℂ) := by
    simp only [gaussianPhase_LIP016, Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum, Real.exp_sum, Complex.ofReal_prod, Finset.prod_mul_distrib]
  rw [show (fun z : ι → ℝ => gaussianPhase_LIP016 (∑ i, u i * z i) *
      (Real.exp (∑ i, -(a i * z i ^ 2) / 2) : ℂ)) =
    (fun z : ι → ℝ => ∏ i, gaussianPhase_LIP016 (u i * z i) *
      (Real.exp (-(a i * z i ^ 2) / 2) : ℂ)) from funext he]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) =>
    gaussianPhase_LIP016 (u i * x) * (Real.exp (-(a i * x ^ 2) / 2) : ℂ))]
  have hs (i : ι) :
      (∫ x : ℝ, gaussianPhase_LIP016 (u i * x) *
        (Real.exp (-(a i * x ^ 2) / 2) : ℂ) ∂gaussianReal 0 1) =
      (Real.sqrt ((1 + a i)⁻¹) : ℂ) *
        Complex.exp ((-(u i ^ 2 / (2 * (1 + a i))) : ℝ) : ℂ) := by
    simpa only [neg_mul] using gaussian_scalar_characteristic_LIP016 (ha i) (u i)
  simp_rw [hs]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Complex.exp_sum]
  congr 2
  rw [← Complex.ofReal_sum]
  congr 1
  have hd (i : ι) : -(u i ^ 2 / (2 * (1 + a i))) = -(u i ^ 2 / (1 + a i)) / 2 := by
    rw [mul_comm (2 : ℝ) (1 + a i), div_mul_eq_div_div]
    ring
  simp_rw [hd]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- Finite-dimensional Gaussian CF formula in a genuine eigenbasis, without an
assumed tilted law. The exponent is left as its explicit spectral sum. -/
theorem gaussian_characteristic_eigenbasis_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) (a : ι → ℝ)
    (hdiag : ∀ i, T (b i) = a i • b i) (ha : ∀ i, 0 < 1 + a i) (u : E) :
    (∫ z : E, gaussianPhase_LIP016 ⟪u, z⟫_ℝ *
      (Real.exp (-⟪z, T z⟫_ℝ / 2) : ℂ) ∂stdGaussian E) =
      (((∫ z : E, Real.exp (-⟪z, T z⟫_ℝ / 2) ∂stdGaussian E : ℝ)) : ℂ) *
        Complex.exp ((-(∑ i, ⟪b i, u⟫_ℝ ^ 2 / (1 + a i)) / 2 : ℝ) : ℂ) := by
  rw [gaussian_normalizer_eigenbasis_LIP016 b T a hdiag ha]
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, integral_map
    (show AEMeasurable (fun x : ι → ℝ => ∑ i, x i • b i)
      (Measure.pi fun _ : ι => gaussianReal 0 1) from
      (show Continuous (fun x : ι → ℝ => ∑ i, x i • b i) by fun_prop).measurable.aemeasurable)
    (by unfold gaussianPhase_LIP016; fun_prop)]
  convert gaussian_diagonal_characteristic_LIP016 a (fun i => ⟪b i, u⟫_ℝ) ha using 1
  congr 1
  funext z
  have hp : ⟪u, ∑ i, z i • b i⟫_ℝ = ∑ i, ⟪b i, u⟫_ℝ * z i := by
    simp only [inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]; ring
  rw [hp, eigenbasis_quadratic_LIP016 b T a hdiag]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]


/-- Multiplication by a fixed unit-modulus cylinder phase preserves the L1 error.
Thus the already proved real-density Vitali limit also controls CF numerators. -/
theorem complex_phase_integral_tendsto_LIP016 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (φ : Ω → ℂ)
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hφ : AEStronglyMeasurable φ μ) (hφnorm : ∀ x, ‖φ x‖ = 1)
    (hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, φ x * (f n x : ℂ) ∂μ) atTop
      (𝓝 (∫ x, φ x * (g x : ℂ) ∂μ)) := by
  have hF (n : ℕ) : Integrable (fun x => φ x * (f n x : ℂ)) μ :=
    (hf n).ofReal.bdd_mul hφ (Eventually.of_forall fun x => (hφnorm x).le)
  have hG : Integrable (fun x => φ x * (g x : ℂ)) μ :=
    hg.ofReal.bdd_mul hφ (Eventually.of_forall fun x => (hφnorm x).le)
  have hn (n : ℕ) :
      eLpNorm ((fun x => φ x * (f n x : ℂ)) - (fun x => φ x * (g x : ℂ))) 1 μ =
        eLpNorm (f n - g) 1 μ := by
    apply eLpNorm_congr_norm_ae ((hF n).sub hG).aestronglyMeasurable
      ((hf n).sub hg).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, ← mul_sub, norm_mul, hφnorm x, one_mul,
        ← Complex.ofReal_sub, Complex.norm_real]
  apply tendsto_integral_of_L1' (fun x => φ x * (g x : ℂ)) (Eventually.of_forall hF)
  convert hL1 using 1
  funext n
  exact hn n

/-- The existing density convergence is strengthened to its explicit L1 form for
bounded characteristic-function tests. This is derived from actual UI, not a law premise. -/
theorem exponential_tendsto_L1_LIP016 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) (q : Ω → ℝ)
    (tr : ℕ → ℝ) (d : ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hF : ∀ n, AEStronglyMeasurable (fun x => Real.exp (-(f n x + tr n) / 2)) μ)
    (hq : TendstoInMeasure μ f atTop q) (htr : Tendsto tr atTop (𝓝 d))
    (hUI : UniformIntegrable (fun n x => Real.exp (-(f n x + tr n) / 2)) 1 μ) :
    Tendsto (fun n => eLpNorm
      ((fun x => Real.exp (-(f n x + tr n) / 2)) -
        (fun x => Real.exp (-(q x + d) / 2))) 1 μ) atTop (𝓝 0) := by
  have hc := exponential_tendstoInMeasure_LIP016 μ f q tr d hf hF hq htr
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by simp) hF
    (hUI.memLp_of_tendstoInMeasure hc) hUI.1 hc


/-- The actual normalized limiting Wick tilt on the sequence space. This definition
does not assert a Gaussian measure on the infinite-dimensional L² state space. -/
noncomputable def wickTiltMeasure_LIP016 (q : Lp ℝ 2 gaussianCountable_LIP016) (d : ℝ) :
    Measure (ℕ → ℝ) :=
  gaussianCountable_LIP016.withDensity (fun z => ENNReal.ofReal
    (Real.exp (-(q z + d) / 2) /
      ∫ x, Real.exp (-(q x + d) / 2) ∂gaussianCountable_LIP016))

theorem wickTilt_isProbability_LIP016 (q : Lp ℝ 2 gaussianCountable_LIP016) (d : ℝ)
    (hi : Integrable (fun z => Real.exp (-(q z + d) / 2)) gaussianCountable_LIP016)
    (hZ : 0 < ∫ z, Real.exp (-(q z + d) / 2) ∂gaussianCountable_LIP016) :
    IsProbabilityMeasure (wickTiltMeasure_LIP016 q d) := by
  let Z := ∫ z, Real.exp (-(q z + d) / 2) ∂gaussianCountable_LIP016
  have hnormalized : Integrable (fun z => Real.exp (-(q z + d) / 2) / Z)
      gaussianCountable_LIP016 := hi.div_const Z
  have hnn : 0 ≤ᵐ[gaussianCountable_LIP016]
      (fun z => Real.exp (-(q z + d) / 2) / Z) :=
    Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hZ.le
  constructor
  rw [wickTiltMeasure_LIP016, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hnormalized hnn, integral_div]
  change ENNReal.ofReal (Z / Z) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]

theorem wickTilt_integral_LIP016 (q : Lp ℝ 2 gaussianCountable_LIP016) (d : ℝ)
    (hi : Integrable (fun z => Real.exp (-(q z + d) / 2)) gaussianCountable_LIP016)
    (hZ : 0 < ∫ z, Real.exp (-(q z + d) / 2) ∂gaussianCountable_LIP016)
    (φ : (ℕ → ℝ) → ℂ) :
    (∫ z, φ z ∂wickTiltMeasure_LIP016 q d) =
      (∫ z, φ z * (Real.exp (-(q z + d) / 2) : ℂ) ∂gaussianCountable_LIP016) /
        ((∫ z, Real.exp (-(q z + d) / 2) ∂gaussianCountable_LIP016 : ℝ) : ℂ) := by
  let Z := ∫ z, Real.exp (-(q z + d) / 2) ∂gaussianCountable_LIP016
  have hnormalized : Integrable (fun z => Real.exp (-(q z + d) / 2) / Z)
      gaussianCountable_LIP016 := hi.div_const Z
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (-(q z + d) / 2) / Z))
      gaussianCountable_LIP016 :=
    (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      hnormalized.aestronglyMeasurable).aemeasurable
  rw [wickTiltMeasure_LIP016,
    integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ]
  have hreal (z : ℕ → ℝ) :
      (ENNReal.ofReal (Real.exp (-(q z + d) / 2) / Z)).toReal =
        Real.exp (-(q z + d) / 2) / Z :=
    ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le)
  simp_rw [hreal, Complex.real_smul]
  calc
    _ = ∫ z, (φ z * (Real.exp (-(q z + d) / 2) : ℂ)) / (Z : ℂ)
        ∂gaussianCountable_LIP016 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by push_cast; ring
    _ = _ := integral_div _ _


/-- Full-space symmetry follows by the same integrable kernel swap as on H0. -/
theorem kernelOp_symmetric_LIP016 {d : ℕ} (J : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    (DGPS.kernelOp J μ : Lp ℝ 2 (μ : Measure (Torus d)) →ₗ[ℝ]
      Lp ℝ 2 (μ : Measure (Torus d))).IsSymmetric := by
  intro f g
  simp only [ContinuousLinearMap.coe_coe]
  rw [real_inner_comm, DGPS.inner_kernelOp, DGPS.inner_kernelOp]
  rw [← integral_prod_swap]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [DGPS.centeredKernel_symm J μ p.2 p.1]
    ring

theorem inverse_symmetric_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (H : E →L[ℝ] E) (hu : IsUnit H)
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric) :
    ((Ring.inverse H : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
  let C := Ring.inverse H
  have hHC (x : E) : H (C x) = x := by
    have h := congrArg (fun L : E →L[ℝ] E => L x) (Ring.mul_inverse_cancel H hu)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  intro f g
  change ⟪C f, g⟫_ℝ = ⟪f, C g⟫_ℝ
  calc
    _ = ⟪C f, H (C g)⟫_ℝ := by rw [hHC]
    _ = ⟪H (C f), C g⟫_ℝ := (hH.apply_clm (C f) (C g)).symm
    _ = _ := by rw [hHC]

theorem inverse_quadratic_nonneg_LIP016 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (H : E →L[ℝ] E) (hu : IsUnit H)
    (hH : ∀ f, 0 ≤ ⟪f, H f⟫_ℝ) (f : E) :
    0 ≤ ⟪f, Ring.inverse H f⟫_ℝ := by
  have he : H (Ring.inverse H f) = f := by
    have h := congrArg (fun L : E →L[ℝ] E => L f) (Ring.mul_inverse_cancel H hu)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have h := hH (Ring.inverse H f)
  rw [he, real_inner_comm] at h
  exact h

theorem originalCovariance_symmetric_nonneg_LIP016 {d : ℕ} (J : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 μ,
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J μ g⟫_ℝ) :
    (((Ring.inverse (1 + DGPS.kernelOp J μ) :
      Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)))) :
      Lp ℝ 2 (μ : Measure (Torus d)) →ₗ[ℝ] Lp ℝ 2 (μ : Measure (Torus d))).IsSymmetric ∧
      ∀ f, 0 ≤ ⟪f, Ring.inverse (1 + DGPS.kernelOp J μ) f⟫_ℝ := by
  let H := 1 + DGPS.kernelOp J μ
  have hc (f : Lp ℝ 2 (μ : Measure (Torus d))) :
      min 1 σ * ‖f‖ ^ 2 ≤ ⟪f, H f⟫_ℝ := by
    simpa only [H, add_apply, one_apply_eq_self, inner_add_right,
      real_inner_self_eq_norm_sq] using centered_coercivity_full_LIP016 J μ hH f
  have ha : 0 < min 1 σ := lt_min zero_lt_one hσ
  have hu : IsUnit H := isUnit_of_coercive_LIP016 H ha hc
  have hs : (H : Lp ℝ 2 (μ : Measure (Torus d)) →ₗ[ℝ]
      Lp ℝ 2 (μ : Measure (Torus d))).IsSymmetric := by
    intro f g
    have h := (kernelOp_symmetric_LIP016 J μ).apply_clm f g
    simpa only [H, ContinuousLinearMap.coe_coe, add_apply, one_apply_eq_self, inner_add_left,
      inner_add_right] using
      congrArg (fun r : ℝ => ⟪f, g⟫_ℝ + r) h
  exact ⟨inverse_symmetric_LIP016 H hu hs, fun f =>
    inverse_quadratic_nonneg_LIP016 H hu
      (fun g => (mul_nonneg ha.le (sq_nonneg ‖g‖)).trans (hc g)) f⟩

/-- Inverse action on an actual eigenvector; no finite inverse construction is needed. -/
theorem inverse_one_add_eigen_LIP016 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : E →L[ℝ] E) (hu : IsUnit (1 + A))
    (w : E) (a : ℝ) (heig : A w = a • w) (ha : 1 + a ≠ 0) :
    Ring.inverse (1 + A) w = (1 + a)⁻¹ • w := by
  have hm : (1 + a)⁻¹ + (1 + a)⁻¹ * a = 1 := by field_simp [ha]
  have hw : (1 + A) ((1 + a)⁻¹ • w) = w := by
    simp only [add_apply, one_apply_eq_self, map_smul, heig, smul_smul, smul_add]
    rw [← add_smul, hm, one_smul]
  calc
    _ = Ring.inverse (1 + A) ((1 + A) ((1 + a)⁻¹ • w)) :=
      congrArg (fun x : E => (Ring.inverse (1 + A)) x) hw.symm
    _ = _ := by rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu, one_apply_eq_self]

theorem orthonormal_finite_quadratic_LIP016 {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (v : ι → E) (hv : Orthonormal ℝ v)
    (T : E →L[ℝ] E) (a : ι → ℝ) (hT : ∀ i, T (v i) = a i • v i) (z : ι → ℝ) :
    ⟪∑ i, z i • v i, T (∑ i, z i • v i)⟫_ℝ = ∑ i, a i * z i ^ 2 := by
  have he : T (∑ i, z i • v i) = ∑ i, (z i * a i) • v i := by
    simp only [map_sum, map_smul, hT, smul_smul]
  rw [he]
  have h := hv.inner_sum z (fun i => z i * a i) Finset.univ
  simp only [conj_trivial] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by ring


noncomputable def finiteEmbedding_LIP016 {d : ℕ} (S : Spec d) (s : Finset ℕ) :
    EuclideanSpace ℝ s →L[ℝ] Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ∑ i : s, z i • spectralBasis_LIP016 S i
      map_add' := fun z w => by
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }

theorem finiteEmbedding_apply_LIP016 {d : ℕ} (S : Spec d) (s : Finset ℕ)
    (z : EuclideanSpace ℝ s) :
    finiteEmbedding_LIP016 S s z = ∑ i : s, z i • spectralBasis_LIP016 S i := rfl

theorem finiteBasis_orthonormal_LIP016 {d : ℕ} (S : Spec d) (s : Finset ℕ) :
    Orthonormal ℝ (fun i : s => spectralBasis_LIP016 S i) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa only [Subtype.coe_inj] using
    (orthonormal_iff_ite.mp (spectralBasis_LIP016 S).orthonormal) (i : ℕ) (j : ℕ)

theorem finiteEmbedding_inner_LIP016 {d : ℕ} (S : Spec d) (s : Finset ℕ)
    (z w : EuclideanSpace ℝ s) :
    ⟪finiteEmbedding_LIP016 S s z, finiteEmbedding_LIP016 S s w⟫_ℝ = ⟪z, w⟫_ℝ := by
  change ⟪∑ i : s, z i • spectralBasis_LIP016 S i,
    ∑ i : s, w i • spectralBasis_LIP016 S i⟫_ℝ = ⟪z, w⟫_ℝ
  rw [(finiteBasis_orthonormal_LIP016 S s).inner_sum
    (fun i => z i) (fun i => w i) Finset.univ]
  rw [PiLp.inner_apply]
  simp only [conj_trivial, RCLike.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem finiteEmbedding_norm_LIP016 {d : ℕ} (S : Spec d) (s : Finset ℕ)
    (z : EuclideanSpace ℝ s) : ‖finiteEmbedding_LIP016 S s z‖ = ‖z‖ := by
  have h := finiteEmbedding_inner_LIP016 S s z z
  simp only [real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

noncomputable def testExtension_LIP016 (s r : Finset ℕ) (u : s → ℝ) : r → ℝ :=
  fun i => if h : (i : ℕ) ∈ s then u ⟨i, h⟩ else 0

theorem testExtension_sum_LIP016 {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (v : ℕ → M) (s r : Finset ℕ) (hsr : s ⊆ r) (u : s → ℝ) :
    (∑ i : r, testExtension_LIP016 s r u i • v i) = ∑ i : s, u i • v i := by
  let a (i : ℕ) := if h : i ∈ s then u ⟨i, h⟩ else 0
  change (∑ i : r, a i • v i) = _
  rw [Finset.sum_coe_sort r (fun i => a i • v i)]
  calc
    _ = ∑ i ∈ s, a i • v i := by
      symm
      apply Finset.sum_subset hsr
      intro i _ hi
      simp only [a, dite_eq_right hi, zero_smul]
    _ = ∑ i : s, a i • v i := (Finset.sum_coe_sort s (fun i => a i • v i)).symm
    _ = _ := Finset.sum_congr rfl fun i _ => by
      simp only [a, dite_eq_left i.property]

theorem finiteEmbedding_extension_LIP016 {d : ℕ} (S : Spec d)
    (s r : Finset ℕ) (hsr : s ⊆ r) (u : s → ℝ) :
    finiteEmbedding_LIP016 S r (WithLp.toLp 2 (testExtension_LIP016 s r u)) =
      finiteEmbedding_LIP016 S s (WithLp.toLp 2 u) :=
  testExtension_sum_LIP016 (spectralBasis_LIP016 S) s r hsr u

noncomputable def cylinderPhase_LIP016 (s : Finset ℕ) (u : s → ℝ)
    (z : ℕ → ℝ) : ℂ := gaussianPhase_LIP016 (∑ i : s, u i * z i)

theorem cylinderPhase_norm_LIP016 (s : Finset ℕ) (u : s → ℝ) (z : ℕ → ℝ) :
    ‖cylinderPhase_LIP016 s u z‖ = 1 := gaussianPhase_norm_LIP016 _

theorem cylinderPhase_measurable_LIP016 (s : Finset ℕ) (u : s → ℝ) :
    Measurable (cylinderPhase_LIP016 s u) := by
  unfold cylinderPhase_LIP016 gaussianPhase_LIP016
  fun_prop

theorem cylinderPhase_extension_LIP016 (s r : Finset ℕ) (hsr : s ⊆ r)
    (u : s → ℝ) (z : ℕ → ℝ) :
    cylinderPhase_LIP016 r (testExtension_LIP016 s r u) z =
      cylinderPhase_LIP016 s u z := by
  unfold cylinderPhase_LIP016
  congr 1
  simpa only [smul_eq_mul] using testExtension_sum_LIP016 (fun i => z i) s r hsr u

noncomputable def coefficientBlock_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) (s : Finset ℕ) : Matrix s s ℝ :=
  Matrix.of fun i j => kernelCoefficient_LIP016 S D t m i j

theorem coefficientBlock_hermitian_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x) (t : ℝ) (m : ℕ) (s : Finset ℕ) :
    (coefficientBlock_LIP016 S D t m s).IsHermitian := by
  ext i j
  exact kernelCoefficient_symmetric_LIP016 S D hK t m j i


theorem kernelCompression_basis_apply_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m k : ℕ) :
    kernelCompression_LIP016 S D hK t m (spectralBasis_LIP016 S k) =
      ∑ i ∈ Finset.range (m + 1), kernelCoefficient_LIP016 S D t m i k •
        spectralBasis_LIP016 S i := by
  rw [kernelCompression_apply_LIP016 S D hK hc]
  apply Finset.sum_congr rfl
  intro i _
  simp only [orthonormal_iff_ite.mp (spectralBasis_LIP016 S).orthonormal]
  have he (j : ℕ) :
      (kernelCoefficient_LIP016 S D t m i j * (if j = k then 1 else 0)) •
        spectralBasis_LIP016 S i =
      if j = k then kernelCoefficient_LIP016 S D t m i k •
        spectralBasis_LIP016 S i else 0 := by
    split_ifs with hj
    · subst j; simp only [mul_one]
    · simp only [mul_zero, zero_smul]
  simp_rw [he]
  by_cases hk : k ∈ Finset.range (m + 1)
  · simp only [Finset.sum_ite_eq', hk, ite_true]
  · simp only [Finset.sum_ite_eq', hk, ite_false]
    rw [kernelCoefficient_support_right_LIP016 S D t m k hk i, zero_smul]

/-- Exact finite-block intertwining, including arbitrary test coordinates outside
the finite compression support. -/
theorem finiteEmbedding_intertwine_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) (t : ℝ) (m : ℕ)
    (s : Finset ℕ) (hms : Finset.range (m + 1) ⊆ s) (z : EuclideanSpace ℝ s) :
    kernelCompression_LIP016 S D hK t m (finiteEmbedding_LIP016 S s z) =
      finiteEmbedding_LIP016 S s (WithLp.toLp 2
        ((coefficientBlock_LIP016 S D t m s) *ᵥ (z : s → ℝ))) := by
  rw [finiteEmbedding_apply_LIP016, map_sum]
  simp only [map_smul, kernelCompression_basis_apply_LIP016 S D hK hc]
  have hpad (j : s) :
      (∑ i ∈ Finset.range (m + 1), kernelCoefficient_LIP016 S D t m i j •
        spectralBasis_LIP016 S i) =
      ∑ i : s, kernelCoefficient_LIP016 S D t m i j • spectralBasis_LIP016 S i := by
    rw [Finset.sum_coe_sort s (fun i => kernelCoefficient_LIP016 S D t m i j •
      spectralBasis_LIP016 S i)]
    apply Finset.sum_subset hms
    intro i _ hi
    rw [kernelCoefficient_support_left_LIP016 S D t m i hi j, zero_smul]
  simp_rw [hpad]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  change (∑ i : s, ∑ j : s,
    (z j * kernelCoefficient_LIP016 S D t m i j) • spectralBasis_LIP016 S i) =
    ∑ i : s, (∑ j : s, kernelCoefficient_LIP016 S D t m i j * z j) •
      spectralBasis_LIP016 S i
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by congr 1; ring

theorem coefficientBlock_trace_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) (s : Finset ℕ) (hms : Finset.range (m + 1) ⊆ s) :
    Matrix.trace (coefficientBlock_LIP016 S D t m s) = kernelTrace_LIP016 S D t m := by
  simp only [coefficientBlock_LIP016, Matrix.trace, Matrix.diag_apply, Matrix.of_apply,
    kernelTrace_LIP016]
  rw [Finset.sum_coe_sort s (fun i => kernelCoefficient_LIP016 S D t m i i)]
  symm
  apply Finset.sum_subset hms
  intro i _ hi
  exact kernelCoefficient_support_left_LIP016 S D t m i hi i

theorem kernelRawGaussian_block_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℝ) (m : ℕ) (s : Finset ℕ) (hms : Finset.range (m + 1) ⊆ s)
    (z : ℕ → ℝ) :
    kernelRawGaussian_LIP016 S D t m z =
      Real.exp (-matrixQuadratic_LIP016 (coefficientBlock_LIP016 S D t m s)
        (s.restrict z) / 2) := by
  have hpad := finiteWickOn_padding_LIP016 (kernelCoefficient_LIP016 S D t m)
    (Finset.range (m + 1)) s hms
    (kernelCoefficient_support_left_LIP016 S D t m)
    (kernelCoefficient_support_right_LIP016 S D t m) z
  unfold kernelRawGaussian_LIP016
  rw [← hpad]
  change Real.exp (-(matrixWick_LIP016 (coefficientBlock_LIP016 S D t m s)
    (s.restrict z) + kernelTrace_LIP016 S D t m) / 2) = _
  rw [matrixWick_LIP016, coefficientBlock_trace_LIP016 S D t m s hms, sub_add_cancel]


/-- The spectral CF exponent is the quadratic form of the already constructed
full-space inverse. The finite window may contain arbitrary additional test coordinates. -/
theorem coefficientBlock_resolvent_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (s : Finset ℕ)
    (hms : Finset.range (m + 1) ⊆ s) :
    let hB := coefficientBlock_hermitian_LIP016 S D hK t m s
    (∀ i, 0 < 1 + hB.eigenvalues i) ∧
      ∀ u : EuclideanSpace ℝ s,
        ⟪finiteEmbedding_LIP016 S s u,
          Ring.inverse (1 + kernelCompression_LIP016 S D hK t m)
            (finiteEmbedding_LIP016 S s u)⟫_ℝ =
        ∑ i, ⟪hB.eigenvectorBasis i, u⟫_ℝ ^ 2 / (1 + hB.eigenvalues i) := by
  dsimp only
  let B := coefficientBlock_LIP016 S D t m s
  let hB := coefficientBlock_hermitian_LIP016 S D hK t m s
  let b := hB.eigenvectorBasis
  let T := kernelCompression_LIP016 S D hK t m
  let C := Ring.inverse (1 + T)
  have heig (i : s) : T (finiteEmbedding_LIP016 S s (b i)) =
      hB.eigenvalues i • finiteEmbedding_LIP016 S s (b i) := by
    have hv :
        WithLp.toLp 2 (B *ᵥ (b i : s → ℝ)) = hB.eigenvalues i • b i := by
      ext j
      change (B *ᵥ (b i : s → ℝ)) j = hB.eigenvalues i * b i j
      simpa only [b, Pi.smul_apply, smul_eq_mul] using
        congrFun (hB.mulVec_eigenvectorBasis i) j
    rw [finiteEmbedding_intertwine_LIP016 S D hK hc t m s hms, hv, map_smul]
  have hnorm (i : s) : ‖finiteEmbedding_LIP016 S s (b i)‖ = 1 := by
    rw [finiteEmbedding_norm_LIP016]
    exact b.orthonormal.1 i
  have hpos (i : s) : 0 < 1 + hB.eigenvalues i := by
    have h := kernelCompression_coercive_LIP016 S D hK hH ht m
      (finiteEmbedding_LIP016 S s (b i))
    rw [heig, inner_smul_right, real_inner_self_eq_norm_sq, hnorm, one_pow, mul_one, mul_one] at h
    exact lt_of_lt_of_le (lt_min zero_lt_one hσ) h
  have hu : IsUnit (1 + T) := kernelCompression_isUnit_LIP016 S D hK hσ hH ht m
  have hinv (i : s) : C (finiteEmbedding_LIP016 S s (b i)) =
      (1 + hB.eigenvalues i)⁻¹ • finiteEmbedding_LIP016 S s (b i) :=
    inverse_one_add_eigen_LIP016 T hu _ _ (heig i) (hpos i).ne'
  have hv : Orthonormal ℝ (fun i : s => finiteEmbedding_LIP016 S s (b i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [finiteEmbedding_inner_LIP016]
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  refine ⟨hpos, fun u => ?_⟩
  have hexpand :
      (∑ i : s, ⟪b i, u⟫_ℝ • finiteEmbedding_LIP016 S s (b i)) =
        finiteEmbedding_LIP016 S s u := by
    have h := congrArg (fun z : EuclideanSpace ℝ s => finiteEmbedding_LIP016 S s z)
      (b.sum_repr' u)
    simpa only [map_sum, map_smul] using h
  rw [← hexpand]
  have h := orthonormal_finite_quadratic_LIP016
    (fun i : s => finiteEmbedding_LIP016 S s (b i)) hv C
    (fun i => (1 + hB.eigenvalues i)⁻¹) hinv (fun i => ⟪b i, u⟫_ℝ)
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem euclidean_inner_sum_LIP016 {ι : Type*} [Fintype ι] (u z : ι → ℝ) :
    ⟪WithLp.toLp 2 u, WithLp.toLp 2 z⟫_ℝ = ∑ i, u i * z i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A finite symmetric-matrix CF on the fixed canonical coordinates. -/
theorem gaussian_matrix_characteristic_LIP016 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (ha : ∀ i, 0 < 1 + hB.eigenvalues i)
    (u : ι → ℝ) :
    (∫ z : ι → ℝ, gaussianPhase_LIP016 (∑ i, u i * z i) *
      (Real.exp (-matrixQuadratic_LIP016 B z / 2) : ℂ)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ((∫ z : ι → ℝ, Real.exp (-matrixQuadratic_LIP016 B z / 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) : ℝ) : ℂ) *
      Complex.exp ((-(∑ i, ⟪hB.eigenvectorBasis i, WithLp.toLp 2 u⟫_ℝ ^ 2 /
        (1 + hB.eigenvalues i)) / 2 : ℝ) : ℂ) := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)
  have heig (i : ι) : T (hB.eigenvectorBasis i) =
      hB.eigenvalues i • hB.eigenvectorBasis i := by
    ext j
    change (B *ᵥ (hB.eigenvectorBasis i : ι → ℝ)) j =
      hB.eigenvalues i * hB.eigenvectorBasis i j
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (hB.mulVec_eigenvectorBasis i) j
  have hnum :
      (∫ z : ι → ℝ, gaussianPhase_LIP016 (∑ i, u i * z i) *
        (Real.exp (-matrixQuadratic_LIP016 B z / 2) : ℂ)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ z : EuclideanSpace ℝ ι, gaussianPhase_LIP016 ⟪WithLp.toLp 2 u, z⟫_ℝ *
        (Real.exp (-⟪z, T z⟫_ℝ / 2) : ℂ) ∂stdGaussian (EuclideanSpace ℝ ι) := by
    rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop)
      (by unfold gaussianPhase_LIP016; fun_prop)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [T, euclidean_inner_sum_LIP016, matrixQuadratic_inner_LIP016]
  have hZ :
      (∫ z : ι → ℝ, Real.exp (-matrixQuadratic_LIP016 B z / 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      ∫ z : EuclideanSpace ℝ ι, Real.exp (-⟪z, T z⟫_ℝ / 2)
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
    rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [T, matrixQuadratic_inner_LIP016]
  rw [hnum, hZ]
  exact gaussian_characteristic_eigenbasis_LIP016 hB.eigenvectorBasis T
    hB.eigenvalues heig ha (WithLp.toLp 2 u)


/-- The genuine finite-rank tilted Gaussian numerator on the one countable product.
The enlarged window retains every requested test coordinate. -/
theorem kernelRawGaussian_characteristic_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (s : Finset ℕ) (u : s → ℝ) :
    (∫ z, cylinderPhase_LIP016 s u z * (kernelRawGaussian_LIP016 S D t m z : ℂ)
      ∂gaussianCountable_LIP016) =
      ((∫ z, kernelRawGaussian_LIP016 S D t m z ∂gaussianCountable_LIP016 : ℝ) : ℂ) *
      Complex.exp ((-⟪finiteEmbedding_LIP016 S s (WithLp.toLp 2 u),
        Ring.inverse (1 + kernelCompression_LIP016 S D hK t m)
          (finiteEmbedding_LIP016 S s (WithLp.toLp 2 u))⟫_ℝ / 2 : ℝ) : ℂ) := by
  let r := s ∪ Finset.range (m + 1)
  have hsr : s ⊆ r := Finset.subset_union_left
  have hmr : Finset.range (m + 1) ⊆ r := Finset.subset_union_right
  let B := coefficientBlock_LIP016 S D t m r
  let hB := coefficientBlock_hermitian_LIP016 S D hK t m r
  let v := testExtension_LIP016 s r u
  obtain ⟨hpos, hquad⟩ := coefficientBlock_resolvent_LIP016 S D hK hc hσ hH ht m r hmr
  have hcf := gaussian_matrix_characteristic_LIP016 B hB hpos v
  have hp : MeasurePreserving r.restrict gaussianCountable_LIP016
      (Measure.pi fun _ : r => gaussianReal 0 1) :=
    ⟨Finset.measurable_restrict r, Measure.infinitePi_map_restrict _⟩
  have hNm : Measurable (fun z : r → ℝ => gaussianPhase_LIP016 (∑ i, v i * z i) *
      (Real.exp (-matrixQuadratic_LIP016 B z / 2) : ℂ)) := by
    unfold gaussianPhase_LIP016 matrixQuadratic_LIP016
    fun_prop
  have hZm : Measurable (fun z : r → ℝ => Real.exp (-matrixQuadratic_LIP016 B z / 2)) := by
    unfold matrixQuadratic_LIP016
    fun_prop
  have hnum :
      (∫ z : r → ℝ, gaussianPhase_LIP016 (∑ i, v i * z i) *
        (Real.exp (-matrixQuadratic_LIP016 B z / 2) : ℂ)
        ∂(Measure.pi fun _ : r => gaussianReal 0 1)) =
      ∫ z, cylinderPhase_LIP016 s u z * (kernelRawGaussian_LIP016 S D t m z : ℂ)
        ∂gaussianCountable_LIP016 := by
    rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hNm.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      have hz := kernelRawGaussian_block_LIP016 S D t m r hmr z
      change kernelRawGaussian_LIP016 S D t m z =
        Real.exp (-matrixQuadratic_LIP016 B (r.restrict z) / 2) at hz
      change cylinderPhase_LIP016 r v z *
        (Real.exp (-matrixQuadratic_LIP016 B (r.restrict z) / 2) : ℂ) = _
      rw [← hz, cylinderPhase_extension_LIP016 s r hsr u]
  have hZ :
      (∫ z : r → ℝ, Real.exp (-matrixQuadratic_LIP016 B z / 2)
        ∂(Measure.pi fun _ : r => gaussianReal 0 1)) =
      ∫ z, kernelRawGaussian_LIP016 S D t m z ∂gaussianCountable_LIP016 := by
    rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hZm.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun z =>
      (kernelRawGaussian_block_LIP016 S D t m r hmr z).symm
  rw [hnum, hZ, ← hquad (WithLp.toLp 2 v)] at hcf
  simpa only [v, finiteEmbedding_extension_LIP016 S s r hsr u] using hcf


theorem kernelRawGaussian_tendsto_L1_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (q : Lp ℝ 2 gaussianCountable_LIP016) (v : ℝ)
    (hq : Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R)) atTop (𝓝 q))
    (htrace : Tendsto (fun R => kernelTrace_LIP016 S D (t R) (m R)) atTop (𝓝 v))
    (hUI : UniformIntegrable (fun R => kernelRawGaussian_LIP016 S D (t R) (m R)) 1
      gaussianCountable_LIP016) :
    Tendsto (fun R => eLpNorm (kernelRawGaussian_LIP016 S D (t R) (m R) -
      (fun z => Real.exp (-(q z + v) / 2))) 1 gaussianCountable_LIP016)
      atTop (𝓝 0) := by
  let f (R : ℕ) := finiteWickOn_LIP016 (kernelCoefficient_LIP016 S D (t R) (m R))
    (Finset.range (m R + 1))
  have hf (R : ℕ) : MemLp (f R) 2 gaussianCountable_LIP016 :=
    finiteWickOn_memLp_LIP016 _ _
  have hAE (R : ℕ) :
      (kernelWickLp_LIP016 S D (t R) (m R) : (ℕ → ℝ) → ℝ) =ᵐ[gaussianCountable_LIP016] f R :=
    (hf R).coeFn_toLp
  have hqm : TendstoInMeasure gaussianCountable_LIP016 f atTop q :=
    TendstoInMeasure.congr_left hAE (tendstoInMeasure_of_tendsto_Lp hq)
  have hFm (R : ℕ) : AEStronglyMeasurable
      (fun z => Real.exp (-(f R z + kernelTrace_LIP016 S D (t R) (m R)) / 2))
      gaussianCountable_LIP016 := by
    apply Measurable.aestronglyMeasurable
    unfold f finiteWickOn_LIP016 matrixWick_LIP016 matrixQuadratic_LIP016 Finset.restrict
    fun_prop
  exact exponential_tendsto_L1_LIP016 gaussianCountable_LIP016 f q
    (fun R => kernelTrace_LIP016 S D (t R) (m R)) v
    (fun R => (hf R).aestronglyMeasurable) hFm hqm htrace hUI

/-- The limiting CF numerator is computed from actual finite Gaussian numerators,
actual density L1 convergence and the actual operator resolvent limit. -/
theorem kernelWick_characteristic_limit_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (q : Lp ℝ 2 gaussianCountable_LIP016) (v : ℝ)
    (hq : Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R)) atTop (𝓝 q))
    (htrace : Tendsto (fun R => kernelTrace_LIP016 S D (t R) (m R)) atTop (𝓝 v))
    (hUI : UniformIntegrable (fun R => kernelRawGaussian_LIP016 S D (t R) (m R)) 1
      gaussianCountable_LIP016)
    (hi : Integrable (fun z => Real.exp (-(q z + v) / 2)) gaussianCountable_LIP016)
    (hcov : Tendsto (fun R => Ring.inverse (1 + kernelCompression_LIP016 S D hK (t R) (m R)))
      atTop (𝓝 (Ring.inverse (1 + kernelOperator_LIP016 S D hK)))) :
    ∀ (s : Finset ℕ) (u : s → ℝ),
      (∫ z, cylinderPhase_LIP016 s u z * (Real.exp (-(q z + v) / 2) : ℂ)
        ∂gaussianCountable_LIP016) =
        ((∫ z, Real.exp (-(q z + v) / 2) ∂gaussianCountable_LIP016 : ℝ) : ℂ) *
        Complex.exp ((-⟪finiteEmbedding_LIP016 S s (WithLp.toLp 2 u),
          Ring.inverse (1 + kernelOperator_LIP016 S D hK)
            (finiteEmbedding_LIP016 S s (WithLp.toLp 2 u))⟫_ℝ / 2 : ℝ) : ℂ) := by
  intro s u
  let f := finiteEmbedding_LIP016 S s (WithLp.toLp 2 u)
  have hfi (R : ℕ) : Integrable (kernelRawGaussian_LIP016 S D (t R) (m R))
      gaussianCountable_LIP016 := memLp_one_iff_integrable.mp (hUI.memLp R)
  have hL1 := kernelRawGaussian_tendsto_L1_LIP016 S D t m q v hq htrace hUI
  have hnum := complex_phase_integral_tendsto_LIP016 gaussianCountable_LIP016
    (fun R => kernelRawGaussian_LIP016 S D (t R) (m R))
    (fun z => Real.exp (-(q z + v) / 2)) (cylinderPhase_LIP016 s u)
    hfi hi (cylinderPhase_measurable_LIP016 s u).aestronglyMeasurable
    (cylinderPhase_norm_LIP016 s u) hL1
  have hZ := tendsto_integral_of_L1' (fun z => Real.exp (-(q z + v) / 2))
    (Eventually.of_forall hfi) hL1
  have hZc : Tendsto
      (fun R => ((∫ z, kernelRawGaussian_LIP016 S D (t R) (m R) z
        ∂gaussianCountable_LIP016 : ℝ) : ℂ)) atTop
      (𝓝 ((∫ z, Real.exp (-(q z + v) / 2) ∂gaussianCountable_LIP016 : ℝ) : ℂ)) := by
    simpa only [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hZ
  have hcont : Continuous
      (fun L : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →L[ℝ]
          Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) => ⟪f, L f⟫_ℝ) :=
    continuous_const.inner (continuous_id.clm_apply continuous_const)
  have hvar : Tendsto
      (fun R => ⟪f, Ring.inverse (1 + kernelCompression_LIP016 S D hK (t R) (m R)) f⟫_ℝ)
      atTop (𝓝 (⟪f, Ring.inverse (1 + kernelOperator_LIP016 S D hK) f⟫_ℝ)) := by
    simpa only [Function.comp_def] using (hcont.tendsto _).comp hcov
  have hec : Continuous (fun r : ℝ => Complex.exp ((-r / 2 : ℝ) : ℂ)) := by fun_prop
  have hexp := (hec.tendsto _).comp hvar
  have hr :
      Tendsto (fun R => ∫ z, cylinderPhase_LIP016 s u z *
        (kernelRawGaussian_LIP016 S D (t R) (m R) z : ℂ) ∂gaussianCountable_LIP016) atTop
      (𝓝 (((∫ z, Real.exp (-(q z + v) / 2) ∂gaussianCountable_LIP016 : ℝ) : ℂ) *
        Complex.exp ((-⟪f, Ring.inverse (1 + kernelOperator_LIP016 S D hK) f⟫_ℝ / 2 : ℝ) : ℂ))) := by
    convert hZc.mul hexp using 1
    funext R
    exact kernelRawGaussian_characteristic_LIP016 S D hK hc hσ hH (ht R) (m R) s u
  exact tendsto_nhds_unique hnum hr


theorem kernelWick_normalized_characteristic_LIP016 {d : ℕ} (S : Spec d) (D : KData d)
    (hK : ∀ x y, D.K x y = D.K y x)
    (hc : ∀ y, ∫ x, D.K x y ∂S.mu = 0) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian (kernelInteraction_LIP016 D hK)
        (specProbability_LIP016 S) g⟫_ℝ)
    (t : ℕ → ℝ) (m : ℕ → ℕ) (ht : ∀ R, 0 ≤ t R)
    (q : Lp ℝ 2 gaussianCountable_LIP016) (v : ℝ)
    (hq : Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R)) atTop (𝓝 q))
    (htrace : Tendsto (fun R => kernelTrace_LIP016 S D (t R) (m R)) atTop (𝓝 v))
    (hUI : UniformIntegrable (fun R => kernelRawGaussian_LIP016 S D (t R) (m R)) 1
      gaussianCountable_LIP016)
    (hi : Integrable (fun z => Real.exp (-(q z + v) / 2)) gaussianCountable_LIP016)
    (hZ : 0 < ∫ z, Real.exp (-(q z + v) / 2) ∂gaussianCountable_LIP016)
    (hcov : Tendsto (fun R => Ring.inverse (1 + kernelCompression_LIP016 S D hK (t R) (m R)))
      atTop (𝓝 (Ring.inverse (1 + kernelOperator_LIP016 S D hK)))) :
    ∀ (s : Finset ℕ) (u : s → ℝ),
      (∫ z, cylinderPhase_LIP016 s u z ∂wickTiltMeasure_LIP016 q v) =
      Complex.exp ((-⟪finiteEmbedding_LIP016 S s (WithLp.toLp 2 u),
        Ring.inverse (1 + kernelOperator_LIP016 S D hK)
          (finiteEmbedding_LIP016 S s (WithLp.toLp 2 u))⟫_ℝ / 2 : ℝ) : ℂ) := by
  intro s u
  rw [wickTilt_integral_LIP016 q v hi hZ]
  rw [kernelWick_characteristic_limit_LIP016 S D hK hc hσ hH
    t m ht q v hq htrace hUI hi hcov s u]
  have hZc : ((∫ z, Real.exp (-(q z + v) / 2) ∂gaussianCountable_LIP016 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hZ.ne'
  exact mul_div_cancel_left₀ _ hZc

/-- On finite centered test combinations, the computed Gaussian CF uses the
original density covariance, rather than only an unnamed full-space inverse. -/
theorem wickTilt_original_centered_characteristic_LIP016 {d : ℕ} (S : Spec d)
    (J : InteractionData d) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J (specProbability_LIP016 S) g⟫_ℝ)
    (q : Lp ℝ 2 gaussianCountable_LIP016) (v : ℝ)
    (hCF : ∀ (s : Finset ℕ) (u : s → ℝ),
      (∫ z, cylinderPhase_LIP016 s u z ∂wickTiltMeasure_LIP016 q v) =
      Complex.exp ((-⟪finiteEmbedding_LIP016 S s (WithLp.toLp 2 u),
        Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S))
          (finiteEmbedding_LIP016 S s (WithLp.toLp 2 u))⟫_ℝ / 2 : ℝ) : ℂ))
    (s : Finset ℕ) (u : s → ℝ)
    (hg : finiteEmbedding_LIP016 S s (WithLp.toLp 2 u) ∈
      DGPS.centeredL2 (specProbability_LIP016 S)) :
    (∫ z, cylinderPhase_LIP016 s u z ∂wickTiltMeasure_LIP016 q v) =
      Complex.exp ((-⟪(⟨finiteEmbedding_LIP016 S s (WithLp.toLp 2 u), hg⟩ :
        DGPS.centeredL2 (specProbability_LIP016 S)),
        DGPS.densityCovariance J (specProbability_LIP016 S) ⟨σ, hσ, hH⟩
          ⟨finiteEmbedding_LIP016 S s (WithLp.toLp 2 u), hg⟩⟫_ℝ / 2 : ℝ) : ℂ) := by
  let g : DGPS.centeredL2 (specProbability_LIP016 S) :=
    ⟨finiteEmbedding_LIP016 S s (WithLp.toLp 2 u), hg⟩
  have he := kernelCovariance_centered_LIP016 J (specProbability_LIP016 S) hσ hH g
  have h := hCF s u
  change Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S))
      (finiteEmbedding_LIP016 S s (WithLp.toLp 2 u)) =
    (DGPS.densityCovariance J (specProbability_LIP016 S) ⟨σ, hσ, hH⟩ g :
      Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) at he
  rw [he] at h
  exact h


noncomputable def finiteCoordinateProjection_LIP016 (s : Finset ℕ)
    (z : ℕ → ℝ) : EuclideanSpace ℝ s := WithLp.toLp 2 (s.restrict z)

theorem finiteCoordinateProjection_apply_LIP016 (s : Finset ℕ)
    (z : ℕ → ℝ) (i : s) : finiteCoordinateProjection_LIP016 s z i = z i := rfl

theorem finiteCoordinateProjection_measurable_LIP016 (s : Finset ℕ) :
    Measurable (finiteCoordinateProjection_LIP016 s) := by
  exact (show Measurable (WithLp.toLp 2 : (s → ℝ) → EuclideanSpace ℝ s) by fun_prop).comp
    (Finset.measurable_restrict s)

noncomputable def finiteCovarianceForm_LIP016 {d : ℕ} (S : Spec d) (s : Finset ℕ)
    (C : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →L[ℝ]
      Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d))) :
    EuclideanSpace ℝ s →L[ℝ] EuclideanSpace ℝ s →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (finiteEmbedding_LIP016 S s) (C.comp (finiteEmbedding_LIP016 S s))

theorem finiteCovarianceForm_apply_LIP016 {d : ℕ} (S : Spec d) (s : Finset ℕ)
    (C : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →L[ℝ]
      Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)))
    (u v : EuclideanSpace ℝ s) :
    finiteCovarianceForm_LIP016 S s C u v =
      ⟪finiteEmbedding_LIP016 S s u, C (finiteEmbedding_LIP016 S s v)⟫_ℝ := rfl

/-- Characteristic-function classification only: the canonical assembly below
supplies hCF from the proved finite Gaussian formula and the L1/resolvent limit. -/
theorem wickTilt_gaussian_marginals_LIP016 {d : ℕ} (S : Spec d) (J : InteractionData d)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J (specProbability_LIP016 S) g⟫_ℝ)
    (q : Lp ℝ 2 gaussianCountable_LIP016) (v : ℝ)
    (hi : Integrable (fun z => Real.exp (-(q z + v) / 2)) gaussianCountable_LIP016)
    (hZ : 0 < ∫ z, Real.exp (-(q z + v) / 2) ∂gaussianCountable_LIP016)
    (hCF : ∀ (s : Finset ℕ) (u : s → ℝ),
      (∫ z, cylinderPhase_LIP016 s u z ∂wickTiltMeasure_LIP016 q v) =
      Complex.exp ((-⟪finiteEmbedding_LIP016 S s (WithLp.toLp 2 u),
        Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S))
          (finiteEmbedding_LIP016 S s (WithLp.toLp 2 u))⟫_ℝ / 2 : ℝ) : ℂ)) :
    ∀ s : Finset ℕ,
      IsGaussian ((wickTiltMeasure_LIP016 q v).map (finiteCoordinateProjection_LIP016 s)) ∧
      (∫ x : EuclideanSpace ℝ s, x
        ∂((wickTiltMeasure_LIP016 q v).map (finiteCoordinateProjection_LIP016 s))) = 0 ∧
      covarianceBilin ((wickTiltMeasure_LIP016 q v).map (finiteCoordinateProjection_LIP016 s)) =
        finiteCovarianceForm_LIP016 S s
          (Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S))) := by
  intro s
  let ν := wickTiltMeasure_LIP016 q v
  let μ := ν.map (finiteCoordinateProjection_LIP016 s)
  let C := Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S))
  let F := finiteCovarianceForm_LIP016 S s C
  let _ : IsProbabilityMeasure ν := wickTilt_isProbability_LIP016 q v hi hZ
  let _ : IsProbabilityMeasure μ := ⟨by
    rw [Measure.map_apply (finiteCoordinateProjection_measurable_LIP016 s) MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ]⟩
  obtain ⟨hCs, hCp⟩ := originalCovariance_symmetric_nonneg_LIP016 J (specProbability_LIP016 S) hσ hH
  have hF : F.toBilinForm.IsPosSemidef := by
    refine ⟨⟨fun u w => ?_⟩, ⟨fun u => ?_⟩⟩
    · change ⟪finiteEmbedding_LIP016 S s u, C (finiteEmbedding_LIP016 S s w)⟫_ℝ =
        ⟪finiteEmbedding_LIP016 S s w, C (finiteEmbedding_LIP016 S s u)⟫_ℝ
      rw [← hCs.apply_clm, real_inner_comm]
    · exact hCp (finiteEmbedding_LIP016 S s u)
  have hchar (u : EuclideanSpace ℝ s) :
      charFun μ u = Complex.exp (⟪u, (0 : EuclideanSpace ℝ s)⟫_ℝ * Complex.I - F u u / 2) := by
    rw [charFun_apply, integral_map
      (finiteCoordinateProjection_measurable_LIP016 s).aemeasurable (by fun_prop)]
    calc
      _ = ∫ z, cylinderPhase_LIP016 s (fun i => u i) z ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
            finiteCoordinateProjection_apply_LIP016, cylinderPhase_LIP016, gaussianPhase_LIP016]
          congr 1
          exact mul_comm _ _
      _ = Complex.exp ((-⟪finiteEmbedding_LIP016 S s u,
          C (finiteEmbedding_LIP016 S s u)⟫_ℝ / 2 : ℝ) : ℂ) := hCF s (fun i => u i)
      _ = _ := by
        rw [finiteCovarianceForm_apply_LIP016]
        simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
        congr 1
        push_cast
        ring
  have hG : IsGaussian μ :=
    isGaussian_iff_gaussian_charFun.mpr ⟨0, F, hF, hchar⟩
  have hparams := gaussian_charFun_congr (μ := μ) (0 : EuclideanSpace ℝ s) F hF hchar
  exact ⟨hG, hparams.1.symm, hparams.2.symm⟩
/-- The original-data LIP016 export. Coercivity is supplied only for the original
density Hessian. The covariance limit on its centered domain is the original
densityCovariance, included isometrically in full L². The normalized Wick tilt is
identified by all finite-test characteristic functions and its actual Gaussian marginals. -/
theorem finite_rank_covariance_positivity_and_wick_normalization {d : ℕ}
    (S : Spec d) (A : Aux S) (D : KData d) (J : InteractionData d)
    (hD : ∀ x y, D.K x y = DGPS.centeredKernel J (specProbability_LIP016 S) x y)
    {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ ⟪g, DGPS.densityHessian J (specProbability_LIP016 S) g⟫_ℝ) :
    let hK := original_kernel_symmetric_LIP016 S D J hD
    let hc := original_kernel_centered_LIP016 S D J hD
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (q : Lp ℝ 2 gaussianCountable_LIP016)
      (hu : ∀ R, IsUnit (1 + kernelCompression_LIP016 S D hK (t R) (m R))),
      (∀ R, 0 < t R) ∧ Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
      (∀ R, FiniteDimensional ℝ (LinearMap.range
        (kernelCompression_LIP016 S D hK (t R) (m R)).toLinearMap)) ∧
      (∀ R, kernelCompression_LIP016 S D hK (t R) (m R) =
        spectralDamping_LIP016 S (t R) (m R) *
          DGPS.kernelOp J (specProbability_LIP016 S) *
            spectralDamping_LIP016 S (t R) (m R)) ∧
      (∀ R f, min 1 σ * ‖f‖ ^ 2 ≤ ‖f‖ ^ 2 +
        ⟪f, kernelCompression_LIP016 S D hK (t R) (m R) f⟫_ℝ) ∧
      (∀ R i j, ⟪spectralBasis_LIP016 S i,
        kernelCompression_LIP016 S D hK (t R) (m R) (spectralBasis_LIP016 S j)⟫_ℝ =
          kernelCoefficient_LIP016 S D (t R) (m R) i j) ∧
      Tendsto (fun R => ∑' ij : ℕ × ℕ,
        (kernelCoefficient_LIP016 S D (t R) (m R) ij.1 ij.2 - TK S D.K ij.1 ij.2) ^ 2)
          atTop (𝓝 0) ∧
      Tendsto (fun R => Ring.inverse (1 + kernelCompression_LIP016 S D hK (t R) (m R)))
        atTop (𝓝 (Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S)))) ∧
      Tendsto (fun R => (Ring.inverse
        (1 + kernelCompression_LIP016 S D hK (t R) (m R))).comp
          (DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL) atTop
        (𝓝 ((DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL.comp
          (DGPS.densityCovariance J (specProbability_LIP016 S) ⟨σ, hσ, hH⟩))) ∧
      Tendsto (fun R => centeredCovarianceApprox_LIP016 S A D hK hc (t R) (m R) (hu R))
        atTop (𝓝 (DGPS.densityCovariance J (specProbability_LIP016 S) ⟨σ, hσ, hH⟩)) ∧
      Tendsto (fun R => kernelTrace_LIP016 S D (t R) (m R))
        atTop (𝓝 (∫ x, D.K x x ∂S.mu)) ∧
      Tendsto (fun R => kernelWickLp_LIP016 S D (t R) (m R)) atTop (𝓝 q) ∧
      (∀ R, ‖kernelWickLp_LIP016 S D (t R) (m R) - q‖ ^ 2 =
        2 * ∑' ij : ℕ × ℕ,
          (kernelCoefficient_LIP016 S D (t R) (m R) ij.1 ij.2 - TK S D.K ij.1 ij.2) ^ 2) ∧
      UniformIntegrable (fun R => kernelRawGaussian_LIP016 S D (t R) (m R)) 1
        gaussianCountable_LIP016 ∧
      Integrable (fun z => Real.exp (-(q z + ∫ x, D.K x x ∂S.mu) / 2))
        gaussianCountable_LIP016 ∧
      0 < ∫ z, Real.exp (-(q z + ∫ x, D.K x x ∂S.mu) / 2) ∂gaussianCountable_LIP016 ∧
      Tendsto (fun R => ∫ z, kernelRawGaussian_LIP016 S D (t R) (m R) z
        ∂gaussianCountable_LIP016) atTop
        (𝓝 (∫ z, Real.exp (-(q z + ∫ x, D.K x x ∂S.mu) / 2) ∂gaussianCountable_LIP016)) ∧
      IsProbabilityMeasure (wickTiltMeasure_LIP016 q (∫ x, D.K x x ∂S.mu)) ∧
      (∀ (s : Finset ℕ) (u : s → ℝ),
        (∫ z, cylinderPhase_LIP016 s u z
          ∂wickTiltMeasure_LIP016 q (∫ x, D.K x x ∂S.mu)) =
        Complex.exp ((-⟪finiteEmbedding_LIP016 S s (WithLp.toLp 2 u),
          Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S))
            (finiteEmbedding_LIP016 S s (WithLp.toLp 2 u))⟫_ℝ / 2 : ℝ) : ℂ)) ∧
      ∀ s : Finset ℕ,
        IsGaussian ((wickTiltMeasure_LIP016 q (∫ x, D.K x x ∂S.mu)).map
          (finiteCoordinateProjection_LIP016 s)) ∧
        (∫ y : EuclideanSpace ℝ s, y
          ∂((wickTiltMeasure_LIP016 q (∫ x, D.K x x ∂S.mu)).map
            (finiteCoordinateProjection_LIP016 s))) = 0 ∧
        covarianceBilin ((wickTiltMeasure_LIP016 q (∫ x, D.K x x ∂S.mu)).map
          (finiteCoordinateProjection_LIP016 s)) =
          finiteCovarianceForm_LIP016 S s
            (Ring.inverse (1 + DGPS.kernelOp J (specProbability_LIP016 S))) := by
  dsimp only
  let hK := original_kernel_symmetric_LIP016 S D J hD
  let hc := original_kernel_centered_LIP016 S D J hD
  have hH' := original_hessian_transport_LIP016 S D hK hc J hD hH
  obtain ⟨t, m, q, ht, htlim, hm, hfin, hcoer, hcoef, hHS, hunit, hcov,
    htrace, hq, herr, hUI, hInt, hpos, hlim⟩ := kernel_packet_LIP016 S A D hK hc hσ hH'
  have hop := kernelOperator_original_LIP016 S D hK hc J hD
  have hcovJ := hcov
  rw [hop] at hcovJ
  have hcont : Continuous
      (fun L : Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) →L[ℝ]
          Lp ℝ 2 (specProbability_LIP016 S : Measure (Torus d)) =>
        L.comp (DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL) :=
    continuous_id.clm_comp_const _
  have hcenter := (hcont.tendsto _).comp hcov
  have he :
      (Ring.inverse (1 + kernelOperator_LIP016 S D hK)).comp
        (DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL =
      (DGPS.centeredL2 (specProbability_LIP016 S)).subtypeL.comp
        (DGPS.densityCovariance J (specProbability_LIP016 S) ⟨σ, hσ, hH⟩) := by
    apply ContinuousLinearMap.ext
    intro g
    exact kernelCovariance_original_centered_LIP016 S D hK hc J hD hσ hH g
  rw [he] at hcenter
  have hcenterExact : Tendsto
      (fun R => centeredCovarianceApprox_LIP016 S A D hK hc (t R) (m R) (hunit R))
      atTop (𝓝 (DGPS.densityCovariance J (specProbability_LIP016 S) ⟨σ, hσ, hH⟩)) := by
    apply (centeredSubtype_tendsto_iff_LIP016
      (DGPS.centeredL2 (specProbability_LIP016 S)) _ _).mpr
    simpa only [Function.comp_def, centeredCovarianceApprox_inclusion_LIP016] using hcenter
  have hν := wickTilt_isProbability_LIP016 q (∫ x, D.K x x ∂S.mu) hInt hpos
  have hCF := kernelWick_normalized_characteristic_LIP016 S D hK hc hσ hH'
    t m (fun R => (ht R).le) q (∫ x, D.K x x ∂S.mu)
    hq htrace hUI hInt hpos hcov
  rw [hop] at hCF
  have hMarg := wickTilt_gaussian_marginals_LIP016 S J hσ hH q
    (∫ x, D.K x x ∂S.mu) hInt hpos hCF
  refine ⟨t, m, q, hunit, ht, htlim, hm, hfin, ?_, hcoer, hcoef, hHS,
    hcovJ, hcenter, hcenterExact, htrace, hq, herr, hUI, hInt, hpos, hlim,
    hν, hCF, hMarg⟩
  intro R
  unfold kernelCompression_LIP016
  rw [hop]

end DGPS.Lipschitz
