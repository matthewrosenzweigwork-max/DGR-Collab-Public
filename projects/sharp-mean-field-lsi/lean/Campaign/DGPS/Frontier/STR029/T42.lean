import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DGPS.Frontier.STR029.T38
import DGPS.Frontier.STR029.T34
import DGPS.Frontier.STR029.T41

/-!
# STR029.42: Weak derivative, weighted energy, and entropy passage

Task id and title: STR029.42, "Weak derivative, weighted energy, and entropy passage" (node STR029).
Fix `|h| ≤ 1/1000`. A further subsequence of the uniformly convergent subsequence of STR029.38 converges
weakly in the periodic Sobolev space `H¹` to its uniform limit `G`; the limit has a periodic weak
derivative `d`, the weighted energy of the limit satisfies `∫ d² q_h dm ≤ liminf E (σ n)`, and the
entropies converge, `H (σ n) → ∫ G² log G² q_h dm`.

## Provides

* `DGPS.Frontier.STR029.str029_42_weak_derivative_weighted_energy_entropy_passage`: the main statement.
  Under the hypotheses of STR029.38 there are a strictly increasing `σ : ℕ → ℕ` and `G d : ℝ → ℝ` such that
  the conclusions of STR029.38 hold along `σ` (`G` continuous, periodic, nonnegative, `∫ G² q_h dm = 1`,
  `F (σ n) → G` uniformly, `E (σ n) → liminf E`), `d` is the periodic weak derivative of `G`,
  `g (σ n) ⇀ G` weakly in `H¹` (with weak derivative pairs `(g (σ n), g' (σ n)) ⇀ (G, d)`), the unweighted
  derivatives `g' (σ n)` converge weakly in `L²` against every `L²` test function, the functions converge
  strongly in `L²(m)`, `∫ d² q_h dm ≤ liminf E (σ n)`, and `H (σ n) → ∫ G² log G² q_h dm`.
* `DGPS.Frontier.STR029.str029_42_weak_derivative_weighted_energy_entropy_passage_weak_derivative_ae_unique`:
  two periodic weak derivatives of the same function agree almost everywhere on `(0, 2π]`.
* `DGPS.Frontier.STR029.str029_42_weak_derivative_weighted_energy_entropy_passage_energy_unique`: the
  weighted energy `∫ d² q_h dm` is the same for any periodic weak derivative `d` of a given function, so
  the energy bound of the main statement is a statement about the energy `E(G)` of the limit itself.
* `DGPS.Frontier.STR029.h1Pair_STR02942`: the `H¹` pairing `∫ u y dm + ∫ u' y' dm` of two pairs
  (function, derivative).
* `DGPS.Frontier.STR029.WeaklyConvergesH1_STR02942`: weak convergence of periodic weak pairs
  `(u n, u' n) ⇀ (G, d)` in `H¹`, namely pairing with every periodic weak pair converges.

## R5 notes

* Hypotheses. The unit statement says "a further subsequence of .38", so the standing data are those of
  STR029.38, with the same hypotheses and the same constants: `|h| ≤ 1/1000`, `g n ≥ 0`, periodic weak
  derivatives `g' n` of `g n`, `∫ (g n)² q_h dm = 1`, `E n` the weighted energy, `H n` the entropy,
  `0 < H n`, the quotient hypothesis `4 E n / (2 H n) ≤ 2`, `K = 8 π² e^{1/500}`, `A = log (K + 2)`, and
  continuous periodic representatives `F n` of `g n`. No hypothesis beyond those of STR029.38 is added.
* Common subsequence. The statement calls STR029.38 to obtain a first subsequence `σ₀`, then extracts a
  further subsequence `τ` by the STR029.41 chain, and returns `σ = σ₀ ∘ τ`. The conclusion contains the
  STR029.38 conclusions for `σ` itself (uniform convergence of `F (σ n)`, convergence of `E (σ n)` to
  `liminf E`), which is why the result is a further subsequence of the one of STR029.38. One common
  subsequence serves for the weak limit, the energy bound and the entropy.
* Carriers. Energy, entropy and normalization use the STR029.04 interval carrier `normInt_STR02904`
  (`(2π)⁻¹ ∫₀^{2π}`) and `qT_STR02904 h`. The weak derivative predicate and the Hilbert space structure use
  the STR029.33 carrier `normInt_STR02933` (`(2π)⁻¹ ∫_{(0, 2π]}`) and `circleMeasure_STR02934`. The two
  carriers are bridged once by `normInt_04_eq_33_STR02942`. The unit does not touch the optimizer chart,
  the Euler or variational range maps, `AbsoluteDensity`, or any Fisher or deficit convention.
* Weak convergence in `H¹` (non-literal reading, made concrete). Mathlib has no periodic `H¹`, so
  `WeaklyConvergesH1_STR02942 u u' G d` is defined as: every `(u n, u' n)` and `(G, d)` is a periodic weak
  pair (STR029.33 predicate), and for every periodic weak pair `(y, y')` the `H¹` pairing
  `∫ u n y dm + ∫ u' n y' dm` converges to `∫ G y dm + ∫ d y' dm`. This is weak convergence in the Hilbert
  space of periodic weak pairs (graph of the weak derivative in `L² × L²`) by the Riesz representation
  theorem. The unweighted measure `m` is used. Since `exp(-2|h|) ≤ q_h ≤ exp(2|h|)`, the weighted and the
  unweighted `H¹` norms are equivalent and the two notions of weak convergence coincide. The specification
  tests with `φ / √q_h`; the conclusion also records weak `L²` convergence of the derivatives against every
  `L²` test function `x` (the quantity `∫ g' (σ n) x dm → ∫ d x dm`), which is the unweighted statement
  obtained by testing with `x / √q_h` in the weighted space.
* Weak derivative of the limit. The weak derivative of `G` is `d = dFun_STR02942 h w`, the `2π`-periodic
  function that equals `w / √q_h` on `(0, 2π]` (extension by `toIocMod`), where `w` is the weak limit in
  `L²(m)` of `√q_h · g' (σ n)`. Passing to the limit in the periodic weak identity uses uniform convergence
  of `F (σ n)` on one side and the weak convergence tested against `φ / √q_h ∈ L²` on the other, as in the
  proof sketch; uniqueness of limits identifies the two.
* Energy. `E(G)` is the weighted energy `normInt_STR02904 (d² q_h)` of the periodic weak derivative of `G`.
  The weak derivative is unique up to almost-everywhere equality
  (`..._weak_derivative_ae_unique`, via the trigonometric Hilbert basis of STR029.34), so this energy does
  not depend on the choice of `d` (`..._energy_unique`). Lower semicontinuity is the norm bound of
  STR029.41 applied to `v n = √q_h · g' (σ n)`, together with `‖w‖² = ∫ d² q_h dm`.
* Boundedness of the sequence in `L²(m)`. The bound `‖v n‖² = E (σ₀ n)` is combined with the convergence of
  `E (σ₀ n)` from STR029.38 (convergent sequences are bounded), not with a separate estimate of STR029.06.
* Basis. The STR029.41 chain needs a Hilbert basis indexed by `ℕ`. The trigonometric basis of STR029.34 is
  indexed by `Option (Bool × ℕ)`, which is countable, so it is re-indexed by an equivalence with `ℕ`
  (`exists_hilbertBasis_nat_STR02942`). The unit does not reprove any Fourier or Hilbert-basis fact.
* Entropy (non-literal reading of the proof sketch). The sketch invokes uniform continuity of
  `x² log x²` (value `0` at `0`) on a common bounded range. The formalization uses instead continuity of
  `x ↦ x² log x²` (`Real.continuous_mul_log` composed with `x ↦ x²`), compactness, and the eventual uniform
  bound of the uniformly convergent sequence, and concludes by dominated convergence on `(0, 2π]` with the
  constant bound `B e^{2|h|}`. This avoids a separate modulus of continuity and gives the same convergence.
  Positivity of the limiting square root is not assumed; only continuity at `0` of `x² log x²` is used.
* Strong convergence. `∫ (g (σ n) - G)² dm → 0` is obtained from uniform convergence by dominated
  convergence, and is part of the conclusion (together with the weak `H¹` statement it gives the weak
  `H¹` convergence of the specification).
* Sobolev infrastructure. The periodic weak derivative predicate and the Fourier machinery of STR029.33 and
  STR029.34 are reused. This unit adds only the two small definitions above and the weak-derivative
  uniqueness lemmas; nothing of the periodic Sobolev infrastructure is duplicated.
* Helpers. Every helper carries the suffix `_STR02942`; public lemmas carry the prefix
  `str029_42_weak_derivative_weighted_energy_entropy_passage`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace DGPS.Frontier.STR029

/-- The square root `√q_h` of the reference density. -/
noncomputable def sqrtQ_STR02942 (h t : ℝ) : ℝ := Real.sqrt (qT_STR02904 h t)

lemma sqrtQ_pos_STR02942 (h t : ℝ) : 0 < sqrtQ_STR02942 h t :=
  Real.sqrt_pos.2 (qT_pos_STR02904 h t)

lemma continuous_sqrtQ_STR02942 (h : ℝ) : Continuous (sqrtQ_STR02942 h) :=
  (continuous_qT_STR02904 h).sqrt

lemma sqrtQ_mul_self_STR02942 (h t : ℝ) :
    sqrtQ_STR02942 h t * sqrtQ_STR02942 h t = qT_STR02904 h t :=
  Real.mul_self_sqrt (qT_pos_STR02904 h t).le

lemma sqrtQ_le_STR02942 (h t : ℝ) : sqrtQ_STR02942 h t ≤ Real.exp |h| := by
  unfold sqrtQ_STR02942
  rw [Real.sqrt_le_iff]
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have h2 : Real.exp |h| ^ 2 = Real.exp (2 * |h|) := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h2]
  exact (qT_bounds_STR02904 h t).2

lemma inv_sqrtQ_le_STR02942 (h t : ℝ) : (sqrtQ_STR02942 h t)⁻¹ ≤ Real.exp |h| := by
  have hlow : Real.exp (-|h|) ≤ sqrtQ_STR02942 h t := by
    unfold sqrtQ_STR02942
    refine Real.le_sqrt_of_sq_le ?_
    have h2 : Real.exp (-|h|) ^ 2 = Real.exp (-(2 * |h|)) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [h2]
    exact (qT_bounds_STR02904 h t).1
  calc (sqrtQ_STR02942 h t)⁻¹ ≤ (Real.exp (-|h|))⁻¹ := inv_anti₀ (Real.exp_pos _) hlow
    _ = Real.exp |h| := by rw [Real.exp_neg, inv_inv]


/-- The two normalized integrals (interval integral over `0..2π` and set integral over `(0, 2π]`) agree. -/
lemma normInt_04_eq_33_STR02942 (f : ℝ → ℝ) : normInt_STR02904 f = normInt_STR02933 f := by
  unfold normInt_STR02904 normInt_STR02933
  rw [intervalIntegral.integral_of_le (by positivity)]

lemma memLp_circle_of_restrict_STR02942 {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) : MemLp u 2 circleMeasure_STR02934 :=
  hu.of_measure_le_smul (c := ENNReal.ofReal (2 * π)⁻¹) ENNReal.ofReal_ne_top
    (by unfold circleMeasure_STR02934; exact le_rfl)

lemma exists_bound_Ioc_STR02942 {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc 0 (2 * π), |f t| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht => ?_⟩
  have := hB t (Ioc_subset_Icc_self ht)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma memLp_restrict_of_continuous_STR02942 {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨B, -, hB⟩ := exists_bound_Ioc_STR02942 hf
  refine MemLp.of_bound hf.aestronglyMeasurable B ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => ?_)
  rw [Real.norm_eq_abs]
  exact hB t ht

lemma memLp_sqrtQ_mul_STR02942 (h : ℝ) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    MemLp (fun t => sqrtQ_STR02942 h t * u t) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  refine hu.of_le_mul (c := Real.exp |h|)
    ((continuous_sqrtQ_STR02942 h).aestronglyMeasurable.mul hu.aestronglyMeasurable)
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (sqrtQ_pos_STR02942 h t)]
  exact mul_le_mul_of_nonneg_right (sqrtQ_le_STR02942 h t) (abs_nonneg _)

lemma memLp_inv_sqrtQ_mul_STR02942 (h : ℝ) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    MemLp (fun t => (sqrtQ_STR02942 h t)⁻¹ * u t) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  refine hu.of_le_mul (c := Real.exp |h|)
    (((continuous_sqrtQ_STR02942 h).inv₀ (fun t => (sqrtQ_pos_STR02942 h t).ne')).aestronglyMeasurable.mul
      hu.aestronglyMeasurable)
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (sqrtQ_pos_STR02942 h t))]
  exact mul_le_mul_of_nonneg_right (inv_sqrtQ_le_STR02942 h t) (abs_nonneg _)

/-- The class of `√q_h · u` in `L²(m)`. -/
noncomputable def sqrtLp_STR02942 (h : ℝ) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) : Lp ℝ 2 circleMeasure_STR02934 :=
  (memLp_circle_of_restrict_STR02942 (memLp_sqrtQ_mul_STR02942 h hu)).toLp _

/-- The class of `u / √q_h` in `L²(m)`. -/
noncomputable def invSqrtLp_STR02942 (h : ℝ) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) : Lp ℝ 2 circleMeasure_STR02934 :=
  (memLp_circle_of_restrict_STR02942 (memLp_inv_sqrtQ_mul_STR02942 h hu)).toLp _

lemma coeFn_sqrtLp_STR02942 (h : ℝ) {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    (sqrtLp_STR02942 h hu : ℝ → ℝ) =ᵐ[circleMeasure_STR02934] fun t => sqrtQ_STR02942 h t * u t :=
  MemLp.coeFn_toLp _

lemma coeFn_invSqrtLp_STR02942 (h : ℝ) {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    (invSqrtLp_STR02942 h hu : ℝ → ℝ) =ᵐ[circleMeasure_STR02934]
      fun t => (sqrtQ_STR02942 h t)⁻¹ * u t :=
  MemLp.coeFn_toLp _

/-- Pairing of `√q_h u` with `ψ / √q_h` in `L²(m)` is the plain pairing `∫ u ψ dm`. -/
lemma inner_sqrtLp_invSqrtLp_STR02942 (h : ℝ) {u ψ : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π))))
    (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 (2 * π)))) :
    inner ℝ (sqrtLp_STR02942 h hu) (invSqrtLp_STR02942 h hψ)
      = normInt_STR02933 (fun t => u t * ψ t) := by
  rw [L2.inner_def, normInt_eq_integral_STR02934]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_sqrtLp_STR02942 h hu, coeFn_invSqrtLp_STR02942 h hψ] with t h1 h2
  rw [h1, h2]
  have := (sqrtQ_pos_STR02942 h t).ne'
  simp only [RCLike.inner_apply, conj_trivial]
  field_simp

/-- Pairing of an arbitrary class `y` against `ψ / √q_h`. -/
lemma inner_invSqrtLp_STR02942 (h : ℝ) {ψ : ℝ → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 (2 * π)))) (y : Lp ℝ 2 circleMeasure_STR02934) :
    inner ℝ y (invSqrtLp_STR02942 h hψ)
      = normInt_STR02933 (fun t => y t * ((sqrtQ_STR02942 h t)⁻¹ * ψ t)) := by
  rw [L2.inner_def, normInt_eq_integral_STR02934]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_invSqrtLp_STR02942 h hψ] with t h2
  rw [h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring


/-- Normalized integrals over the period only see the values on `(0, 2π]`. -/
lemma normInt_congr_Ioc_STR02942 {u v : ℝ → ℝ} (huv : ∀ t ∈ Ioc 0 (2 * π), u t = v t) :
    normInt_STR02933 u = normInt_STR02933 v := by
  unfold normInt_STR02933
  rw [setIntegral_congr_fun measurableSet_Ioc huv]

/-- Normalized integrals ignore almost-everywhere changes on the period. -/
lemma normInt_congr_ae_Ioc_STR02942 {u v : ℝ → ℝ}
    (huv : u =ᵐ[volume.restrict (Ioc 0 (2 * π))] v) :
    normInt_STR02933 u = normInt_STR02933 v := by
  unfold normInt_STR02933
  rw [integral_congr_ae huv]

/-- The `2π`-periodic function that equals `w / √q_h` on `(0, 2π]`. -/
noncomputable def dFun_STR02942 (h : ℝ) (w : Lp ℝ 2 circleMeasure_STR02934) (t : ℝ) : ℝ :=
  (w : ℝ → ℝ) (toIocMod Real.two_pi_pos 0 t) * (sqrtQ_STR02942 h (toIocMod Real.two_pi_pos 0 t))⁻¹

lemma dFun_eq_STR02942 (h : ℝ) (w : Lp ℝ 2 circleMeasure_STR02934) {t : ℝ}
    (ht : t ∈ Ioc 0 (2 * π)) : dFun_STR02942 h w t = w t * (sqrtQ_STR02942 h t)⁻¹ := by
  have : toIocMod Real.two_pi_pos 0 t = t := (toIocMod_eq_self Real.two_pi_pos).2 (by simpa using ht)
  rw [dFun_STR02942, this]

lemma periodic_dFun_STR02942 (h : ℝ) (w : Lp ℝ 2 circleMeasure_STR02934) :
    Function.Periodic (dFun_STR02942 h w) (2 * π) := by
  intro t
  unfold dFun_STR02942
  rw [toIocMod_add_right]

lemma dFun_ae_eq_STR02942 (h : ℝ) (w : Lp ℝ 2 circleMeasure_STR02934) :
    dFun_STR02942 h w =ᵐ[volume.restrict (Ioc 0 (2 * π))] fun t => (sqrtQ_STR02942 h t)⁻¹ * w t :=
  (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => by
    rw [dFun_eq_STR02942 h w ht, mul_comm])

lemma memLp_lp_restrict_STR02942 (w : Lp ℝ 2 circleMeasure_STR02934) :
    MemLp (w : ℝ → ℝ) 2 (volume.restrict (Ioc 0 (2 * π))) :=
  memLp_restrict_of_circle_STR02934 (Lp.memLp w)

lemma memLp_dFun_STR02942 (h : ℝ) (w : Lp ℝ 2 circleMeasure_STR02934) :
    MemLp (dFun_STR02942 h w) 2 (volume.restrict (Ioc 0 (2 * π))) :=
  (memLp_inv_sqrtQ_mul_STR02942 h (memLp_lp_restrict_STR02942 w)).ae_eq (dFun_ae_eq_STR02942 h w).symm

/-- Pairing of `w` with `x / √q_h` in `L²(m)` is the plain pairing of `d = w / √q_h` with `x`. -/
lemma inner_dFun_STR02942 (h : ℝ) (w : Lp ℝ 2 circleMeasure_STR02934) {x : ℝ → ℝ}
    (hx : MemLp x 2 (volume.restrict (Ioc 0 (2 * π)))) :
    inner ℝ w (invSqrtLp_STR02942 h hx) = normInt_STR02933 (fun t => dFun_STR02942 h w t * x t) := by
  rw [inner_invSqrtLp_STR02942]
  refine normInt_congr_Ioc_STR02942 fun t ht => ?_
  rw [dFun_eq_STR02942 h w ht]
  ring

lemma energy_dFun_STR02942 (h : ℝ) (w : Lp ℝ 2 circleMeasure_STR02934) :
    normInt_STR02904 (fun t => dFun_STR02942 h w t ^ 2 * qT_STR02904 h t) = ‖w‖ ^ 2 := by
  rw [normInt_04_eq_33_STR02942, ← real_inner_self_eq_norm_sq, L2.inner_def,
    ← normInt_eq_integral_STR02934 (fun t => inner ℝ (w t) (w t))]
  refine normInt_congr_Ioc_STR02942 fun t ht => ?_
  rw [dFun_eq_STR02942 h w ht]
  have := (sqrtQ_pos_STR02942 h t).ne'
  have h2 := sqrtQ_mul_self_STR02942 h t
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← h2]
  field_simp

lemma norm_sq_sqrtLp_STR02942 (h : ℝ) {u : ℝ → ℝ} (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π)))) :
    ‖sqrtLp_STR02942 h hu‖ ^ 2 = normInt_STR02933 (fun t => u t ^ 2 * qT_STR02904 h t) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, normInt_eq_integral_STR02934]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_sqrtLp_STR02942 h hu] with t h1
  rw [h1]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← sqrtQ_mul_self_STR02942 h t]
  ring

lemma exists_hilbertBasis_nat_STR02942 :
    Nonempty (HilbertBasis ℕ ℝ (Lp ℝ 2 circleMeasure_STR02934)) := by
  obtain ⟨b, -⟩ := exists_hilbertBasis_trig_STR02934
  obtain ⟨e⟩ : Nonempty (ℕ ≃ Option (Bool × ℕ)) := nonempty_equiv_of_countable
  refine ⟨HilbertBasis.mk (v := fun n => b (e n)) (b.orthonormal.comp _ e.injective) ?_⟩
  have hr : Set.range (fun n => b (e n)) = Set.range b := e.surjective.range_comp b
  rw [hr]
  exact b.dense_span.ge


/-- Dominated convergence for the normalized integral over the period. -/
lemma tendsto_normInt_dominated_STR02942 {f : ℕ → ℝ → ℝ} {f₀ b : ℝ → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioc 0 (2 * π))))
    (hb : Integrable b (volume.restrict (Ioc 0 (2 * π))))
    (hbd : ∀ᶠ n in atTop, ∀ t ∈ Ioc 0 (2 * π), |f n t| ≤ b t)
    (hlim : ∀ t ∈ Ioc 0 (2 * π), Tendsto (fun n => f n t) atTop (𝓝 (f₀ t))) :
    Tendsto (fun n => normInt_STR02933 (f n)) atTop (𝓝 (normInt_STR02933 f₀)) := by
  unfold normInt_STR02933
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_filter_of_dominated_convergence b (Eventually.of_forall hmeas) ?_ hb ?_
  · filter_upwards [hbd] with n hn
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun t ht => by rw [Real.norm_eq_abs]; exact hn t ht)
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hlim)

/-- A uniformly convergent sequence with a continuous limit is eventually uniformly bounded on the period. -/
lemma uniform_bound_STR02942 {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} (hG : Continuous G)
    (hu : TendstoUniformly F G atTop) :
    ∃ S : ℝ, 0 ≤ S ∧ (∀ t ∈ Ioc 0 (2 * π), |G t| ≤ S) ∧
      ∀ᶠ n in atTop, ∀ t ∈ Ioc 0 (2 * π), |F n t| ≤ S := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_Ioc_STR02942 hG
  refine ⟨B + 1, by linarith, fun t ht => (hB t ht).trans (by linarith), ?_⟩
  filter_upwards [Metric.tendstoUniformly_iff.1 hu 1 one_pos] with n hn t ht
  have h1 := hn t
  rw [Real.dist_eq] at h1
  have h2 := hB t ht
  calc |F n t| = |G t - (G t - F n t)| := by ring_nf
    _ ≤ |G t| + |G t - F n t| := abs_sub _ _
    _ ≤ B + 1 := by linarith

/-- Pairing of a uniformly convergent sequence against an integrable function converges. -/
lemma tendsto_normInt_mul_STR02942 {F : ℕ → ℝ → ℝ} {G y : ℝ → ℝ} (hFc : ∀ n, Continuous (F n))
    (hG : Continuous G) (hu : TendstoUniformly F G atTop)
    (hy : Integrable y (volume.restrict (Ioc 0 (2 * π)))) :
    Tendsto (fun n => normInt_STR02933 (fun t => F n t * y t)) atTop
      (𝓝 (normInt_STR02933 (fun t => G t * y t))) := by
  obtain ⟨S, -, -, hS⟩ := uniform_bound_STR02942 hG hu
  refine tendsto_normInt_dominated_STR02942 (b := fun t => S * |y t|)
    (fun n => (hFc n).aestronglyMeasurable.mul hy.aestronglyMeasurable) (hy.abs.const_mul S) ?_ ?_
  · filter_upwards [hS] with n hn t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hn t ht) (abs_nonneg _)
  · intro t _
    exact (hu.tendsto_at t).mul_const _

/-- Strong `L²(m)` convergence of a uniformly convergent sequence. -/
lemma tendsto_normInt_sq_sub_STR02942 {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} (hFc : ∀ n, Continuous (F n))
    (hG : Continuous G) (hu : TendstoUniformly F G atTop) :
    Tendsto (fun n => normInt_STR02933 (fun t => (F n t - G t) ^ 2)) atTop (𝓝 0) := by
  have h0 : normInt_STR02933 (fun _ : ℝ => (0 : ℝ)) = 0 := by simp [normInt_STR02933]
  have key := tendsto_normInt_dominated_STR02942 (f := fun n t => (F n t - G t) ^ 2)
    (f₀ := fun _ => 0) (b := fun _ => 1)
    (fun n => (((hFc n).sub hG).pow 2).aestronglyMeasurable) (integrable_const _) ?_ ?_
  · rwa [h0] at key
  · filter_upwards [Metric.tendstoUniformly_iff.1 hu 1 one_pos] with n hn t _
    have h1 := hn t
    rw [Real.dist_eq, abs_sub_comm] at h1
    rw [abs_of_nonneg (sq_nonneg _)]
    have h2 := abs_nonneg (F n t - G t)
    nlinarith [sq_abs (F n t - G t)]
  · intro t _
    have := ((hu.tendsto_at t).sub_const (G t)).pow 2
    simpa using this

lemma continuous_entropy_STR02942 : Continuous (fun x : ℝ => x ^ 2 * Real.log (x ^ 2)) :=
  Real.continuous_mul_log.comp (continuous_pow 2)

/-- The entropy integrals converge along a uniformly convergent sequence. -/
lemma tendsto_normInt_entropy_STR02942 (h : ℝ) {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hFc : ∀ n, Continuous (F n)) (hG : Continuous G) (hu : TendstoUniformly F G atTop) :
    Tendsto (fun n => normInt_STR02933
        (fun t => F n t ^ 2 * Real.log (F n t ^ 2) * qT_STR02904 h t)) atTop
      (𝓝 (normInt_STR02933 (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t))) := by
  obtain ⟨S, hS0, -, hS⟩ := uniform_bound_STR02942 hG hu
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -S) (b := S)).exists_bound_of_continuousOn
    continuous_entropy_STR02942.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨by linarith, hS0⟩)
  refine tendsto_normInt_dominated_STR02942 (b := fun _ => B * Real.exp (2 * |h|))
    (fun n => ((continuous_entropy_STR02942.comp (hFc n)).mul
      (continuous_qT_STR02904 h)).aestronglyMeasurable) (integrable_const _) ?_ ?_
  · filter_upwards [hS] with n hn t ht
    have h1 := hB (F n t) ⟨by linarith [(abs_le.1 (hn t ht)).1], (abs_le.1 (hn t ht)).2⟩
    rw [Real.norm_eq_abs] at h1
    rw [abs_mul, abs_of_pos (qT_pos_STR02904 h t)]
    exact mul_le_mul h1 (qT_bounds_STR02904 h t).2 (qT_pos_STR02904 h t).le hB0
  · intro t _
    exact ((continuous_entropy_STR02942.tendsto (G t)).comp (hu.tendsto_at t)).mul_const _


/-- The pairing of the difference of two weak derivatives with a smooth periodic test vanishes. -/
lemma normInt_diff_test_STR02942 {w d₁ d₂ : ℝ → ℝ} (h₁ : IsPeriodicWeakDerivative_STR02933 w d₁)
    (h₂ : IsPeriodicWeakDerivative_STR02933 w d₂) {φ : ℝ → ℝ}
    (hφ : IsSmoothPeriodicTest_STR02933 φ) :
    normInt_STR02933 (fun t => (d₁ t - d₂ t) * φ t) = 0 := by
  have hφm := memLp_restrict_of_continuous_STR02942 hφ.1.continuous
  have i1 : Integrable (fun t => d₁ t * φ t) (volume.restrict (Ioc 0 (2 * π))) :=
    h₁.2.1.2.integrable_mul hφm
  have i2 : Integrable (fun t => d₂ t * φ t) (volume.restrict (Ioc 0 (2 * π))) :=
    h₂.2.1.2.integrable_mul hφm
  have e : normInt_STR02933 (fun t => (d₁ t - d₂ t) * φ t)
      = normInt_STR02933 (fun t => d₁ t * φ t) - normInt_STR02933 (fun t => d₂ t * φ t) := by
    unfold normInt_STR02933
    rw [← mul_sub, ← integral_sub i1 i2]
    simp only [sub_mul]
  rw [e, h₁.2.2 φ hφ, h₂.2.2 φ hφ]
  ring

/-- Two periodic weak derivatives of the same function agree almost everywhere on the period. -/
theorem str029_42_weak_derivative_weighted_energy_entropy_passage_weak_derivative_ae_unique
    {w d₁ d₂ : ℝ → ℝ} (h₁ : IsPeriodicWeakDerivative_STR02933 w d₁)
    (h₂ : IsPeriodicWeakDerivative_STR02933 w d₂) :
    d₁ =ᵐ[volume.restrict (Ioc 0 (2 * π))] d₂ := by
  have hz : MemLp (fun t => d₁ t - d₂ t) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    h₁.2.1.2.sub h₂.2.1.2
  let x : Lp ℝ 2 circleMeasure_STR02934 := (memLp_circle_of_restrict_STR02942 hz).toLp _
  have hxz : (x : ℝ → ℝ) =ᵐ[circleMeasure_STR02934] fun t => d₁ t - d₂ t := MemLp.coeFn_toLp _
  have hae : ae circleMeasure_STR02934 = ae (volume.restrict (Ioc 0 (2 * π))) := by
    unfold circleMeasure_STR02934
    exact Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 (by positivity)).ne' _
  have hxz' : (x : ℝ → ℝ) =ᵐ[volume.restrict (Ioc 0 (2 * π))] fun t => d₁ t - d₂ t := by
    rw [← hae]; exact hxz
  have hcoef : ∀ φ : ℝ → ℝ, IsSmoothPeriodicTest_STR02933 φ →
      normInt_STR02933 (fun t => x t * φ t) = 0 := fun φ hφ => by
    rw [normInt_congr_ae_Ioc_STR02942 (v := fun t => (d₁ t - d₂ t) * φ t)]
    · exact normInt_diff_test_STR02942 h₁ h₂ hφ
    · filter_upwards [hxz'] with t ht
      rw [ht]
  have hperp : ∀ i, inner ℝ (trigBasisLp_STR02934 i) x = (0 : ℝ) := by
    intro i
    rw [inner_trigBasisLp_STR02934]
    rcases i with _ | ⟨_ | _, k⟩
    · simpa [trigBasisFun_STR02934] using hcoef _ const_test_STR02933
    · have := hcoef _ (cos_test_STR02933 (k + 1))
      simp only [trigBasisFun_STR02934]
      have e : (fun t => x t * (Real.sqrt 2 * Real.cos (((k + 1 : ℕ) : ℝ) * t)))
          = fun t => Real.sqrt 2 * (x t * Real.cos (((k + 1 : ℕ) : ℝ) * t)) := by
        funext t; ring
      rw [e, normInt_mul_const_STR02933, this, mul_zero]
    · have := hcoef _ (sin_test_STR02933 (k + 1))
      simp only [trigBasisFun_STR02934]
      have e : (fun t => x t * (Real.sqrt 2 * Real.sin (((k + 1 : ℕ) : ℝ) * t)))
          = fun t => Real.sqrt 2 * (x t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
        funext t; ring
      rw [e, normInt_mul_const_STR02933, this, mul_zero]
  have hx : x ∈ (Submodule.span ℝ (Set.range trigBasisLp_STR02934))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hperp i
    | zero => exact inner_zero_left _
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [inner_smul_left, hy, mul_zero]
  rw [orthogonal_trigBasisLp_eq_bot_STR02934, Submodule.mem_bot] at hx
  have h0 : (x : ℝ → ℝ) =ᵐ[circleMeasure_STR02934] 0 := by
    rw [← Lp.eq_zero_iff_ae_eq_zero]; exact hx
  rw [hae] at h0
  filter_upwards [h0, hxz'] with t h0t hxt
  have : d₁ t - d₂ t = 0 := by rw [← hxt]; simpa using h0t
  linarith

/-- The weighted energy `∫ d² q_h dm` does not depend on the choice of the periodic weak derivative `d`. -/
theorem str029_42_weak_derivative_weighted_energy_entropy_passage_energy_unique (h : ℝ)
    {w d₁ d₂ : ℝ → ℝ} (h₁ : IsPeriodicWeakDerivative_STR02933 w d₁)
    (h₂ : IsPeriodicWeakDerivative_STR02933 w d₂) :
    normInt_STR02904 (fun t => d₁ t ^ 2 * qT_STR02904 h t)
      = normInt_STR02904 (fun t => d₂ t ^ 2 * qT_STR02904 h t) := by
  rw [normInt_04_eq_33_STR02942, normInt_04_eq_33_STR02942]
  refine normInt_congr_ae_Ioc_STR02942 ?_
  filter_upwards [str029_42_weak_derivative_weighted_energy_entropy_passage_weak_derivative_ae_unique
    h₁ h₂] with t ht
  rw [ht]

/-- The `H¹` inner product `∫ u y dm + ∫ u' y' dm` of two periodic weak pairs `(u, u')` and `(y, y')`. -/
noncomputable def h1Pair_STR02942 (u u' y y' : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => u t * y t) + normInt_STR02933 (fun t => u' t * y' t)

/-- Weak convergence in the periodic Sobolev space `H¹`: the pairs `(u n, u' n)` and `(G, d)` are periodic weak
pairs, and the `H¹` pairing with every periodic weak pair `(y, y')` converges. -/
def WeaklyConvergesH1_STR02942 (u u' : ℕ → ℝ → ℝ) (G d : ℝ → ℝ) : Prop :=
  (∀ n, IsPeriodicWeakDerivative_STR02933 (u n) (u' n)) ∧ IsPeriodicWeakDerivative_STR02933 G d ∧
    ∀ y y' : ℝ → ℝ, IsPeriodicWeakDerivative_STR02933 y y' →
      Tendsto (fun n => h1Pair_STR02942 (u n) (u' n) y y') atTop (𝓝 (h1Pair_STR02942 G d y y'))

/-- STR029.42. Under the STR029.38 hypotheses, a further subsequence `σ` of the one of STR029.38 has a
uniform limit `G` with periodic weak derivative `d`, `g (σ n) ⇀ G` weakly in `H¹`, `g' (σ n) ⇀ d` weakly in
`L²`, `g (σ n) → G` in `L²(m)`, `∫ d² q_h dm ≤ liminf E (σ n)`, and `H (σ n) → ∫ G² log G² q_h dm`. -/
theorem str029_42_weak_derivative_weighted_energy_entropy_passage
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' F : ℕ → ℝ → ℝ} {E H : ℕ → ℝ} {K A : ℝ}
    (hg0 : ∀ n t, 0 ≤ g n t)
    (hH1 : ∀ n, IsPeriodicWeakDerivative_STR02933 (g n) (g' n))
    (hnorm : ∀ n, normInt_STR02904 (fun t => g n t ^ 2 * qT_STR02904 h t) = 1)
    (hE : ∀ n, E n = normInt_STR02904 (fun t => g' n t ^ 2 * qT_STR02904 h t))
    (hH : ∀ n, H n = normInt_STR02904
      (fun t => g n t ^ 2 * Real.log (g n t ^ 2) * qT_STR02904 h t))
    (hHpos : ∀ n, 0 < H n) (hquot : ∀ n, 4 * E n / (2 * H n) ≤ 2)
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2))
    (hFc : ∀ n, Continuous (F n)) (hFp : ∀ n, Function.Periodic (F n) (2 * π))
    (hFg : ∀ n, F n =ᵐ[volume.restrict (Ioc 0 (2 * π))] g n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ G d : ℝ → ℝ,
      (Continuous G ∧ Function.Periodic G (2 * π) ∧ (∀ t, 0 ≤ G t) ∧
        normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1 ∧
        TendstoUniformly (fun n => F (σ n)) G atTop ∧
        Tendsto (fun n => E (σ n)) atTop (𝓝 (liminf E atTop))) ∧
      IsPeriodicWeakDerivative_STR02933 G d ∧
      WeaklyConvergesH1_STR02942 (fun n => g (σ n)) (fun n => g' (σ n)) G d ∧
      (∀ x : ℝ → ℝ, MemLp x 2 (volume.restrict (Ioc 0 (2 * π))) →
        Tendsto (fun n => normInt_STR02933 (fun t => g' (σ n) t * x t)) atTop
          (𝓝 (normInt_STR02933 (fun t => d t * x t)))) ∧
      Tendsto (fun n => normInt_STR02933 (fun t => (g (σ n) t - G t) ^ 2)) atTop (𝓝 0) ∧
      normInt_STR02904 (fun t => d t ^ 2 * qT_STR02904 h t) ≤ liminf (fun n => E (σ n)) atTop ∧
      Tendsto (fun n => H (σ n)) atTop
        (𝓝 (normInt_STR02904 (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t))) := by
  obtain ⟨σ₀, hσ₀, G, hGc, hGp, hG0, hGn, hGu, hEσ₀⟩ :=
    str029_38_uniform_subsequence_preserving_energy_liminf hh hg0 hH1 hnorm hE hH hHpos hquot hK hA
      hFc hFp hFg
  have hg'mem : ∀ n, MemLp (g' n) 2 (volume.restrict (Ioc 0 (2 * π))) := fun n => (hH1 n).2.1.2
  -- the vectors `√q_h · g'_n` in `L²(m)`
  let v : ℕ → Lp ℝ 2 circleMeasure_STR02934 := fun n => sqrtLp_STR02942 h (hg'mem (σ₀ n))
  have hvE : ∀ n, ‖v n‖ ^ 2 = E (σ₀ n) := fun n => by
    rw [hE (σ₀ n), normInt_04_eq_33_STR02942]
    exact norm_sq_sqrtLp_STR02942 h (hg'mem (σ₀ n))
  obtain ⟨C₀, hC₀⟩ := hEσ₀.bddAbove_range
  have hvC : ∀ n, ‖v n‖ ≤ Real.sqrt C₀ := fun n => by
    refine Real.le_sqrt_of_sq_le ?_
    rw [hvE n]
    exact hC₀ ⟨n, rfl⟩
  obtain ⟨b⟩ := exists_hilbertBasis_nat_STR02942
  obtain ⟨τ, hτ, w, hw, hwE⟩ :=
    str029_41_weak_convergence_norm_lower_semicontinuity_chain b v (Real.sqrt C₀)
      (Real.sqrt_nonneg _) hvC
  have hσmono : StrictMono (fun n => σ₀ (τ n)) := hσ₀.comp hτ
  have hGu' : TendstoUniformly (fun n => F (σ₀ (τ n))) G atTop :=
    Metric.tendstoUniformly_iff.2 fun ε hε =>
      hτ.tendsto_atTop.eventually (Metric.tendstoUniformly_iff.1 hGu ε hε)
  have hEσ : Tendsto (fun n => E (σ₀ (τ n))) atTop (𝓝 (liminf E atTop)) :=
    hEσ₀.comp hτ.tendsto_atTop
  have hGmem := memLp_restrict_of_continuous_STR02942 hGc
  have hgF : ∀ n (y : ℝ → ℝ), normInt_STR02933 (fun t => g n t * y t)
      = normInt_STR02933 (fun t => F n t * y t) := by
    intro n y
    refine normInt_congr_ae_Ioc_STR02942 ?_
    filter_upwards [hFg n] with t ht
    rw [ht]
  -- weak convergence of the unweighted derivatives
  have hpair : ∀ x : ℝ → ℝ, MemLp x 2 (volume.restrict (Ioc 0 (2 * π))) →
      Tendsto (fun n => normInt_STR02933 (fun t => g' (σ₀ (τ n)) t * x t)) atTop
        (𝓝 (normInt_STR02933 (fun t => dFun_STR02942 h w t * x t))) := by
    intro x hx
    have key := hw (invSqrtLp_STR02942 h hx)
    rw [inner_dFun_STR02942 h w hx] at key
    refine Tendsto.congr (fun n => ?_) key
    exact inner_sqrtLp_invSqrtLp_STR02942 h (hg'mem (σ₀ (τ n))) hx
  -- the limit `d` is the weak derivative of `G`
  have hd : IsPeriodicWeakDerivative_STR02933 G (dFun_STR02942 h w) := by
    refine ⟨⟨hGp, hGmem⟩, ⟨periodic_dFun_STR02942 h w, memLp_dFun_STR02942 h w⟩, ?_⟩
    intro φ hφ
    have hφc : Continuous φ := hφ.1.continuous
    have hφ'c : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
    have hlim1 := hpair φ (memLp_restrict_of_continuous_STR02942 hφc)
    have hlim2 : Tendsto (fun n => normInt_STR02933 (fun t => g' (σ₀ (τ n)) t * φ t)) atTop
        (𝓝 (-normInt_STR02933 (fun t => G t * deriv φ t))) := by
      have key := (tendsto_normInt_mul_STR02942 (fun n => hFc (σ₀ (τ n))) hGc hGu'
        (integrable_of_memLp_STR02934 (memLp_restrict_of_continuous_STR02942 hφ'c))).neg
      refine Tendsto.congr (fun n => ?_) key
      rw [(hH1 (σ₀ (τ n))).2.2 φ hφ, hgF]
    exact tendsto_nhds_unique hlim1 hlim2
  -- weak convergence in `H¹`
  have hfun : ∀ y : ℝ → ℝ, MemLp y 2 (volume.restrict (Ioc 0 (2 * π))) →
      Tendsto (fun n => normInt_STR02933 (fun t => g (σ₀ (τ n)) t * y t)) atTop
        (𝓝 (normInt_STR02933 (fun t => G t * y t))) := by
    intro y hy
    have key := tendsto_normInt_mul_STR02942 (fun n => hFc (σ₀ (τ n))) hGc hGu'
      (integrable_of_memLp_STR02934 hy)
    exact Tendsto.congr (fun n => (hgF _ y).symm) key
  have hH1lim : WeaklyConvergesH1_STR02942 (fun n => g (σ₀ (τ n))) (fun n => g' (σ₀ (τ n))) G
      (dFun_STR02942 h w) := by
    refine ⟨fun n => hH1 (σ₀ (τ n)), hd, fun y y' hy => ?_⟩
    exact (hfun y hy.1.2).add (hpair y' hy.2.1.2)
  -- strong `L²` convergence of the functions
  have hstrong : Tendsto (fun n => normInt_STR02933 (fun t => (g (σ₀ (τ n)) t - G t) ^ 2)) atTop
      (𝓝 0) := by
    refine Tendsto.congr (fun n => ?_)
      (tendsto_normInt_sq_sub_STR02942 (fun n => hFc (σ₀ (τ n))) hGc hGu')
    refine normInt_congr_ae_Ioc_STR02942 ?_
    filter_upwards [hFg (σ₀ (τ n))] with t ht
    rw [ht]
  -- lower semicontinuity of the weighted energy
  have hen : normInt_STR02904 (fun t => dFun_STR02942 h w t ^ 2 * qT_STR02904 h t)
      ≤ liminf (fun n => E (σ₀ (τ n))) atTop := by
    rw [energy_dFun_STR02942]
    have e : (fun n => ‖v (τ n)‖ ^ 2) = fun n => E (σ₀ (τ n)) := funext fun n => hvE (τ n)
    rw [← e]
    exact hwE
  -- entropy passage
  have hent : Tendsto (fun n => H (σ₀ (τ n))) atTop
      (𝓝 (normInt_STR02904 (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t))) := by
    rw [normInt_04_eq_33_STR02942]
    refine Tendsto.congr (fun n => ?_)
      (tendsto_normInt_entropy_STR02942 h (fun n => hFc (σ₀ (τ n))) hGc hGu')
    rw [hH (σ₀ (τ n)), normInt_04_eq_33_STR02942]
    refine normInt_congr_ae_Ioc_STR02942 ?_
    filter_upwards [hFg (σ₀ (τ n))] with t ht
    rw [ht]
  exact ⟨fun n => σ₀ (τ n), hσmono, G, dFun_STR02942 h w, ⟨hGc, hGp, hG0, hGn, hGu', hEσ⟩, hd,
    hH1lim, hpair, hstrong, hen, hent⟩

end DGPS.Frontier.STR029
