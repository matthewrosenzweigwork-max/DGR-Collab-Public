import DGPS.Foundations.Entropy
import DGPS.Foundations.SobolevEntropy

/-!
# Uniform square integrability from a defective entropy bound (LIP050)

Abstract setting: for each `n` a probability space `(Ω n, P n)`, a real-valued energy `E n` on
functions `Ω n → ℝ` and a class of tests `S n`.  The *defective entropy bound* with constants
`A C : ℝ` says `Ent_{P n}(f²) ≤ A · E n f + C ∫ f² dP n` for every `f ∈ S n` (the right side is
read in `ℝ≥0∞` through `ENNReal.ofReal`).

* `DGPS.Analysis.UniformSquareIntegrable P f`: the squares `f i ^ 2` are uniformly integrable,
  i.e. for every `ε > 0` there is `K` with `∫_{f i ^ 2 > K} f i ^ 2 dP i ≤ ε` for all `i`.
* `DGPS.Analysis.uniform_square_integrability_from_a_defective_entropy_bound`: any family of
  tests of the class with uniformly bounded `L²` masses and energies is uniformly square
  integrable.  The class `S` is arbitrary, so the statement applies verbatim to normalized
  tests and affine rescalings of tests whenever these lie in the class.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Analysis

/-- Uniform integrability of the squares of a family `f i : Ω i → ℝ` over probability spaces
`(Ω i, P i)`: the tails `∫_{f i ^ 2 > K} f i ^ 2` are uniformly small. -/
def UniformSquareIntegrable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) (f : ∀ i, Ω i → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ i, ∫ x in {x | K < f i x ^ 2}, f i x ^ 2 ∂P i ≤ ε

/-- Single-space tail estimate: if `Ent_P(v) ≤ ofReal R`, `∫ v ≤ M'` with `M' > 0`, then the
tail of `v` above `M' exp (2 + R/ε)` has integral at most `ε`. -/
theorem tail_integral_le_of_entropy_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {v : Ω → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hvm : Measurable v) (hvi : Integrable v P)
    {M' R ε : ℝ} (hM' : 0 < M') (haM : ∫ x, v x ∂P ≤ M') (hR : 0 ≤ R) (hε : 0 < ε)
    (hent : homogeneousEntropy P v ≤ ENNReal.ofReal R) :
    ∫ x in {x | M' * Real.exp (2 + R / ε) < v x}, v x ∂P ≤ ε := by
  set a := ∫ x, v x ∂P with ha
  have ha0 : 0 ≤ a := integral_nonneg hv0
  rcases ha0.eq_or_lt with h0 | h0
  · have : ∫ x in {x | M' * Real.exp (2 + R / ε) < v x}, v x ∂P ≤ a :=
      setIntegral_le_integral hvi (Filter.Eventually.of_forall hv0)
    rw [← h0] at this
    linarith
  set K := M' * Real.exp (2 + R / ε) with hK
  set L : ℝ := 1 + R / ε with hL
  have hRε : 0 ≤ R / ε := div_nonneg hR hε.le
  have hLpos : 0 < L := by rw [hL]; linarith
  have hKM : M' ≤ K := by
    have : 1 ≤ Real.exp (2 + R / ε) := Real.one_le_exp (by linarith)
    rw [hK]; nlinarith
  have hlogK : Real.log (K / M') = 2 + R / ε := by
    rw [hK, mul_div_cancel_left₀ _ hM'.ne', Real.log_exp]
  -- the entropy integrand
  set g : Ω → ℝ := fun x => entropyIntegrand a (v x) with hg
  have hgnn : ∀ x, 0 ≤ g x := fun x => entropyIntegrand_nonneg h0 (hv0 x)
  have hgm : Measurable g := by
    simp only [hg, entropyIntegrand]
    fun_prop
  have hent' : ∫⁻ x, ENNReal.ofReal (g x) ∂P ≤ ENNReal.ofReal R := by
    have := hent
    rwa [homogeneousEntropy_of_integral_ne_zero h0.ne'] at this
  have hgi : Integrable g P := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hgnn)]
    exact lt_of_le_of_lt hent' ENNReal.ofReal_lt_top
  have hgint : ∫ x, g x ∂P ≤ R := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgnn)
      hgm.aestronglyMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hent'
    rwa [ENNReal.toReal_ofReal hR] at this
  have hset : MeasurableSet {x | K < v x} := measurableSet_lt measurable_const hvm
  -- pointwise: `L v ≤ g` on the tail
  have hpt : ∀ x ∈ {x | K < v x}, L * v x ≤ g x := by
    intro x hx
    have hxK : K < v x := hx
    have hvpos : 0 < v x := lt_trans (lt_of_lt_of_le hM' hKM) hxK
    have haM' : a ≤ M' := haM
    have h1 : K / M' ≤ v x / a := by
      rw [div_le_div_iff₀ hM' h0]
      nlinarith [mul_nonneg ha0 (sub_nonneg.2 hxK.le), mul_nonneg hvpos.le (sub_nonneg.2 haM')]
    have h2 : 2 + R / ε ≤ Real.log (v x / a) := by
      rw [← hlogK]
      exact Real.log_le_log (div_pos (lt_of_lt_of_le hM' hKM) hM') h1
    simp only [hg, entropyIntegrand]
    nlinarith [mul_le_mul_of_nonneg_left h2 hvpos.le]
  have hI1 : IntegrableOn (fun x => L * v x) {x | K < v x} P := (hvi.const_mul L).integrableOn
  have hI2 : IntegrableOn g {x | K < v x} P := hgi.integrableOn
  have hmono : ∫ x in {x | K < v x}, L * v x ∂P ≤ ∫ x in {x | K < v x}, g x ∂P :=
    setIntegral_mono_on hI1 hI2 hset hpt
  have hle : ∫ x in {x | K < v x}, g x ∂P ≤ ∫ x, g x ∂P :=
    setIntegral_le_integral hgi (Filter.Eventually.of_forall hgnn)
  rw [integral_const_mul] at hmono
  have hfin : L * ∫ x in {x | K < v x}, v x ∂P ≤ R := hmono.trans (hle.trans hgint)
  have hRL : R ≤ ε * L := by
    rw [hL]; field_simp; linarith
  have : L * (∫ x in {x | K < v x}, v x ∂P) ≤ L * ε := by nlinarith
  exact le_of_mul_le_mul_left this hLpos

/-- LIP050.  Let `(Ω n, P n)` be probability spaces with energies `E n` and a class of tests
`S n` (measurable, with integrable square), obeying the defective entropy bound
`Ent_{P n}(f²) ≤ A E n f + C ∫ f² dP n` for all `f ∈ S n`, with fixed constants `A C`.
Any family `f i ∈ S (n i)` with `∫ (f i)² ≤ M` and `|E (n i) (f i)| ≤ B` has uniformly
integrable squares.  Since `S` is an arbitrary class, this covers normalized tests and affine
rescalings whenever they lie in the class. -/
theorem uniform_square_integrability_from_a_defective_entropy_bound
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (E : ∀ n, (Ω n → ℝ) → ℝ) (S : ∀ n, Set (Ω n → ℝ))
    (A C : ℝ)
    (hmeas : ∀ n, ∀ f ∈ S n, Measurable f)
    (hint : ∀ n, ∀ f ∈ S n, Integrable (fun x => f x ^ 2) (P n))
    (hdef : ∀ n, ∀ f ∈ S n, homogeneousEntropy (P n) (fun x => f x ^ 2)
      ≤ ENNReal.ofReal (A * E n f + C * ∫ x, f x ^ 2 ∂P n))
    {ι : Type*} (n : ι → ℕ) (f : ∀ i, Ω (n i) → ℝ) (hf : ∀ i, f i ∈ S (n i))
    (M B : ℝ) (hM : ∀ i, ∫ x, f i x ^ 2 ∂P (n i) ≤ M) (hB : ∀ i, |E (n i) (f i)| ≤ B) :
    UniformSquareIntegrable (fun i => P (n i)) f := by
  intro ε hε
  set M' : ℝ := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set R : ℝ := |A| * max B 0 + |C| * M' with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨M' * Real.exp (2 + R / ε), fun i => ?_⟩
  have hmi := hmeas _ _ (hf i)
  have hsq0 : ∀ x, 0 ≤ f i x ^ 2 := fun x => sq_nonneg _
  have hmass : ∫ x, f i x ^ 2 ∂P (n i) ≤ M' := (hM i).trans (le_max_left _ _)
  have hmass0 : 0 ≤ ∫ x, f i x ^ 2 ∂P (n i) := integral_nonneg hsq0
  refine tail_integral_le_of_entropy_le (v := fun x => f i x ^ 2) hsq0 (by fun_prop)
    (hint _ _ (hf i)) hM'pos hmass hR0 hε ?_
  refine (hdef _ _ (hf i)).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : A * E (n i) (f i) ≤ |A| * max B 0 := by
    calc A * E (n i) (f i) ≤ |A * E (n i) (f i)| := le_abs_self _
      _ = |A| * |E (n i) (f i)| := abs_mul _ _
      _ ≤ |A| * max B 0 := by
        gcongr
        exact (hB i).trans (le_max_left _ _)
  have h2 : C * ∫ x, f i x ^ 2 ∂P (n i) ≤ |C| * M' := by
    calc C * ∫ x, f i x ^ 2 ∂P (n i) ≤ |C| * ∫ x, f i x ^ 2 ∂P (n i) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hmass0
      _ ≤ |C| * M' := by gcongr
  linarith

end DGPS.Analysis
