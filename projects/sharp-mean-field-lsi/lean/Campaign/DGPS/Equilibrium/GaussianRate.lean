import DGPS.Equilibrium.Hessian
import DGPS.Analysis.RelativeFisher
import DGPS.Foundations.WeakSobolev
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Poincaré rate and Gaussian Hessian rate (DEF027)

INTERFACES/definitions.md §5–6, common_lemmas.md DEF027, `PINNED_MANUSCRIPT/lower_bounds.tex`
eq:gaussian-rate.

For a probability measure `μ` on the torus (in the applications a bounded positive reference
`μ = w m`):

* `weightedVariance μ u = ∫ (u - μ(u))² dμ`;
* `IsMeasureWeakGradient μ u g` is the weighted weak gradient relation: `u ∈ L²(μ)`,
  `g ∈ L²(μ; ℝ^d)`, `u, g` are Haar-integrable and `∫ u ∂ⱼφ dm = -∫ gⱼ φ dm` for every smooth
  periodic `φ`.  `WeakH1Test μ` bundles a function with a weak gradient; this is the weighted weak
  form domain (it is the Haar `H¹` domain when `μ` has a density bounded above and below, see
  `isMeasureWeakGradient_iff` below);
* `dirichletEnergy μ f = ∫ |∇f|² dμ` in `ℝ≥0∞`;
* `poincareRate μ = inf_{Var_μ(f) > 0} ∫|∇f|² dμ / Var_μ(f)` over `WeakH1Test μ`;
* for coercive `H = I + T` (`IsCoerciveDensityHessian A μ`), the bounded inverse
  `densityCovariance A μ hH = H⁻¹` on `L²_0(μ)` is built by Lax–Milgram, and
  `gaussianRate A μ hH = inf_{f ∈ H¹(μ), μ(f)=0, f ≠ 0} ∫|∇f|² dμ / ⟨f, C f⟩`.

Both rates are basis-free quadratic-form quotients with values in `ℝ≥0∞`.  No commutation of
`C` with the generator is assumed (spectral coordinates are the separate theorem FOU020).
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-! ### The weighted weak form domain -/

/-- `g` is a weak gradient of `u` for the probability `μ`: `u ∈ L²(μ)`, `g ∈ L²(μ; ℝ^d)`, both are
Haar-integrable (so the distributional pairing is meaningful) and `∫ u ∂ⱼφ dm = -∫ gⱼ φ dm` for
every smooth periodic `φ`. -/
structure IsMeasureWeakGradient (μ : ProbabilityMeasure (Torus d)) (u : Torus d → ℝ)
    (g : Torus d → Tangent d) : Prop where
  memLp : MemLp u 2 (μ : Measure (Torus d))
  memLp_grad : MemLp g 2 (μ : Measure (Torus d))
  integrable : Integrable u (haar d)
  integrable_grad : Integrable g (haar d)
  ibp : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → ∀ j : Fin d,
    ∫ x, u x * coordPartial j φ x ∂haar d = -∫ x, g x j * φ x ∂haar d

/-- An element of the weighted weak form domain together with a chosen weak gradient. -/
structure WeakH1Test (μ : ProbabilityMeasure (Torus d)) where
  fn : Torus d → ℝ
  grad : Torus d → Tangent d
  isWeak : IsMeasureWeakGradient μ fn grad

/-- The weighted variance `∫ (u - μ(u))² dμ`. -/
noncomputable def weightedVariance (μ : ProbabilityMeasure (Torus d)) (u : Torus d → ℝ) : ℝ :=
  ∫ x, (u x - ∫ y, u y ∂(μ : Measure (Torus d))) ^ 2 ∂(μ : Measure (Torus d))

/-- The Dirichlet energy `∫ |∇f|² dμ` of a test function, in `ℝ≥0∞`. -/
noncomputable def dirichletEnergy (μ : ProbabilityMeasure (Torus d)) (f : WeakH1Test μ) : ℝ≥0∞ :=
  ∫⁻ x, ‖f.grad x‖ₑ ^ 2 ∂(μ : Measure (Torus d))

theorem weightedVariance_nonneg (μ : ProbabilityMeasure (Torus d)) (u : Torus d → ℝ) :
    0 ≤ weightedVariance μ u :=
  integral_nonneg fun _ => sq_nonneg _

/-- For a bounded positive reference `P = w m`, the weighted weak gradient relation of DEF022
(`IsWeightedWeakGradient`) coincides with `IsMeasureWeakGradient`; in particular the form domain
is the full weighted `H¹(P)` of `WeightedH1 P`. -/
theorem isMeasureWeakGradient_iff (P : BoundedPositiveReference d) {u : Torus d → ℝ}
    {g : Torus d → Tangent d} :
    IsMeasureWeakGradient ⟨P.measure, P.isProbabilityMeasure⟩ u g ↔ IsWeightedWeakGradient P u g := by
  constructor
  · intro h
    exact ⟨h.memLp, h.memLp_grad, h.ibp⟩
  · intro h
    have h1 := (P.memLp_measure_iff.1 h.memLp)
    have h2 := (P.memLp_measure_iff.1 h.memLp_grad)
    exact ⟨h.memLp, h.memLp_grad, h1.integrable one_le_two, h2.integrable one_le_two, h.ibp⟩

/-! ### The Poincaré rate -/

/-- The Poincaré quotient `∫|∇f|² dμ / Var_μ(f)` in `ℝ≥0∞`. -/
noncomputable def poincareQuotient (μ : ProbabilityMeasure (Torus d)) (f : WeakH1Test μ) : ℝ≥0∞ :=
  dirichletEnergy μ f / ENNReal.ofReal (weightedVariance μ f.fn)

/-- DEF027: the Poincaré rate `λ_P(μ) = inf_{Var_μ(f) > 0} ∫|∇f|² dμ / Var_μ(f)` over the full
weighted weak `H¹(μ)` form domain. -/
noncomputable def poincareRate (μ : ProbabilityMeasure (Torus d)) : ℝ≥0∞ :=
  ⨅ f : {f : WeakH1Test μ // 0 < weightedVariance μ f.fn}, poincareQuotient μ f.1

theorem poincareRate_le_quotient (μ : ProbabilityMeasure (Torus d)) (f : WeakH1Test μ)
    (hf : 0 < weightedVariance μ f.fn) : poincareRate μ ≤ poincareQuotient μ f :=
  iInf_le (fun g : {f : WeakH1Test μ // 0 < weightedVariance μ f.fn} => poincareQuotient μ g.1)
    ⟨f, hf⟩

theorem le_poincareRate_iff (μ : ProbabilityMeasure (Torus d)) (r : ℝ≥0∞) :
    r ≤ poincareRate μ ↔ ∀ f : WeakH1Test μ, 0 < weightedVariance μ f.fn →
      r ≤ poincareQuotient μ f := by
  unfold poincareRate
  rw [le_iInf_iff]
  exact ⟨fun h f hf => h ⟨f, hf⟩, fun h f => h f.1 f.2⟩

/-- A Poincaré inequality with constant `r` in the multiplicative form
`r Var_μ(f) ≤ ∫|∇f|² dμ` holds for all tests iff `r ≤ poincareRate μ`. -/
theorem le_poincareRate_iff_forall (μ : ProbabilityMeasure (Torus d)) (r : ℝ≥0∞) :
    r ≤ poincareRate μ ↔ ∀ f : WeakH1Test μ, 0 < weightedVariance μ f.fn →
      r * ENNReal.ofReal (weightedVariance μ f.fn) ≤ dirichletEnergy μ f := by
  rw [le_poincareRate_iff]
  refine forall_congr' fun f => imp_congr_right fun hf => ?_
  unfold poincareQuotient
  have h0 : ENNReal.ofReal (weightedVariance μ f.fn) ≠ 0 := (ENNReal.ofReal_pos.2 hf).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top)]

/-! ### The inverse Hessian -/

section Covariance

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

/-- The pairing of a function with the constant `1` in `L²(μ)` computes the mean. -/
theorem inner_const_one (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    inner ℝ (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)) f = ∫ x, f x ∂(μ : Measure (Torus d)) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const (E := ℝ) (p := 2) (μ : Measure (Torus d)) (1 : ℝ)] with x hx
  rw [hx]; simp

theorem isClosed_centeredL2 : IsClosed (centeredL2 μ : Set (Lp ℝ 2 (μ : Measure (Torus d)))) := by
  have : (centeredL2 μ : Set (Lp ℝ 2 (μ : Measure (Torus d)))) =
      (fun f => inner ℝ (Lp.const 2 (μ : Measure (Torus d)) (1 : ℝ)) f) ⁻¹' {0} := by
    ext f
    simp [mem_centeredL2, inner_const_one]
  rw [this]
  exact isClosed_singleton.preimage (continuous_const.inner continuous_id)

instance : CompleteSpace (centeredL2 μ) :=
  (isClosed_centeredL2 μ).completeSpace_coe

/-- The bilinear form `(f, g) ↦ ⟨H f, g⟩` of the density Hessian. -/
noncomputable def hessianForm : centeredL2 μ →L[ℝ] centeredL2 μ →L[ℝ] ℝ :=
  (innerSL ℝ : centeredL2 μ →L[ℝ] centeredL2 μ →L[ℝ] ℝ).comp (densityHessian A μ)

theorem hessianForm_apply (f g : centeredL2 μ) :
    hessianForm A μ f g = inner ℝ (densityHessian A μ f) g := rfl

/-- Coercivity of the density Hessian gives Lax–Milgram coercivity of its form. -/
theorem isCoercive_hessianForm (hH : IsCoerciveDensityHessian A μ) :
    IsCoercive (hessianForm A μ) := by
  obtain ⟨c, hc, h⟩ := hH
  refine ⟨c, hc, fun f => ?_⟩
  rw [hessianForm_apply, real_inner_comm]
  calc c * ‖f‖ * ‖f‖ = c * ‖f‖ ^ 2 := by ring
    _ ≤ _ := h f

/-- The Hessian as a continuous linear equivalence of `L²_0(μ)` (Lax–Milgram). -/
noncomputable def hessianEquiv (hH : IsCoerciveDensityHessian A μ) :
    centeredL2 μ ≃L[ℝ] centeredL2 μ :=
  (isCoercive_hessianForm A μ hH).continuousLinearEquivOfBilin

theorem hessianEquiv_apply (hH : IsCoerciveDensityHessian A μ) (f : centeredL2 μ) :
    hessianEquiv A μ hH f = densityHessian A μ f := by
  refine ext_inner_right ℝ fun w => ?_
  rw [hessianEquiv, IsCoercive.continuousLinearEquivOfBilin_apply, hessianForm_apply]

/-- The bounded centered inverse `C_μ = H_μ⁻¹` on `L²_0(μ)`, defined under Hessian coercivity. -/
noncomputable def densityCovariance (hH : IsCoerciveDensityHessian A μ) :
    centeredL2 μ →L[ℝ] centeredL2 μ :=
  ((hessianEquiv A μ hH).symm : centeredL2 μ ≃L[ℝ] centeredL2 μ)

theorem densityHessian_densityCovariance (hH : IsCoerciveDensityHessian A μ) (f : centeredL2 μ) :
    densityHessian A μ (densityCovariance A μ hH f) = f := by
  rw [← hessianEquiv_apply A μ hH]
  exact (hessianEquiv A μ hH).apply_symm_apply f

theorem densityCovariance_densityHessian (hH : IsCoerciveDensityHessian A μ) (f : centeredL2 μ) :
    densityCovariance A μ hH (densityHessian A μ f) = f := by
  rw [← hessianEquiv_apply A μ hH]
  exact (hessianEquiv A μ hH).symm_apply_apply f

/-- `⟨f, C f⟩ = ⟨H h, h⟩` with `h = C f`. -/
theorem inner_densityCovariance_eq (hH : IsCoerciveDensityHessian A μ) (f : centeredL2 μ) :
    inner ℝ f (densityCovariance A μ hH f) =
      inner ℝ (densityHessian A μ (densityCovariance A μ hH f)) (densityCovariance A μ hH f) := by
  rw [densityHessian_densityCovariance]

theorem densityCovariance_symmetric (hH : IsCoerciveDensityHessian A μ) (f g : centeredL2 μ) :
    inner ℝ (densityCovariance A μ hH f) g = inner ℝ f (densityCovariance A μ hH g) := by
  have hs : ∀ a b : centeredL2 μ, inner ℝ (densityHessian A μ a) b = inner ℝ a (densityHessian A μ b) := by
    intro a b
    have h1 : inner ℝ (densityHessian A μ a) b = inner ℝ a b + inner ℝ (centeredInteraction A μ a) b := by
      rw [← inner_add_left]; rfl
    have h2 : inner ℝ a (densityHessian A μ b) = inner ℝ a b + inner ℝ a (centeredInteraction A μ b) := by
      rw [← inner_add_right]; rfl
    rw [h1, h2, centeredInteraction_symmetric]
  calc inner ℝ (densityCovariance A μ hH f) g
      = inner ℝ (densityCovariance A μ hH f)
          (densityHessian A μ (densityCovariance A μ hH g)) := by
        rw [densityHessian_densityCovariance]
    _ = inner ℝ (densityHessian A μ (densityCovariance A μ hH f)) (densityCovariance A μ hH g) :=
        (hs _ _).symm
    _ = inner ℝ f (densityCovariance A μ hH g) := by rw [densityHessian_densityCovariance]

/-- Positivity of the covariance form: `⟨f, C f⟩ > 0` for `f ≠ 0`. -/
theorem inner_densityCovariance_pos (hH : IsCoerciveDensityHessian A μ) {f : centeredL2 μ}
    (hf : f ≠ 0) : 0 < inner ℝ f (densityCovariance A μ hH f) := by
  obtain ⟨c, hc, h⟩ := hH
  have hH' : IsCoerciveDensityHessian A μ := ⟨c, hc, h⟩
  rw [inner_densityCovariance_eq A μ hH', real_inner_comm]
  have hne : densityCovariance A μ hH' f ≠ 0 := fun h0 => by
    apply hf
    rw [← densityHessian_densityCovariance A μ hH' f, h0, map_zero]
  exact lt_of_lt_of_le (by positivity) (h _)

theorem inner_densityCovariance_nonneg (hH : IsCoerciveDensityHessian A μ) (f : centeredL2 μ) :
    0 ≤ inner ℝ f (densityCovariance A μ hH f) := by
  by_cases hf : f = 0
  · simp [hf]
  · exact (inner_densityCovariance_pos A μ hH hf).le

end Covariance

/-! ### The Gaussian Hessian rate -/

section Gaussian

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

/-- The class of a centered test function in `L²_0(μ)`. -/
noncomputable def WeakH1Test.toCentered (f : WeakH1Test μ) (hf : ∫ x, f.fn x ∂(μ : Measure (Torus d)) = 0) :
    centeredL2 μ :=
  ⟨f.isWeak.memLp.toLp f.fn, by
    rw [mem_centeredL2]
    rw [integral_congr_ae f.isWeak.memLp.coeFn_toLp]
    exact hf⟩

/-- The set of nonzero centered tests: `μ(f) = 0` and `f ≠ 0` in `L²(μ)`. -/
def IsNonzeroCentered (μ : ProbabilityMeasure (Torus d)) (f : WeakH1Test μ) : Prop :=
  (∫ x, f.fn x ∂(μ : Measure (Torus d)) = 0) ∧ ¬ f.fn =ᵐ[(μ : Measure (Torus d))] 0

/-- The inverse-Hessian covariance form `⟨f, C f⟩` of a nonzero centered test. -/
noncomputable def gaussianDenominator (hH : IsCoerciveDensityHessian A μ) (f : WeakH1Test μ)
    (hf : ∫ x, f.fn x ∂(μ : Measure (Torus d)) = 0) : ℝ :=
  inner ℝ (f.toCentered μ hf) (densityCovariance A μ hH (f.toCentered μ hf))

theorem toCentered_ne_zero {f : WeakH1Test μ} (hf : IsNonzeroCentered μ f) :
    f.toCentered μ hf.1 ≠ 0 := by
  intro h
  apply hf.2
  have h' : f.isWeak.memLp.toLp f.fn = 0 := congrArg Subtype.val h
  have := Lp.eq_zero_iff_ae_eq_zero.1 h'
  exact f.isWeak.memLp.coeFn_toLp.symm.trans this

theorem gaussianDenominator_pos (hH : IsCoerciveDensityHessian A μ) {f : WeakH1Test μ}
    (hf : IsNonzeroCentered μ f) : 0 < gaussianDenominator A μ hH f hf.1 :=
  inner_densityCovariance_pos A μ hH (toCentered_ne_zero μ hf)

/-- The Gaussian quotient `∫|∇f|² dμ / ⟨f, C f⟩` in `ℝ≥0∞`. -/
noncomputable def gaussianQuotient (hH : IsCoerciveDensityHessian A μ) (f : WeakH1Test μ)
    (hf : ∫ x, f.fn x ∂(μ : Measure (Torus d)) = 0) : ℝ≥0∞ :=
  dirichletEnergy μ f / ENNReal.ofReal (gaussianDenominator A μ hH f hf)

/-- DEF027: the Gaussian Hessian rate
`λ_G = inf_{f ∈ H¹(μ), μ(f) = 0, f ≠ 0} ∫|∇f|² dμ / ⟨f, C_μ f⟩` with `C_μ = H_μ⁻¹`, defined only
under Hessian coercivity. -/
noncomputable def gaussianRate (hH : IsCoerciveDensityHessian A μ) : ℝ≥0∞ :=
  ⨅ f : {f : WeakH1Test μ // IsNonzeroCentered μ f}, gaussianQuotient A μ hH f.1 f.2.1

theorem gaussianRate_le_quotient (hH : IsCoerciveDensityHessian A μ) (f : WeakH1Test μ)
    (hf : IsNonzeroCentered μ f) : gaussianRate A μ hH ≤ gaussianQuotient A μ hH f hf.1 :=
  iInf_le (fun g : {f : WeakH1Test μ // IsNonzeroCentered μ f} =>
    gaussianQuotient A μ hH g.1 g.2.1) ⟨f, hf⟩

theorem le_gaussianRate_iff (hH : IsCoerciveDensityHessian A μ) (r : ℝ≥0∞) :
    r ≤ gaussianRate A μ hH ↔ ∀ (f : WeakH1Test μ) (hf : IsNonzeroCentered μ f),
      r ≤ gaussianQuotient A μ hH f hf.1 := by
  unfold gaussianRate
  rw [le_iInf_iff]
  exact ⟨fun h f hf => h ⟨f, hf⟩, fun h f => h f.1 f.2⟩

/-- Multiplicative form: `r ⟨f, C f⟩ ≤ ∫|∇f|² dμ` for every nonzero centered test iff
`r ≤ gaussianRate`. -/
theorem le_gaussianRate_iff_forall (hH : IsCoerciveDensityHessian A μ) (r : ℝ≥0∞) :
    r ≤ gaussianRate A μ hH ↔ ∀ (f : WeakH1Test μ) (hf : IsNonzeroCentered μ f),
      r * ENNReal.ofReal (gaussianDenominator A μ hH f hf.1) ≤ dirichletEnergy μ f := by
  rw [le_gaussianRate_iff]
  refine forall_congr' fun f => forall_congr' fun hf => ?_
  unfold gaussianQuotient
  have h0 : ENNReal.ofReal (gaussianDenominator A μ hH f hf.1) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (gaussianDenominator_pos A μ hH hf)).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top)]

end Gaussian

end DGPS
