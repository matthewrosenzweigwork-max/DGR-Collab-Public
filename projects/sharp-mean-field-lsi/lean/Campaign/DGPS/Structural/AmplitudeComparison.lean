import DGPS.Equilibrium.GaussianRate

/-!
# Full-product oscillation controls the Hessian upper bound (STR014)

Frozen source: `campaign/frozen_gibbs_rate_comparison.md` §4.  For a probability measure `μ` on the
torus (in the application a Gibbs equilibrium) and interaction data `A`, put
`B = osc W = sup W - inf W` on the FULL product torus.  On centered real `L²(μ)`:

* `|⟨f, T f⟩| ≤ (B/2) ‖f‖²` (`centeredInteraction_form_bound_oscillation`);
* `H = I + T ≤ (1 + B/2) I` (`densityHessian_form_le`);
* if `H` is coercive, `⟨g, H⁻¹ g⟩ ≥ ‖g‖² / (1 + B/2)` (`norm_sq_div_le_inner_densityCovariance`),
  proved by Cauchy–Schwarz for the form of `H`, without an operator-monotone theorem;
* `λ_G ≤ (1 + B/2) λ_P(μ)` (`gaussianRate_le_hessianUpper_poincare`).

No commutation of `T` with the reference generator is assumed and no Gibbs property of `μ` is used.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Structural

variable {d : ℕ}

/-- The oscillation `osc W = sup W - inf W` of the interaction on the FULL product torus. -/
noncomputable def interactionOscillation (A : InteractionData d) : ℝ :=
  sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) -
    sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2)

section Oscillation

variable (A : InteractionData d)

theorem interaction_range_bddAbove :
    BddAbove (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) :=
  (isCompact_range A.W_continuous).bddAbove

theorem interaction_range_bddBelow :
    BddBelow (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) :=
  (isCompact_range A.W_continuous).bddBelow

theorem interaction_le_sSup (x y : Torus d) :
    A.W x y ≤ sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) :=
  le_csSup (interaction_range_bddAbove A) ⟨(x, y), rfl⟩

theorem sInf_le_interaction (x y : Torus d) :
    sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) ≤ A.W x y :=
  csInf_le (interaction_range_bddBelow A) ⟨(x, y), rfl⟩

theorem interactionOscillation_nonneg : 0 ≤ interactionOscillation A := by
  have h := (sInf_le_interaction A (Classical.arbitrary _) (Classical.arbitrary _)).trans
    (interaction_le_sSup A (Classical.arbitrary _) (Classical.arbitrary _))
  unfold interactionOscillation
  linarith

/-- After subtracting the midpoint, the interaction is at most `B/2` in absolute value. -/
theorem abs_interaction_sub_midpoint_le (x y : Torus d) :
    |A.W x y - (sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) +
        sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2)) / 2| ≤
      interactionOscillation A / 2 := by
  have h1 := interaction_le_sSup A x y
  have h2 := sInf_le_interaction A x y
  unfold interactionOscillation
  rw [abs_le]
  constructor <;> linarith

end Oscillation

/-! ### Elementary integral facts -/

section Integrals

variable (μ : ProbabilityMeasure (Torus d))

theorem norm_sq_eq_integral_sq (h : Lp ℝ 2 (μ : Measure (Torus d))) :
    ‖h‖ ^ 2 = ∫ x, (h x) ^ 2 ∂(μ : Measure (Torus d)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [sq]

theorem sq_integral_abs_le (h : Lp ℝ 2 (μ : Measure (Torus d))) :
    (∫ x, |h x| ∂(μ : Measure (Torus d))) ^ 2 ≤ ‖h‖ ^ 2 := by
  rw [norm_sq_eq_integral_sq]
  set c := ∫ x, |h x| ∂(μ : Measure (Torus d)) with hc
  have hi : Integrable (fun x => |h x|) (μ : Measure (Torus d)) := (integrable_lp μ h).abs
  have hsq : Integrable (fun x => (h x) ^ 2) (μ : Measure (Torus d)) :=
    (Lp.memLp h).integrable_sq
  have key : 0 ≤ ∫ x, (|h x| - c) ^ 2 ∂(μ : Measure (Torus d)) :=
    integral_nonneg fun _ => sq_nonneg _
  have e : ∀ x, (|h x| - c) ^ 2 = (h x) ^ 2 - 2 * c * |h x| + c ^ 2 := fun x => by
    rw [sub_sq, sq_abs]; ring
  simp_rw [e] at key
  have hA : Integrable (fun x => (h x) ^ 2 - 2 * c * |h x|) (μ : Measure (Torus d)) :=
    hsq.sub (hi.const_mul _)
  rw [integral_add hA (integrable_const _), integral_sub hsq (hi.const_mul _),
    integral_const_mul] at key
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at key
  rw [← hc] at key
  nlinarith

end Integrals

/-! ### The oscillation bound on the interaction form -/

section Form

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

/-- STR014, first output: on centered `L²(μ)`, `|⟨f, T f⟩| ≤ (B/2) ‖f‖²`, `B = osc W`. -/
theorem centeredInteraction_form_bound_oscillation (f : centeredL2 μ) :
    |inner ℝ f (centeredInteraction A μ f)| ≤ interactionOscillation A / 2 * ‖f‖ ^ 2 := by
  set φ : Torus d → ℝ := ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) with hφ
  set m : ℝ := (sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) +
        sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2)) / 2 with hm
  have hf0 : ∫ x, φ x ∂(μ : Measure (Torus d)) = 0 := f.2
  have hfi : Integrable φ (μ : Measure (Torus d)) := integrable_lp μ _
  have h1 : inner ℝ f (centeredInteraction A μ f) =
      ∫ p, centeredKernel A μ p.1 p.2 * (φ p.1 * φ p.2) ∂((μ : Measure (Torus d)).prod μ) :=
    inner_kernelOp A μ _ _
  rw [h1, integral_centeredKernel_form A μ f]
  have i1 := integrable_prod_cont_mul μ (fun p => A.W p.1 p.2) A.W_continuous hfi hfi
  have i4 := integrable_prod_cont_mul μ (fun _ => m) continuous_const hfi hfi
  have z4 : ∫ p : Torus d × Torus d, m * (φ p.1 * φ p.2)
      ∂((μ : Measure (Torus d)).prod μ) = 0 := by
    rw [integral_const_mul, integral_prod_mul φ φ, hf0]; simp
  have hsub : ∫ p : Torus d × Torus d, A.W p.1 p.2 * (φ p.1 * φ p.2)
        ∂((μ : Measure (Torus d)).prod μ) =
      ∫ p : Torus d × Torus d, (A.W p.1 p.2 - m) * (φ p.1 * φ p.2)
        ∂((μ : Measure (Torus d)).prod μ) := by
    have : ∀ p : Torus d × Torus d, (A.W p.1 p.2 - m) * (φ p.1 * φ p.2) =
        A.W p.1 p.2 * (φ p.1 * φ p.2) - m * (φ p.1 * φ p.2) := fun p => by ring
    simp_rw [this]
    rw [integral_sub i1 i4, z4, sub_zero]
  rw [hsub]
  have hint : Integrable (fun p : Torus d × Torus d =>
      interactionOscillation A / 2 * (|φ p.1| * |φ p.2|))
      ((μ : Measure (Torus d)).prod μ) :=
    (hfi.abs.mul_prod hfi.abs).const_mul _
  have h2 : ‖∫ p : Torus d × Torus d, (A.W p.1 p.2 - m) * (φ p.1 * φ p.2)
        ∂((μ : Measure (Torus d)).prod μ)‖ ≤
      ∫ p : Torus d × Torus d, interactionOscillation A / 2 * (|φ p.1| * |φ p.2|)
        ∂((μ : Measure (Torus d)).prod μ) := by
    refine norm_integral_le_of_norm_le hint (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_interaction_sub_midpoint_le A p.1 p.2)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have h3 : ∫ p : Torus d × Torus d, interactionOscillation A / 2 * (|φ p.1| * |φ p.2|)
        ∂((μ : Measure (Torus d)).prod μ) =
      interactionOscillation A / 2 *
        ((∫ x, |φ x| ∂(μ : Measure (Torus d))) ^ 2) := by
    rw [integral_const_mul, integral_prod_mul (fun x => |φ x|) (fun x => |φ x|)]
    ring
  rw [Real.norm_eq_abs, h3] at h2
  refine h2.trans ?_
  have hB := interactionOscillation_nonneg A
  exact mul_le_mul_of_nonneg_left (sq_integral_abs_le μ _) (by positivity)

/-- `H = I + T ≤ (1 + B/2) I` on `L²_0(μ)`. -/
theorem densityHessian_form_le (f : centeredL2 μ) :
    inner ℝ f (densityHessian A μ f) ≤ (1 + interactionOscillation A / 2) * ‖f‖ ^ 2 := by
  have h1 : inner ℝ f (densityHessian A μ f) =
      inner ℝ f f + inner ℝ f (centeredInteraction A μ f) := by
    rw [← inner_add_right]; rfl
  have h2 := (abs_le.1 (centeredInteraction_form_bound_oscillation A μ f)).2
  rw [h1, real_inner_self_eq_norm_sq]
  linarith

theorem inner_densityHessian_symm (a b : centeredL2 μ) :
    inner ℝ (densityHessian A μ a) b = inner ℝ a (densityHessian A μ b) := by
  have h1 : inner ℝ (densityHessian A μ a) b =
      inner ℝ a b + inner ℝ (centeredInteraction A μ a) b := by
    rw [← inner_add_left]; rfl
  have h2 : inner ℝ a (densityHessian A μ b) =
      inner ℝ a b + inner ℝ a (centeredInteraction A μ b) := by
    rw [← inner_add_right]; rfl
  rw [h1, h2, centeredInteraction_symmetric]

/-- The lower quadratic bound for `C = H⁻¹`: `⟨g, C g⟩ ≥ ‖g‖² / (1 + B/2)`, proved by
Cauchy–Schwarz for the nonnegative symmetric form of `H`. -/
theorem norm_sq_div_le_inner_densityCovariance (hH : IsCoerciveDensityHessian A μ)
    (g : centeredL2 μ) :
    ‖g‖ ^ 2 / (1 + interactionOscillation A / 2) ≤
      inner ℝ g (densityCovariance A μ hH g) := by
  have hB := interactionOscillation_nonneg A
  have hΛ : 0 < 1 + interactionOscillation A / 2 := by positivity
  rw [div_le_iff₀ hΛ]
  set h := densityCovariance A μ hH g with hh
  have hHh : densityHessian A μ h = g := densityHessian_densityCovariance A μ hH g
  obtain ⟨c, hc, hcoer⟩ := hH
  set Λ := 1 + interactionOscillation A / 2 with hΛdef
  have hq : inner ℝ g h = inner ℝ h (densityHessian A μ h) := by
    rw [hHh, real_inner_comm]
  have hdisc := discrim_le_zero (a := inner ℝ h (densityHessian A μ h))
    (b := -2 * ‖g‖ ^ 2) (c := inner ℝ g (densityHessian A μ g)) (fun t => by
      have hpos := le_trans (mul_nonneg hc.le (sq_nonneg ‖g - t • h‖)) (hcoer (g - t • h))
      have e1 : inner ℝ (g - t • h) (densityHessian A μ (g - t • h)) =
          inner ℝ g (densityHessian A μ g) - t * inner ℝ g (densityHessian A μ h) -
            t * inner ℝ h (densityHessian A μ g) +
            t * (t * inner ℝ h (densityHessian A μ h)) := by
        have s1 : ∀ x y : centeredL2 μ, inner ℝ (t • x) y = t * inner ℝ x y :=
          fun x y => real_inner_smul_left x y t
        have s2 : ∀ x y : centeredL2 μ, inner ℝ x (t • y) = t * inner ℝ x y :=
          fun x y => real_inner_smul_right x y t
        simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, s1, s2]
        ring
      have e2 : inner ℝ g (densityHessian A μ h) = ‖g‖ ^ 2 := by
        rw [hHh, real_inner_self_eq_norm_sq]
      have e3 : inner ℝ h (densityHessian A μ g) = ‖g‖ ^ 2 := by
        rw [← inner_densityHessian_symm, hHh, real_inner_self_eq_norm_sq]
      rw [e1, e2, e3] at hpos
      nlinarith)
  have hge := densityHessian_form_le A μ g
  unfold discrim at hdisc
  have hqnn : 0 ≤ inner ℝ h (densityHessian A μ h) :=
    le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer h)
  rw [hq]
  by_cases hg : ‖g‖ = 0
  · rw [hg]; simpa using mul_nonneg hqnn hΛ.le
  · have hpos : 0 < ‖g‖ ^ 2 := by positivity
    have h5 : ‖g‖ ^ 2 * ‖g‖ ^ 2 ≤ (inner ℝ h (densityHessian A μ h) * Λ) * ‖g‖ ^ 2 := by
      nlinarith [hdisc, hge, mul_le_mul_of_nonneg_left hge hqnn]
    exact le_of_mul_le_mul_right h5 hpos

end Form

/-! ### Comparison of the Gaussian and Poincaré rates -/

section Rates

variable (μ : ProbabilityMeasure (Torus d))

theorem integral_coordPartial_haar {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    ∫ x, coordPartial j φ x ∂haar d = 0 := by
  have h1 : IsSmoothPeriodic (fun _ : Torus d => (1 : ℝ)) := contDiff_const
  have := integral_mul_coordPartial_of_smooth h1 hφ j
  have e : ∀ x : Torus d, coordPartial j (fun _ : Torus d => (1 : ℝ)) x = 0 := by
    intro x; simp [coordPartial, Function.comp_def]
  simp only [e, zero_mul, integral_zero, one_mul] at this
  linarith

/-- Subtracting a constant from a weak `H¹(μ)` test keeps the weak gradient. -/
noncomputable def shiftTest (f : WeakH1Test μ) (c : ℝ) : WeakH1Test μ where
  fn := fun x => f.fn x - c
  grad := f.grad
  isWeak :=
    { memLp := f.isWeak.memLp.sub (memLp_const c)
      memLp_grad := f.isWeak.memLp_grad
      integrable := f.isWeak.integrable.sub (integrable_const c)
      integrable_grad := f.isWeak.integrable_grad
      ibp := fun φ hφ j => by
        have hb : Integrable (fun x => f.fn x * coordPartial j φ x) (haar d) := by
          obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
            (hφ.continuous_coordPartial j).continuousOn
          exact (f.isWeak.integrable.bdd_mul (c := C)
            (hφ.continuous_coordPartial j).aestronglyMeasurable
            (ae_of_all _ fun x => by simpa using hC x (Set.mem_univ _))).congr
            (ae_of_all _ fun x => by simp [mul_comm])
        have hc : Integrable (fun x => c * coordPartial j φ x) (haar d) :=
          ((hφ.continuous_coordPartial j).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).const_mul c
        have e : ∀ x, (f.fn x - c) * coordPartial j φ x =
            f.fn x * coordPartial j φ x - c * coordPartial j φ x := fun x => by ring
        simp_rw [e]
        rw [integral_sub hb hc, integral_const_mul, integral_coordPartial_haar hφ j,
          mul_zero, sub_zero]
        exact f.isWeak.ibp φ hφ j }

theorem shiftTest_fn (f : WeakH1Test μ) (c : ℝ) (x : Torus d) :
    (shiftTest μ f c).fn x = f.fn x - c := rfl

theorem dirichletEnergy_shiftTest (f : WeakH1Test μ) (c : ℝ) :
    dirichletEnergy μ (shiftTest μ f c) = dirichletEnergy μ f := rfl

variable (A : InteractionData d)

/-- STR014, second output: `λ_G ≤ (1 + B/2) λ_P(μ)` with `B = osc W` on the full product. -/
theorem gaussianRate_le_hessianUpper_poincare (hH : IsCoerciveDensityHessian A μ) :
    gaussianRate A μ hH ≤
      ENNReal.ofReal (1 + interactionOscillation A / 2) * poincareRate μ := by
  have hB := interactionOscillation_nonneg A
  set Λ : ℝ := 1 + interactionOscillation A / 2 with hΛdef
  have hΛ : 0 < Λ := by positivity
  have key : ∀ f : WeakH1Test μ, 0 < weightedVariance μ f.fn →
      gaussianRate A μ hH ≤ ENNReal.ofReal Λ * poincareQuotient μ f := by
    intro f hf
    set c : ℝ := ∫ x, f.fn x ∂(μ : Measure (Torus d)) with hc
    set g : WeakH1Test μ := shiftTest μ f c with hg
    have hfi : Integrable f.fn (μ : Measure (Torus d)) :=
      f.isWeak.memLp.integrable (by norm_num)
    have hg0 : ∫ x, g.fn x ∂(μ : Measure (Torus d)) = 0 := by
      show ∫ x, (f.fn x - c) ∂(μ : Measure (Torus d)) = 0
      rw [integral_sub hfi (integrable_const c)]
      simp [hc]
    have hvar : weightedVariance μ g.fn = weightedVariance μ f.fn := by
      unfold weightedVariance
      rw [hg0]
      simp only [sub_zero]
      rfl
    have hnz : IsNonzeroCentered μ g := by
      refine ⟨hg0, fun hae => ?_⟩
      have : weightedVariance μ g.fn = 0 := by
        unfold weightedVariance
        rw [hg0]
        have : ∫ x, (g.fn x - 0) ^ 2 ∂(μ : Measure (Torus d)) = ∫ _x, (0 : ℝ) ∂(μ : Measure (Torus d)) :=
          integral_congr_ae (hae.mono fun x hx => by simp [hx])
        rw [this]; simp
      linarith
    have hnorm : ‖g.toCentered μ hg0‖ ^ 2 = weightedVariance μ f.fn := by
      rw [← hvar]
      show ‖((g.toCentered μ hg0 : centeredL2 μ) : Lp ℝ 2 (μ : Measure (Torus d)))‖ ^ 2 = _
      rw [norm_sq_eq_integral_sq]
      unfold weightedVariance
      rw [hg0]
      refine integral_congr_ae ?_
      filter_upwards [g.isWeak.memLp.coeFn_toLp] with x hx
      simp only [WeakH1Test.toCentered] at *
      rw [hx]; simp
    have hden := norm_sq_div_le_inner_densityCovariance A μ hH (g.toCentered μ hg0)
    rw [hnorm] at hden
    have hden' : weightedVariance μ f.fn ≤ Λ * gaussianDenominator A μ hH g hg0 := by
      have := (div_le_iff₀ hΛ).1 hden
      unfold gaussianDenominator
      linarith
    have hV0 : ENNReal.ofReal (weightedVariance μ f.fn) ≠ 0 := (ENNReal.ofReal_pos.2 hf).ne'
    have hden0 : ENNReal.ofReal (gaussianDenominator A μ hH g hg0) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (gaussianDenominator_pos A μ hH hnz)).ne'
    have hE : ENNReal.ofReal (weightedVariance μ f.fn) ≤
        ENNReal.ofReal Λ * ENNReal.ofReal (gaussianDenominator A μ hH g hg0) := by
      rw [← ENNReal.ofReal_mul hΛ.le]
      exact ENNReal.ofReal_le_ofReal hden'
    refine (gaussianRate_le_quotient A μ hH g hnz).trans ?_
    unfold gaussianQuotient poincareQuotient
    rw [ENNReal.div_le_iff hden0 ENNReal.ofReal_ne_top]
    have hdE : dirichletEnergy μ g = dirichletEnergy μ f := rfl
    rw [hdE]
    calc dirichletEnergy μ f
        = dirichletEnergy μ f / ENNReal.ofReal (weightedVariance μ f.fn) *
            ENNReal.ofReal (weightedVariance μ f.fn) :=
          (ENNReal.div_mul_cancel hV0 ENNReal.ofReal_ne_top).symm
      _ ≤ dirichletEnergy μ f / ENNReal.ofReal (weightedVariance μ f.fn) *
            (ENNReal.ofReal Λ * ENNReal.ofReal (gaussianDenominator A μ hH g hg0)) := by
          gcongr
      _ = _ := by ring
  have hΛ0 : ENNReal.ofReal Λ ≠ 0 := (ENNReal.ofReal_pos.2 hΛ).ne'
  have h1 : gaussianRate A μ hH / ENNReal.ofReal Λ ≤ poincareRate μ := by
    rw [le_poincareRate_iff]
    intro f hf
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm]
    exact key f hf
  rw [ENNReal.div_le_iff_le_mul (Or.inl hΛ0) (Or.inl ENNReal.ofReal_ne_top)] at h1
  rwa [mul_comm]

end Rates

end DGPS.Structural
