import DGPS.Lipschitz.Representatives
import DGPS.Foundations.AbsoluteDensity
import DGPS.Model.Drift

/-!
# Weak interaction convolution (LIP002)

Let `W : 𝕋^d → 𝕋^d → ℝ` be continuous, Lipschitz in its first variable (uniformly in the second,
for the Euclidean quotient distance `torusDist`), and let `B : 𝕋^d → 𝕋^d → ℝ^d` be a bounded
jointly measurable weak-gradient representative of `∇₁ W`: for a.e. `y`, `x ↦ B x y` is an `L^∞`
weak gradient (`IsWeakGradientLp ∞`, tested against smooth periodic functions) of `x ↦ W x y`.

`DGPS.Lipschitz.weak_interaction_convolution` states:
* for every probability density `ρ`, `x ↦ B * ρ = ∫ ρ(y) B(x,y) dm(y)` is an `L^∞` weak gradient of
  `W * ρ = ∫ W(x,y) ρ(y) dm(y)` (so `∇(W * ρ) = B * ρ` a.e.), and the integral against `ρ m`
  is the integral against `ρ` for Haar measure;
* for probability densities `ρ, η`, `‖B * (ρ - η)‖_∞ ≤ ‖B‖_∞ ‖ρ - η‖₁`;
* for every probability measure `ν` (possibly singular), `W * ν` (integration of the continuous `W`)
  is Lipschitz with the same constant: no a.e. gradient is integrated against `ν`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- `ρ` is a probability density with respect to the Haar probability measure `m`. -/
def IsProbDensity (ρ : Torus d → ℝ) : Prop :=
  Integrable ρ (haar d) ∧ 0 ≤ᵐ[haar d] ρ ∧ ∫ x, ρ x ∂haar d = 1

/-- The density `u²` of an absolute-admissible competitor is a probability density. -/
theorem isProbDensity_density (ρ : AbsoluteDensity d) : IsProbDensity ρ.density :=
  ⟨ρ.integrable_density, Eventually.of_forall ρ.density_nonneg, ρ.integral_density⟩

theorem integrable_const_mul_comp_snd {ρ : Torus d → ℝ} (hρ : Integrable ρ (haar d)) (K : ℝ) :
    Integrable (fun p : Torus d × Torus d => K * |ρ p.2|) ((haar d).prod (haar d)) :=
  (hρ.abs.comp_snd (haar d)).const_mul K

/-- Joint bound of a continuous function of two torus variables. -/
theorem exists_bound_continuous_prod {W : Torus d → Torus d → ℝ}
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2) : ∃ C, ∀ x y, |W x y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    hWc.continuousOn
  exact ⟨C, fun x y => by simpa using hC (x, y) (Set.mem_univ _)⟩

/-- The a.e. bound of an essentially bounded kernel on the product. -/
theorem ae_prod_norm_le_of_memLp_top {B : Torus d → Torus d → Tangent d}
    (hB : MemLp (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d))) :
    ∀ᵐ p ∂(haar d).prod (haar d),
      ‖B p.1 p.2‖ ≤ (eLpNorm (fun p : Torus d × Torus d => B p.1 p.2) ∞
        ((haar d).prod (haar d))).toReal := by
  have hfin : eLpNorm (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) ≠ ⊤ :=
    hB.eLpNorm_lt_top.ne
  have h := ae_le_eLpNormEssSup (f := fun p : Torus d × Torus d => B p.1 p.2)
    (μ := (haar d).prod (haar d))
  rw [← eLpNorm_exponent_top hB.aestronglyMeasurable] at h
  filter_upwards [h] with p hp
  rw [← ofReal_norm] at hp
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hp

/-- Core of the estimates: an `L¹` weight against a kernel bounded by `M` (a.e. in `y`). -/
theorem norm_integral_smul_le {B : Torus d → Torus d → Tangent d} {δ : Torus d → ℝ} {M : ℝ}
    (hδ : Integrable δ (haar d)) {x : Torus d} (hx : ∀ᵐ y ∂haar d, ‖B x y‖ ≤ M) :
    ‖∫ y, δ y • B x y ∂haar d‖ ≤ M * ∫ y, |δ y| ∂haar d := by
  have h := norm_integral_le_of_norm_le (μ := haar d) (f := fun y => δ y • B x y)
    (g := fun y => M * |δ y|) (hδ.abs.const_mul M) (by
      filter_upwards [hx] with y hy
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right hy (abs_nonneg _))
  rwa [integral_const_mul] at h

theorem integrable_smul_slice {B : Torus d → Torus d → Tangent d}
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2) {δ : Torus d → ℝ} {M : ℝ}
    (hδ : Integrable δ (haar d)) {x : Torus d} (hx : ∀ᵐ y ∂haar d, ‖B x y‖ ≤ M) :
    Integrable (fun y => δ y • B x y) (haar d) := by
  refine Integrable.mono' (hδ.abs.const_mul M) ?_ ?_
  · exact hδ.aestronglyMeasurable.smul
      (hBm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [hx] with y hy
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)

/-- Measurability of `x ↦ ∫ δ(y) B(x,y) dm(y)`. -/
theorem aestronglyMeasurable_convolution {B : Torus d → Torus d → Tangent d}
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2) {δ : Torus d → ℝ}
    (hδ : AEStronglyMeasurable δ (haar d)) :
    AEStronglyMeasurable (fun x => ∫ y, δ y • B x y ∂haar d) (haar d) := by
  have : AEStronglyMeasurable (fun p : Torus d × Torus d => δ p.2 • B p.1 p.2)
      ((haar d).prod (haar d)) := hδ.comp_snd.smul hBm.aestronglyMeasurable
  exact this.integral_prod_right'

/-- The `L^∞` weak gradient statement for the convolution against an integrable `ρ`. -/
theorem isWeakGradientLp_convolution {W : Torus d → Torus d → ℝ}
    {B : Torus d → Torus d → Tangent d}
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hB : MemLp (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)))
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {ρ : Torus d → ℝ} (hρ : Integrable ρ (haar d)) :
    IsWeakGradientLp ∞ (fun x => ∫ y, W x y * ρ y ∂haar d)
      (fun x => ∫ y, ρ y • B x y ∂haar d) := by
  obtain ⟨C, hC⟩ := exists_bound_continuous_prod hWc
  set M := (eLpNorm (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d))).toReal
    with hM
  have hBp := ae_prod_norm_le_of_memLp_top hB
  have hBae : ∀ᵐ x ∂haar d, ∀ᵐ y ∂haar d, ‖B x y‖ ≤ M := Measure.ae_ae_of_ae_prod hBp
  have hWm : Measurable fun p : Torus d × Torus d => W p.1 p.2 := hWc.measurable
  have hρm : AEStronglyMeasurable ρ (haar d) := hρ.aestronglyMeasurable
  have hu_meas : AEStronglyMeasurable (fun x => ∫ y, W x y * ρ y ∂haar d) (haar d) := by
    have : AEStronglyMeasurable (fun p : Torus d × Torus d => W p.1 p.2 * ρ p.2)
        ((haar d).prod (haar d)) := hWm.aestronglyMeasurable.mul hρm.comp_snd
    exact this.integral_prod_right'
  have hu_top : MemLp (fun x => ∫ y, W x y * ρ y ∂haar d) ∞ (haar d) := by
    refine memLp_top_of_bound hu_meas (C * ∫ y, |ρ y| ∂haar d) (Eventually.of_forall fun x => ?_)
    have h := norm_integral_le_of_norm_le (μ := haar d) (f := fun y => W x y * ρ y)
      (g := fun y => C * |ρ y|) (hρ.abs.const_mul C) (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC x y) (abs_nonneg _))
    rwa [integral_const_mul] at h
  have hg_meas := aestronglyMeasurable_convolution hBm hρm
  have hg_top : MemLp (fun x => ∫ y, ρ y • B x y ∂haar d) ∞ (haar d) := by
    refine memLp_top_of_bound hg_meas (M * ∫ y, |ρ y| ∂haar d) ?_
    filter_upwards [hBae] with x hx
    exact norm_integral_smul_le hρ hx
  refine ⟨hu_top, hg_top, fun φ hφ j => ?_⟩
  obtain ⟨Kψ, hKψ⟩ := exists_bound_continuous (hφ.continuous_coordPartial j)
  obtain ⟨Kφ, hKφ⟩ := exists_bound_continuous hφ.continuous_torus
  have hψm : Measurable (coordPartial j φ) := measurable_coordPartial j
  have hφm : Measurable φ := hφ.continuous_torus.measurable
  -- left side: Fubini
  have hF_int : Integrable (Function.uncurry fun x y => W x y * ρ y * coordPartial j φ x)
      ((haar d).prod (haar d)) := by
    refine Integrable.mono' (integrable_const_mul_comp_snd hρ (C * Kψ)) ?_ ?_
    · exact (hWm.aestronglyMeasurable.mul hρm.comp_snd).mul
        (hψm.comp measurable_fst).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
      have h1 := hC p.1 p.2
      have h2 := hKψ p.1
      have hC0 : 0 ≤ C := (abs_nonneg _).trans h1
      calc |W p.1 p.2| * |ρ p.2| * |coordPartial j φ p.1|
          ≤ C * |ρ p.2| * Kψ := by gcongr
        _ = C * Kψ * |ρ p.2| := by ring
  have hL : ∫ x, (∫ y, W x y * ρ y ∂haar d) * coordPartial j φ x ∂haar d
      = ∫ y, ρ y * ∫ x, W x y * coordPartial j φ x ∂haar d ∂haar d := by
    calc ∫ x, (∫ y, W x y * ρ y ∂haar d) * coordPartial j φ x ∂haar d
        = ∫ x, ∫ y, W x y * ρ y * coordPartial j φ x ∂haar d ∂haar d :=
          integral_congr_ae (Eventually.of_forall fun x => (integral_mul_const _ _).symm)
      _ = ∫ y, ∫ x, W x y * ρ y * coordPartial j φ x ∂haar d ∂haar d :=
          integral_integral_swap hF_int
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  -- right side: Fubini
  have hG_int : Integrable (Function.uncurry fun x y => ρ y * B x y j * φ x)
      ((haar d).prod (haar d)) := by
    refine Integrable.mono' (integrable_const_mul_comp_snd hρ (M * Kφ)) ?_ ?_
    · have hBj : Measurable fun p : Torus d × Torus d => B p.1 p.2 j :=
        (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.measurable.comp hBm
      exact (hρm.comp_snd.mul hBj.aestronglyMeasurable).mul
        (hφm.comp measurable_fst).aestronglyMeasurable
    · filter_upwards [hBp] with p hp
      simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
      have hj : |B p.1 p.2 j| ≤ M := by
        have := PiLp.norm_apply_le (B p.1 p.2) j
        rw [Real.norm_eq_abs] at this
        exact this.trans hp
      have hM0 : 0 ≤ M := (norm_nonneg _).trans hp
      have h2 := hKφ p.1
      calc |ρ p.2| * |B p.1 p.2 j| * |φ p.1|
          ≤ |ρ p.2| * M * Kφ := by gcongr
        _ = M * Kφ * |ρ p.2| := by ring
  have hcomp : ∀ᵐ x ∂haar d,
      (∫ y, ρ y • B x y ∂haar d) j = ∫ y, ρ y * B x y j ∂haar d := by
    filter_upwards [hBae] with x hx
    have := (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integral_comp_comm
      (integrable_smul_slice hBm hρ hx)
    simpa using this.symm
  have hR : ∫ x, (∫ y, ρ y • B x y ∂haar d) j * φ x ∂haar d
      = ∫ y, ρ y * ∫ x, B x y j * φ x ∂haar d ∂haar d := by
    calc ∫ x, (∫ y, ρ y • B x y ∂haar d) j * φ x ∂haar d
        = ∫ x, ∫ y, ρ y * B x y j * φ x ∂haar d ∂haar d := by
          refine integral_congr_ae ?_
          filter_upwards [hcomp] with x hx
          rw [hx, ← integral_mul_const]
      _ = ∫ y, ∫ x, ρ y * B x y j * φ x ∂haar d ∂haar d := integral_integral_swap hG_int
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [hL, hR, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hWB] with y hy
  rw [hy.ibp φ hφ j]
  ring

/-- The `L^∞` estimate `‖B * δ‖_∞ ≤ ‖B‖_∞ ‖δ‖₁`. -/
theorem eLpNorm_convolution_le {B : Torus d → Torus d → Tangent d}
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hB : MemLp (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)))
    {δ : Torus d → ℝ} (hδ : Integrable δ (haar d)) :
    eLpNorm (fun x => ∫ y, δ y • B x y ∂haar d) ∞ (haar d) ≤
      eLpNorm (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) *
        eLpNorm δ 1 (haar d) := by
  have hfin : eLpNorm (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) ≠ ⊤ :=
    hB.eLpNorm_lt_top.ne
  set E := eLpNorm (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) with hE
  have hbd : ∀ᵐ x ∂haar d, ‖∫ y, δ y • B x y ∂haar d‖ ≤ E.toReal * ∫ y, |δ y| ∂haar d := by
    filter_upwards [Measure.ae_ae_of_ae_prod (ae_prod_norm_le_of_memLp_top hB)] with x hx
    exact norm_integral_smul_le hδ hx
  rw [eLpNorm_exponent_top (aestronglyMeasurable_convolution hBm hδ.aestronglyMeasurable)]
  refine (eLpNormEssSup_le_of_ae_bound hbd).trans ?_
  have h1 : ENNReal.ofReal (∫ y, |δ y| ∂haar d) = eLpNorm δ 1 (haar d) := by
    rw [eLpNorm_one_eq_lintegral_enorm hδ.aestronglyMeasurable, ← ofReal_integral_norm_eq_lintegral_enorm hδ]
    simp only [Real.norm_eq_abs]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, h1, ENNReal.ofReal_toReal hfin]

/-- A Lipschitz bound for the integral of an `x`-Lipschitz kernel against a probability measure. -/
theorem lipschitz_integral_of_lipschitz {W : Torus d → Torus d → ℝ} {L : ℝ}
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hL : ∀ y, TorusLipschitzWith L fun x => W x y) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] :
    TorusLipschitzWith L fun x => ∫ y, W x y ∂ν := by
  intro x x'
  have hint : ∀ z, Integrable (fun y => W z y) ν := fun z =>
    (hWc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub (hint x) (hint x')]
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => W x y - W x' y)
    (C := L * torusDist x x') (Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hL y x x')
  simpa using this

/-- **LIP002.** Weak interaction convolution. -/
theorem weak_interaction_convolution (d : ℕ) (W : Torus d → Torus d → ℝ)
    (B : Torus d → Torus d → Tangent d) (L : ℝ)
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hL : ∀ y, TorusLipschitzWith L fun x => W x y)
    (hBm : Measurable fun p : Torus d × Torus d => B p.1 p.2)
    (hB : MemLp (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)))
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y)) :
    (∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      IsWeakGradientLp ∞ (fun x => ∫ y, W x y * ρ y ∂haar d)
        (fun x => ∫ y, ρ y • B x y ∂haar d) ∧
      IsProbabilityMeasure ((haar d).withDensity fun y => ENNReal.ofReal (ρ y)) ∧
      ∀ x, ∫ y, W x y ∂((haar d).withDensity fun y => ENNReal.ofReal (ρ y)) =
        ∫ y, W x y * ρ y ∂haar d) ∧
    (∀ ρ η : Torus d → ℝ, IsProbDensity ρ → IsProbDensity η →
      eLpNorm (fun x => ∫ y, (ρ y - η y) • B x y ∂haar d) ∞ (haar d) ≤
        eLpNorm (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) *
          eLpNorm (fun y => ρ y - η y) 1 (haar d)) ∧
    (∀ ν : Measure (Torus d), IsProbabilityMeasure ν →
      TorusLipschitzWith L fun x => ∫ y, W x y ∂ν) := by
  refine ⟨fun ρ hρ => ⟨isWeakGradientLp_convolution hWc hBm hB hWB hρ.1, ?_, ?_⟩,
    fun ρ η hρ η' => eLpNorm_convolution_le hBm hB (hρ.1.sub η'.1),
    fun ν hν => lipschitz_integral_of_lipschitz hWc hL ν⟩
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hρ.1 hρ.2.1, hρ.2.2, ENNReal.ofReal_one]
  · intro x
    rw [integral_withDensity_eq_integral_toReal_smul₀]
    · refine integral_congr_ae ?_
      filter_upwards [hρ.2.1] with y hy
      simp [ENNReal.toReal_ofReal hy, mul_comm]
    · exact hρ.1.aemeasurable.ennreal_ofReal
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

end DGPS.Lipschitz

/-!
## DEF021: weak-gradient convolution under Lipschitz hypotheses and the canonical drift

For `A : InteractionData d` with `LipschitzData A`, the kernel `interactionGradient A x y` is the
Lipschitz (a.e. differentiation) gradient `∇₁ W(·, y)(x)`, jointly measurable and bounded.
`weakGradient_convolution` packages LIP002 for this kernel, and `lipschitz_absoluteDrift` is the
`AbsoluteDrift` provider with force `∇V + ∫ ρ(y) ∇₁W(·,y) dm(y)`.
-/

namespace DGPS

variable {d : ℕ}

/-- The first-variable gradient `B x y = ∇₁ W(x, y)` of the interaction (almost-everywhere
derivative of the Lipschitz section `W(·, y)`). -/
noncomputable def interactionGradient (A : InteractionData d) (x y : Torus d) : Tangent d :=
  smoothGrad (fun x' => A.W x' y) x

/-- A Lipschitz constant (nonnegative) for the `x`-sections of `W`. -/
theorem LipschitzData.exists_W_section_const {A : InteractionData d} (h : LipschitzData A) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y, TorusLipschitzWith L fun x => A.W x y := by
  obtain ⟨L, hL⟩ := h.W_lipschitz
  refine ⟨|L|, abs_nonneg _, fun y x x' => ?_⟩
  have h0 : 0 ≤ torusDist x x' := Real.sqrt_nonneg _
  have := hL x y x' y
  simp only [torusDist_metric.1 y, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, Real.sqrt_sq h0] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self L) h0)

/-- A Lipschitz constant (nonnegative) for `V`. -/
theorem LipschitzData.exists_V_const {A : InteractionData d} (h : LipschitzData A) :
    ∃ L : ℝ, 0 ≤ L ∧ TorusLipschitzWith L A.V := by
  obtain ⟨L, hL⟩ := h.V_lipschitz
  have h0 : ∀ x y : Torus d, 0 ≤ torusDist x y := fun x y => Real.sqrt_nonneg _
  exact ⟨|L|, abs_nonneg _, fun x y =>
    (hL x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (h0 x y))⟩

theorem measurable_interactionGradient (A : InteractionData d) :
    Measurable fun p : Torus d × Torus d => interactionGradient A p.1 p.2 := by
  have hF : Continuous (Function.uncurry fun (y : Torus d) (z : Fin d → ℝ) =>
      A.W (torusLift z) y) :=
    A.W_continuous.comp ((SharpLSI.continuous_liftT.comp continuous_snd).prodMk continuous_fst)
  have hq : Measurable fun q : Torus d × Torus d => (q.2, SharpLSI.secT q.1) :=
    measurable_snd.prodMk (SharpLSI.measurable_secT.comp measurable_fst)
  refine (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun j => ?_)
  exact (measurable_fderiv_apply_const_with_param ℝ hF (Pi.single j 1)).comp hq

theorem ae_norm_interactionGradient_le {A : InteractionData d} {L : ℝ} (hL : 0 ≤ L)
    (hW : ∀ y, TorusLipschitzWith L fun x => A.W x y) :
    ∀ᵐ p ∂(haar d).prod (haar d), ‖interactionGradient A p.1 p.2‖ ≤ L := by
  have hmeas : MeasurableSet {p : Torus d × Torus d | ‖interactionGradient A p.1 p.2‖ ≤ L} :=
    measurableSet_le (measurable_interactionGradient A).norm measurable_const
  have h1 : ∀ᵐ y ∂haar d, ∀ᵐ x ∂haar d, ‖interactionGradient A x y‖ ≤ L :=
    Eventually.of_forall fun y => Lipschitz.ae_norm_smoothGrad_le hL (hW y)
  have h2 : ∀ᵐ x ∂haar d, ∀ᵐ y ∂haar d, ‖interactionGradient A x y‖ ≤ L :=
    (Measure.ae_ae_comm (μ := haar d) (ν := haar d)
      (p := fun x y => ‖interactionGradient A x y‖ ≤ L) hmeas).mpr h1
  exact (Measure.ae_prod_iff_ae_ae (μ := haar d) (ν := haar d) hmeas).mpr h2

theorem isWeakGradientLp_add {u v : Torus d → ℝ} {g h : Torus d → Tangent d}
    (hu : IsWeakGradientLp ∞ u g) (hv : IsWeakGradientLp ∞ v h) :
    IsWeakGradientLp ∞ (fun x => u x + v x) (fun x => g x + h x) := by
  refine ⟨hu.memLp.add hv.memLp, hu.memLp_grad.add hv.memLp_grad, fun φ hφ j => ?_⟩
  have hψ : MemLp (coordPartial j φ) 1 (haar d) :=
    (memLp_top_of_bound (hφ.continuous_coordPartial j).aestronglyMeasurable
      (Classical.choose (Lipschitz.exists_bound_continuous (hφ.continuous_coordPartial j)))
      (Eventually.of_forall fun x => by
        simpa using Classical.choose_spec
          (Lipschitz.exists_bound_continuous (hφ.continuous_coordPartial j)) x)).mono_exponent
      le_top
  have hφ' : MemLp φ 1 (haar d) :=
    (memLp_top_of_bound hφ.continuous_torus.aestronglyMeasurable
      (Classical.choose (Lipschitz.exists_bound_continuous hφ.continuous_torus))
      (Eventually.of_forall fun x => by
        simpa using Classical.choose_spec
          (Lipschitz.exists_bound_continuous hφ.continuous_torus) x)).mono_exponent le_top
  have h1 : Integrable (fun x => u x * coordPartial j φ x) (haar d) :=
    hu.memLp.integrable_mul hψ
  have h2 : Integrable (fun x => v x * coordPartial j φ x) (haar d) :=
    hv.memLp.integrable_mul hψ
  have h3 : Integrable (fun x => (g x) j * φ x) (haar d) :=
    (memLp_coord_of_memLp hu.memLp_grad j).integrable_mul hφ'
  have h4 : Integrable (fun x => (h x) j * φ x) (haar d) :=
    (memLp_coord_of_memLp hv.memLp_grad j).integrable_mul hφ'
  have e1 := hu.ibp φ hφ j
  have e2 := hv.ibp φ hφ j
  simp only [add_mul, PiLp.add_apply]
  rw [integral_add h1 h2, integral_add h3 h4, e1, e2]
  ring

/-- A measurable representative of the density `ρ²` of an absolute competitor. -/
noncomputable def densityRep (ρ : AbsoluteDensity d) : Torus d → ℝ :=
  ρ.integrable_density.aestronglyMeasurable.mk _

theorem densityRep_ae (ρ : AbsoluteDensity d) : ρ.density =ᵐ[haar d] densityRep ρ :=
  ρ.integrable_density.aestronglyMeasurable.ae_eq_mk

theorem stronglyMeasurable_densityRep (ρ : AbsoluteDensity d) :
    StronglyMeasurable (densityRep ρ) :=
  ρ.integrable_density.aestronglyMeasurable.stronglyMeasurable_mk

theorem interactionForce_eq (A : InteractionData d) (ρ : AbsoluteDensity d) (x : Torus d) :
    ∫ y, densityRep ρ y • interactionGradient A x y ∂haar d =
      ∫ y, ρ.density y • interactionGradient A x y ∂haar d := by
  refine integral_congr_ae ?_
  filter_upwards [densityRep_ae ρ] with y hy
  rw [hy]

/-- **DEF021 (weak-gradient convolution).** For Lipschitz interaction data, `B = ∇₁W` is a jointly
measurable, essentially bounded kernel with `L^∞` weak gradients `B(·, y) = ∇ W(·, y)`; for every
probability density `ρ` the convolution `B * ρ` is the `L^∞` weak gradient of `W * ρ`, the integral
against `ρ m` is the integral against `ρ`, `‖B * (ρ - η)‖_∞ ≤ ‖B‖_∞ ‖ρ - η‖₁`, and for every
probability measure `ν` (possibly singular) the continuous representative `W * ν` is Lipschitz
(by integrating increments of `W`, not an a.e. gradient). -/
theorem weakGradient_convolution (A : InteractionData d) (hLip : LipschitzData A) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ y, TorusLipschitzWith L fun x => A.W x y) ∧
      Measurable (fun p : Torus d × Torus d => interactionGradient A p.1 p.2) ∧
      (∀ᵐ p ∂(haar d).prod (haar d), ‖interactionGradient A p.1 p.2‖ ≤ L) ∧
      MemLp (fun p : Torus d × Torus d => interactionGradient A p.1 p.2) ∞
        ((haar d).prod (haar d)) ∧
      (∀ y, IsWeakGradientLp ∞ (fun x => A.W x y) (fun x => interactionGradient A x y)) ∧
      (∀ ρ : Torus d → ℝ, Lipschitz.IsProbDensity ρ →
        IsWeakGradientLp ∞ (fun x => ∫ y, A.W x y * ρ y ∂haar d)
          (fun x => ∫ y, ρ y • interactionGradient A x y ∂haar d) ∧
        IsProbabilityMeasure ((haar d).withDensity fun y => ENNReal.ofReal (ρ y)) ∧
        ∀ x, ∫ y, A.W x y ∂((haar d).withDensity fun y => ENNReal.ofReal (ρ y)) =
          ∫ y, A.W x y * ρ y ∂haar d) ∧
      (∀ ρ η : Torus d → ℝ, Lipschitz.IsProbDensity ρ → Lipschitz.IsProbDensity η →
        eLpNorm (fun x => ∫ y, (ρ y - η y) • interactionGradient A x y ∂haar d) ∞ (haar d) ≤
          eLpNorm (fun p : Torus d × Torus d => interactionGradient A p.1 p.2) ∞
            ((haar d).prod (haar d)) * eLpNorm (fun y => ρ y - η y) 1 (haar d)) ∧
      (∀ ν : Measure (Torus d), IsProbabilityMeasure ν →
        TorusLipschitzWith L fun x => ∫ y, A.W x y ∂ν) := by
  obtain ⟨L, hL0, hW⟩ := hLip.exists_W_section_const
  have hbd := ae_norm_interactionGradient_le hL0 hW
  have hmeas := measurable_interactionGradient A
  have hB : MemLp (fun p : Torus d × Torus d => interactionGradient A p.1 p.2) ∞
      ((haar d).prod (haar d)) :=
    memLp_top_of_bound hmeas.aestronglyMeasurable L hbd
  have hWB : ∀ y, IsWeakGradientLp ∞ (fun x => A.W x y) (fun x => interactionGradient A x y) :=
    fun y => (Lipschitz.exists_weak_gradient hL0 (hW y)).1
  have key := Lipschitz.weak_interaction_convolution d A.W (interactionGradient A) L
    A.W_continuous hW hmeas hB (Eventually.of_forall hWB)
  exact ⟨L, hL0, hW, hmeas, hbd, hB, hWB, key⟩

/-- **DEF021 (canonical drift).** For Lipschitz interaction data, the weak `L¹` force provider of
every absolute competitor `ρ`: `∇V + ∫ ρ(y) ∇₁W(·, y) dm(y)`, from the actual Lipschitz
functions. -/
noncomputable def lipschitz_absoluteDrift (A : InteractionData d) (hLip : LipschitzData A) :
    AbsoluteDrift A where
  force ρ x := smoothGrad A.V x + ∫ y, densityRep ρ y • interactionGradient A x y ∂haar d
  measurable_force ρ := by
    refine (Lipschitz.measurable_smoothGrad).add ?_
    have hf : StronglyMeasurable fun p : Torus d × Torus d =>
        densityRep ρ p.2 • interactionGradient A p.1 p.2 :=
      ((stronglyMeasurable_densityRep ρ).comp_measurable measurable_snd).smul
        (measurable_interactionGradient A).stronglyMeasurable
    exact (hf.integral_prod_right' (ν := haar d)).measurable
  weak_gradient ρ := by
    obtain ⟨L, hL0, hW, hmeas, hbd, hB, hWB, key⟩ := weakGradient_convolution A hLip
    obtain ⟨LV, hLV0, hV⟩ := hLip.exists_V_const
    have hVg := Lipschitz.exists_weak_gradient hLV0 hV
    have hc := (key.1 ρ.density (Lipschitz.isProbDensity_density ρ)).1
    have hs := isWeakGradientLp_add hVg.1 hc
    have hpot : interactionPotential A ρ =
        fun x => A.V x + ∫ y, A.W x y * ρ.density y ∂haar d := by
      funext x
      rw [interactionPotential_eq]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    have hforce : (fun x => smoothGrad A.V x +
        ∫ y, densityRep ρ y • interactionGradient A x y ∂haar d) =
        fun x => smoothGrad A.V x + ∫ y, ρ.density y • interactionGradient A x y ∂haar d := by
      funext x
      rw [interactionForce_eq]
    rw [hpot]
    show IsWeakGradientLp 1 _ (fun x => smoothGrad A.V x +
        ∫ y, densityRep ρ y • interactionGradient A x y ∂haar d)
    rw [hforce]
    exact ⟨hs.memLp.mono_exponent le_top, hs.memLp_grad.mono_exponent le_top, hs.ibp⟩

end DGPS
