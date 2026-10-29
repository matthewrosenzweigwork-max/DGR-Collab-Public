import DGPS.Foundations.RelativeEntropy
import DGPS.Model.Data
import DGPS.Model.FreeEnergy


/-!
# Density Hessian at an equilibrium (DEF026)

For a probability measure `μ` on the torus (in the application a Gibbs equilibrium `μ = q m`)
and interaction data `A`, the centred kernel is
`K(x,y) = W(x,y) - (W*μ)(x) - (W*μ)(y) + ∬ W dμ²`.  It is symmetric and centred in each variable.
`L²_0(μ)` is the closed submodule of `Lp ℝ 2 μ` of mean-zero classes.  The operator
`T h = ∫ K(·,y) h(y) dμ(y)` is a bounded self-adjoint operator on `L²_0(μ)`, the density Hessian
is `H = I + T`, and `⟨h, H h⟩ = ‖h‖² + ∬ W h⊗h dμ²`.  Coercivity is `∃ c > 0, ∀ h, c‖h‖² ≤ ⟨h, H h⟩`.
-/

open MeasureTheory
open scoped BoundedContinuousFunction

namespace DGPS

variable {d : ℕ}

/-- `(W * μ)(x) = ∫ W(x, z) dμ(z)`. -/
noncomputable def interactionConvolution (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (x : Torus d) : ℝ :=
  ∫ z, A.W x z ∂(μ : Measure (Torus d))

/-- The mean interaction `∬ W dμ²`. -/
noncomputable def meanInteraction (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) : ℝ :=
  ∫ p, A.W p.1 p.2 ∂((μ : Measure (Torus d)).prod μ)

noncomputable def centeredKernel (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (x y : Torus d) : ℝ :=
  A.W x y - interactionConvolution A μ x - interactionConvolution A μ y + meanInteraction A μ

theorem continuous_interactionConvolution (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) : Continuous (interactionConvolution A μ) := by
  unfold interactionConvolution
  have := continuous_parametric_integral_of_continuous (μ := (μ : Measure (Torus d)))
    (f := fun x z => A.W x z) A.W_continuous isCompact_univ
  simpa using this

theorem centeredKernel_symm (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (x y : Torus d) : centeredKernel A μ x y = centeredKernel A μ y x := by
  unfold centeredKernel
  rw [A.W_symm x y]; ring

theorem continuous_centeredKernel (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    Continuous (fun p : Torus d × Torus d => centeredKernel A μ p.1 p.2) := by
  unfold centeredKernel
  have h1 := continuous_interactionConvolution A μ
  have h2 := A.W_continuous
  fun_prop

theorem centeredKernel_bounded (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |centeredKernel A μ x y| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_centeredKernel A μ).continuousOn
  exact ⟨|C|, abs_nonneg _, fun x y => by
    simpa using (hC (x, y) (Set.mem_univ _)).trans (le_abs_self C)⟩

theorem integral_interactionConvolution (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    ∫ x, interactionConvolution A μ x ∂(μ : Measure (Torus d)) = meanInteraction A μ := by
  unfold meanInteraction interactionConvolution
  rw [integral_prod _ (integrable_W_prod A μ)]

/-- `K` is centered in its second variable. -/
theorem integral_centeredKernel_right (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (x : Torus d) : ∫ y, centeredKernel A μ x y ∂(μ : Measure (Torus d)) = 0 := by
  have hW : Integrable (fun y => A.W x y) (μ : Measure (Torus d)) :=
    (A.W_continuous_right x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (interactionConvolution A μ) (μ : Measure (Torus d)) :=
    (continuous_interactionConvolution A μ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold centeredKernel
  have h1 : Integrable (fun y => A.W x y - interactionConvolution A μ x)
      (μ : Measure (Torus d)) := hW.sub (integrable_const _)
  have h2 : Integrable (fun y => A.W x y - interactionConvolution A μ x - interactionConvolution A μ y)
      (μ : Measure (Torus d)) := h1.sub hc
  rw [integral_add h2 (integrable_const _), integral_sub h1 hc, integral_sub hW (integrable_const _),
    integral_interactionConvolution]
  simp [interactionConvolution]

theorem integral_centeredKernel_left (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (y : Torus d) : ∫ x, centeredKernel A μ x y ∂(μ : Measure (Torus d)) = 0 := by
  simp_rw [centeredKernel_symm A μ _ y]
  exact integral_centeredKernel_right A μ y


section Operator

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem norm_toLp_le_norm (g : Torus d →ᵇ ℝ) :
    ‖BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ g‖ ≤ ‖g‖ := by
  have := (BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ).le_opNorm g
  have h3 := BoundedContinuousFunction.toLp_norm_le (E := ℝ) (p := 2) (μ : Measure (Torus d))
    (𝕜 := ℝ)
  have h4 : ‖(BoundedContinuousFunction.toLp (E := ℝ) 2 (μ : Measure (Torus d)) ℝ)‖ ≤ 1 := by
    simpa [measureUnivNNReal] using h3
  calc _ ≤ _ := this
    _ ≤ 1 * ‖g‖ := by gcongr
    _ = ‖g‖ := one_mul _

/-- Cauchy–Schwarz against a bounded continuous function. -/
theorem abs_integral_mul_le (g : Torus d →ᵇ ℝ) (h : Lp ℝ 2 (μ : Measure (Torus d))) :
    |∫ y, g y * h y ∂(μ : Measure (Torus d))| ≤ ‖g‖ * ‖h‖ := by
  have h1 : inner ℝ (BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ g) h
      = ∫ y, g y * h y ∂(μ : Measure (Torus d)) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (μ : Measure (Torus d)) ℝ g] with y hy
    rw [hy]; simp [mul_comm]
  rw [← h1]
  calc _ ≤ ‖BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ g‖ * ‖h‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖g‖ * ‖h‖ := by gcongr; exact norm_toLp_le_norm μ g

theorem integrable_lp (h : Lp ℝ 2 (μ : Measure (Torus d))) :
    Integrable h (μ : Measure (Torus d)) :=
  (Lp.memLp h).integrable (by norm_num)

/-- The transform `x ↦ ∫ K(x,y) h(y) dμ(y)` of an `L²` function. -/
noncomputable def kernelTransform (h : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ :=
  fun x => ∫ y, centeredKernel A μ x y * h y ∂(μ : Measure (Torus d))

theorem continuous_kernelSection (x : Torus d) : Continuous (fun y => centeredKernel A μ x y) :=
  (continuous_centeredKernel A μ).comp (continuous_const.prodMk continuous_id)

theorem continuous_kernelTransform (h : Lp ℝ 2 (μ : Measure (Torus d))) :
    Continuous (kernelTransform A μ h) := by
  obtain ⟨C, hC0, hC⟩ := centeredKernel_bounded A μ
  refine continuous_of_dominated (bound := fun y => C * ‖h y‖) (fun x => ?_) (fun x => ?_)
    ?_ (ae_of_all _ fun y => ?_)
  · exact (continuous_kernelSection A μ x).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable h)
  · refine ae_of_all _ fun y => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hC x y) (norm_nonneg _)
  · exact (integrable_lp μ h).norm.const_mul C
  · exact ((continuous_centeredKernel A μ).comp (continuous_id.prodMk continuous_const)).mul
      continuous_const

/-- The transform as a bounded continuous function. -/
noncomputable def kernelBCF (h : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨kernelTransform A μ h, continuous_kernelTransform A μ h⟩

theorem kernelBCF_apply (h : Lp ℝ 2 (μ : Measure (Torus d))) (x : Torus d) :
    kernelBCF A μ h x = kernelTransform A μ h x := rfl

theorem integrable_kernel_mul (x : Torus d) (h : Lp ℝ 2 (μ : Measure (Torus d))) :
    Integrable (fun y => centeredKernel A μ x y * h y) (μ : Measure (Torus d)) := by
  obtain ⟨C, hC0, hC⟩ := centeredKernel_bounded A μ
  exact (integrable_lp μ h).bdd_mul (c := C) (continuous_kernelSection A μ x).aestronglyMeasurable
    (ae_of_all _ fun y => by simpa using hC x y)

theorem kernelTransform_add (h h' : Lp ℝ 2 (μ : Measure (Torus d))) (x : Torus d) :
    kernelTransform A μ (h + h') x = kernelTransform A μ h x + kernelTransform A μ h' x := by
  unfold kernelTransform
  rw [← integral_add (integrable_kernel_mul A μ x h) (integrable_kernel_mul A μ x h')]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add h h'] with y hy
  rw [hy]; simp [mul_add]

theorem kernelTransform_smul (c : ℝ) (h : Lp ℝ 2 (μ : Measure (Torus d))) (x : Torus d) :
    kernelTransform A μ (c • h) x = c * kernelTransform A μ h x := by
  unfold kernelTransform
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c h] with y hy
  rw [hy]; simp; ring

theorem norm_kernelBCF_le (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x y, |centeredKernel A μ x y| ≤ C)
    (h : Lp ℝ 2 (μ : Measure (Torus d))) : ‖kernelBCF A μ h‖ ≤ C * ‖h‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
  let g : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => centeredKernel A μ x y, continuous_kernelSection A μ x⟩
  have hg : ‖g‖ ≤ C := (BoundedContinuousFunction.norm_le hC0).2 fun y => by
    simpa [g] using hC x y
  have := abs_integral_mul_le μ g h
  rw [kernelBCF_apply, Real.norm_eq_abs]
  calc _ ≤ ‖g‖ * ‖h‖ := this
    _ ≤ C * ‖h‖ := by gcongr

/-- The (uncentered-domain) integral operator `h ↦ ∫ K(·,y) h(y) dμ(y)` on `L²(μ)`. -/
noncomputable def kernelOp : Lp ℝ 2 (μ : Measure (Torus d)) →L[ℝ] Lp ℝ 2 (μ : Measure (Torus d)) :=
  LinearMap.mkContinuous
    { toFun := fun h => BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ (kernelBCF A μ h)
      map_add' := fun h h' => by
        rw [← map_add]; congr 1; ext x; simp [kernelBCF_apply, kernelTransform_add]
      map_smul' := fun c h => by
        rw [← map_smul]; congr 1; ext x; simp [kernelBCF_apply, kernelTransform_smul] }
    (centeredKernel_bounded A μ).choose
    (fun h => (norm_toLp_le_norm μ _).trans (norm_kernelBCF_le A μ _
      (centeredKernel_bounded A μ).choose_spec.1 (centeredKernel_bounded A μ).choose_spec.2 h))

theorem kernelOp_ae (h : Lp ℝ 2 (μ : Measure (Torus d))) :
    (kernelOp A μ h : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))] kernelTransform A μ h :=
  BoundedContinuousFunction.coeFn_toLp 2 (μ : Measure (Torus d)) ℝ (kernelBCF A μ h)


/-! ### The centered space and the operators -/

/-- `L²_0(μ)`: real `L²(μ)` functions with zero `μ`-mean, as a submodule of `Lp ℝ 2 μ`. -/
noncomputable def centeredL2 (μ : ProbabilityMeasure (Torus d)) :
    Submodule ℝ (Lp ℝ 2 (μ : Measure (Torus d))) where
  carrier := {f | ∫ x, f x ∂(μ : Measure (Torus d)) = 0}
  add_mem' := fun {a b} ha hb => by
    have ha' : ∫ x, a x ∂(μ : Measure (Torus d)) = 0 := ha
    have hb' : ∫ x, b x ∂(μ : Measure (Torus d)) = 0 := hb
    show ∫ x, (a + b) x ∂(μ : Measure (Torus d)) = 0
    rw [integral_congr_ae (Lp.coeFn_add a b)]
    simp only [Pi.add_apply]
    rw [integral_add (integrable_lp μ a) (integrable_lp μ b), ha', hb', add_zero]
  zero_mem' := by
    show ∫ x, (0 : Lp ℝ 2 (μ : Measure (Torus d))) x ∂(μ : Measure (Torus d)) = 0
    rw [integral_congr_ae (Lp.coeFn_zero ℝ 2 (μ : Measure (Torus d)))]
    simp
  smul_mem' := fun c a ha => by
    have ha' : ∫ x, a x ∂(μ : Measure (Torus d)) = 0 := ha
    show ∫ x, (c • a) x ∂(μ : Measure (Torus d)) = 0
    rw [integral_congr_ae (Lp.coeFn_smul c a)]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, ha', mul_zero]

theorem mem_centeredL2 {μ : ProbabilityMeasure (Torus d)} (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    f ∈ centeredL2 μ ↔ ∫ x, f x ∂(μ : Measure (Torus d)) = 0 := Iff.rfl

theorem integrable_prod_cont_mul (φ : Torus d × Torus d → ℝ) (hφ : Continuous φ)
    {a b : Torus d → ℝ} (ha : Integrable a (μ : Measure (Torus d)))
    (hb : Integrable b (μ : Measure (Torus d))) :
    Integrable (fun p : Torus d × Torus d => φ p * (a p.1 * b p.2))
      ((μ : Measure (Torus d)).prod μ) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact (ha.mul_prod hb).bdd_mul (c := C) hφ.aestronglyMeasurable
    (ae_of_all _ fun p => by simpa using hC p (Set.mem_univ _))

theorem kernelOp_mem_centeredL2 {f : Lp ℝ 2 (μ : Measure (Torus d))} (hf : f ∈ centeredL2 μ) :
    kernelOp A μ f ∈ centeredL2 μ := by
  have hf' : ∫ x, f x ∂(μ : Measure (Torus d)) = 0 := hf
  show ∫ x, (kernelOp A μ f) x ∂(μ : Measure (Torus d)) = 0
  rw [integral_congr_ae (kernelOp_ae A μ f)]
  unfold kernelTransform
  have hint : Integrable (Function.uncurry fun x y => centeredKernel A μ x y * f y)
      ((μ : Measure (Torus d)).prod μ) := by
    have := integrable_prod_cont_mul μ (fun p => centeredKernel A μ p.1 p.2)
      (continuous_centeredKernel A μ) (integrable_const (1 : ℝ)) (integrable_lp μ f)
    exact this.congr (ae_of_all _ fun p => by simp [Function.uncurry])
  rw [integral_integral_swap hint]
  have : ∀ y, ∫ x, centeredKernel A μ x y * f y ∂(μ : Measure (Torus d)) = 0 := fun y => by
    rw [integral_mul_const, integral_centeredKernel_left, zero_mul]
  simp [this]

end Operator

/-- The integral operator `T_μ f(x) = ∫ K_μ(x, y) f(y) dμ(y)` on `L²_0(μ)`. -/
noncomputable def centeredInteraction (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    centeredL2 μ →L[ℝ] centeredL2 μ :=
  ((kernelOp A μ).comp (centeredL2 μ).subtypeL).codRestrict (centeredL2 μ)
    fun f => kernelOp_mem_centeredL2 A μ f.2

/-- The density Hessian `H_μ = I + T_μ` on `L²_0(μ)`. -/
noncomputable def densityHessian (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    centeredL2 μ →L[ℝ] centeredL2 μ :=
  ContinuousLinearMap.id ℝ (centeredL2 μ) + centeredInteraction A μ

/-- Coercivity of the density Hessian: `∃ c > 0, ∀ f ∈ L²_0(μ), ⟨f, H f⟩ ≥ c ‖f‖²`. -/
def IsCoerciveDensityHessian (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ f : centeredL2 μ, c * ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian A μ f)


section Form

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

theorem coe_centeredInteraction (f : centeredL2 μ) :
    ((centeredInteraction A μ f : centeredL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) =
      kernelOp A μ f := rfl

/-- The pairing `⟨f, T g⟩` as a double integral against the kernel (Fubini). -/
theorem inner_kernelOp (f g : Lp ℝ 2 (μ : Measure (Torus d))) :
    inner ℝ f (kernelOp A μ g) =
      ∫ p, centeredKernel A μ p.1 p.2 * (f p.1 * g p.2) ∂((μ : Measure (Torus d)).prod μ) := by
  rw [L2.inner_def]
  have h1 : ∀ᵐ x ∂(μ : Measure (Torus d)),
      inner ℝ (f x) ((kernelOp A μ g) x) = ∫ y, centeredKernel A μ x y * (f x * g y)
        ∂(μ : Measure (Torus d)) := by
    filter_upwards [kernelOp_ae A μ g] with x hx
    rw [hx]
    unfold kernelTransform
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  rw [integral_congr_ae h1]
  have hint := integrable_prod_cont_mul μ (fun p => centeredKernel A μ p.1 p.2)
    (continuous_centeredKernel A μ) (integrable_lp μ f) (integrable_lp μ g)
  exact (integral_prod _ hint).symm

theorem centeredInteraction_symmetric (f g : centeredL2 μ) :
    inner ℝ (centeredInteraction A μ f) g = inner ℝ f (centeredInteraction A μ g) := by
  show inner ℝ (kernelOp A μ (f : Lp ℝ 2 (μ : Measure (Torus d)))) (g : Lp ℝ 2 _) =
    inner ℝ (f : Lp ℝ 2 _) (kernelOp A μ (g : Lp ℝ 2 _))
  rw [real_inner_comm, inner_kernelOp, inner_kernelOp]
  rw [← integral_prod_swap]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [centeredKernel_symm A μ p.2 p.1]; ring



/-- On centered functions the centering terms of `K` drop out of the double integral. -/
theorem integral_centeredKernel_form (f : centeredL2 μ) :
    ∫ p, centeredKernel A μ p.1 p.2 *
        (((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.1 *
          ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.2)
        ∂((μ : Measure (Torus d)).prod μ) =
      ∫ p, A.W p.1 p.2 *
        (((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.1 *
          ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.2)
        ∂((μ : Measure (Torus d)).prod μ) := by
  set φ : Torus d → ℝ := ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) with hφ
  have hf0 : ∫ x, φ x ∂(μ : Measure (Torus d)) = 0 := f.2
  have hfi : Integrable φ (μ : Measure (Torus d)) := integrable_lp μ _
  have hc := continuous_interactionConvolution A μ
  have hW := A.W_continuous
  have i1 := integrable_prod_cont_mul μ (fun p => A.W p.1 p.2) hW hfi hfi
  have i2 := integrable_prod_cont_mul μ (fun p => interactionConvolution A μ p.1)
    (hc.comp continuous_fst) hfi hfi
  have i3 := integrable_prod_cont_mul μ (fun p => interactionConvolution A μ p.2)
    (hc.comp continuous_snd) hfi hfi
  have i4 := integrable_prod_cont_mul μ (fun _ => meanInteraction A μ) continuous_const hfi hfi
  have e : ∀ p : Torus d × Torus d, centeredKernel A μ p.1 p.2 * (φ p.1 * φ p.2) =
      A.W p.1 p.2 * (φ p.1 * φ p.2) - interactionConvolution A μ p.1 * (φ p.1 * φ p.2) -
        interactionConvolution A μ p.2 * (φ p.1 * φ p.2) + meanInteraction A μ * (φ p.1 * φ p.2) :=
    fun p => by unfold centeredKernel; ring
  simp_rw [e]
  have j1 : Integrable (fun p : Torus d × Torus d => A.W p.1 p.2 * (φ p.1 * φ p.2) -
      interactionConvolution A μ p.1 * (φ p.1 * φ p.2)) ((μ : Measure (Torus d)).prod μ) :=
    i1.sub i2
  have j2 : Integrable (fun p : Torus d × Torus d => A.W p.1 p.2 * (φ p.1 * φ p.2) -
      interactionConvolution A μ p.1 * (φ p.1 * φ p.2) -
      interactionConvolution A μ p.2 * (φ p.1 * φ p.2)) ((μ : Measure (Torus d)).prod μ) :=
    j1.sub i3
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2]
  have hcφ : Integrable (fun x => interactionConvolution A μ x * φ x) (μ : Measure (Torus d)) :=
    (hfi.bdd_mul (c := (isCompact_univ.exists_bound_of_continuousOn hc.continuousOn).choose)
      hc.aestronglyMeasurable (ae_of_all _ fun x => by
        simpa using (isCompact_univ.exists_bound_of_continuousOn hc.continuousOn).choose_spec x
          (Set.mem_univ _)))
  have z2 : ∫ p : Torus d × Torus d, interactionConvolution A μ p.1 * (φ p.1 * φ p.2)
      ∂((μ : Measure (Torus d)).prod μ) = 0 := by
    have := integral_prod_mul (μ := (μ : Measure (Torus d))) (ν := (μ : Measure (Torus d)))
      (fun x => interactionConvolution A μ x * φ x) φ
    rw [hf0, mul_zero] at this
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    ring
  have z3 : ∫ p : Torus d × Torus d, interactionConvolution A μ p.2 * (φ p.1 * φ p.2)
      ∂((μ : Measure (Torus d)).prod μ) = 0 := by
    have := integral_prod_mul (μ := (μ : Measure (Torus d))) (ν := (μ : Measure (Torus d)))
      φ (fun x => interactionConvolution A μ x * φ x)
    rw [hf0, zero_mul] at this
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    ring
  have z4 : ∫ p : Torus d × Torus d, meanInteraction A μ * (φ p.1 * φ p.2)
      ∂((μ : Measure (Torus d)).prod μ) = 0 := by
    rw [integral_const_mul, integral_prod_mul φ φ, hf0]; simp
  rw [z2, z3, z4]; ring

/-- The second variation: `⟨f, H f⟩ = ‖f‖² + ∬ W f⊗f dμ²` for `f ∈ L²_0(μ)`. -/
theorem inner_densityHessian (f : centeredL2 μ) :
    inner ℝ f (densityHessian A μ f) = ‖f‖ ^ 2 +
      ∫ p, A.W p.1 p.2 *
        (((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.1 *
          ((f : Lp ℝ 2 (μ : Measure (Torus d))) : Torus d → ℝ) p.2)
        ∂((μ : Measure (Torus d)).prod μ) := by
  have h1 : inner ℝ f (densityHessian A μ f) = inner ℝ f f + inner ℝ f (centeredInteraction A μ f) := by
    rw [← inner_add_right]; rfl
  rw [h1, real_inner_self_eq_norm_sq, ← integral_centeredKernel_form A μ f]
  congr 1
  exact inner_kernelOp A μ _ _

end Form

end DGPS
