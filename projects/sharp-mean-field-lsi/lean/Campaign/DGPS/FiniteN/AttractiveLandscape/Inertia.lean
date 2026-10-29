import DGPS.FiniteN.AttractiveLandscape.Entropy
import DGPS.FiniteN.AttractiveLandscape.AbstractInertia
import DGPS.Equilibrium.Hessian

/-!
# Inertia comparison for the attractive finite rank landscape (FIN047)

For `μ` a probability measure and `ξ = Φ - m_μ`, the centered kernel of the attractive model is
`K(x,y) = -⟪ξ x, ξ y⟫`.  With `A v = [x ↦ ⟪v, ξ x⟫] : ℝ^r → L²_0(μ)` and `B f = ∫ f ξ dμ` (formal
adjoint of `A`), the density Hessian is `I - A B` and, for `μ = q_z`, `D²ψ(z) = I - B A`.
Abstract inertia transfer (`AbstractInertia`) gives equality of negative indices, nullities and
coercivity.
-/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal BoundedContinuousFunction

namespace DGPS.FiniteN.AttractiveLandscape

variable {d r : ℕ} {U : Torus d → ℝ} {Φ : Torus d → Feature r}

/-- The centered feature `ξ = Φ - m_μ`. -/
noncomputable def centeredFeature (Φ : Torus d → Feature r) (μ : ProbabilityMeasure (Torus d))
    (x : Torus d) : Feature r :=
  Φ x - measureMean Φ (μ : Measure (Torus d))

theorem continuous_centeredFeature (μ : ProbabilityMeasure (Torus d)) (hΦ : Continuous Φ) :
    Continuous (centeredFeature Φ μ) :=
  hΦ.sub continuous_const

section Kernel

variable (hU : Continuous U) (hΦ : Continuous Φ) (μ : ProbabilityMeasure (Torus d))

theorem meanInteraction_attractive :
    meanInteraction (attractiveData hU hΦ) μ =
      2 * sqMean Φ (μ : Measure (Torus d)) - ‖measureMean Φ (μ : Measure (Torus d))‖ ^ 2 := by
  rw [← integral_interactionConvolution]
  have h : ∀ x, interactionConvolution (attractiveData hU hΦ) μ x =
      ‖Φ x‖ ^ 2 / 2 + sqMean Φ (μ : Measure (Torus d)) -
        ⟪measureMean Φ (μ : Measure (Torus d)), Φ x⟫ := fun x => by
    rw [real_inner_comm]
    exact interactionConvolution_attractive hU hΦ (μ : Measure (Torus d)) x
  simp_rw [h]
  have i1 : Integrable (fun y => ‖Φ y‖ ^ 2 / 2) (μ : Measure (Torus d)) :=
    integrable_cont _ ((hΦ.norm.pow 2).div_const 2)
  have i2 : Integrable (fun x => ⟪measureMean Φ (μ : Measure (Torus d)), Φ x⟫)
      (μ : Measure (Torus d)) := integrable_cont _ (continuous_const.inner hΦ)
  have ia : Integrable (fun x => ‖Φ x‖ ^ 2 / 2 + sqMean Φ (μ : Measure (Torus d)))
      (μ : Measure (Torus d)) := i1.add (integrable_const _)
  rw [integral_sub ia i2, integral_add i1 (integrable_const _),
    integral_const, integral_inner (integrable_feature _ hΦ)]
  simp only [probReal_univ, one_smul]
  unfold sqMean
  rw [show ⟪measureMean Φ (μ : Measure (Torus d)), ∫ x, Φ x ∂(μ : Measure (Torus d))⟫ =
    ‖measureMean Φ (μ : Measure (Torus d))‖ ^ 2 from real_inner_self_eq_norm_sq _]
  ring

theorem centeredKernel_attractive (x y : Torus d) :
    centeredKernel (attractiveData hU hΦ) μ x y =
      -⟪centeredFeature Φ μ x, centeredFeature Φ μ y⟫ := by
  have hx := interactionConvolution_attractive hU hΦ (μ : Measure (Torus d)) x
  have hy := interactionConvolution_attractive hU hΦ (μ : Measure (Torus d)) y
  have hW : (attractiveData hU hΦ).W x y = ‖Φ x - Φ y‖ ^ 2 / 2 := rfl
  unfold centeredKernel
  rw [hW, show interactionConvolution (attractiveData hU hΦ) μ x = _ from hx,
    show interactionConvolution (attractiveData hU hΦ) μ y = _ from hy,
    meanInteraction_attractive hU hΦ μ]
  unfold centeredFeature
  have hm : ⟪measureMean Φ (μ : Measure (Torus d)), measureMean Φ (μ : Measure (Torus d))⟫ =
      ‖measureMean Φ (μ : Measure (Torus d))‖ ^ 2 := real_inner_self_eq_norm_sq _
  simp only [inner_sub_left, inner_sub_right, norm_sub_sq_real, hm]
  rw [real_inner_comm (measureMean Φ (μ : Measure (Torus d))) (Φ y)]
  ring

end Kernel


section Operators

variable (hΦ : Continuous Φ) (μ : ProbabilityMeasure (Torus d))

include hΦ

theorem integrable_centeredFeature :
    Integrable (centeredFeature Φ μ) (μ : Measure (Torus d)) :=
  Continuous.integrable_of_hasCompactSupport (continuous_centeredFeature μ hΦ)
    (HasCompactSupport.of_compactSpace _)

theorem integral_centeredFeature :
    ∫ x, centeredFeature Φ μ x ∂(μ : Measure (Torus d)) = 0 := by
  unfold centeredFeature
  rw [integral_sub (integrable_feature _ hΦ) (integrable_const _)]
  simp [measureMean]

/-- The function `x ↦ ⟪v, ξ x⟫` as a bounded continuous function. -/
noncomputable def featureBCF (v : Feature r) : Torus d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ⟪v, centeredFeature Φ μ x⟫,
      continuous_const.inner (continuous_centeredFeature μ hΦ)⟩

theorem featureBCF_apply (v : Feature r) (x : Torus d) :
    featureBCF hΦ μ v x = ⟪v, centeredFeature Φ μ x⟫ := rfl

/-- The class of `x ↦ ⟪v, ξ x⟫` in `L²(μ)`. -/
noncomputable def toLpFeature (v : Feature r) : Lp ℝ 2 (μ : Measure (Torus d)) :=
  BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ (featureBCF hΦ μ v)

theorem toLpFeature_ae (v : Feature r) :
    (toLpFeature hΦ μ v : Torus d → ℝ) =ᵐ[(μ : Measure (Torus d))]
      fun x => ⟪v, centeredFeature Φ μ x⟫ :=
  BoundedContinuousFunction.coeFn_toLp 2 (μ : Measure (Torus d)) ℝ (featureBCF hΦ μ v)

theorem toLpFeature_mem (v : Feature r) : toLpFeature hΦ μ v ∈ centeredL2 μ := by
  rw [mem_centeredL2, integral_congr_ae (toLpFeature_ae hΦ μ v),
    integral_inner (integrable_centeredFeature hΦ μ), integral_centeredFeature hΦ μ,
    inner_zero_right]

/-- `A v = [x ↦ ⟪v, Φ x - m_μ⟫]` as a linear map `ℝ^r → L²_0(μ)`. -/
noncomputable def opA : Feature r →ₗ[ℝ] centeredL2 μ where
  toFun v := ⟨toLpFeature hΦ μ v, toLpFeature_mem hΦ μ v⟩
  map_add' v w := by
    apply Subtype.ext
    show toLpFeature hΦ μ (v + w) = toLpFeature hΦ μ v + toLpFeature hΦ μ w
    unfold toLpFeature
    rw [← map_add]; congr 1; ext x
    simp [featureBCF_apply, inner_add_left]
  map_smul' c v := by
    apply Subtype.ext
    show toLpFeature hΦ μ (c • v) = c • toLpFeature hΦ μ v
    unfold toLpFeature
    rw [← map_smul]; congr 1; ext x
    simp [featureBCF_apply, real_inner_smul_left]

theorem coe_opA (v : Feature r) :
    ((opA hΦ μ v : centeredL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) = toLpFeature hΦ μ v := rfl

theorem integrable_smul_feature (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    Integrable (fun x => f x • centeredFeature Φ μ x) (μ : Measure (Torus d)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_centeredFeature μ hΦ).norm.continuousOn
  refine Integrable.mono' ((integrable_lp μ f).norm.mul_const C)
    ((Lp.aestronglyMeasurable f).smul (continuous_centeredFeature μ hΦ).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_smul]
  have := hC x (Set.mem_univ _)
  rw [norm_norm] at this
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

/-- `B f = ∫ f ξ dμ` on `L²(μ)`. -/
noncomputable def opBL : Lp ℝ 2 (μ : Measure (Torus d)) →ₗ[ℝ] Feature r where
  toFun f := ∫ x, f x • centeredFeature Φ μ x ∂(μ : Measure (Torus d))
  map_add' f g := by
    rw [← integral_add (integrable_smul_feature hΦ μ f) (integrable_smul_feature hΦ μ g)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx]; simp [add_smul]
  map_smul' c f := by
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx]; simp [smul_smul]

/-- `B f = ∫ f ξ dμ` on `L²_0(μ)`. -/
noncomputable def opB : centeredL2 μ →ₗ[ℝ] Feature r :=
  opBL hΦ μ ∘ₗ (centeredL2 μ).subtype

theorem opB_apply (f : centeredL2 μ) :
    opB hΦ μ f = ∫ x, (f : Lp ℝ 2 (μ : Measure (Torus d))) x • centeredFeature Φ μ x
      ∂(μ : Measure (Torus d)) := rfl

theorem opA_opB_adjoint (v : Feature r) (f : centeredL2 μ) :
    ⟪opA hΦ μ v, f⟫ = ⟪v, opB hΦ μ f⟫ := by
  rw [opB_apply, ← integral_inner (integrable_smul_feature hΦ μ _)]
  rw [show ⟪opA hΦ μ v, f⟫ = ⟪((opA hΦ μ v : centeredL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))),
    (f : Lp ℝ 2 (μ : Measure (Torus d)))⟫ from rfl, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [toLpFeature_ae hΦ μ v] with x hx
  rw [coe_opA, hx]
  simp [real_inner_smul_right]

end Operators


section Identities

variable (hU : Continuous U) (hΦ : Continuous Φ) (μ : ProbabilityMeasure (Torus d))

include hU hΦ

theorem kernelBCF_attractive (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    kernelBCF (attractiveData hU hΦ) μ f = -featureBCF hΦ μ (opBL hΦ μ f) := by
  ext x
  rw [kernelBCF_apply, BoundedContinuousFunction.coe_neg, Pi.neg_apply, featureBCF_apply]
  unfold kernelTransform
  have : ∀ y, centeredKernel (attractiveData hU hΦ) μ x y * f y =
      -⟪centeredFeature Φ μ x, f y • centeredFeature Φ μ y⟫ := fun y => by
    rw [centeredKernel_attractive hU hΦ μ x y, real_inner_smul_right]; ring
  simp_rw [this]
  rw [integral_neg, integral_inner (integrable_smul_feature hΦ μ f), real_inner_comm]
  rfl

/-- On `L²_0(μ)` the density Hessian is `I - A B`. -/
theorem densityHessian_eq (f : centeredL2 μ) :
    densityHessian (attractiveData hU hΦ) μ f = f - opA hΦ μ (opB hΦ μ f) := by
  apply Subtype.ext
  show (f : Lp ℝ 2 (μ : Measure (Torus d))) +
      BoundedContinuousFunction.toLp 2 (μ : Measure (Torus d)) ℝ
        (kernelBCF (attractiveData hU hΦ) μ f) =
    (f : Lp ℝ 2 (μ : Measure (Torus d))) - toLpFeature hΦ μ (opB hΦ μ f)
  rw [kernelBCF_attractive hU hΦ μ f, map_neg, sub_eq_add_neg]
  rfl

theorem inner_densityHessian_attractive (f : centeredL2 μ) :
    ⟪f, densityHessian (attractiveData hU hΦ) μ f⟫ = ‖f‖ ^ 2 - ‖opB hΦ μ f‖ ^ 2 := by
  rw [densityHessian_eq hU hΦ, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_comm (opA hΦ μ (opB hΦ μ f)) f, opA_opB_adjoint hΦ μ,
    real_inner_self_eq_norm_sq]

theorem densityHessian_linearMap :
    ((densityHessian (attractiveData hU hΦ) μ : centeredL2 μ →L[ℝ] centeredL2 μ) :
        centeredL2 μ →ₗ[ℝ] centeredL2 μ) =
      LinearMap.id - opA hΦ μ ∘ₗ opB hΦ μ :=
  LinearMap.ext fun f => by
    rw [LinearMap.sub_apply]
    exact densityHessian_eq hU hΦ μ f

theorem featureCov_eq_inner_opA (z v w : Feature r) :
    featureCov U Φ z v w =
      ⟪opA hΦ (gibbsPM hU hΦ z) v, opA hΦ (gibbsPM hU hΦ z) w⟫ := by
  rw [show ⟪opA hΦ (gibbsPM hU hΦ z) v, opA hΦ (gibbsPM hU hΦ z) w⟫ =
    ⟪((opA hΦ (gibbsPM hU hΦ z) v : centeredL2 (gibbsPM hU hΦ z)) :
        Lp ℝ 2 ((gibbsPM hU hΦ z : ProbabilityMeasure (Torus d)) : Measure (Torus d))),
      ((opA hΦ (gibbsPM hU hΦ z) w : centeredL2 (gibbsPM hU hΦ z)) :
        Lp ℝ 2 ((gibbsPM hU hΦ z : ProbabilityMeasure (Torus d)) : Measure (Torus d)))⟫ from rfl,
    L2.inner_def]
  unfold featureCov
  refine integral_congr_ae ?_
  filter_upwards [toLpFeature_ae hΦ (gibbsPM hU hΦ z) v,
    toLpFeature_ae hΦ (gibbsPM hU hΦ z) w] with x hv hw
  rw [coe_opA, coe_opA, hv, hw]
  have hξ : centeredFeature Φ (gibbsPM hU hΦ z) x = Φ x - featureMean U Φ z := rfl
  rw [hξ]
  simp [mul_comm]

theorem hessian_psi_eq (z v w : Feature r) :
    fderiv ℝ (fderiv ℝ (psi U Φ)) z v w =
      ⟪v, w⟫ - ⟪opA hΦ (gibbsPM hU hΦ z) v, opA hΦ (gibbsPM hU hΦ z) w⟫ := by
  rw [hessian_psi hU hΦ, featureCov_eq_inner_opA hU hΦ]

theorem hessian_psi_diag (z v : Feature r) :
    fderiv ℝ (fderiv ℝ (psi U Φ)) z v v =
      ‖v‖ ^ 2 - ‖opA hΦ (gibbsPM hU hΦ z) v‖ ^ 2 := by
  rw [hessian_psi_eq hU hΦ, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem hessian_psi_eq_inner (z v w : Feature r) :
    fderiv ℝ (fderiv ℝ (psi U Φ)) z v w =
      ⟪v - opB hΦ (gibbsPM hU hΦ z) (opA hΦ (gibbsPM hU hΦ z) v), w⟫ := by
  rw [hessian_psi_eq hU hΦ, inner_sub_left,
    real_inner_comm (opA hΦ (gibbsPM hU hΦ z) w) (opA hΦ (gibbsPM hU hΦ z) v),
    opA_opB_adjoint hΦ,
    real_inner_comm (opB hΦ (gibbsPM hU hΦ z) (opA hΦ (gibbsPM hU hΦ z) v)) w]

theorem ker_hessian_psi (z : Feature r) :
    LinearMap.ker ((fderiv ℝ (fderiv ℝ (psi U Φ)) z : Feature r →L[ℝ] Feature r →L[ℝ] ℝ) :
        Feature r →ₗ[ℝ] (Feature r →L[ℝ] ℝ)) =
      LinearMap.ker (LinearMap.id - opB hΦ (gibbsPM hU hΦ z) ∘ₗ opA hΦ (gibbsPM hU hΦ z)) := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]
  rw [ContinuousLinearMap.ext_iff]
  simp only [zero_apply, hessian_psi_eq_inner hU hΦ]
  constructor
  · intro h
    exact ext_inner_right ℝ (fun w => by rw [h w, inner_zero_left])
  · intro h w
    rw [h, inner_zero_left]

end Identities


section Inertia

variable (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r)

/-- Equality of negative inertia indices: the Hessian of `ψ` at `z` and the centered
free-energy Hessian at `q_z` have negative subspaces of exactly the same dimensions. -/
theorem hasNegativeSubspace_hessian_iff (n : ℕ) :
    HasNegativeSubspace (fun v : Feature r => fderiv ℝ (fderiv ℝ (psi U Φ)) z v v) n ↔
      HasNegativeSubspace
        (fun f : centeredL2 (gibbsPM hU hΦ z) =>
          ⟪f, densityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z) f⟫) n := by
  have h1 : (fun v : Feature r => fderiv ℝ (fderiv ℝ (psi U Φ)) z v v) =
      fun v => ‖v‖ ^ 2 - ‖opA hΦ (gibbsPM hU hΦ z) v‖ ^ 2 :=
    funext fun v => hessian_psi_diag hU hΦ z v
  have h2 : (fun f : centeredL2 (gibbsPM hU hΦ z) =>
      ⟪f, densityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z) f⟫) =
      fun f => ‖f‖ ^ 2 - ‖opB hΦ (gibbsPM hU hΦ z) f‖ ^ 2 :=
    funext fun f => inner_densityHessian_attractive hU hΦ _ f
  rw [h1, h2]
  exact hasNegativeSubspace_iff _ _ (opA_opB_adjoint hΦ _) n

/-- Equality of the nullities. -/
theorem finrank_ker_hessian_eq :
    Module.finrank ℝ (LinearMap.ker ((fderiv ℝ (fderiv ℝ (psi U Φ)) z :
        Feature r →L[ℝ] Feature r →L[ℝ] ℝ) : Feature r →ₗ[ℝ] (Feature r →L[ℝ] ℝ))) =
      Module.finrank ℝ (LinearMap.ker
        ((densityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z) :
          centeredL2 (gibbsPM hU hΦ z) →L[ℝ] centeredL2 (gibbsPM hU hΦ z)) :
          centeredL2 (gibbsPM hU hΦ z) →ₗ[ℝ] centeredL2 (gibbsPM hU hΦ z))) := by
  rw [ker_hessian_psi hU hΦ, densityHessian_linearMap hU hΦ]
  exact finrank_ker_eq _ _

/-- Coercivity of `D²ψ(z)` is equivalent to coercivity of the density Hessian at `q_z`. -/
theorem coercive_hessian_iff :
    (∃ c : ℝ, 0 < c ∧ ∀ v : Feature r, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (psi U Φ)) z v v) ↔
      IsCoerciveDensityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z) := by
  unfold IsCoerciveDensityHessian
  simp only [hessian_psi_diag hU hΦ, inner_densityHessian_attractive hU hΦ]
  exact coercive_iff _ _ (opA_opB_adjoint hΦ _)

end Inertia

end DGPS.FiniteN.AttractiveLandscape
