import DGPS.Examples.ThreeSpeciesCircle.Model
import DGPS.Equilibrium.Hessian
import DGPS.Foundations.WeakSobolev
import DGPS.Foundations.TotalVariation
import DGPS.Model.FreeEnergy
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.WeakContractions

open MeasureTheory InformationTheory
open scoped ContDiff BoundedContinuousFunction

open DGPS

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The constant `a₀ = 4π²`. -/
noncomputable def a0 : ℝ := 4 * Real.pi ^ 2

theorem a0_pos : 0 < a0 := by unfold a0; positivity

/-- Coefficient `8 / a₀` of the two positive rank-one terms. -/
noncomputable def kAlpha : ℝ := 8 / a0
/-- Coefficient `1 / (17 a₀)` of the negative rank-one term. -/
noncomputable def kBeta : ℝ := 1 / (17 * a0)

theorem kAlpha_pos : 0 < kAlpha := div_pos (by norm_num) a0_pos
theorem kBeta_pos : 0 < kBeta := by unfold kBeta; have := a0_pos; positivity

/-- The rank-three kernel `K_h = (8/a₀)(c_h ⊗ c_h + s_h ⊗ s_h) - (1/(17 a₀)) b_h ⊗ b_h`. -/
noncomputable def kernelK (h : ℝ) (x y : Torus 1) : ℝ :=
  kAlpha * (featureC h x * featureC h y + featureS h x * featureS h y)
    - kBeta * (featureB h x * featureB h y)

/-- One-body potential `V = -h cos(6πx) + (ε/2) K_h(x,x)`. -/
noncomputable def modelV (h ε : ℝ) (x : Torus 1) : ℝ :=
  -h * cosHarm 3 x + ε / 2 * kernelK h x x

/-- Two-body interaction `W = ε [K_h(x,y) - (K_h(x,x) + K_h(y,y))/2]`. -/
noncomputable def modelW (h ε : ℝ) (x y : Torus 1) : ℝ :=
  ε * (kernelK h x y - (kernelK h x x + kernelK h y y) / 2)

theorem continuous_kernelK (h : ℝ) : Continuous (fun p : Torus 1 × Torus 1 => kernelK h p.1 p.2) := by
  have := featureC_continuous h; have := featureS_continuous h; have := featureB_continuous h
  unfold kernelK; fun_prop

theorem kernelK_symm (h : ℝ) (x y : Torus 1) : kernelK h x y = kernelK h y x := by
  unfold kernelK; ring

theorem continuous_kernelK_diag (h : ℝ) : Continuous (fun x : Torus 1 => kernelK h x x) :=
  (continuous_kernelK h).comp (continuous_id.prodMk continuous_id)

theorem continuous_modelV (h ε : ℝ) : Continuous (modelV h ε) := by
  unfold modelV
  exact ((continuous_const.mul (continuous_cosHarm 3)).add
    ((continuous_const.mul (continuous_kernelK_diag h))))

theorem continuous_modelW (h ε : ℝ) :
    Continuous (fun p : Torus 1 × Torus 1 => modelW h ε p.1 p.2) := by
  unfold modelW
  have h3 : Continuous (fun p : Torus 1 × Torus 1 => kernelK h p.1 p.1) :=
    (continuous_kernelK_diag h).comp continuous_fst
  have h4 : Continuous (fun p : Torus 1 × Torus 1 => kernelK h p.2 p.2) :=
    (continuous_kernelK_diag h).comp continuous_snd
  exact continuous_const.mul ((continuous_kernelK h).sub ((h3.add h4).div_const 2))

/-- The interaction data of the elementary model. -/
noncomputable def modelData (h ε : ℝ) : DGPS.InteractionData 1 where
  V := modelV h ε
  W := modelW h ε
  V_continuous := continuous_modelV h ε
  W_continuous := continuous_modelW h ε
  W_symm := fun x y => by unfold modelW; rw [kernelK_symm h x y]; ring
  W_diag := fun x => by unfold modelW; ring

theorem modelData_V (h ε : ℝ) : (modelData h ε).V = modelV h ε := rfl
theorem modelData_W (h ε : ℝ) : (modelData h ε).W = modelW h ε := rfl


/-! ### Smoothness -/

theorem smooth_cosHarm (k : ℕ) : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => cosHarm k (torusLift y)) := by
  have : (fun y : Fin 1 → ℝ => cosHarm k (torusLift y))
      = fun y => Real.cos (2 * Real.pi * k * y 0) := funext fun y => cosHarm_lift k y
  rw [this]; fun_prop

theorem smooth_sinHarm (k : ℕ) : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => sinHarm k (torusLift y)) := by
  have : (fun y : Fin 1 → ℝ => sinHarm k (torusLift y))
      = fun y => Real.sin (2 * Real.pi * k * y 0) := funext fun y => sinHarm_lift k y
  rw [this]; fun_prop

theorem smooth_featureC (h : ℝ) : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => featureC h (torusLift y)) := by
  unfold featureC; exact (smooth_cosHarm 1).div_const _

theorem smooth_featureS (h : ℝ) : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => featureS h (torusLift y)) := by
  unfold featureS; exact (smooth_sinHarm 1).div_const _

theorem smooth_featureB (h : ℝ) : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => featureB h (torusLift y)) := by
  have := smooth_cosHarm 3
  unfold featureB; fun_prop

abbrev CirclePair := (Fin 1 → ℝ) × (Fin 1 → ℝ)

theorem smooth_kernelK (h : ℝ) :
    ContDiff ℝ ∞ (fun p : CirclePair => kernelK h (torusLift p.1) (torusLift p.2)) := by
  have c1 : ContDiff ℝ ∞ (fun p : CirclePair => featureC h (torusLift p.1)) :=
    (smooth_featureC h).comp contDiff_fst
  have c2 : ContDiff ℝ ∞ (fun p : CirclePair => featureC h (torusLift p.2)) :=
    (smooth_featureC h).comp contDiff_snd
  have s1 : ContDiff ℝ ∞ (fun p : CirclePair => featureS h (torusLift p.1)) :=
    (smooth_featureS h).comp contDiff_fst
  have s2 : ContDiff ℝ ∞ (fun p : CirclePair => featureS h (torusLift p.2)) :=
    (smooth_featureS h).comp contDiff_snd
  have b1 : ContDiff ℝ ∞ (fun p : CirclePair => featureB h (torusLift p.1)) :=
    (smooth_featureB h).comp contDiff_fst
  have b2 : ContDiff ℝ ∞ (fun p : CirclePair => featureB h (torusLift p.2)) :=
    (smooth_featureB h).comp contDiff_snd
  unfold kernelK
  exact (contDiff_const.mul ((c1.mul c2).add (s1.mul s2))).sub (contDiff_const.mul (b1.mul b2))

theorem smooth_kernelK_diag (h : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => kernelK h (torusLift y) (torusLift y)) := by
  have c := smooth_featureC h
  have s := smooth_featureS h
  have b := smooth_featureB h
  unfold kernelK
  exact (contDiff_const.mul ((c.mul c).add (s.mul s))).sub (contDiff_const.mul (b.mul b))

theorem isSmoothPeriodic_modelV (h ε : ℝ) : IsSmoothPeriodic (modelV h ε) := by
  have e : (modelV h ε ∘ torusLift) = fun y : Fin 1 → ℝ =>
      -h * cosHarm 3 (torusLift y) + ε / 2 * kernelK h (torusLift y) (torusLift y) := rfl
  unfold IsSmoothPeriodic
  rw [e]
  exact (contDiff_const.mul (smooth_cosHarm 3)).add (contDiff_const.mul (smooth_kernelK_diag h))

theorem smooth_modelW (h ε : ℝ) :
    ContDiff ℝ ∞ (fun p : CirclePair => modelW h ε (torusLift p.1) (torusLift p.2)) := by
  unfold modelW
  have d1 : ContDiff ℝ ∞ (fun p : CirclePair => kernelK h (torusLift p.1) (torusLift p.1)) :=
    (smooth_kernelK_diag h).comp contDiff_fst
  have d2 : ContDiff ℝ ∞ (fun p : CirclePair => kernelK h (torusLift p.2) (torusLift p.2)) :=
    (smooth_kernelK_diag h).comp contDiff_snd
  exact contDiff_const.mul ((smooth_kernelK h).sub ((d1.add d2).div_const 2))

/-! ### Gauge -/

/-- The reference probability `μ_h` as a `ProbabilityMeasure`. -/
noncomputable def refProb {h : ℝ} (hh : 0 < h) : ProbabilityMeasure (Torus 1) :=
  ⟨threefoldReference h, (threefoldReference_integral_properties hh).2.2.2.2.1⟩

theorem coe_refProb {h : ℝ} (hh : 0 < h) :
    ((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) = threefoldReference h := rfl

theorem integrable_ref {h : ℝ} (hh : 0 < h) {f : Torus 1 → ℝ} (hf : Continuous f) :
    Integrable f (threefoldReference h) := by
  have : IsProbabilityMeasure (threefoldReference h) :=
    (threefoldReference_integral_properties hh).2.2.2.2.1
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_kernelK_right {h : ℝ} (hh : 0 < h) (x : Torus 1) :
    ∫ z, kernelK h x z ∂threefoldReference h = 0 := by
  obtain ⟨hc, hs, hb, -⟩ := elementaryFeatures_centered_independent hh
  have ic := integrable_ref hh (featureC_continuous h)
  have is := integrable_ref hh (featureS_continuous h)
  have ib := integrable_ref hh (featureB_continuous h)
  have e : (fun z => kernelK h x z) = fun z => (kAlpha * featureC h x) * featureC h z
      + (kAlpha * featureS h x) * featureS h z + (-(kBeta * featureB h x)) * featureB h z := by
    funext z; unfold kernelK; ring
  have i1 : Integrable (fun z => (kAlpha * featureC h x) * featureC h z) (threefoldReference h) :=
    ic.const_mul _
  have i2 : Integrable (fun z => (kAlpha * featureS h x) * featureS h z) (threefoldReference h) :=
    is.const_mul _
  have i3 : Integrable (fun z => (-(kBeta * featureB h x)) * featureB h z) (threefoldReference h) :=
    ib.const_mul _
  have i12 : Integrable (fun z => (kAlpha * featureC h x) * featureC h z
      + (kAlpha * featureS h x) * featureS h z) (threefoldReference h) := i1.add i2
  rw [e, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, hc, hs, hb]
  ring

theorem integral_modelW_right {h : ℝ} (hh : 0 < h) (ε : ℝ) (x : Torus 1) :
    ∫ z, modelW h ε x z ∂threefoldReference h
      = -(ε / 2) * (kernelK h x x + ∫ z, kernelK h z z ∂threefoldReference h) := by
  have : IsProbabilityMeasure (threefoldReference h) :=
    (threefoldReference_integral_properties hh).2.2.2.2.1
  have iK : Integrable (fun z => kernelK h x z) (threefoldReference h) :=
    integrable_ref hh ((continuous_kernelK h).comp (continuous_const.prodMk continuous_id))
  have iD : Integrable (fun z => kernelK h z z) (threefoldReference h) :=
    integrable_ref hh (continuous_kernelK_diag h)
  have e : ∀ z, modelW h ε x z = (ε * kernelK h x z - ε / 2 * kernelK h x x) - ε / 2 * kernelK h z z := by
    intro z; unfold modelW; ring
  have i1 : Integrable (fun z => ε * kernelK h x z) (threefoldReference h) := iK.const_mul _
  have i2 : Integrable (fun z : Torus 1 => ε / 2 * kernelK h x x) (threefoldReference h) :=
    integrable_const _
  have i3 : Integrable (fun z => ε / 2 * kernelK h z z) (threefoldReference h) := iD.const_mul _
  have i12 : Integrable (fun z => ε * kernelK h x z - ε / 2 * kernelK h x x)
      (threefoldReference h) := i1.sub i2
  simp_rw [e]
  rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul ε (fun z => kernelK h x z),
    integral_const_mul (ε / 2) (fun z => kernelK h z z),
    integral_const, integral_kernelK_right hh x]
  simp
  ring

theorem centeredKernel_model {h : ℝ} (hh : 0 < h) (ε : ℝ) (x y : Torus 1) :
    DGPS.centeredKernel (modelData h ε) (refProb hh) x y = ε * kernelK h x y := by
  have : IsProbabilityMeasure (threefoldReference h) :=
    (threefoldReference_integral_properties hh).2.2.2.2.1
  have iD : Integrable (fun z => kernelK h z z) (threefoldReference h) :=
    integrable_ref hh (continuous_kernelK_diag h)
  have hconv : ∀ x, DGPS.interactionConvolution (modelData h ε) (refProb hh) x
      = -(ε / 2) * (kernelK h x x + ∫ z, kernelK h z z ∂threefoldReference h) := fun x =>
    integral_modelW_right hh ε x
  have hmean : DGPS.meanInteraction (modelData h ε) (refProb hh)
      = -ε * ∫ z, kernelK h z z ∂threefoldReference h := by
    rw [← DGPS.integral_interactionConvolution (modelData h ε) (refProb hh)]
    simp_rw [hconv]
    show ∫ x, -(ε / 2) * (kernelK h x x + ∫ z, kernelK h z z ∂threefoldReference h)
      ∂threefoldReference h = _
    rw [integral_const_mul, integral_add iD (integrable_const _), integral_const]
    simp; ring
  unfold DGPS.centeredKernel
  rw [hconv, hconv, hmean]
  show modelW h ε x y - _ - _ + _ = _
  unfold modelW
  ring

/-! ### Hessian -/

/-- The feature `b_h` as a bounded continuous function. -/
noncomputable def bBCF (h : ℝ) : Torus 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨featureB h, featureB_continuous h⟩

/-- The sup-norm bound `‖b_h‖_∞`. -/
noncomputable def featureBBound (h : ℝ) : ℝ := ‖bBCF h‖

/-- Admissible coupling range. -/
noncomputable def epsMax (h : ℝ) : ℝ := 1 / (2 * kBeta * (featureBBound h ^ 2 + 1))

theorem epsMax_pos (h : ℝ) : 0 < epsMax h := by
  unfold epsMax; have := kBeta_pos; positivity

theorem eps_mul_lt {h ε : ℝ} (hε : ε < epsMax h) : ε * kBeta * featureBBound h ^ 2 < 1 / 2 := by
  have hb := kBeta_pos
  have hB : 0 < 2 * kBeta * (featureBBound h ^ 2 + 1) := by positivity
  have : ε < 1 / (2 * kBeta * (featureBBound h ^ 2 + 1)) := hε
  rw [lt_div_iff₀ hB] at this
  nlinarith [sq_nonneg (featureBBound h)]

theorem eps_mul_le {h ε : ℝ} (hε : ε < epsMax h) : ε * kBeta * featureBBound h ^ 2 ≤ 1 / 2 := by
  have hb := kBeta_pos
  have hB : 0 < 2 * kBeta * (featureBBound h ^ 2 + 1) := by positivity
  have : ε < 1 / (2 * kBeta * (featureBBound h ^ 2 + 1)) := hε
  rw [lt_div_iff₀ hB] at this
  nlinarith [sq_nonneg (featureBBound h)]

theorem hessian_form {h ε : ℝ} (μ : ProbabilityMeasure (Torus 1))
    (hK : ∀ x y, DGPS.centeredKernel (modelData h ε) μ x y = ε * kernelK h x y)
    (f : centeredL2 μ) :
    inner ℝ f (DGPS.densityHessian (modelData h ε) μ f) = ‖f‖ ^ 2 +
      ε * (kAlpha * ((∫ x, featureC h x * (f : Lp ℝ 2 (μ : Measure (Torus 1))) x ∂(μ : Measure (Torus 1))) ^ 2
        + (∫ x, featureS h x * (f : Lp ℝ 2 (μ : Measure (Torus 1))) x ∂(μ : Measure (Torus 1))) ^ 2)
        - kBeta * (∫ x, featureB h x * (f : Lp ℝ 2 (μ : Measure (Torus 1))) x ∂(μ : Measure (Torus 1))) ^ 2) := by
  set φ : Torus 1 → ℝ := ((f : Lp ℝ 2 (μ : Measure (Torus 1))) : Torus 1 → ℝ) with hφ
  have hfi : Integrable φ (μ : Measure (Torus 1)) := DGPS.integrable_lp μ _
  have hI : ∀ g : Torus 1 → ℝ, Continuous g → Integrable (fun x => g x * φ x) (μ : Measure (Torus 1)) := by
    intro g hg
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact hfi.bdd_mul (c := C) hg.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa using hC x (Set.mem_univ _))
  have ic := hI _ (featureC_continuous h)
  have is := hI _ (featureS_continuous h)
  have ib := hI _ (featureB_continuous h)
  have h1 : inner ℝ f (DGPS.densityHessian (modelData h ε) μ f)
      = inner ℝ f f + inner ℝ f (DGPS.centeredInteraction (modelData h ε) μ f) := by
    rw [← inner_add_right]; rfl
  rw [h1, real_inner_self_eq_norm_sq]
  congr 1
  have h2 : inner ℝ f (DGPS.centeredInteraction (modelData h ε) μ f)
      = inner ℝ (f : Lp ℝ 2 (μ : Measure (Torus 1)))
        (DGPS.kernelOp (modelData h ε) μ (f : Lp ℝ 2 (μ : Measure (Torus 1)))) := rfl
  rw [h2, DGPS.inner_kernelOp]
  have e : ∀ p : Torus 1 × Torus 1, DGPS.centeredKernel (modelData h ε) μ p.1 p.2 * (φ p.1 * φ p.2)
      = (ε * kAlpha) * ((featureC h p.1 * φ p.1) * (featureC h p.2 * φ p.2))
        + (ε * kAlpha) * ((featureS h p.1 * φ p.1) * (featureS h p.2 * φ p.2))
        - (ε * kBeta) * ((featureB h p.1 * φ p.1) * (featureB h p.2 * φ p.2)) := by
    intro p; rw [hK]; unfold kernelK; ring
  refine (integral_congr_ae (ae_of_all _ e)).trans ?_
  have pc : Integrable (fun p : Torus 1 × Torus 1 => (ε * kAlpha) *
      ((featureC h p.1 * φ p.1) * (featureC h p.2 * φ p.2))) ((μ : Measure (Torus 1)).prod μ) :=
    (ic.mul_prod ic).const_mul _
  have ps : Integrable (fun p : Torus 1 × Torus 1 => (ε * kAlpha) *
      ((featureS h p.1 * φ p.1) * (featureS h p.2 * φ p.2))) ((μ : Measure (Torus 1)).prod μ) :=
    (is.mul_prod is).const_mul _
  have pb : Integrable (fun p : Torus 1 × Torus 1 => (ε * kBeta) *
      ((featureB h p.1 * φ p.1) * (featureB h p.2 * φ p.2))) ((μ : Measure (Torus 1)).prod μ) :=
    (ib.mul_prod ib).const_mul _
  have pcs : Integrable (fun p : Torus 1 × Torus 1 => (ε * kAlpha) *
      ((featureC h p.1 * φ p.1) * (featureC h p.2 * φ p.2)) + (ε * kAlpha) *
      ((featureS h p.1 * φ p.1) * (featureS h p.2 * φ p.2))) ((μ : Measure (Torus 1)).prod μ) :=
    pc.add ps
  rw [integral_sub pcs pb, integral_add pc ps, integral_const_mul, integral_const_mul,
    integral_const_mul,
    integral_prod_mul (fun x => featureC h x * φ x) (fun x => featureC h x * φ x),
    integral_prod_mul (fun x => featureS h x * φ x) (fun x => featureS h x * φ x),
    integral_prod_mul (fun x => featureB h x * φ x) (fun x => featureB h x * φ x)]
  ring

/-! ### Rank -/

theorem finrank_range_rankThree {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : Fin 3 → E) (he : LinearIndependent ℝ e) (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0)
    (T : E →ₗ[ℝ] E) (hT : ∀ f, T f = ∑ i, (a i * inner ℝ (e i) f) • e i) :
    Module.finrank ℝ (LinearMap.range T) = 3 := by
  set S : Submodule ℝ E := Submodule.span ℝ (Set.range e) with hS
  have hfS : Module.finrank ℝ S = 3 := by
    rw [hS, finrank_span_eq_card he]; simp
  have hle : LinearMap.range T ≤ S := by
    rintro _ ⟨f, rfl⟩
    rw [hT]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfin : Module.Finite ℝ S := Module.Finite.span_of_finite ℝ (Set.finite_range e)
  have hfinR : Module.Finite ℝ (LinearMap.range T) := Module.Finite.of_injective
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hinj : Function.Injective (T.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : T x = 0 := hx
    rw [hT] at hx'
    have hc := Fintype.linearIndependent_iff.mp he (fun i => a i * inner ℝ (e i) (x : E))
      (by simpa using hx')
    have h0 : ∀ i, inner ℝ (e i) (x : E) = 0 := fun i => by
      have := hc i
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ha i)
      · exact h
    have hperp : ∀ y ∈ S, inner ℝ y (x : E) = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz => obtain ⟨i, rfl⟩ := hz; exact h0 i
      | zero => simp
      | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
      | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]
    have := hperp x x.2
    have hx0 : (x : E) = 0 := inner_self_eq_zero.mp this
    exact Subtype.ext hx0
  have h1 : Module.finrank ℝ (LinearMap.range (T.domRestrict S)) = 3 := by
    rw [LinearMap.finrank_range_of_inj hinj, hfS]
  have h2 : LinearMap.range (T.domRestrict S) ≤ LinearMap.range T :=
    LinearMap.range_domRestrict_le_range T S
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_mono hle
  omega

/-- The `L²(μ)` class of a continuous function. -/
noncomputable def lpOf (μ : ProbabilityMeasure (Torus 1)) (g : Torus 1 → ℝ) (hg : Continuous g) :
    Lp ℝ 2 (μ : Measure (Torus 1)) :=
  BoundedContinuousFunction.toLp 2 (μ : Measure (Torus 1)) ℝ
    (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩)

theorem lpOf_ae (μ : ProbabilityMeasure (Torus 1)) (g : Torus 1 → ℝ) (hg : Continuous g) :
    (lpOf μ g hg : Torus 1 → ℝ) =ᵐ[(μ : Measure (Torus 1))] g := by
  have := BoundedContinuousFunction.coeFn_toLp 2 (μ : Measure (Torus 1)) ℝ
    (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩)
  exact this

theorem integrable_cont_mul_lp (μ : ProbabilityMeasure (Torus 1)) {g : Torus 1 → ℝ}
    (hg : Continuous g) (φ : Lp ℝ 2 (μ : Measure (Torus 1))) :
    Integrable (fun x => g x * φ x) (μ : Measure (Torus 1)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact (DGPS.integrable_lp μ φ).bdd_mul (c := C) hg.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa using hC x (Set.mem_univ _))

theorem inner_lpOf (μ : ProbabilityMeasure (Torus 1)) {g : Torus 1 → ℝ} (hg : Continuous g)
    (φ : Lp ℝ 2 (μ : Measure (Torus 1))) :
    inner ℝ (lpOf μ g hg) φ = ∫ x, g x * φ x ∂(μ : Measure (Torus 1)) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpOf_ae μ g hg] with y hy
  rw [hy]; simp [mul_comm]

/-- The three feature functions. -/
noncomputable def featVec (h : ℝ) : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]

theorem continuous_featVec (h : ℝ) (i : Fin 3) : Continuous (featVec h i) := by
  fin_cases i
  · exact featureC_continuous h
  · exact featureS_continuous h
  · exact featureB_continuous h

theorem kernelK_eq_sum (h : ℝ) (x y : Torus 1) :
    kernelK h x y = ∑ i, (![kAlpha, kAlpha, -kBeta] i * featVec h i x) * featVec h i y := by
  simp [Fin.sum_univ_three, featVec, kernelK]; ring

theorem rank_three_general {h ε : ℝ} (μ : ProbabilityMeasure (Torus 1)) (hε : ε ≠ 0)
    (hK : ∀ x y, DGPS.centeredKernel (modelData h ε) μ x y = ε * kernelK h x y)
    (hcen : ∀ i, ∫ x, featVec h i x ∂(μ : Measure (Torus 1)) = 0)
    (hind : ∀ a b c : ℝ, (∀ᵐ x ∂(μ : Measure (Torus 1)),
        a * featureC h x + b * featureS h x + c * featureB h x = 0) → a = 0 ∧ b = 0 ∧ c = 0) :
    Module.finrank ℝ (LinearMap.range
      (DGPS.centeredInteraction (modelData h ε) μ : DGPS.centeredL2 μ →ₗ[ℝ] DGPS.centeredL2 μ)) = 3 := by
  let u : Fin 3 → Lp ℝ 2 (μ : Measure (Torus 1)) := fun i => lpOf μ (featVec h i) (continuous_featVec h i)
  have hu : ∀ i, u i ∈ DGPS.centeredL2 μ := by
    intro i
    show ∫ x, (u i) x ∂(μ : Measure (Torus 1)) = 0
    rw [integral_congr_ae (lpOf_ae μ _ _)]
    exact hcen i
  let e : Fin 3 → DGPS.centeredL2 μ := fun i => ⟨u i, hu i⟩
  let a : Fin 3 → ℝ := fun i => ε * ![kAlpha, kAlpha, -kBeta] i
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    have := kAlpha_pos; have := kBeta_pos
    fin_cases i <;> simp [a] <;> exact ⟨hε, by positivity⟩
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∑ i, g i • u i = 0 := by
      have := congrArg (fun z : DGPS.centeredL2 μ => (z : Lp ℝ 2 (μ : Measure (Torus 1)))) hg
      simpa [e] using this
    have h2 : (∑ i, g i • u i : Lp ℝ 2 (μ : Measure (Torus 1))) =ᵐ[(μ : Measure (Torus 1))]
        fun x => g 0 * featureC h x + g 1 * featureS h x + g 2 * featureB h x := by
      rw [Fin.sum_univ_three]
      filter_upwards [Lp.coeFn_add (g 0 • u 0 + g 1 • u 1) (g 2 • u 2),
        Lp.coeFn_add (g 0 • u 0) (g 1 • u 1), Lp.coeFn_smul (g 0) (u 0),
        Lp.coeFn_smul (g 1) (u 1), Lp.coeFn_smul (g 2) (u 2),
        lpOf_ae μ _ (continuous_featVec h 0), lpOf_ae μ _ (continuous_featVec h 1),
        lpOf_ae μ _ (continuous_featVec h 2)] with x e1 e2 e3 e4 e5 f0 f1 f2
      rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, e4, e5]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [f0, f1, f2]
      rfl
    have h3 : ∀ᵐ x ∂(μ : Measure (Torus 1)),
        g 0 * featureC h x + g 1 * featureS h x + g 2 * featureB h x = 0 := by
      filter_upwards [h2, Lp.coeFn_zero ℝ 2 (μ : Measure (Torus 1))] with x hx hz
      rw [← hx, h1, hz]; rfl
    obtain ⟨g0, g1, g2⟩ := hind _ _ _ h3
    intro i; fin_cases i <;> assumption
  refine finrank_range_rankThree e hli a ha _ ?_
  intro f
  apply Subtype.ext
  apply Lp.ext
  set F : Lp ℝ 2 (μ : Measure (Torus 1)) := (f : Lp ℝ 2 (μ : Measure (Torus 1))) with hF
  have hLHS : ((DGPS.centeredInteraction (modelData h ε) μ f : DGPS.centeredL2 μ) :
      Lp ℝ 2 (μ : Measure (Torus 1))) =ᵐ[(μ : Measure (Torus 1))]
      DGPS.kernelTransform (modelData h ε) μ F := DGPS.kernelOp_ae _ μ F
  have hpt : ∀ x, DGPS.kernelTransform (modelData h ε) μ F x
      = ∑ i, (a i * ∫ y, featVec h i y * F y ∂(μ : Measure (Torus 1))) * featVec h i x := by
    intro x
    unfold DGPS.kernelTransform
    have e1 : ∀ y, DGPS.centeredKernel (modelData h ε) μ x y * F y
        = ∑ i, (a i * featVec h i x) * (featVec h i y * F y) := by
      intro y
      simp only [hK, kernelK_eq_sum, a, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [e1]
    rw [integral_finsetSum _ (fun i _ =>
      (integrable_cont_mul_lp μ (continuous_featVec h i) F).const_mul _)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring
  have hinner : ∀ i, inner ℝ (e i) f = ∫ y, featVec h i y * F y ∂(μ : Measure (Torus 1)) :=
    fun i => inner_lpOf μ (continuous_featVec h i) F
  refine hLHS.trans ?_
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add ((a 0 * inner ℝ (e 0) f) • u 0 + (a 1 * inner ℝ (e 1) f) • u 1)
      ((a 2 * inner ℝ (e 2) f) • u 2),
    Lp.coeFn_add ((a 0 * inner ℝ (e 0) f) • u 0) ((a 1 * inner ℝ (e 1) f) • u 1),
    Lp.coeFn_smul (a 0 * inner ℝ (e 0) f) (u 0), Lp.coeFn_smul (a 1 * inner ℝ (e 1) f) (u 1),
    Lp.coeFn_smul (a 2 * inner ℝ (e 2) f) (u 2),
    lpOf_ae μ _ (continuous_featVec h 0), lpOf_ae μ _ (continuous_featVec h 1),
    lpOf_ae μ _ (continuous_featVec h 2)] with x e1 e2 e3 e4 e5 f0 f1 f2
  rw [hpt, e1, Pi.add_apply, e2, Pi.add_apply, e3, e4, e5]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [f0, f1, f2, Fin.sum_univ_three, hinner 0, hinner 1, hinner 2]

theorem hessian_half {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h)
    (f : DGPS.centeredL2 (refProb hh)) :
    (1 / 2) * ‖f‖ ^ 2 ≤ inner ℝ f (DGPS.densityHessian (modelData h ε) (refProb hh) f) := by
  rw [hessian_form (refProb hh) (centeredKernel_model hh ε)]
  set φ : Lp ℝ 2 ((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) := f.1 with hφ
  have hab : |∫ x, featureB h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))|
      ≤ featureBBound h * ‖φ‖ :=
    DGPS.abs_integral_mul_le (refProb hh) (bBCF h) φ
  have hsq : (∫ x, featureB h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) ^ 2
      ≤ featureBBound h ^ 2 * ‖f‖ ^ 2 := by
    have h0 := abs_nonneg (∫ x, featureB h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
    have : ‖φ‖ = ‖f‖ := rfl
    rw [← sq_abs, ← mul_pow, ← this]
    exact pow_le_pow_left₀ h0 hab 2
  have hkey := eps_mul_le hεmax
  have hb := kBeta_pos
  have ha := kAlpha_pos
  have hsc := sq_nonneg (∫ x, featureC h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
  have hss := sq_nonneg (∫ x, featureS h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)))
  have hn := sq_nonneg ‖f‖
  have h1 : ε * kBeta * (∫ x, featureB h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) ^ 2
      ≤ 1 / 2 * ‖f‖ ^ 2 := by
    calc _ ≤ ε * kBeta * (featureBBound h ^ 2 * ‖f‖ ^ 2) := by gcongr
      _ = (ε * kBeta * featureBBound h ^ 2) * ‖f‖ ^ 2 := by ring
      _ ≤ 1 / 2 * ‖f‖ ^ 2 := by gcongr
  have h2 : 0 ≤ ε * (kAlpha * ((∫ x, featureC h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) ^ 2
      + (∫ x, featureS h x * φ x ∂((refProb hh : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))) ^ 2)) := by positivity
  nlinarith

theorem elementaryModel_gauge_and_rank {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) :
    IsSmoothPeriodic (modelV h ε) ∧
    ContDiff ℝ ∞ (fun p : CirclePair => modelW h ε (torusLift p.1) (torusLift p.2)) ∧
    (∀ x y, modelW h ε x y = modelW h ε y x) ∧ (∀ x, modelW h ε x x = 0) ∧
    (∀ x y, DGPS.centeredKernel (modelData h ε) (refProb hh) x y = ε * kernelK h x y) ∧
    Module.finrank ℝ (LinearMap.range (DGPS.centeredInteraction (modelData h ε) (refProb hh) :
      DGPS.centeredL2 (refProb hh) →ₗ[ℝ] DGPS.centeredL2 (refProb hh))) = 3 ∧
    (∀ f : DGPS.centeredL2 (refProb hh),
      (1 / 2) * ‖f‖ ^ 2 ≤ inner ℝ f (DGPS.densityHessian (modelData h ε) (refProb hh) f)) := by
  refine ⟨isSmoothPeriodic_modelV h ε, smooth_modelW h ε,
    (modelData h ε).W_symm, (modelData h ε).W_diag, centeredKernel_model hh ε, ?_,
    hessian_half hh hε hεmax⟩
  obtain ⟨hc, hs, hb, hind, -⟩ := elementaryFeatures_centered_independent hh
  refine rank_three_general (refProb hh) hε.ne' (centeredKernel_model hh ε) ?_ hind
  intro i; fin_cases i
  · exact hc
  · exact hs
  · exact hb


/-! ### Circle infrastructure -/

theorem circ_exists_pt (x : Torus 1) : ∃ t : ℝ, pt t = x := by
  refine ⟨SharpLSI.secT x 0, ?_⟩
  have h := SharpLSI.liftT_secT x
  have e : (fun _ : Fin 1 => SharpLSI.secT x 0) = SharpLSI.secT x := by
    funext i; fin_cases i; rfl
  show SharpLSI.liftT (fun _ : Fin 1 => SharpLSI.secT x 0) = x
  rw [e]; exact h

theorem circ_pt_one_add (t : ℝ) : pt (t + 1) = pt t := torusLift_one_add t

theorem circ_smooth_pt {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) :
    ContDiff ℝ ∞ (fun t : ℝ => f (pt t)) :=
  hf.comp (contDiff_pi.mpr fun _ => contDiff_id)

theorem circ_periodic_pt (f : Torus 1 → ℝ) : Function.Periodic (fun t : ℝ => f (pt t)) 1 := by
  intro t; simp only [circ_pt_one_add]

theorem circ_coordPartial_pt {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (pt s)) (coordPartial 0 f (pt t)) t :=
  hasDerivAt_smooth_one hf t

/-- Smooth periodic real functions descend to the circle. -/
theorem circ_exists_torus {G : ℝ → ℝ} (hs : ContDiff ℝ ∞ G) (hp : Function.Periodic G 1) :
    ∃ F : Torus 1 → ℝ, IsSmoothPeriodic F ∧ ∀ t, F (pt t) = G t := by
  refine ⟨fun x => hp.lift (x 0), ?_, fun t => ?_⟩
  · have : ((fun x : Torus 1 => hp.lift (x 0)) ∘ torusLift) = fun y : Fin 1 → ℝ => G (y 0) := by
      funext y
      show hp.lift ((y 0 : ℝ) : AddCircle (1:ℝ)) = G (y 0)
      exact Function.Periodic.lift_coe hp _
    unfold IsSmoothPeriodic
    rw [this]
    exact hs.comp (contDiff_apply ℝ ℝ 0)
  · show hp.lift ((t : ℝ) : AddCircle (1:ℝ)) = G t
    exact Function.Periodic.lift_coe hp _

/-- Mean zero smooth periodic functions have smooth periodic antiderivatives. -/
theorem circ_exists_antideriv {f : ℝ → ℝ} (hs : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (h0 : ∫ t in (0:ℝ)..1, f t = 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ Function.Periodic G 1 ∧ ∀ t, HasDerivAt G (f t) t := by
  have hc : Continuous f := hs.continuous
  refine ⟨fun u => ∫ x in (0:ℝ)..u, f x, ?_, ?_, fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt⟩
  · have hd : ∀ t, HasDerivAt (fun u => ∫ x in (0:ℝ)..u, f x) (f t) t :=
      fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt, ?_⟩
    have : deriv (fun u => ∫ x in (0:ℝ)..u, f x) = f := funext fun t => (hd t).deriv
    rw [this]; exact hs
  · intro t
    show ∫ x in (0:ℝ)..(t+1), f x = ∫ x in (0:ℝ)..t, f x
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := t)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h1 : ∫ x in t..(t+1), f x = ∫ x in (0:ℝ)..(0+1), f x := hp.intervalIntegral_add_eq t 0
    rw [h1, zero_add, h0, add_zero]

theorem circ_integral_exp_pos {u : ℝ → ℝ} (hu : Continuous u) :
    0 < ∫ t in (0:ℝ)..1, Real.exp (u t) := by
  apply intervalIntegral.intervalIntegral_pos_of_pos (hu.rexp.intervalIntegrable _ _)
    (fun t => Real.exp_pos _) zero_lt_one

/-- The Gibbs-weighted mean `λ` of `g`. -/
noncomputable def circLam (u g : ℝ → ℝ) : ℝ :=
  (∫ t in (0:ℝ)..1, Real.exp (-u t) * g t) / ∫ t in (0:ℝ)..1, Real.exp (-u t)

theorem circ_ode {u g : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hup : Function.Periodic u 1)
    (hg : ContDiff ℝ ∞ g) (hgp : Function.Periodic g 1) :
    ∃ ψ ψ' : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Function.Periodic ψ 1 ∧ (∀ t, HasDerivAt ψ (ψ' t) t) ∧
      (∀ t, HasDerivAt ψ' (deriv u t * ψ' t + (g t - circLam u g)) t) := by
  set lam := circLam u g with hlam
  have hu_c : Continuous u := hu.continuous
  have hne : 0 < ∫ t in (0:ℝ)..1, Real.exp (-u t) := by
    have := circ_integral_exp_pos (u := fun t => -u t) hu_c.neg
    exact this
  -- the flux density
  have hf_s : ContDiff ℝ ∞ (fun t => Real.exp (-u t) * (g t - lam)) :=
    (Real.contDiff_exp.comp hu.neg).mul (hg.sub contDiff_const)
  have hf_p : Function.Periodic (fun t => Real.exp (-u t) * (g t - lam)) 1 := by
    intro t; simp only [hup t, hgp t]
  have hf0 : ∫ t in (0:ℝ)..1, Real.exp (-u t) * (g t - lam) = 0 := by
    have i1 : IntervalIntegrable (fun t => Real.exp (-u t) * g t) MeasureTheory.volume 0 1 :=
      (hu_c.neg.rexp.mul hg.continuous).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => Real.exp (-u t) * lam) MeasureTheory.volume 0 1 :=
      (hu_c.neg.rexp.mul continuous_const).intervalIntegrable _ _
    have : (fun t => Real.exp (-u t) * (g t - lam))
        = fun t => Real.exp (-u t) * g t - Real.exp (-u t) * lam := by funext t; ring
    rw [this, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_mul_const]
    have : lam * ∫ t in (0:ℝ)..1, Real.exp (-u t) = ∫ t in (0:ℝ)..1, Real.exp (-u t) * g t := by
      rw [hlam]; unfold circLam; field_simp
    linarith
  obtain ⟨F, hF_s, hF_p, hF_d⟩ := circ_exists_antideriv hf_s hf_p hf0
  -- the derivative of the solution
  set EU : ℝ := ∫ t in (0:ℝ)..1, Real.exp (u t) with hEU
  have hEU_pos : 0 < EU := circ_integral_exp_pos hu_c
  set C : ℝ := -(∫ t in (0:ℝ)..1, Real.exp (u t) * F t) / EU with hC
  have hp_s : ContDiff ℝ ∞ (fun t => Real.exp (u t) * (F t + C)) :=
    (Real.contDiff_exp.comp hu).mul (hF_s.add contDiff_const)
  have hp_p : Function.Periodic (fun t => Real.exp (u t) * (F t + C)) 1 := by
    intro t; simp only [hup t, hF_p t]
  have hp0 : ∫ t in (0:ℝ)..1, Real.exp (u t) * (F t + C) = 0 := by
    have i1 : IntervalIntegrable (fun t => Real.exp (u t) * F t) MeasureTheory.volume 0 1 :=
      (hu_c.rexp.mul hF_s.continuous).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => Real.exp (u t) * C) MeasureTheory.volume 0 1 :=
      (hu_c.rexp.mul continuous_const).intervalIntegrable _ _
    have : (fun t => Real.exp (u t) * (F t + C))
        = fun t => Real.exp (u t) * F t + Real.exp (u t) * C := by funext t; ring
    rw [this, intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const]
    have : C * EU = -(∫ t in (0:ℝ)..1, Real.exp (u t) * F t) := by
      rw [hC]; field_simp
    linarith
  obtain ⟨ψ, hψ_s, hψ_p, hψ_d⟩ := circ_exists_antideriv hp_s hp_p hp0
  refine ⟨ψ, fun t => Real.exp (u t) * (F t + C), hψ_s, hψ_p, hψ_d, fun t => ?_⟩
  have hu_d : HasDerivAt u (deriv u t) t := (hu.differentiable (by simp) t).hasDerivAt
  have h1 : HasDerivAt (fun t => Real.exp (u t)) (Real.exp (u t) * deriv u t) t := hu_d.exp
  have h2 : HasDerivAt (fun t => F t + C) (Real.exp (-u t) * (g t - lam)) t := (hF_d t).add_const C
  have h3 := h1.mul h2
  convert h3 using 1
  have : Real.exp (u t) * Real.exp (-u t) = 1 := by rw [← Real.exp_add]; simp
  calc deriv u t * (Real.exp (u t) * (F t + C)) + (g t - lam)
      = Real.exp (u t) * deriv u t * (F t + C) + (Real.exp (u t) * Real.exp (-u t)) * (g t - lam) := by
        rw [this]; ring
    _ = _ := by ring

theorem circ_coordPartial_eq_deriv {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) (t : ℝ) :
    coordPartial 0 f (pt t) = deriv (fun s : ℝ => f (pt s)) t :=
  ((circ_coordPartial_pt hf t).deriv).symm

/-- Solvability of `φ'' - U' φ' = g - λ` on the circle. -/
theorem circ_test_exists {U g : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) (hg : IsSmoothPeriodic g) :
    ∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧ ∀ x : Torus 1,
      coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x
        = g x - circLam (fun t => U (pt t)) (fun t => g (pt t)) := by
  obtain ⟨ψ, ψ', hψ_s, hψ_p, hψ_d, hψ'_d⟩ := circ_ode (circ_smooth_pt hU) (circ_periodic_pt U)
    (circ_smooth_pt hg) (circ_periodic_pt g)
  obtain ⟨φ, hφ_s, hφ_pt⟩ := circ_exists_torus hψ_s hψ_p
  have hder : ∀ t, coordPartial 0 φ (pt t) = ψ' t := by
    intro t
    have h1 := circ_coordPartial_pt hφ_s t
    have h2 : (fun s : ℝ => φ (pt s)) = ψ := funext hφ_pt
    rw [h2] at h1
    exact h1.unique (hψ_d t)
  refine ⟨φ, hφ_s, fun x => ?_⟩
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have hφ1 : IsSmoothPeriodic (coordPartial 0 φ) := hφ_s.isSmoothPeriodic_coordPartial 0
  have h3 : (fun s : ℝ => coordPartial 0 φ (pt s)) = ψ' := funext hder
  have h4 := circ_coordPartial_pt hφ1 t
  rw [h3] at h4
  rw [h4.unique (hψ'_d t), hder t, circ_coordPartial_eq_deriv hU t]
  ring


/-! ### Symmetrized Pinsker for bounded positive densities -/

theorem circ_withDensity_integral {α : Type*} [MeasurableSpace α] (m : Measure α) {q : α → ℝ}
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (f : α → ℝ) :
    ∫ x, f x ∂(m.withDensity fun x => ENNReal.ofReal (q x)) = ∫ x, q x * f x ∂m := by
  rw [integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hq0 x)]

theorem circ_withDensity_integrable {α : Type*} [MeasurableSpace α] (m : Measure α) {q : α → ℝ}
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) {f : α → ℝ} :
    Integrable f (m.withDensity fun x => ENNReal.ofReal (q x)) ↔ Integrable (fun x => q x * f x) m := by
  rw [integrable_withDensity_iff_integrable_smul' hq.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hq0 x)]

theorem circ_isProb_withDensity {α : Type*} [MeasurableSpace α] (m : Measure α)
    [IsProbabilityMeasure m] {q : α → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hqi : Integrable q m) (hq1 : ∫ x, q x ∂m = 1) :
    IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (q x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hqi (Filter.Eventually.of_forall hq0), hq1]
  simp

theorem circ_log_bound {a b : ℝ} (ha : 0 < a) {x : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have h1 : Real.log a ≤ Real.log x := Real.log_le_log ha hx.1
  have h2 : Real.log x ≤ Real.log b := Real.log_le_log hx0 hx.2
  have := le_abs_self (Real.log a); have := neg_abs_le (Real.log a)
  have := le_abs_self (Real.log b); have := neg_abs_le (Real.log b)
  rw [abs_le]; constructor <;> linarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem circ_bdd_integrable {α : Type*} [MeasurableSpace α] (m : Measure α) [IsFiniteMeasure m]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

theorem circ_pinsker_one {α : Type*} [MeasurableSpace α] (m : Measure α) [IsProbabilityMeasure m]
    {ρ q : α → ℝ} (hρm : Measurable ρ) (hqm : Measurable q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hρ : ∀ x, a ≤ ρ x ∧ ρ x ≤ b) (hq : ∀ x, a ≤ q x ∧ q x ≤ b)
    (hρ1 : ∫ x, ρ x ∂m = 1) (hq1 : ∫ x, q x ∂m = 1) :
    (∫ x, |ρ x - q x| ∂m) ^ 2 ≤ 2 * ∫ x, ρ x * (Real.log (ρ x) - Real.log (q x)) ∂m := by
  have hρ0 : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le ha (hρ x).1
  have hq0 : ∀ x, 0 < q x := fun x => lt_of_lt_of_le ha (hq x).1
  set M : ℝ := |Real.log a| + |Real.log b| with hM
  have hM0 : 0 ≤ M := by positivity
  have hρabs : ∀ x, |ρ x| ≤ b := fun x => by rw [abs_of_pos (hρ0 x)]; exact (hρ x).2
  have hqabs : ∀ x, |q x| ≤ b := fun x => by rw [abs_of_pos (hq0 x)]; exact (hq x).2
  have hρi : Integrable ρ m := circ_bdd_integrable m hρm hρabs
  have hqi : Integrable q m := circ_bdd_integrable m hqm hqabs
  have hlρ : ∀ x, |Real.log (ρ x)| ≤ M := fun x => circ_log_bound ha (hρ x)
  have hlq : ∀ x, |Real.log (q x)| ≤ M := fun x => circ_log_bound ha (hq x)
  have hlρm : Measurable fun x => Real.log (ρ x) := Real.measurable_log.comp hρm
  have hlqm : Measurable fun x => Real.log (q x) := Real.measurable_log.comp hqm
  have i1 : Integrable (fun x => ρ x * Real.log (ρ x)) m := by
    refine circ_bdd_integrable m (hρm.mul hlρm) (C := b * M) fun x => ?_
    rw [abs_mul]; exact mul_le_mul (hρabs x) (hlρ x) (abs_nonneg _) hb.le
  have i2 : Integrable (fun x => ρ x * Real.log (q x)) m := by
    refine circ_bdd_integrable m (hρm.mul hlqm) (C := b * M) fun x => ?_
    rw [abs_mul]; exact mul_le_mul (hρabs x) (hlq x) (abs_nonneg _) hb.le
  have hP : IsProbabilityMeasure (m.withDensity fun x => ENNReal.ofReal (q x)) :=
    circ_isProb_withDensity m (fun x => (hq0 x).le) hqi hq1
  set P := m.withDensity fun x => ENNReal.ofReal (q x) with hPdef
  set v : α → ℝ := fun x => ρ x / q x with hv
  have hvm : Measurable v := hρm.div hqm
  have hqv : ∀ x, q x * v x = ρ x := fun x => by
    simp only [hv]; field_simp [(hq0 x).ne']
  have hv0 : ∀ x, 0 ≤ v x := fun x => (div_pos (hρ0 x) (hq0 x)).le
  have hvi : Integrable v P := by
    rw [circ_withDensity_integrable m hqm (fun x => (hq0 x).le)]
    simpa only [hqv] using hρi
  have hv1 : ∫ x, v x ∂P = 1 := by
    rw [hPdef, circ_withDensity_integral m hqm (fun x => (hq0 x).le)]
    simp only [hqv]; exact hρ1
  have hkey : ∀ x, q x * (v x * Real.log (v x) - v x + 1)
      = ρ x * Real.log (ρ x) - ρ x * Real.log (q x) - ρ x + q x := fun x => by
    have hlog : Real.log (v x) = Real.log (ρ x) - Real.log (q x) :=
      Real.log_div (hρ0 x).ne' (hq0 x).ne'
    rw [hlog]
    have := hqv x
    calc q x * (v x * (Real.log (ρ x) - Real.log (q x)) - v x + 1)
        = (q x * v x) * (Real.log (ρ x) - Real.log (q x)) - q x * v x + q x := by ring
      _ = _ := by rw [this]; ring
  have hki : Integrable (fun x => v x * Real.log (v x) - v x + 1) P := by
    rw [circ_withDensity_integrable m hqm (fun x => (hq0 x).le)]
    simp only [hkey]
    exact ((i1.sub i2).sub hρi).add hqi
  have hpins := sq_integral_abs_sub_one_le (P := P) hv0 hvi hv1 hki
  have e1 : ∫ x, |v x - 1| ∂P = ∫ x, |ρ x - q x| ∂m := by
    rw [hPdef, circ_withDensity_integral m hqm (fun x => (hq0 x).le)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : q x * |v x - 1| = |q x * (v x - 1)| := by
      rw [abs_mul, abs_of_pos (hq0 x)]
    simp only [this]
    congr 1
    have := hqv x
    linarith [mul_sub (q x) (v x) 1]
  have e2 : ∫ x, (v x * Real.log (v x) - v x + 1) ∂P
      = ∫ x, ρ x * (Real.log (ρ x) - Real.log (q x)) ∂m := by
    rw [hPdef, circ_withDensity_integral m hqm (fun x => (hq0 x).le)]
    simp only [hkey]
    have : ∫ x, (ρ x * Real.log (ρ x) - ρ x * Real.log (q x) - ρ x + q x) ∂m
        = (∫ x, ρ x * Real.log (ρ x) ∂m - ∫ x, ρ x * Real.log (q x) ∂m) - ∫ x, ρ x ∂m
          + ∫ x, q x ∂m := by
      have j1 : Integrable (fun x => ρ x * Real.log (ρ x) - ρ x * Real.log (q x)) m := i1.sub i2
      have j2 : Integrable
          (fun x => ρ x * Real.log (ρ x) - ρ x * Real.log (q x) - ρ x) m := j1.sub hρi
      rw [integral_add j2 hqi, integral_sub j1 hρi, integral_sub i1 i2]
    rw [this, hρ1, hq1, ← integral_sub i1 i2]
    simp only [mul_sub]; ring
  rw [e1, e2] at hpins
  exact hpins

theorem circ_sym_pinsker {α : Type*} [MeasurableSpace α] (m : Measure α) [IsProbabilityMeasure m]
    {ρ q : α → ℝ} (hρm : Measurable ρ) (hqm : Measurable q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hρ : ∀ x, a ≤ ρ x ∧ ρ x ≤ b) (hq : ∀ x, a ≤ q x ∧ q x ≤ b)
    (hρ1 : ∫ x, ρ x ∂m = 1) (hq1 : ∫ x, q x ∂m = 1) :
    (∫ x, |ρ x - q x| ∂m) ^ 2 ≤ ∫ x, (ρ x - q x) * (Real.log (ρ x) - Real.log (q x)) ∂m := by
  have p1 := circ_pinsker_one m hρm hqm ha hb hρ hq hρ1 hq1
  have p2 := circ_pinsker_one m hqm hρm ha hb hq hρ hq1 hρ1
  have habs : (fun x => |q x - ρ x|) = fun x => |ρ x - q x| := funext fun x => abs_sub_comm _ _
  rw [habs] at p2
  set M : ℝ := |Real.log a| + |Real.log b| with hM
  have hM0 : 0 ≤ M := by positivity
  have hlρm : Measurable fun x => Real.log (ρ x) := Real.measurable_log.comp hρm
  have hlqm : Measurable fun x => Real.log (q x) := Real.measurable_log.comp hqm
  have hρ0 : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le ha (hρ x).1
  have hq0 : ∀ x, 0 < q x := fun x => lt_of_lt_of_le ha (hq x).1
  have hdiff : ∀ x, |Real.log (ρ x) - Real.log (q x)| ≤ 2 * M := fun x => by
    have h1 := circ_log_bound ha (hρ x); have h2 := circ_log_bound ha (hq x)
    calc _ ≤ |Real.log (ρ x)| + |Real.log (q x)| := abs_sub _ _
      _ ≤ 2 * M := by rw [hM] at *; linarith
  have j1 : Integrable (fun x => ρ x * (Real.log (ρ x) - Real.log (q x))) m := by
    refine circ_bdd_integrable m (hρm.mul (hlρm.sub hlqm)) (C := b * (2 * M)) fun x => ?_
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_of_pos (hρ0 x)]; exact (hρ x).2) (hdiff x) (abs_nonneg _) hb.le
  have j2 : Integrable (fun x => q x * (Real.log (q x) - Real.log (ρ x))) m := by
    refine circ_bdd_integrable m (hqm.mul (hlqm.sub hlρm)) (C := b * (2 * M)) fun x => ?_
    rw [abs_mul]
    have := hdiff x
    rw [abs_sub_comm] at this
    exact mul_le_mul (by rw [abs_of_pos (hq0 x)]; exact (hq x).2) this (abs_nonneg _) hb.le
  have hsum : ∫ x, (ρ x - q x) * (Real.log (ρ x) - Real.log (q x)) ∂m
      = ∫ x, ρ x * (Real.log (ρ x) - Real.log (q x)) ∂m
        + ∫ x, q x * (Real.log (q x) - Real.log (ρ x)) ∂m := by
    rw [← integral_add j1 j2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hsum]; linarith

/-! ### Measures on the circle are determined by smooth periodic tests -/

theorem circ_smooth_cosHarm (k : ℕ) : IsSmoothPeriodic (cosHarm k) := by
  unfold IsSmoothPeriodic
  have : (cosHarm k ∘ torusLift) = fun y : Fin 1 → ℝ => Real.cos (2 * Real.pi * (k:ℝ) * y 0) := by
    funext y; simp only [Function.comp, cosHarm_lift]
  rw [this]
  fun_prop

/-- Bounded continuous functions on the circle that are smooth periodic. -/
def circSmoothSubalg : StarSubalgebra ℝ (Torus 1 →ᵇ ℝ) where
  carrier := {g | IsSmoothPeriodic (g : Torus 1 → ℝ)}
  mul_mem' := fun {a b} ha hb => by
    change ContDiff ℝ ∞ (((a * b : Torus 1 →ᵇ ℝ) : Torus 1 → ℝ) ∘ torusLift)
    exact ContDiff.mul ha hb
  add_mem' := fun {a b} ha hb => by
    change ContDiff ℝ ∞ (((a + b : Torus 1 →ᵇ ℝ) : Torus 1 → ℝ) ∘ torusLift)
    exact ContDiff.add ha hb
  algebraMap_mem' := fun r => by
    change ContDiff ℝ ∞ (((algebraMap ℝ (Torus 1 →ᵇ ℝ) r : Torus 1 →ᵇ ℝ) : Torus 1 → ℝ) ∘ torusLift)
    exact contDiff_const
  star_mem' := fun {a} ha => by simpa using ha

theorem circ_point_sep {x y : Torus 1} (hxy : x ≠ y) : cosHarm 1 x ≠ cosHarm 1 y ∨ sinHarm 1 x ≠ sinHarm 1 y := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  apply hxy
  have h1 : fourier (1 : ℤ) (x 0) = fourier (1 : ℤ) (y 0) := by
    apply Complex.ext
    · exact hcon.1
    · exact hcon.2
  have h2 : x 0 = y 0 := by
    have hfo : (fourier (1 : ℤ) : AddCircle (1:ℝ) → ℂ) = fun z => (AddCircle.toCircle z : ℂ) := by
      funext z; exact fourier_one
    rw [hfo] at h1
    exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h1)
  funext i; fin_cases i; exact h2

theorem circ_smooth_sinHarm (k : ℕ) : IsSmoothPeriodic (sinHarm k) := by
  unfold IsSmoothPeriodic
  have : (sinHarm k ∘ torusLift) = fun y : Fin 1 → ℝ => Real.sin (2 * Real.pi * (k:ℝ) * y 0) := by
    funext y; simp only [Function.comp, sinHarm_lift]
  rw [this]
  fun_prop

theorem circ_measure_ext {P P' : Measure (Torus 1)} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ g : Torus 1 → ℝ, IsSmoothPeriodic g → ∫ x, g x ∂P = ∫ x, g x ∂P') : P = P' := by
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (𝕜 := ℝ) (A := circSmoothSubalg) ?_ ?_
  · intro x y hxy
    rcases circ_point_sep hxy with hc | hs
    · refine ⟨_, ⟨_, ⟨BoundedContinuousFunction.mkOfCompact ⟨cosHarm 1, continuous_cosHarm 1⟩, ?_, rfl⟩, rfl⟩, hc⟩
      exact circ_smooth_cosHarm 1
    · refine ⟨_, ⟨_, ⟨BoundedContinuousFunction.mkOfCompact ⟨sinHarm 1, continuous_sinHarm 1⟩, ?_, rfl⟩, rfl⟩, hs⟩
      exact circ_smooth_sinHarm 1
  · intro g hg
    exact h _ hg


/-! ### Gibbs measures on the circle -/

/-- Normalising constant of the Gibbs density `exp(-U)`. -/
noncomputable def gibbsZ (U : Torus 1 → ℝ) : ℝ := ∫ x, Real.exp (-U x) ∂haar 1

/-- The Gibbs density `exp(-U)/Z`. -/
noncomputable def gibbsDensity (U : Torus 1 → ℝ) (x : Torus 1) : ℝ := Real.exp (-U x) / gibbsZ U

/-- The Gibbs probability `exp(-U)/Z · m`. -/
noncomputable def gibbsMeasure (U : Torus 1 → ℝ) : Measure (Torus 1) :=
  (haar 1).withDensity fun x => ENNReal.ofReal (gibbsDensity U x)

theorem gibbsZ_pos {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) : 0 < gibbsZ U := by
  unfold gibbsZ
  have hc : Continuous fun x => Real.exp (-U x) := hU.continuous_torus.neg.rexp
  rw [DGPS.Examples.ThreeSpeciesCircle.integral_haar_one _ hc]
  exact circ_integral_exp_pos (u := fun t => -U (pt t)) (circ_smooth_pt hU).continuous.neg

theorem continuous_gibbsDensity {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) :
    Continuous (gibbsDensity U) :=
  (hU.continuous_torus.neg.rexp).div_const _

theorem gibbsDensity_pos {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) (x : Torus 1) :
    0 < gibbsDensity U x := div_pos (Real.exp_pos _) (gibbsZ_pos hU)

theorem integral_gibbsDensity {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) :
    ∫ x, gibbsDensity U x ∂haar 1 = 1 := by
  have hZ := gibbsZ_pos hU
  unfold gibbsDensity
  rw [integral_div]
  exact div_self hZ.ne'

instance gibbsMeasure_isProb {U : Torus 1 → ℝ} [Fact (IsSmoothPeriodic U)] :
    IsProbabilityMeasure (gibbsMeasure U) := by
  have hU : IsSmoothPeriodic U := Fact.out
  exact circ_isProb_withDensity (haar 1) (fun x => (gibbsDensity_pos hU x).le)
    ((continuous_gibbsDensity hU).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integral_gibbsDensity hU)

theorem gibbsDensity_bounds {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a ≤ gibbsDensity U x ∧ gibbsDensity U x ≤ b := by
  have hc := continuous_gibbsDensity hU
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  obtain ⟨x1, -, hx1⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  exact ⟨gibbsDensity U x0, gibbsDensity U x1, gibbsDensity_pos hU x0, gibbsDensity_pos hU x1,
    fun x => ⟨hx0 (Set.mem_univ x), hx1 (Set.mem_univ x)⟩⟩

theorem integral_gibbs {U g : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) (hg : Continuous g) :
    ∫ x, g x ∂gibbsMeasure U = circLam (fun t => U (pt t)) (fun t => g (pt t)) := by
  have hZ := gibbsZ_pos hU
  unfold gibbsMeasure
  rw [circ_withDensity_integral (haar 1) (continuous_gibbsDensity hU).measurable
    (fun x => (gibbsDensity_pos hU x).le)]
  have e : ∀ x, gibbsDensity U x * g x = (gibbsZ U)⁻¹ * (Real.exp (-U x) * g x) := by
    intro x; unfold gibbsDensity; field_simp
  simp_rw [e]
  rw [integral_const_mul]
  have hc : Continuous fun x => Real.exp (-U x) * g x := hU.continuous_torus.neg.rexp.mul hg
  rw [DGPS.Examples.ThreeSpeciesCircle.integral_haar_one _ hc]
  have hz : gibbsZ U = ∫ t in (0:ℝ)..1, Real.exp (-U (pt t)) :=
    DGPS.Examples.ThreeSpeciesCircle.integral_haar_one _ hU.continuous_torus.neg.rexp
  rw [hz, inv_mul_eq_div]
  rfl

/-- A probability measure that is stationary for the generator `φ'' - U' φ'` is the Gibbs measure. -/
theorem eq_gibbs_of_stationary {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U)
    {ν : Measure (Torus 1)} [IsProbabilityMeasure ν]
    (hs : ∀ φ : Torus 1 → ℝ, IsSmoothPeriodic φ →
      ∫ x, (coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x) ∂ν = 0) :
    ν = gibbsMeasure U := by
  have : Fact (IsSmoothPeriodic U) := ⟨hU⟩
  refine circ_measure_ext fun g hg => ?_
  obtain ⟨φ, hφ, hφe⟩ := circ_test_exists hU hg
  have h0 := hs φ hφ
  have e : (fun x => coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x)
      = fun x => g x - circLam (fun t => U (pt t)) (fun t => g (pt t)) := funext hφe
  rw [e] at h0
  have hi : Integrable g ν := hg.continuous_torus.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hi (integrable_const _), integral_const] at h0
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h0
  rw [integral_gibbs hU hg.continuous_torus]
  linarith

theorem gibbs_stationary {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) {φ : Torus 1 → ℝ}
    (hφ : IsSmoothPeriodic φ) :
    ∫ x, (coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x)
      ∂gibbsMeasure U = 0 := by
  have hZ := gibbsZ_pos hU
  have hφ1 : IsSmoothPeriodic (coordPartial 0 φ) := hφ.isSmoothPeriodic_coordPartial 0
  have hφ2 : IsSmoothPeriodic (coordPartial 0 (coordPartial 0 φ)) :=
    hφ1.isSmoothPeriodic_coordPartial 0
  have hU1 : IsSmoothPeriodic (coordPartial 0 U) := hU.isSmoothPeriodic_coordPartial 0
  unfold gibbsMeasure
  rw [circ_withDensity_integral (haar 1) (continuous_gibbsDensity hU).measurable
    (fun x => (gibbsDensity_pos hU x).le)]
  obtain ⟨F, hF⟩ : ∃ F : Torus 1 → ℝ, F = fun x =>
      coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x := ⟨_, rfl⟩
  have hFx : ∀ x, coordPartial 0 (coordPartial 0 φ) x - coordPartial 0 U x * coordPartial 0 φ x
      = F x := fun x => by rw [hF]
  simp_rw [hFx]
  have e : ∀ x, gibbsDensity U x * F x = (gibbsZ U)⁻¹ * (Real.exp (-U x) * F x) := by
    intro x; unfold gibbsDensity; field_simp
  simp_rw [e]
  rw [integral_const_mul]
  have hFs : IsSmoothPeriodic F := by rw [hF]; exact hφ2.sub' (hU1.mul hφ1)
  have hFc : Continuous F := hFs.continuous_torus
  have hc : Continuous fun x => Real.exp (-U x) * F x := hU.continuous_torus.neg.rexp.mul hFc
  rw [DGPS.Examples.ThreeSpeciesCircle.integral_haar_one _ hc]
  have hd : ∀ t, HasDerivAt (fun s => Real.exp (-U (pt s)) * coordPartial 0 φ (pt s))
      (Real.exp (-U (pt t)) * F (pt t)) t := by
    intro t
    have h1 := ((circ_coordPartial_pt hU t).neg).exp
    have h2 := circ_coordPartial_pt hφ1 t
    have h3 := h1.mul h2
    convert h3 using 1
    rw [hF]; simp only [Pi.neg_apply]; ring
  have hcont : Continuous fun t : ℝ => Real.exp (-U (pt t)) * F (pt t) :=
    (circ_smooth_pt hU).continuous.neg.rexp.mul (circ_smooth_pt hFs).continuous
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  have h10 : pt 1 = pt 0 := by simpa using circ_pt_one_add 0
  simp only [h10, sub_self, mul_zero]

/-! ### Stationarity and the drift potential -/

/-- Distributional stationarity on the circle (local version of the interface predicate
`IsDistributionalStationary`): for every smooth periodic `φ`,
`∫ [φ'' - (V' + ∫ ∂₁W(·,y) dν(y)) φ'] dν = 0`. -/
def IsCircleDistributionalStationary (A : DGPS.InteractionData 1)
    (ν : ProbabilityMeasure (Torus 1)) : Prop :=
  ∀ φ : Torus 1 → ℝ, IsSmoothPeriodic φ →
    ∫ x, (coordPartial 0 (coordPartial 0 φ) x -
      (coordPartial 0 A.V x + ∫ y, coordPartial 0 (fun x' => A.W x' y) x ∂(ν : Measure (Torus 1))) *
        coordPartial 0 φ x) ∂(ν : Measure (Torus 1)) = 0

theorem isSmooth_featureC (h : ℝ) : IsSmoothPeriodic (featureC h) := smooth_featureC h
theorem isSmooth_featureS (h : ℝ) : IsSmoothPeriodic (featureS h) := smooth_featureS h
theorem isSmooth_featureB (h : ℝ) : IsSmoothPeriodic (featureB h) := smooth_featureB h
theorem isSmooth_cos3 : IsSmoothPeriodic (cosHarm 3) := circ_smooth_cosHarm 3

/-- First moments of a measure against the three features. -/
noncomputable def momC (h : ℝ) (ν : Measure (Torus 1)) : ℝ := ∫ y, featureC h y ∂ν
noncomputable def momS (h : ℝ) (ν : Measure (Torus 1)) : ℝ := ∫ y, featureS h y ∂ν
noncomputable def momB (h : ℝ) (ν : Measure (Torus 1)) : ℝ := ∫ y, featureB h y ∂ν

/-- The mean-field potential `U_ν = -h cos 6πx + ε(α(c̄ c + s̄ s) - β b̄ b)`. -/
noncomputable def driftPot (h ε : ℝ) (ν : Measure (Torus 1)) (x : Torus 1) : ℝ :=
  -h * cosHarm 3 x + ε * (kAlpha * (momC h ν * featureC h x + momS h ν * featureS h x)
    - kBeta * (momB h ν * featureB h x))

theorem isSmooth_driftPot (h ε : ℝ) (ν : Measure (Torus 1)) : IsSmoothPeriodic (driftPot h ε ν) := by
  have hc := smooth_featureC h
  have hs := smooth_featureS h
  have hb := smooth_featureB h
  have h3 := circ_smooth_cosHarm 3
  unfold IsSmoothPeriodic driftPot
  exact (contDiff_const.mul h3).add (contDiff_const.mul
    ((contDiff_const.mul ((contDiff_const.mul hc).add (contDiff_const.mul hs))).sub
      (contDiff_const.mul (contDiff_const.mul hb))))

theorem integral_affine3 {h : ℝ} (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (a1 a2 a3 e : ℝ) :
    ∫ y, (a1 * featureC h y + a2 * featureS h y + a3 * featureB h y + e) ∂ν
      = a1 * momC h ν + a2 * momS h ν + a3 * momB h ν + e := by
  have ic : Integrable (featureC h) ν := (featureC_continuous h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have is : Integrable (featureS h) ν := (featureS_continuous h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have ib : Integrable (featureB h) ν := (featureB_continuous h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have i1 : Integrable (fun y => a1 * featureC h y) ν := ic.const_mul _
  have i2 : Integrable (fun y => a2 * featureS h y) ν := is.const_mul _
  have i3 : Integrable (fun y => a3 * featureB h y) ν := ib.const_mul _
  have i12 : Integrable (fun y => a1 * featureC h y + a2 * featureS h y) ν := i1.add i2
  have i123 : Integrable (fun y => a1 * featureC h y + a2 * featureS h y + a3 * featureB h y) ν :=
    i12.add i3
  rw [integral_add i123 (integrable_const _), integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
  simp [momC, momS, momB]

theorem isSmooth_modelW_left (h ε : ℝ) (y : Torus 1) :
    IsSmoothPeriodic (fun x => modelW h ε x y) := by
  have hc := smooth_featureC h
  have hs := smooth_featureS h
  have hb := smooth_featureB h
  have hd := smooth_kernelK_diag h
  unfold kernelK at hd
  unfold IsSmoothPeriodic modelW kernelK
  exact contDiff_const.mul (((contDiff_const.mul ((hc.mul contDiff_const).add (hs.mul contDiff_const))).sub
    (contDiff_const.mul (hb.mul contDiff_const))).sub ((hd.add contDiff_const).div_const 2))

theorem isSmooth_modelV (h ε : ℝ) : IsSmoothPeriodic (modelV h ε) := isSmoothPeriodic_modelV h ε

/-- The mean-field drift is the derivative of `U_ν`. -/
theorem drift_eq {h ε : ℝ} (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (x : Torus 1) :
    coordPartial 0 (modelData h ε).V x
      + ∫ y, coordPartial 0 (fun x' => (modelData h ε).W x' y) x ∂ν
      = coordPartial 0 (driftPot h ε ν) x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  set c := featureC h (pt t) with hcdef
  set s := featureS h (pt t) with hsdef
  set b := featureB h (pt t) with hbdef
  set Dc := coordPartial 0 (featureC h) (pt t) with hDc
  set Ds := coordPartial 0 (featureS h) (pt t) with hDs
  set Db := coordPartial 0 (featureB h) (pt t) with hDb
  set D3 := coordPartial 0 (cosHarm 3) (pt t) with hD3
  have hc := circ_coordPartial_pt (isSmooth_featureC h) t
  have hs := circ_coordPartial_pt (isSmooth_featureS h) t
  have hb := circ_coordPartial_pt (isSmooth_featureB h) t
  have h3 := circ_coordPartial_pt isSmooth_cos3 t
  -- derivative of V
  have hV : HasDerivAt (fun r => modelV h ε (pt r))
      (-h * D3 + ε / 2 * (kAlpha * (c * Dc + Dc * c + (s * Ds + Ds * s)) - kBeta * (b * Db + Db * b))) t := by
    have := (h3.const_mul (-h)).add
      ((((hc.mul hc).add (hs.mul hs)).const_mul kAlpha).sub ((hb.mul hb).const_mul kBeta) |>.const_mul (ε / 2))
    convert this using 1
    · funext r; simp [modelV, kernelK]
    · simp only [hcdef, hsdef, hbdef, hDc, hDs, hDb]; ring
  have hV' := (circ_coordPartial_pt (isSmooth_modelV h ε) t).unique hV
  -- derivative of W in the first variable
  have hW : ∀ y : Torus 1, coordPartial 0 (fun x' => modelW h ε x' y) (pt t)
      = kAlpha * ε * Dc * featureC h y + kAlpha * ε * Ds * featureS h y
        + (-(kBeta * ε * Db)) * featureB h y
        + (-(ε / 2) * (kAlpha * (c * Dc + Dc * c + (s * Ds + Ds * s)) - kBeta * (b * Db + Db * b))) := by
    intro y
    have hA := (((hc.mul_const (featureC h y)).add (hs.mul_const (featureS h y))).const_mul kAlpha).sub
      ((hb.mul_const (featureB h y)).const_mul kBeta)
    have hB := ((((hc.mul hc).add (hs.mul hs)).const_mul kAlpha).sub
      ((hb.mul hb).const_mul kBeta)).add_const (kernelK h y y)
    have := (hA.sub (hB.div_const 2)).const_mul ε
    have hd : HasDerivAt (fun r => modelW h ε (pt r) y)
        (ε * ((kAlpha * (Dc * featureC h y + Ds * featureS h y) - kBeta * (Db * featureB h y))
          - (kAlpha * (c * Dc + Dc * c + (s * Ds + Ds * s)) - kBeta * (b * Db + Db * b)) / 2)) t := by
      convert this using 1
      · funext r; simp only [modelW, kernelK, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
      · simp only [hcdef, hsdef, hbdef, hDc, hDs, hDb]; ring
    rw [(circ_coordPartial_pt (isSmooth_modelW_left h ε y) t).unique hd]
    ring
  have hint : ∫ y, coordPartial 0 (fun x' => (modelData h ε).W x' y) (pt t) ∂ν
      = kAlpha * ε * Dc * momC h ν + kAlpha * ε * Ds * momS h ν + (-(kBeta * ε * Db)) * momB h ν
        + (-(ε / 2) * (kAlpha * (c * Dc + Dc * c + (s * Ds + Ds * s)) - kBeta * (b * Db + Db * b))) := by
    simp_rw [modelData_W, hW]
    exact integral_affine3 ν _ _ _ _
  have hU : HasDerivAt (fun r => driftPot h ε ν (pt r))
      (-h * D3 + ε * (kAlpha * (momC h ν * Dc + momS h ν * Ds) - kBeta * (momB h ν * Db))) t := by
    have := (h3.const_mul (-h)).add
      ((((hc.const_mul (momC h ν)).add (hs.const_mul (momS h ν))).const_mul kAlpha).sub
        ((hb.const_mul (momB h ν)).const_mul kBeta) |>.const_mul ε)
    convert this using 1
    funext r; simp only [driftPot, Pi.add_apply, Pi.sub_apply]
  have hU' := (circ_coordPartial_pt (isSmooth_driftPot h ε ν) t).unique hU
  rw [modelData_V, hV', hint, hU']
  ring

theorem stationary_iff_gibbs (h ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    IsCircleDistributionalStationary (modelData h ε) ν
      ↔ (ν : Measure (Torus 1)) = gibbsMeasure (driftPot h ε (ν : Measure (Torus 1))) := by
  have hsm := isSmooth_driftPot h ε (ν : Measure (Torus 1))
  have key : ∀ φ : Torus 1 → ℝ,
      ∫ x, (coordPartial 0 (coordPartial 0 φ) x -
      (coordPartial 0 (modelData h ε).V x + ∫ y, coordPartial 0 (fun x' => (modelData h ε).W x' y) x
        ∂(ν : Measure (Torus 1))) * coordPartial 0 φ x) ∂(ν : Measure (Torus 1))
      = ∫ x, (coordPartial 0 (coordPartial 0 φ) x
        - coordPartial 0 (driftPot h ε (ν : Measure (Torus 1))) x * coordPartial 0 φ x)
          ∂(ν : Measure (Torus 1)) := by
    intro φ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [drift_eq (h := h) (ε := ε) (ν : Measure (Torus 1)) x]
  constructor
  · intro hs
    exact eq_gibbs_of_stationary hsm fun φ hφ => by rw [← key]; exact hs φ hφ
  · intro heq φ hφ
    rw [key]
    have := gibbs_stationary hsm hφ
    rwa [← heq] at this

/-! ### The reference measure is a Gibbs measure -/

theorem refPot_smooth (h : ℝ) : IsSmoothPeriodic (fun x : Torus 1 => -h * cosHarm 3 x) := by
  have h3 := circ_smooth_cosHarm 3
  unfold IsSmoothPeriodic
  exact contDiff_const.mul h3

theorem gibbsZ_ref {h : ℝ} (hh : 0 < h) :
    gibbsZ (fun x : Torus 1 => -h * cosHarm 3 x) = besselI 0 h := by
  obtain ⟨hI0, -, -, h1, -⟩ := threefoldReference_integral_properties hh
  have hq : ∫ x, referenceDensity h x ∂haar 1
      = (∫ x, Real.exp (h * cosHarm 3 x) ∂haar 1) / besselI 0 h := by
    unfold referenceDensity; rw [integral_div]
  rw [hq, div_eq_one_iff_eq hI0.ne'] at h1
  unfold gibbsZ
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [neg_mul, neg_neg]

theorem gibbsDensity_ref {h : ℝ} (hh : 0 < h) (x : Torus 1) :
    gibbsDensity (fun x : Torus 1 => -h * cosHarm 3 x) x = referenceDensity h x := by
  unfold gibbsDensity referenceDensity
  rw [gibbsZ_ref hh]
  simp only [neg_mul, neg_neg]

theorem threefoldReference_eq_gibbs {h : ℝ} (hh : 0 < h) :
    threefoldReference h = gibbsMeasure (fun x : Torus 1 => -h * cosHarm 3 x) := by
  unfold threefoldReference gibbsMeasure
  simp only [gibbsDensity_ref hh]

theorem driftPot_ref {h ε : ℝ} (hh : 0 < h) :
    driftPot h ε (refProb hh : Measure (Torus 1)) = fun x : Torus 1 => -h * cosHarm 3 x := by
  obtain ⟨c0, s0, b0, -⟩ := elementaryFeatures_centered_independent hh
  funext x
  have hc : momC h (refProb hh : Measure (Torus 1)) = 0 := c0
  have hs : momS h (refProb hh : Measure (Torus 1)) = 0 := s0
  have hb : momB h (refProb hh : Measure (Torus 1)) = 0 := b0
  simp only [driftPot, hc, hs, hb]
  ring

theorem refProb_stationary {h ε : ℝ} (hh : 0 < h) :
    IsCircleDistributionalStationary (modelData h ε) (refProb hh) := by
  rw [stationary_iff_gibbs, driftPot_ref hh]
  exact threefoldReference_eq_gibbs hh

/-! ### Uniqueness -/

theorem integral_gibbsMeasure_eq {U : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) (g : Torus 1 → ℝ) :
    ∫ x, g x ∂gibbsMeasure U = ∫ x, gibbsDensity U x * g x ∂haar 1 := by
  unfold gibbsMeasure
  exact circ_withDensity_integral (haar 1) (q := gibbsDensity U)
    (continuous_gibbsDensity hU).measurable (fun x => (gibbsDensity_pos hU x).le) g

theorem integral_rho_sub_q {U V : Torus 1 → ℝ} (hU : IsSmoothPeriodic U) (hV : IsSmoothPeriodic V)
    {g : Torus 1 → ℝ} (hg : Continuous g) :
    ∫ x, (gibbsDensity U x - gibbsDensity V x) * g x ∂haar 1
      = ∫ x, g x ∂gibbsMeasure U - ∫ x, g x ∂gibbsMeasure V := by
  rw [integral_gibbsMeasure_eq hU, integral_gibbsMeasure_eq hV, ← integral_sub]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_mul]
  · exact integrable_of_continuous_torus ((continuous_gibbsDensity hU).mul hg)
  · exact integrable_of_continuous_torus ((continuous_gibbsDensity hV).mul hg)

theorem uniq_core {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h)
    (ν : ProbabilityMeasure (Torus 1))
    (hfix : (ν : Measure (Torus 1)) = gibbsMeasure (driftPot h ε (ν : Measure (Torus 1)))) :
    ν = refProb hh := by
  obtain ⟨c0, s0, b0, -⟩ := elementaryFeatures_centered_independent hh
  have hμeq : (refProb hh : Measure (Torus 1)) = gibbsMeasure (fun x : Torus 1 => -h * cosHarm 3 x) :=
    threefoldReference_eq_gibbs hh
  set Uν := driftPot h ε (ν : Measure (Torus 1)) with hUν
  set Uμ : Torus 1 → ℝ := fun x => -h * cosHarm 3 x with hUμ
  have sν : IsSmoothPeriodic Uν := isSmooth_driftPot h ε _
  have sμ : IsSmoothPeriodic Uμ := refPot_smooth h
  obtain ⟨a1, b1, ha1, hb1, hab1⟩ := gibbsDensity_bounds sν
  obtain ⟨a2, b2, ha2, hb2, hab2⟩ := gibbsDensity_bounds sμ
  have ha : 0 < min a1 a2 := lt_min ha1 ha2
  have hb : 0 < max b1 b2 := lt_max_of_lt_left hb1
  have hρ : ∀ x, min a1 a2 ≤ gibbsDensity Uν x ∧ gibbsDensity Uν x ≤ max b1 b2 := fun x =>
    ⟨(min_le_left _ _).trans (hab1 x).1, (hab1 x).2.trans (le_max_left _ _)⟩
  have hq : ∀ x, min a1 a2 ≤ gibbsDensity Uμ x ∧ gibbsDensity Uμ x ≤ max b1 b2 := fun x =>
    ⟨(min_le_right _ _).trans (hab2 x).1, (hab2 x).2.trans (le_max_right _ _)⟩
  have cρ := continuous_gibbsDensity sν
  have cq := continuous_gibbsDensity sμ
  have hsym := circ_sym_pinsker (haar 1) cρ.measurable cq.measurable ha hb hρ hq
    (integral_gibbsDensity sν) (integral_gibbsDensity sμ)
  -- moments
  set cb := momC h (ν : Measure (Torus 1)) with hcb
  set sb := momS h (ν : Measure (Torus 1)) with hsb
  set bb := momB h (ν : Measure (Torus 1)) with hbb
  set κ : ℝ := Real.log (gibbsZ Uμ) - Real.log (gibbsZ Uν) with hκ
  have hZν := gibbsZ_pos sν
  have hZμ := gibbsZ_pos sμ
  have hlog : ∀ x, Real.log (gibbsDensity Uν x) - Real.log (gibbsDensity Uμ x)
      = (-(ε * kAlpha * cb)) * featureC h x + (-(ε * kAlpha * sb)) * featureS h x
        + (ε * kBeta * bb) * featureB h x + κ := by
    intro x
    unfold gibbsDensity
    rw [Real.log_div (Real.exp_pos _).ne' hZν.ne', Real.log_div (Real.exp_pos _).ne' hZμ.ne',
      Real.log_exp, Real.log_exp, hκ]
    have : Uν x = Uμ x + ε * (kAlpha * (cb * featureC h x + sb * featureS h x)
        - kBeta * (bb * featureB h x)) := by
      simp only [hUν, hUμ, driftPot, hcb, hsb, hbb]
    rw [this]
    ring
  have hcont : Continuous fun x : Torus 1 =>
      (-(ε * kAlpha * cb)) * featureC h x + (-(ε * kAlpha * sb)) * featureS h x
        + (ε * kBeta * bb) * featureB h x + κ := by
    have := featureC_continuous h; have := featureS_continuous h; have := featureB_continuous h
    fun_prop
  have hrhs : ∫ x, (gibbsDensity Uν x - gibbsDensity Uμ x) *
        (Real.log (gibbsDensity Uν x) - Real.log (gibbsDensity Uμ x)) ∂haar 1
      = -(ε * kAlpha * (cb ^ 2 + sb ^ 2)) + ε * kBeta * bb ^ 2 := by
    simp only [hlog]
    rw [integral_rho_sub_q sν sμ hcont, ← hfix, hμeq.symm,
      integral_affine3 (ν : Measure (Torus 1)), integral_affine3 (refProb hh : Measure (Torus 1))]
    have e1 : momC h (refProb hh : Measure (Torus 1)) = 0 := c0
    have e2 : momS h (refProb hh : Measure (Torus 1)) = 0 := s0
    have e3 : momB h (refProb hh : Measure (Torus 1)) = 0 := b0
    rw [e1, e2, e3]
    ring
  -- bound on b̄
  set T : ℝ := ∫ x, |gibbsDensity Uν x - gibbsDensity Uμ x| ∂haar 1 with hT
  have hT0 : 0 ≤ T := integral_nonneg fun x => abs_nonneg _
  have hbbar : bb = ∫ x, (gibbsDensity Uν x - gibbsDensity Uμ x) * featureB h x ∂haar 1 := by
    rw [integral_rho_sub_q sν sμ (featureB_continuous h), ← hfix, ← hμeq]
    have e3 : ∫ x, featureB h x ∂(refProb hh : Measure (Torus 1)) = 0 := b0
    rw [e3]; simp [hbb, momB]
  have hbnd : |bb| ≤ featureBBound h * T := by
    rw [hbbar]
    have hB : ∀ x, |featureB h x| ≤ featureBBound h := fun x => by
      have := BoundedContinuousFunction.norm_coe_le_norm (bBCF h) x
      simpa [featureBBound, bBCF, Real.norm_eq_abs] using this
    have ic : Continuous fun x => (gibbsDensity Uν x - gibbsDensity Uμ x) * featureB h x :=
      (cρ.sub cq).mul (featureB_continuous h)
    calc |∫ x, (gibbsDensity Uν x - gibbsDensity Uμ x) * featureB h x ∂haar 1|
        ≤ ∫ x, |(gibbsDensity Uν x - gibbsDensity Uμ x) * featureB h x| ∂haar 1 :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, featureBBound h * |gibbsDensity Uν x - gibbsDensity Uμ x| ∂haar 1 := by
          refine integral_mono (integrable_of_continuous_torus ic.abs)
            (integrable_of_continuous_torus (continuous_const.mul (cρ.sub cq).abs)) fun x => ?_
          simp only
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      _ = featureBBound h * T := by rw [integral_const_mul]
  have hbsq : bb ^ 2 ≤ featureBBound h ^ 2 * T ^ 2 := by
    rw [← mul_pow, ← sq_abs bb]
    exact pow_le_pow_left₀ (abs_nonneg _) hbnd 2
  have hkey := eps_mul_lt hεmax
  have hα := kAlpha_pos
  have hβ := kBeta_pos
  have hpos : 0 ≤ ε * kAlpha * (cb ^ 2 + sb ^ 2) := by positivity
  rw [hrhs] at hsym
  have h2 : T ^ 2 ≤ ε * kBeta * (featureBBound h ^ 2 * T ^ 2) := by
    calc T ^ 2 ≤ -(ε * kAlpha * (cb ^ 2 + sb ^ 2)) + ε * kBeta * bb ^ 2 := hsym
      _ ≤ ε * kBeta * bb ^ 2 := by linarith
      _ ≤ _ := by gcongr
  have hT2 : T ^ 2 = 0 := by
    have : 0 ≤ T ^ 2 := sq_nonneg T
    nlinarith [mul_nonneg this (sub_nonneg.2 hkey.le)]
  have hT00 : T = 0 := by simpa using hT2
  have hae : (fun x => |gibbsDensity Uν x - gibbsDensity Uμ x|) =ᵐ[haar 1] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _)
      (integrable_of_continuous_torus (cρ.sub cq).abs)).1 hT00
  have hae2 : (fun x => ENNReal.ofReal (gibbsDensity Uν x)) =ᵐ[haar 1]
      fun x => ENNReal.ofReal (gibbsDensity Uμ x) := by
    filter_upwards [hae] with x hx
    have : gibbsDensity Uν x - gibbsDensity Uμ x = 0 := by simpa using hx
    rw [sub_eq_zero.1 this]
  apply Subtype.ext
  show (ν : Measure (Torus 1)) = (refProb hh : Measure (Torus 1))
  rw [hfix, hμeq]
  exact withDensity_congr_ae hae2

/-- **Unique stationary probability.** -/
theorem elementaryModel_uniqueStationary {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (ν : ProbabilityMeasure (Torus 1)) :
    IsCircleDistributionalStationary (modelData h ε) ν ↔ ν = refProb hh := by
  constructor
  · intro hs
    exact uniq_core hh hε hεmax ν ((stationary_iff_gibbs h ε ν).1 hs)
  · rintro rfl
    exact refProb_stationary hh


section StrictConvexity
open Real
open scoped ENNReal


/-! ### Strong convexity of the entropy integrand -/

theorem klFun_sub_sq_convexOn {M : ℝ} (hM : 0 < M) :
    ConvexOn ℝ (Set.Icc 0 M) (fun u => klFun u - (1 / (2 * M)) * u ^ 2) := by
  have hderiv : ∀ u : ℝ, u ≠ 0 →
      HasDerivAt (fun u => klFun u - (1 / (2 * M)) * u ^ 2) (Real.log u - u / M) u := by
    intro u hu
    have h1 := hasDerivAt_klFun hu
    have h2 := ((hasDerivAt_pow 2 u).const_mul (1 / (2 * M)))
    convert h1.sub h2 using 1
    field_simp
    ring
  refine MonotoneOn.convexOn_of_deriv (convex_Icc 0 M) ?_ ?_ ?_
  · exact (continuous_klFun.sub (continuous_const.mul (continuous_pow 2))).continuousOn
  · rw [interior_Icc]
    intro u hu
    exact (hderiv u hu.1.ne').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro u hu v hv huv
    rw [(hderiv u hu.1.ne').deriv, (hderiv v hv.1.ne').deriv]
    have h1 : 1 - (v / u)⁻¹ ≤ Real.log (v / u) := Real.one_sub_inv_le_log_of_pos (div_pos hv.1 hu.1)
    rw [Real.log_div hv.1.ne' hu.1.ne', inv_div] at h1
    have h2 : (v - u) / M ≤ 1 - u / v := by
      rw [show 1 - u / v = (v - u) / v by field_simp [hv.1.ne']]
      exact div_le_div_of_nonneg_left (by linarith) hv.1 hv.2.le
    have : v / M - u / M = (v - u) / M := by ring
    linarith

theorem klFun_mix_gap {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hM : 0 < a + b) :
    t * (1 - t) * (a - b) ^ 2 * (1 / (2 * (a + b)))
      ≤ (1 - t) * klFun a + t * klFun b - klFun ((1 - t) * a + t * b) := by
  have hc := (klFun_sub_sq_convexOn hM).2 (x := a) (y := b)
    ⟨ha, by linarith⟩ ⟨hb, by linarith⟩ (by linarith : 0 ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at hc
  nlinarith [hc]

theorem klFun_mix_gap_lam {a b t lam : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1 - t) / 2 * (2 * lam * |a - b| - lam ^ 2 * (a + b))
      ≤ (1 - t) * klFun a + t * klFun b - klFun ((1 - t) * a + t * b) := by
  rcases (add_nonneg ha hb).eq_or_lt with h0 | hM
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0; subst hb0
    simp [klFun_zero]
  · have hg := klFun_mix_gap ha hb ht0 ht1 hM
    refine le_trans ?_ hg
    have hq : 0 < 1 / (2 * (a + b)) := by positivity
    have hkey : 2 * lam * |a - b| - lam ^ 2 * (a + b) ≤ (a - b) ^ 2 * (1 / (a + b)) := by
      have : 0 ≤ (|a - b| - lam * (a + b)) ^ 2 := sq_nonneg _
      have hsq : (a - b) ^ 2 = |a - b| ^ 2 := (sq_abs _).symm
      rw [hsq]
      have e : |a - b| ^ 2 * (1 / (a + b)) - (2 * lam * |a - b| - lam ^ 2 * (a + b))
          = (|a - b| - lam * (a + b)) ^ 2 * (1 / (a + b)) := by
        field_simp; ring
      have : 0 ≤ (|a - b| - lam * (a + b)) ^ 2 * (1 / (a + b)) := by positivity
      linarith
    have ht : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
    have e2 : t * (1 - t) * (a - b) ^ 2 * (1 / (2 * (a + b)))
        = t * (1 - t) / 2 * ((a - b) ^ 2 * (1 / (a + b))) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)


/-! ### Integrated strong convexity of relative entropy along a mixture -/

theorem integrable_of_lintegral_ofReal_ne_top {α : Type*} [MeasurableSpace α] {P : Measure α}
    {g : α → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x)
    (h : ∫⁻ x, ENNReal.ofReal (g x) ∂P ≠ ⊤) : Integrable g P := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp only [Real.enorm_eq_ofReal (h0 _)]
  exact lt_top_iff_ne_top.2 h

theorem toReal_lintegral_ofReal_eq {α : Type*} [MeasurableSpace α] {P : Measure α}
    {g : α → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂P).toReal = ∫ x, g x ∂P :=
  (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0)
    hg.aestronglyMeasurable).symm

theorem mix_entropy_bound {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {f₀ f₁ : α → ℝ} (m0 : Measurable f₀) (m1 : Measurable f₁)
    (n0 : ∀ x, 0 ≤ f₀ x) (n1 : ∀ x, 0 ≤ f₁ x)
    (i0 : Integrable f₀ P) (i1 : Integrable f₁ P)
    (k0 : ∫⁻ x, ENNReal.ofReal (klFun (f₀ x)) ∂P ≠ ⊤)
    (k1 : ∫⁻ x, ENNReal.ofReal (klFun (f₁ x)) ∂P ≠ ⊤)
    (e0 : ∫ x, f₀ x ∂P = 1) (e1 : ∫ x, f₁ x ∂P = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (klFun ((1 - t) * f₀ x + t * f₁ x)) ∂P ≠ ⊤ ∧
    (∫⁻ x, ENNReal.ofReal (klFun ((1 - t) * f₀ x + t * f₁ x)) ∂P).toReal
      ≤ (1 - t) * (∫⁻ x, ENNReal.ofReal (klFun (f₀ x)) ∂P).toReal
        + t * (∫⁻ x, ENNReal.ofReal (klFun (f₁ x)) ∂P).toReal
        - t * (1 - t) * (∫ x, |f₀ x - f₁ x| ∂P) ^ 2 / 4 := by
  have mK0 : Measurable fun x => klFun (f₀ x) := measurable_klFun.comp m0
  have mK1 : Measurable fun x => klFun (f₁ x) := measurable_klFun.comp m1
  have nK0 : ∀ x, 0 ≤ klFun (f₀ x) := fun x => klFun_nonneg (n0 x)
  have nK1 : ∀ x, 0 ≤ klFun (f₁ x) := fun x => klFun_nonneg (n1 x)
  have iK0 := integrable_of_lintegral_ofReal_ne_top mK0 nK0 k0
  have iK1 := integrable_of_lintegral_ofReal_ne_top mK1 nK1 k1
  set ft : α → ℝ := fun x => (1 - t) * f₀ x + t * f₁ x with hft
  have mft : Measurable ft := (m0.const_mul _).add (m1.const_mul _)
  have nft : ∀ x, 0 ≤ ft x := fun x => by
    simp only [hft]
    have := n0 x; have := n1 x
    have h1 : 0 ≤ 1 - t := by linarith
    positivity
  have mKt : Measurable fun x => klFun (ft x) := measurable_klFun.comp mft
  have nKt : ∀ x, 0 ≤ klFun (ft x) := fun x => klFun_nonneg (nft x)
  have hgap0 : ∀ x, klFun (ft x) ≤ (1 - t) * klFun (f₀ x) + t * klFun (f₁ x) := fun x => by
    have := klFun_mix_gap_lam (n0 x) (n1 x) ht0 ht1 (lam := 0)
    simp only [hft]
    simpa using this
  have iKt : Integrable (fun x => klFun (ft x)) P := by
    refine Integrable.mono' ((iK0.const_mul (1 - t)).add (iK1.const_mul t)) mKt.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (nKt x)]
    exact hgap0 x
  have hfin : ∫⁻ x, ENNReal.ofReal (klFun (ft x)) ∂P ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal iKt (Filter.Eventually.of_forall nKt)]
    exact ENNReal.ofReal_ne_top
  refine ⟨hfin, ?_⟩
  rw [toReal_lintegral_ofReal_eq mKt nKt, toReal_lintegral_ofReal_eq mK0 nK0,
    toReal_lintegral_ofReal_eq mK1 nK1]
  -- the integrated gap
  set T : ℝ := ∫ x, |f₀ x - f₁ x| ∂P with hT
  have iabs : Integrable (fun x => |f₀ x - f₁ x|) P := (i0.sub i1).abs
  have hT0 : 0 ≤ T := integral_nonneg fun x => abs_nonneg _
  set lam : ℝ := T / 2 with hlam
  set c : ℝ := t * (1 - t) / 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  have iG : Integrable (fun x => (1 - t) * klFun (f₀ x) + t * klFun (f₁ x) - klFun (ft x)) P :=
    ((iK0.const_mul (1 - t)).add (iK1.const_mul t)).sub iKt
  have iR : Integrable (fun x => c * (2 * lam * |f₀ x - f₁ x| - lam ^ 2 * (f₀ x + f₁ x))) P :=
    (((iabs.const_mul (2 * lam)).sub ((i0.add i1).const_mul (lam ^ 2)))).const_mul c
  have hmono : ∫ x, c * (2 * lam * |f₀ x - f₁ x| - lam ^ 2 * (f₀ x + f₁ x)) ∂P
      ≤ ∫ x, ((1 - t) * klFun (f₀ x) + t * klFun (f₁ x) - klFun (ft x)) ∂P :=
    integral_mono iR iG fun x => by
      simpa [hc, hft] using klFun_mix_gap_lam (lam := lam) (n0 x) (n1 x) ht0 ht1
  have hRint : ∫ x, c * (2 * lam * |f₀ x - f₁ x| - lam ^ 2 * (f₀ x + f₁ x)) ∂P
      = c * (2 * lam * T - lam ^ 2 * 2) := by
    have j1 : Integrable (fun x => 2 * lam * |f₀ x - f₁ x|) P := iabs.const_mul _
    have j2 : Integrable (fun x => lam ^ 2 * (f₀ x + f₁ x)) P := (i0.add i1).const_mul _
    rw [integral_const_mul, integral_sub j1 j2, integral_const_mul, integral_const_mul,
      integral_add i0 i1, e0, e1]
    ring
  have hGint : ∫ x, ((1 - t) * klFun (f₀ x) + t * klFun (f₁ x) - klFun (ft x)) ∂P
      = (1 - t) * ∫ x, klFun (f₀ x) ∂P + t * ∫ x, klFun (f₁ x) ∂P - ∫ x, klFun (ft x) ∂P := by
    have j1 : Integrable (fun x => (1 - t) * klFun (f₀ x)) P := iK0.const_mul _
    have j2 : Integrable (fun x => t * klFun (f₁ x)) P := iK1.const_mul _
    have j3 : Integrable (fun x => (1 - t) * klFun (f₀ x) + t * klFun (f₁ x)) P := j1.add j2
    rw [integral_sub j3 iKt, integral_add j1 j2, integral_const_mul, integral_const_mul]
  rw [hRint, hGint] at hmono
  have : c * (2 * lam * T - lam ^ 2 * 2) = t * (1 - t) * T ^ 2 / 4 := by
    simp only [hc, hlam]; ring
  linarith


/-! ### Densities of finite-entropy probabilities on the circle -/

/-- The mixture `(1-t) ν₀ + t ν₁` of two probabilities. -/
noncomputable def circMix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : ProbabilityMeasure (Torus 1) :=
  ⟨ENNReal.ofReal (1 - t) • (ν₀ : Measure (Torus 1)) + ENNReal.ofReal t • (ν₁ : Measure (Torus 1)),
    ⟨by
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (by linarith) ht0]
      simp⟩⟩

theorem coe_circMix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ν₀ ν₁ : ProbabilityMeasure (Torus 1)) :
    ((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
      = ENNReal.ofReal (1 - t) • (ν₀ : Measure (Torus 1)) + ENNReal.ofReal t • (ν₁ : Measure (Torus 1)) :=
  rfl

/-- The real density of `ν` with respect to Haar measure. -/
noncomputable def dens (ν : Measure (Torus 1)) (x : Torus 1) : ℝ := (ν.rnDeriv (haar 1) x).toReal

theorem ac_of_entropy_ne_top {ν : Measure (Torus 1)} (h : relativeEntropy ν (haar 1) ≠ ⊤) :
    ν ≪ haar 1 := by
  by_contra hn
  exact h (relativeEntropy_of_not_absolutelyContinuous hn)

theorem measurable_dens (ν : Measure (Torus 1)) : Measurable (dens ν) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem dens_nonneg (ν : Measure (Torus 1)) (x : Torus 1) : 0 ≤ dens ν x := ENNReal.toReal_nonneg

theorem integrable_dens (ν : Measure (Torus 1)) [IsFiniteMeasure ν] : Integrable (dens ν) (haar 1) :=
  Measure.integrable_toReal_rnDeriv

theorem integral_dens (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (hac : ν ≪ haar 1) :
    ∫ x, dens ν x ∂haar 1 = 1 := by
  unfold dens
  rw [Measure.integral_toReal_rnDeriv hac]
  simp

theorem withDensity_dens (ν : Measure (Torus 1)) [IsFiniteMeasure ν] (hac : ν ≪ haar 1) :
    (haar 1).withDensity (fun x => ENNReal.ofReal (dens ν x)) = ν := by
  calc (haar 1).withDensity (fun x => ENNReal.ofReal (dens ν x))
      = (haar 1).withDensity (ν.rnDeriv (haar 1)) := by
        refine withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top ν (haar 1)] with x hx
        exact ENNReal.ofReal_toReal hx.ne
    _ = ν := Measure.withDensity_rnDeriv_eq ν (haar 1) hac

theorem entropy_eq_dens (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (hac : ν ≪ haar 1) :
    relativeEntropy ν (haar 1) = ∫⁻ x, ENNReal.ofReal (klFun (dens ν x)) ∂haar 1 := by
  rw [Analysis.relativeEntropy_eq_klDiv, klDiv_eq_lintegral_klFun_of_ac hac]
  rfl

/-- The density of a mixture is the mixture of the densities. -/
theorem circMix_eq_withDensity (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ν₀ ν₁ : ProbabilityMeasure (Torus 1))
    (h0 : (ν₀ : Measure (Torus 1)) ≪ haar 1) (h1 : (ν₁ : Measure (Torus 1)) ≪ haar 1) :
    ((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
      = (haar 1).withDensity (fun x =>
        ENNReal.ofReal ((1 - t) * dens ν₀ x + t * dens ν₁ x)) := by
  have hm0 : Measurable fun x => ENNReal.ofReal (dens ν₀ x) := (measurable_dens _).ennreal_ofReal
  have hm1 : Measurable fun x => ENNReal.ofReal (dens ν₁ x) := (measurable_dens _).ennreal_ofReal
  have hfun : (fun x => ENNReal.ofReal ((1 - t) * dens ν₀ x + t * dens ν₁ x))
      = ENNReal.ofReal (1 - t) • (fun x => ENNReal.ofReal (dens ν₀ x))
        + ENNReal.ofReal t • (fun x => ENNReal.ofReal (dens ν₁ x)) := by
    funext x
    have : 0 ≤ 1 - t := by linarith
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_add (mul_nonneg this (dens_nonneg _ _)) (mul_nonneg ht0 (dens_nonneg _ _)),
      ENNReal.ofReal_mul this, ENNReal.ofReal_mul ht0]
  rw [hfun, withDensity_add_left (hm0.const_smul _), withDensity_smul _ hm0,
    withDensity_smul _ hm1, withDensity_dens _ h0, withDensity_dens _ h1, coe_circMix]


/-! ### The real part of the free energy in moment form -/

theorem integral_affine3_add {h : ℝ} (ν : Measure (Torus 1)) [IsProbabilityMeasure ν]
    (a1 a2 a3 e κ : ℝ) :
    ∫ y, (a1 * featureC h y + a2 * featureS h y + a3 * featureB h y + e + κ * kernelK h y y) ∂ν
      = a1 * momC h ν + a2 * momS h ν + a3 * momB h ν + e + κ * ∫ y, kernelK h y y ∂ν := by
  have ia : Integrable (fun y => a1 * featureC h y + a2 * featureS h y + a3 * featureB h y + e) ν := by
    have hc : Continuous (fun y => a1 * featureC h y + a2 * featureS h y + a3 * featureB h y + e) := by
      have := featureC_continuous h; have := featureS_continuous h; have := featureB_continuous h
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ik : Integrable (fun y => κ * kernelK h y y) ν :=
    ((continuous_const.mul (continuous_kernelK_diag h))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add ia ik, integral_affine3, integral_const_mul]

theorem energy_formula (h ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    potentialEnergy (modelData h ε) ν + (1 / 2 : ℝ) * interactionEnergy (modelData h ε) ν
      = -h * ∫ x, cosHarm 3 x ∂(ν : Measure (Torus 1))
        + ε / 2 * (kAlpha * (momC h ν ^ 2 + momS h ν ^ 2) - kBeta * momB h ν ^ 2) := by
  set D : ℝ := ∫ y, kernelK h y y ∂(ν : Measure (Torus 1)) with hD
  have hpot : potentialEnergy (modelData h ε) ν
      = -h * ∫ x, cosHarm 3 x ∂(ν : Measure (Torus 1)) + ε / 2 * D := by
    unfold potentialEnergy
    simp only [modelData_V, modelV]
    have i1 : Integrable (fun x => -h * cosHarm 3 x) (ν : Measure (Torus 1)) :=
      (continuous_const.mul (continuous_cosHarm 3)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have i2 : Integrable (fun x => ε / 2 * kernelK h x x) (ν : Measure (Torus 1)) :=
      (continuous_const.mul (continuous_kernelK_diag h)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
  have hinner : ∀ y : Torus 1, ∫ x, modelW h ε x y ∂(ν : Measure (Torus 1))
      = (ε * kAlpha * momC h ν) * featureC h y + (ε * kAlpha * momS h ν) * featureS h y
        + (-(ε * kBeta * momB h ν)) * featureB h y + (-ε / 2 * D) + (-ε / 2) * kernelK h y y := by
    intro y
    have hpt : ∀ x : Torus 1, modelW h ε x y
        = (ε * kAlpha * featureC h y) * featureC h x + (ε * kAlpha * featureS h y) * featureS h x
          + (-(ε * kBeta * featureB h y)) * featureB h x + (-ε / 2 * kernelK h y y)
          + (-ε / 2) * kernelK h x x := by
      intro x; unfold modelW kernelK; ring
    simp_rw [hpt]
    rw [integral_affine3_add]
    ring
  have hint : interactionEnergy (modelData h ε) ν
      = ε * kAlpha * momC h ν ^ 2 + ε * kAlpha * momS h ν ^ 2 - ε * kBeta * momB h ν ^ 2 - ε * D := by
    rw [interactionEnergy_eq_iterated]
    simp only [modelData_W]
    simp_rw [hinner]
    rw [integral_affine3_add]
    ring
  rw [hpot, hint]
  ring


/-! ### Moments of mixtures and the real value of the free energy -/

theorem integral_circMix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ν₀ ν₁ : ProbabilityMeasure (Torus 1))
    {g : Torus 1 → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
      = (1 - t) * ∫ x, g x ∂(ν₀ : Measure (Torus 1)) + t * ∫ x, g x ∂(ν₁ : Measure (Torus 1)) := by
  have i0 : Integrable g (ν₀ : Measure (Torus 1)) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i1 : Integrable g (ν₁ : Measure (Torus 1)) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [coe_circMix, integral_add_measure (i0.smul_measure ENNReal.ofReal_ne_top)
    (i1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ht0]
  simp

theorem freeEnergy_eq_real (A : DGPS.InteractionData 1) (ν : ProbabilityMeasure (Torus 1))
    (hH : relativeEntropy (ν : Measure (Torus 1)) (haar 1) ≠ ⊤) :
    freeEnergy A ν = (((relativeEntropy (ν : Measure (Torus 1)) (haar 1)).toReal
      + (potentialEnergy A ν + (1 / 2 : ℝ) * interactionEnergy A ν) : ℝ) : EReal) := by
  unfold freeEnergy
  rw [← EReal.coe_ennreal_toReal hH, ← EReal.coe_add, ← EReal.coe_add, add_assoc]

theorem integral_dens_mul (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (hac : ν ≪ haar 1)
    {g : Torus 1 → ℝ} (hg : Continuous g) :
    Integrable (fun x => dens ν x * g x) (haar 1) ∧
      ∫ x, g x ∂ν = ∫ x, dens ν x * g x ∂haar 1 := by
  have hint : Integrable g ν :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  constructor
  · have : Integrable g ((haar 1).withDensity fun x => ENNReal.ofReal (dens ν x)) := by
      rw [withDensity_dens ν hac]; exact hint
    exact (circ_withDensity_integrable (haar 1) (measurable_dens ν) (dens_nonneg ν)).1 this
  · have hν : ν = (haar 1).withDensity fun x => ENNReal.ofReal (dens ν x) :=
      (withDensity_dens ν hac).symm
    conv_lhs => rw [hν]
    exact circ_withDensity_integral (haar 1) (measurable_dens ν) (dens_nonneg ν) g

theorem abs_momB_sub_le {h : ℝ} (ν₀ ν₁ : ProbabilityMeasure (Torus 1))
    (h0 : (ν₀ : Measure (Torus 1)) ≪ haar 1) (h1 : (ν₁ : Measure (Torus 1)) ≪ haar 1) :
    |momB h ν₁ - momB h ν₀|
      ≤ featureBBound h * ∫ x, |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x| ∂haar 1 := by
  obtain ⟨j0, e0⟩ := integral_dens_mul (ν₀ : Measure (Torus 1)) h0 (featureB_continuous h)
  obtain ⟨j1, e1⟩ := integral_dens_mul (ν₁ : Measure (Torus 1)) h1 (featureB_continuous h)
  have hB : ∀ x, |featureB h x| ≤ featureBBound h := fun x => by
    have := BoundedContinuousFunction.norm_coe_le_norm (bBCF h) x
    simpa [featureBBound, bBCF, Real.norm_eq_abs] using this
  have hdiff : momB h ν₁ - momB h ν₀
      = ∫ x, (dens (ν₁ : Measure (Torus 1)) x - dens (ν₀ : Measure (Torus 1)) x) * featureB h x ∂haar 1 := by
    simp only [momB]
    rw [e0, e1, ← integral_sub j1 j0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have ic : Integrable (fun x => (dens (ν₁ : Measure (Torus 1)) x - dens (ν₀ : Measure (Torus 1)) x)
      * featureB h x) (haar 1) := by
    have : (fun x => (dens (ν₁ : Measure (Torus 1)) x - dens (ν₀ : Measure (Torus 1)) x) * featureB h x)
        = fun x => dens (ν₁ : Measure (Torus 1)) x * featureB h x
          - dens (ν₀ : Measure (Torus 1)) x * featureB h x := by funext x; ring
    rw [this]; exact j1.sub j0
  have iabs : Integrable (fun x => |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x|)
      (haar 1) := ((integrable_dens _).sub (integrable_dens _)).abs
  rw [hdiff]
  calc |∫ x, (dens (ν₁ : Measure (Torus 1)) x - dens (ν₀ : Measure (Torus 1)) x) * featureB h x ∂haar 1|
      ≤ ∫ x, |(dens (ν₁ : Measure (Torus 1)) x - dens (ν₀ : Measure (Torus 1)) x) * featureB h x| ∂haar 1 :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, featureBBound h * |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x| ∂haar 1 := by
        refine integral_mono ic.abs (iabs.const_mul _) fun x => ?_
        simp only
        rw [abs_mul, abs_sub_comm, mul_comm]
        exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
    _ = _ := by rw [integral_const_mul]


/-! ### Strict mixture convexity -/

theorem mix_relEntropy_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ν₀ ν₁ : ProbabilityMeasure (Torus 1))
    (H0 : relativeEntropy (ν₀ : Measure (Torus 1)) (haar 1) ≠ ⊤)
    (H1 : relativeEntropy (ν₁ : Measure (Torus 1)) (haar 1) ≠ ⊤) :
    relativeEntropy ((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
        (haar 1) ≠ ⊤ ∧
      (relativeEntropy ((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
        (haar 1)).toReal
      ≤ (1 - t) * (relativeEntropy (ν₀ : Measure (Torus 1)) (haar 1)).toReal
        + t * (relativeEntropy (ν₁ : Measure (Torus 1)) (haar 1)).toReal
        - t * (1 - t) * (∫ x, |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x| ∂haar 1) ^ 2 / 4 := by
  have h0 := ac_of_entropy_ne_top H0
  have h1 := ac_of_entropy_ne_top H1
  have e0 := entropy_eq_dens (ν₀ : Measure (Torus 1)) h0
  have e1 := entropy_eq_dens (ν₁ : Measure (Torus 1)) h1
  have k0 : ∫⁻ x, ENNReal.ofReal (klFun (dens (ν₀ : Measure (Torus 1)) x)) ∂haar 1 ≠ ⊤ := e0 ▸ H0
  have k1 : ∫⁻ x, ENNReal.ofReal (klFun (dens (ν₁ : Measure (Torus 1)) x)) ∂haar 1 ≠ ⊤ := e1 ▸ H1
  obtain ⟨hne, hle⟩ := mix_entropy_bound (haar 1) (measurable_dens _) (measurable_dens _)
    (dens_nonneg _) (dens_nonneg _) (integrable_dens _) (integrable_dens _) k0 k1
    (integral_dens _ h0) (integral_dens _ h1) ht0 ht1
  have hmix := circMix_eq_withDensity t ht0 ht1 ν₀ ν₁ h0 h1
  have hmeas : Measurable fun x => (1 - t) * dens (ν₀ : Measure (Torus 1)) x
      + t * dens (ν₁ : Measure (Torus 1)) x :=
    ((measurable_dens _).const_mul _).add ((measurable_dens _).const_mul _)
  have hnn : ∀ x, 0 ≤ (1 - t) * dens (ν₀ : Measure (Torus 1)) x + t * dens (ν₁ : Measure (Torus 1)) x :=
    fun x => add_nonneg (mul_nonneg (by linarith) (dens_nonneg _ _)) (mul_nonneg ht0 (dens_nonneg _ _))
  have hac : ((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) ≪ haar 1 := by
    rw [hmix]; exact withDensity_absolutelyContinuous _ _
  have hd : (fun x => dens ((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) x)
      =ᵐ[haar 1] fun x => (1 - t) * dens (ν₀ : Measure (Torus 1)) x + t * dens (ν₁ : Measure (Torus 1)) x := by
    have := Measure.rnDeriv_withDensity (haar 1) (hmeas.ennreal_ofReal)
    rw [← hmix] at this
    filter_upwards [this] with x hx
    rw [dens, hx, ENNReal.toReal_ofReal (hnn x)]
  have hent : relativeEntropy ((circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
      (haar 1) = ∫⁻ x, ENNReal.ofReal (klFun ((1 - t) * dens (ν₀ : Measure (Torus 1)) x
        + t * dens (ν₁ : Measure (Torus 1)) x)) ∂haar 1 := by
    rw [entropy_eq_dens _ hac]
    refine lintegral_congr_ae ?_
    filter_upwards [hd] with x hx
    rw [hx]
  rw [hent]
  refine ⟨hne, ?_⟩
  rw [e0, e1]
  exact hle

theorem energy_mix {h ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ν₀ ν₁ : ProbabilityMeasure (Torus 1)) :
    potentialEnergy (modelData h ε) (circMix t ht0 ht1 ν₀ ν₁)
        + (1 / 2 : ℝ) * interactionEnergy (modelData h ε) (circMix t ht0 ht1 ν₀ ν₁)
      ≤ (1 - t) * (potentialEnergy (modelData h ε) ν₀ + (1 / 2 : ℝ) * interactionEnergy (modelData h ε) ν₀)
        + t * (potentialEnergy (modelData h ε) ν₁ + (1 / 2 : ℝ) * interactionEnergy (modelData h ε) ν₁)
        + ε / 2 * kBeta * (t * (1 - t) * (momB h ν₁ - momB h ν₀) ^ 2) := by
  rw [energy_formula, energy_formula, energy_formula]
  have mc : momC h (circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1))
      = (1 - t) * momC h ν₀ + t * momC h ν₁ := integral_circMix t ht0 ht1 ν₀ ν₁ (featureC_continuous h)
  have ms : momS h (circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1))
      = (1 - t) * momS h ν₀ + t * momS h ν₁ := integral_circMix t ht0 ht1 ν₀ ν₁ (featureS_continuous h)
  have mb : momB h (circMix t ht0 ht1 ν₀ ν₁ : ProbabilityMeasure (Torus 1))
      = (1 - t) * momB h ν₀ + t * momB h ν₁ := integral_circMix t ht0 ht1 ν₀ ν₁ (featureB_continuous h)
  have m3 := integral_circMix t ht0 ht1 ν₀ ν₁ (continuous_cosHarm 3)
  rw [mc, ms, mb, m3]
  have hε2 : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have hk := kAlpha_pos
  have hc : 0 ≤ ε / 2 * kAlpha * (t * (1 - t) * ((momC h ν₁ - momC h ν₀) ^ 2
      + (momS h ν₁ - momS h ν₀) ^ 2)) := by positivity
  nlinarith [hc]

theorem dens_L1_pos (ν₀ ν₁ : ProbabilityMeasure (Torus 1)) (h0 : (ν₀ : Measure (Torus 1)) ≪ haar 1)
    (h1 : (ν₁ : Measure (Torus 1)) ≪ haar 1) (hne : ν₀ ≠ ν₁) :
    0 < ∫ x, |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x| ∂haar 1 := by
  have iabs : Integrable (fun x => |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x|)
      (haar 1) := ((integrable_dens _).sub (integrable_dens _)).abs
  rcases (integral_nonneg fun x => abs_nonneg _ : 0 ≤ ∫ x, |dens (ν₀ : Measure (Torus 1)) x
      - dens (ν₁ : Measure (Torus 1)) x| ∂haar 1).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) iabs).1 h.symm
    have hae : (fun x => ENNReal.ofReal (dens (ν₀ : Measure (Torus 1)) x))
        =ᵐ[haar 1] fun x => ENNReal.ofReal (dens (ν₁ : Measure (Torus 1)) x) := by
      filter_upwards [hz] with x hx
      have : dens (ν₀ : Measure (Torus 1)) x = dens (ν₁ : Measure (Torus 1)) x := by
        have h' : |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x| = 0 := hx
        have := abs_eq_zero.1 h'
        linarith
      rw [this]
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [← withDensity_dens _ h0, ← withDensity_dens _ h1]
    exact withDensity_congr_ae hae

/-- Local version of the interface predicate `StrictMixtureConvexFreeEnergy` (definitions.md §7):
for distinct probabilities with finite free energy and `0 < t < 1`, the free energy of the
mixture is strictly below the convex combination of the two (finite, real) values. -/
def CircleStrictMixtureConvexFreeEnergy (A : DGPS.InteractionData 1) : Prop :=
  ∀ (ν₀ ν₁ : ProbabilityMeasure (Torus 1)), ν₀ ≠ ν₁ →
    ∀ (hf0 : FiniteFreeEnergy A ν₀) (hf1 : FiniteFreeEnergy A ν₁)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
      freeEnergy A (circMix t ht0.le ht1.le ν₀ ν₁)
        < (((1 - t) * freeEnergyValue A ν₀ hf0 + t * freeEnergyValue A ν₁ hf1 : ℝ) : EReal)

/-- **Strict convexity of the free energy along probability mixtures.** -/
theorem elementaryModel_strictConvexity {h ε : ℝ} (hε : 0 < ε) (hεmax : ε < epsMax h) :
    CircleStrictMixtureConvexFreeEnergy (modelData h ε) := by
  intro ν₀ ν₁ hne hf0 hf1 t ht0 ht1
  have H0 := (finiteFreeEnergy_iff _ _).1 hf0
  have H1 := (finiteFreeEnergy_iff _ _).1 hf1
  have h0 := ac_of_entropy_ne_top H0
  have h1 := ac_of_entropy_ne_top H1
  obtain ⟨Hm, hbound⟩ := mix_relEntropy_bound t ht0.le ht1.le ν₀ ν₁ H0 H1
  have hT := dens_L1_pos ν₀ ν₁ h0 h1 hne
  set T := ∫ x, |dens (ν₀ : Measure (Torus 1)) x - dens (ν₁ : Measure (Torus 1)) x| ∂haar 1 with hTdef
  have hB := abs_momB_sub_le (h := h) ν₀ ν₁ h0 h1
  have hEn := energy_mix (h := h) hε.le t ht0.le ht1.le ν₀ ν₁
  have hkey := eps_mul_lt hεmax
  have hfe0 : freeEnergyValue (modelData h ε) ν₀ hf0 = (relativeEntropy (ν₀ : Measure (Torus 1)) (haar 1)).toReal
      + (potentialEnergy (modelData h ε) ν₀ + (1 / 2 : ℝ) * interactionEnergy (modelData h ε) ν₀) := by
    unfold freeEnergyValue; rw [freeEnergy_eq_real _ _ H0]; rfl
  have hfe1 : freeEnergyValue (modelData h ε) ν₁ hf1 = (relativeEntropy (ν₁ : Measure (Torus 1)) (haar 1)).toReal
      + (potentialEnergy (modelData h ε) ν₁ + (1 / 2 : ℝ) * interactionEnergy (modelData h ε) ν₁) := by
    unfold freeEnergyValue; rw [freeEnergy_eq_real _ _ H1]; rfl
  rw [freeEnergy_eq_real _ _ Hm]
  rw [EReal.coe_lt_coe_iff]
  rw [hfe0, hfe1]
  have hΔ : (momB h ν₁ - momB h ν₀) ^ 2 ≤ featureBBound h ^ 2 * T ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.1 hB, mul_nonneg (by unfold featureBBound; positivity : 0 ≤ featureBBound h) hT.le]) (abs_le.1 hB).2
    nlinarith [sq_abs (momB h ν₁ - momB h ν₀), abs_nonneg (momB h ν₁ - momB h ν₀),
      mul_nonneg (by unfold featureBBound; positivity : 0 ≤ featureBBound h) hT.le]
  have htt : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have hq : ε / 2 * kBeta * (t * (1 - t) * (momB h ν₁ - momB h ν₀) ^ 2)
      ≤ ε / 2 * kBeta * (t * (1 - t) * (featureBBound h ^ 2 * T ^ 2)) := by
    have := kBeta_pos
    gcongr
  have hfin : ε / 2 * kBeta * (t * (1 - t) * (featureBBound h ^ 2 * T ^ 2)) < t * (1 - t) * T ^ 2 / 4 := by
    have hT2 : 0 < t * (1 - t) * T ^ 2 := mul_pos htt (pow_pos hT 2)
    nlinarith [mul_lt_mul_of_pos_right hkey hT2]
  nlinarith [hbound, hEn, hq, hfin]


end StrictConvexity

end DGPS.Examples.ThreeSpeciesCircle
